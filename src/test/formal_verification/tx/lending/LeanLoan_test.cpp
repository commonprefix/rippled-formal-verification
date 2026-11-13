#include <test/formal_verification/common/LeanSuite.h>
#include <test/formal_verification/ffi/lending/LoanFFI.h>
#include <test/formal_verification/tx/lending/LendingTestHelpers.h>
#include <test/jtx/Env.h>

#include <xrpl/basics/Number.h>
#include <xrpl/ledger/OpenView.h>
#include <xrpl/protocol/TER.h>

#include <cstdint>
#include <optional>
#include <span>
#include <string>

namespace xrpl::test::formal_verification {

// One loan field set to `value`: C++ LoanSet preflight answers `expected`, and the model's
// lawfulness of the ledger's loan with that field answers `leanError` (notLawful where C++ rejects
// the field, none where it creates the loan).
struct LoanFieldCase
{
    std::int64_t value{};
    TER expected;
    std::optional<LeanError> leanError{};
};

// The loan lawfulness check (RawLoan.WF / RawLoan.Valid): a loan read from the ledger is lawful,
// and each case below breaks one clause of it.
// The model's loans are built field by field, including loans no transaction sequence may reach;
// a lawfulness verdict is not a claim that the loan is reachable.
class LeanLoan_test : public LeanSuite
{
    void
    runLawful(Loan const& s, bool shouldBeLawful, std::string const& label)
    {
        testcase(label);
        BEAST_EXPECTS(LoanFFI::build(s).has_value() == shouldBeLawful, label);
    }

    // Each row sets one field, on the LoanSet of the ledger's loan (applied on a throwaway view)
    // and on that loan as the model reads it; C++ preflight and the model's lawfulness must give
    // the row's pair of verdicts.
    // - Rate cap: every rate (interest, late, close, overpayment interest, overpayment fee) is
    //   capped at 100% (100'000); above it temINVALID / not lawful.
    // - Grace period: the grace period must lie in [60, payment interval] (600 here).
    // - Interval minimum: the payment interval must be at least 60 s (the stored grace period is
    //   60); the model's loan has its first due date one interval after its start.
    // clang-format off
    static constexpr LoanFieldCase kRateCap[] = {
        // 100% cap
        {.value = 99'998, .expected = tesSUCCESS},
        {.value = 99'999, .expected = tesSUCCESS},
        {.value = 100'000, .expected = tesSUCCESS},
        {.value = 100'001, .expected = temINVALID, .leanError = LeanError::notLawful},
        {.value = 100'002, .expected = temINVALID, .leanError = LeanError::notLawful},
    };
    static constexpr LoanFieldCase kGracePeriod[] = {
        // 60 s minimum
        {.value = 58, .expected = temINVALID, .leanError = LeanError::notLawful},
        {.value = 59, .expected = temINVALID, .leanError = LeanError::notLawful},
        {.value = 60, .expected = tesSUCCESS},
        {.value = 61, .expected = tesSUCCESS},
        {.value = 62, .expected = tesSUCCESS},
        // the payment interval (600)
        {.value = 598, .expected = tesSUCCESS},
        {.value = 599, .expected = tesSUCCESS},
        {.value = 600, .expected = tesSUCCESS},
        {.value = 601, .expected = temINVALID, .leanError = LeanError::notLawful},
        {.value = 602, .expected = temINVALID, .leanError = LeanError::notLawful},
    };
    static constexpr LoanFieldCase kIntervalMinimum[] = {
        // 60 s minimum
        {.value = 58, .expected = temINVALID, .leanError = LeanError::notLawful},
        {.value = 59, .expected = temINVALID, .leanError = LeanError::notLawful},
        {.value = 60, .expected = tesSUCCESS},
        {.value = 61, .expected = tesSUCCESS},
        {.value = 62, .expected = tesSUCCESS},
    };
    // clang-format on
    template <class Param, class Field>
    void
    runField(
        jtx::Env& env,
        BrokerFixture const& f,
        LoanParams const& p,
        Loan const& baseline,
        std::string const& name,
        Param LoanParams::* param,
        Field Loan::* field,
        std::span<LoanFieldCase const> cases)
    {
        beginCase(("loan " + name).c_str());
        for (LoanFieldCase const& c : cases)
        {
            LoanParams q = p;
            Loan s = baseline;
            q.*param = static_cast<Field>(c.value);
            s.*field = static_cast<Field>(c.value);
            if (field == &Loan::paymentInterval)
                s.nextPaymentDueDate = s.startDate + static_cast<std::uint32_t>(c.value);
            OpenView view{*env.current()};
            AppliedLoanTx const cpp = applyLoanSet(env, view, f, q);
            LeanLoanTx const lean{
                .result = {
                    .leanError =
                        LoanFFI::build(s) ? std::nullopt : std::optional{LeanError::notLawful}}};
            expectSame(
                *this,
                name + " " + std::to_string(c.value) + ": ",
                cpp,
                lean,
                c.expected,
                c.leanError);
        }
    }

    void
    runLoanFieldBoundaries(
        jtx::Env& env,
        BrokerFixture const& f,
        LoanParams const& p,
        Loan const& s)
    {
        auto const run = [&](char const* name, auto param, auto field, auto const& cases) {
            runField(env, f, p, s, name, param, field, cases);
        };
        run("interest rate cap", &LoanParams::interestRate, &Loan::interestRate, kRateCap);
        run("late interest rate cap",
            &LoanParams::lateInterestRate,
            &Loan::lateInterestRate,
            kRateCap);
        run("close interest rate cap",
            &LoanParams::closeInterestRate,
            &Loan::closeInterestRate,
            kRateCap);
        run("overpayment interest rate cap",
            &LoanParams::overpaymentInterestRate,
            &Loan::overpaymentInterestRate,
            kRateCap);
        run("overpayment fee cap", &LoanParams::overpaymentFee, &Loan::overpaymentFee, kRateCap);
        run("grace period", &LoanParams::gracePeriod, &Loan::gracePeriod, kGracePeriod);
        run("payment interval minimum",
            &LoanParams::paymentInterval,
            &Loan::paymentInterval,
            kIntervalMinimum);
    }

    void
    testLoanFieldBoundaries(
        jtx::Env& env,
        BrokerFixture const& f,
        LoanParams const& p,
        Loan const& s)
    {
        runLoanFieldBoundaries(env, f, p, s);
    }

    void
    runTests() override
    {
        using namespace jtx;
        Env env{*this, lendingTestAmendments()};
        auto const f = setUpBrokerVault(env, BrokerConfig{});
        depositCover(env, f, Number{500});
        LoanParams const p{
            .interestRate = 10'000,
            .originationFee = Number{5},
            .serviceFee = Number{1},
            .latePaymentFee = Number{2},
            .closePaymentFee = Number{3},
            .paymentTotal = 3};
        auto const loanKeylet = submitLoanSet(env, f, p);
        Loan const baseline = readLoan(*env.current(), loanKeylet, f, p);

        runLawful(baseline, true, "a loan read from the ledger");
        {
            auto s = baseline;
            s.paymentRemaining = 0;
            runLawful(s, false, "no payments left with value outstanding");
        }
        {
            auto s = baseline;
            s.paymentRemaining = 0;
            s.totalValueOutstanding = s.principalOutstanding = s.managementFeeOutstanding =
                Number{0};
            runLawful(s, false, "paid off but a due date remains");
        }
        {
            auto s = baseline;
            s.paymentRemaining = 0;
            s.totalValueOutstanding = s.principalOutstanding = s.managementFeeOutstanding =
                Number{0};
            s.nextPaymentDueDate = 0;
            runLawful(s, true, "paid off");
        }
        {
            auto s = baseline;
            s.principalOutstanding = Number{-1};
            runLawful(s, false, "negative principal");
        }
        {
            auto s = baseline;
            s.serviceFee = Number{-1};
            runLawful(s, false, "negative service fee");
        }
        {
            auto s = baseline;
            s.periodicPayment = Number{0};
            runLawful(s, false, "zero periodic payment");
        }
        {
            auto s = baseline;
            s.totalValueOutstanding = s.principalOutstanding;
            runLawful(s, false, "interest below the tolerance");
        }
        {
            auto s = baseline;
            s.interestRate = 100'001;
            runLawful(s, false, "interest rate above 100%");
        }
        {
            auto s = baseline;
            s.gracePeriod = s.paymentInterval + 1;
            runLawful(s, false, "grace period above the payment interval");
        }
        {
            auto s = baseline;
            s.loanScale = 100;
            runLawful(s, false, "loan scale out of range");
        }
        {
            auto s = baseline;
            s.paymentRemaining = s.paymentTotal + 1;
            runLawful(s, false, "more payments left than scheduled");
        }
        {
            auto s = baseline;
            s.previousPaymentDueDate = s.nextPaymentDueDate;
            runLawful(s, true, "due dates out of order (not an invariant)");
        }
        {
            auto s = baseline;
            s.nextPaymentDueDate += 7;
            runLawful(s, false, "next due date off the schedule");
        }
        {
            auto s = baseline;
            s.principalOutstanding = s.principalOutstanding + Number{1, -9};
            s.totalValueOutstanding = s.totalValueOutstanding + Number{1, -9};
            runLawful(s, false, "amounts below the loan scale");
        }
        {
            auto s = baseline;
            s.broker.managementFeeRate = 10'001;
            runLawful(s, false, "unlawful broker");
        }
        testLoanFieldBoundaries(env, f, p, baseline);
    }
};

BEAST_DEFINE_TESTSUITE(LeanLoan, formal_verification, xrpl);

}  // namespace xrpl::test::formal_verification
