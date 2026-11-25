#include <test/formal_verification/common/LeanSuite.h>
#include <test/formal_verification/ffi/lending/LoanFFI.h>
#include <test/formal_verification/tx/lending/LendingTestHelpers.h>
#include <test/jtx/Env.h>

#include <xrpl/basics/Number.h>
#include <xrpl/ledger/OpenView.h>
#include <xrpl/protocol/TER.h>

#include <cstddef>
#include <cstdint>
#include <functional>
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
    using Mutation = std::function<void(Loan&)>;

    // `mutate` applied to `loan`: build accepts the loan or rejects it.
    void
    expectBuild(std::string const& label, Mutation const& mutate, Loan loan, bool valid)
    {
        if (mutate)
            mutate(loan);
        testcase(label);
        BEAST_EXPECTS(LoanFFI::build(loan).has_value() == valid, label);
    }

    // Each row sets one field, on the LoanSet of the ledger's loan (applied on a throwaway view)
    // and on that loan as the model reads it; C++ preflight and the model's lawfulness must give
    // the row's pair of verdicts.
    // A group comment names a boundary value (the cusp); its rows step those values around it.
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
        testcase("loan " + name);
        for (std::size_t i = 0; LoanFieldCase const& c : cases)
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
            expectCppOnlyRejection(
                *this,
                rowText(i++) + name + " " + std::to_string(c.value) + ": ",
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

        auto const expectValid = [&](std::string const& label, Mutation const& mutate = {}) {
            expectBuild(label, mutate, baseline, true);
        };
        auto const expectInvalid = [&](std::string const& label, Mutation const& mutate) {
            expectBuild(label, mutate, baseline, false);
        };
        expectValid("a loan read from the ledger");
        expectInvalid("no payments left with value outstanding", [](Loan& loan) {
            loan.paymentRemaining = 0;
        });
        expectInvalid("paid off but a due date remains", [](Loan& loan) {
            loan.paymentRemaining = 0;
            loan.totalValueOutstanding = loan.principalOutstanding = loan.managementFeeOutstanding =
                Number{0};
        });
        expectValid("paid off", [](Loan& loan) {
            loan.paymentRemaining = 0;
            loan.totalValueOutstanding = loan.principalOutstanding = loan.managementFeeOutstanding =
                Number{0};
            loan.nextPaymentDueDate = 0;
        });
        expectInvalid(
            "negative principal", [](Loan& loan) { loan.principalOutstanding = Number{-1}; });
        expectInvalid("negative service fee", [](Loan& loan) { loan.serviceFee = Number{-1}; });
        expectInvalid(
            "zero periodic payment", [](Loan& loan) { loan.periodicPayment = Number{0}; });
        expectInvalid("interest below the tolerance", [](Loan& loan) {
            loan.totalValueOutstanding = loan.principalOutstanding;
        });
        expectInvalid("interest rate above 100%", [](Loan& loan) { loan.interestRate = 100'001; });
        expectInvalid("grace period above the payment interval", [](Loan& loan) {
            loan.gracePeriod = loan.paymentInterval + 1;
        });
        expectInvalid("loan scale out of range", [](Loan& loan) { loan.loanScale = 100; });
        expectInvalid("more payments left than scheduled", [](Loan& loan) {
            loan.paymentRemaining = loan.paymentTotal + 1;
        });
        expectValid("due dates out of order (not an invariant)", [](Loan& loan) {
            loan.previousPaymentDueDate = loan.nextPaymentDueDate;
        });
        expectInvalid(
            "next due date off the schedule", [](Loan& loan) { loan.nextPaymentDueDate += 7; });
        expectInvalid("amounts below the loan scale", [](Loan& loan) {
            loan.principalOutstanding = loan.principalOutstanding + Number{1, -9};
            loan.totalValueOutstanding = loan.totalValueOutstanding + Number{1, -9};
        });
        expectInvalid(
            "unlawful broker", [](Loan& loan) { loan.broker.managementFeeRate = 10'001; });
        testLoanFieldBoundaries(env, f, p, baseline);
    }
};

BEAST_DEFINE_TESTSUITE(LeanLoan, formal_verification, xrpl);

}  // namespace xrpl::test::formal_verification
