#include <test/formal_verification/common/LeanSuite.h>
#include <test/formal_verification/ffi/lending/LoanFFI.h>
#include <test/formal_verification/tx/lending/LendingTestHelpers.h>
#include <test/formal_verification/tx/lending/LoanPaySweepCases.h>
#include <test/jtx/Env.h>

#include <xrpl/basics/Number.h>
#include <xrpl/ledger/OpenView.h>
#include <xrpl/protocol/TER.h>

#include <cstdint>
#include <string>

namespace xrpl::test::formal_verification {

using namespace loan_pay_sweep;

// The loan lawfulness check (RawLoan.WF / RawLoan.Valid): a loan read from the ledger is lawful,
// and each case below breaks one clause of it.
class LeanLoan_test : public LeanSuite
{
    void
    runLawful(Loan const& s, bool shouldBeLawful, std::string const& label)
    {
        testcase(label);
        BEAST_EXPECTS(LoanFFI::build(s).has_value() == shouldBeLawful, label);
    }

    // The model's lawfulness of a loan with `value` in one field against C++ LoanSet's preflight
    // for the same field: a lawful loan must be one C++ creates. Returns the C++ verdict.
    template <class Field>
    TER
    checkField(
        jtx::Env& env,
        BrokerFixture const& f,
        LoanParams p,
        Loan s,
        Field LoanParams::* param,
        Field Loan::* field,
        std::int64_t value)
    {
        p.*param = static_cast<Field>(value);
        s.*field = static_cast<Field>(value);
        OpenView view{*env.current()};
        TER const cpp = applyLoanSet(env, view, f, p);
        bool const lawful = LoanFFI::build(s).has_value();
        BEAST_EXPECTS(
            lawful == isTesSuccess(cpp),
            describe(value) + ": cpp=" + transToken(cpp) +
                (lawful ? " lean=lawful" : " lean=not lawful"));
        return cpp;
    }

    // Every rate is capped at 100% (100'000), in C++ preflight and in the model's lawful loan.
    void
    testRateCapSweep(jtx::Env& env, BrokerFixture const& f, LoanParams const& p, Loan const& s)
    {
        sweepRateCap(env, f, p, s, "interest rate", &LoanParams::interestRate, &Loan::interestRate);
        sweepRateCap(
            env,
            f,
            p,
            s,
            "late interest rate",
            &LoanParams::lateInterestRate,
            &Loan::lateInterestRate);
        sweepRateCap(
            env,
            f,
            p,
            s,
            "close interest rate",
            &LoanParams::closeInterestRate,
            &Loan::closeInterestRate);
        sweepRateCap(
            env,
            f,
            p,
            s,
            "overpayment interest rate",
            &LoanParams::overpaymentInterestRate,
            &Loan::overpaymentInterestRate);
        sweepRateCap(
            env, f, p, s, "overpayment fee", &LoanParams::overpaymentFee, &Loan::overpaymentFee);
    }

    // Above 100% the loan is temINVALID in C++ and not lawful in the model.
    void
    sweepRateCap(
        jtx::Env& env,
        BrokerFixture const& f,
        LoanParams const& p,
        Loan const& s,
        std::string const& name,
        std::uint32_t LoanParams::* param,
        std::uint32_t Loan::* field)
    {
        beginCase(("loan " + name + " cap-Sweep").c_str());
        runAroundCusp(kRateCapCases, [&](std::int64_t rate) {
            return checkField(env, f, p, s, param, field, rate);
        });
    }

    // The grace period must lie in [60, payment interval] (600 here), else temINVALID / not
    // lawful.
    void
    testGracePeriodSweep(jtx::Env& env, BrokerFixture const& f, LoanParams const& p, Loan const& s)
    {
        beginCase("loan grace period-Sweep");
        runAroundCusp(kGraceCases, [&](std::int64_t grace) {
            LoanParams withGrace = p;
            withGrace.gracePeriod = static_cast<std::uint32_t>(grace);
            Loan loan = s;
            loan.gracePeriod = static_cast<std::uint32_t>(grace);
            OpenView view{*env.current()};
            TER const cpp = applyLoanSet(env, view, f, withGrace);
            bool const lawful = LoanFFI::build(loan).has_value();
            BEAST_EXPECTS(
                lawful == isTesSuccess(cpp),
                describe(grace) + ": cpp=" + transToken(cpp) +
                    (lawful ? " lean=lawful" : " lean=not lawful"));
            return cpp;
        });
    }

    void
    runTests() override
    {
        using namespace jtx;
        Env env(*this);
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
        Loan const baseline = readLoanState(env, loanKeylet, f.asset.raw(), p.paymentTotal);
        Number const grid{1, -6};

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
            runLawful(s, true, "more payments left than scheduled (not an invariant)");
        }
        {
            auto s = baseline;
            s.previousPaymentDueDate = s.nextPaymentDueDate;
            runLawful(s, true, "due dates out of order (not an invariant)");
        }
        {
            auto s = baseline;
            s.nextPaymentDueDate += 7;
            runLawful(s, true, "next due date off the schedule (not an invariant)");
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

        testRateCapSweep(env, f, p, baseline);
        testGracePeriodSweep(env, f, p, baseline);
    }
};

BEAST_DEFINE_TESTSUITE(LeanLoan, formal_verification, xrpl);

}  // namespace xrpl::test::formal_verification
