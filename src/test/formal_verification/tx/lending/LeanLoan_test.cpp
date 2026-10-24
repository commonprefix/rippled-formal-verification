#include <test/formal_verification/common/LeanSuite.h>
#include <test/formal_verification/ffi/lending/LoanFFI.h>
#include <test/formal_verification/tx/lending/LendingTestHelpers.h>
#include <test/jtx/Env.h>

#include <xrpl/basics/Number.h>

#include <string>

namespace xrpl::test::formal_verification {

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
    }
};

BEAST_DEFINE_TESTSUITE(LeanLoan, formal_verification, xrpl);

}  // namespace xrpl::test::formal_verification
