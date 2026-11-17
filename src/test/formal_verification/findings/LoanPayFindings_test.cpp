#include <test/app/lending/LoanManageFixedPrecisionBase.h>
#include <test/formal_verification/findings/LendingFindingsHelpers.h>
#include <test/jtx/Account.h>
#include <test/jtx/Env.h>
#include <test/jtx/TestHelpers.h>
#include <test/jtx/amount.h>
#include <test/jtx/fee.h>
#include <test/jtx/sig.h>
#include <test/jtx/ter.h>
#include <test/jtx/vault.h>

#include <xrpl/basics/Number.h>
#include <xrpl/basics/chrono.h>
#include <xrpl/beast/unit_test/suite.h>
#include <xrpl/ledger/helpers/LendingHelpers.h>
#include <xrpl/protocol/Feature.h>
#include <xrpl/protocol/Indexes.h>
#include <xrpl/protocol/Issue.h>
#include <xrpl/protocol/Keylet.h>
#include <xrpl/protocol/LedgerFormats.h>
#include <xrpl/protocol/Protocol.h>
#include <xrpl/protocol/SField.h>
#include <xrpl/protocol/STAmount.h>
#include <xrpl/protocol/SeqProxy.h>
#include <xrpl/protocol/TER.h>
#include <xrpl/protocol/TxFlags.h>
#include <xrpl/protocol/Units.h>

#include <chrono>
#include <cstdint>
#include <string>

namespace xrpl {

// One failing test per open bug in LoanPay. A test is enabled by uncommenting its call in run().
class LoanPayFindings_test : public LoanManageFixedPrecisionBase
{
    // The trust limit is above every balance. RedemptionDate is after every loan schedule.
    static inline Number const kTrustLimit{1, 31};
    static constexpr std::chrono::seconds kInvestmentWindow = std::chrono::hours{20 * 365 * 24};

    // The loan's NextPaymentDueDate as a ledger close time.
    static NetClock::time_point
    nextPaymentDueDate(test::jtx::Env const& env, Keylet const& loanKeylet)
    {
        return NetClock::time_point{
            NetClock::duration{env.le(loanKeylet)->at(sfNextPaymentDueDate)}};
    }

    // FV_M4_21: on a coarsened vault a regular or late payment of an installment smaller than
    // 1 ULP at the vault scale fails with tecPRECISION_LOSS.
    void
    testLoanPayCoarsenedInstalment()
    {
        testcase("FV_M4_21 LoanPayCoarsenedInstalment");

        using namespace test::jtx;
        Env env{*this, all_ | featureLendingProtocolV1_1};
        auto const accounts = setupIou(
            env,
            {.depositorTrust = kTrustLimit, .depositorFunds = Number{10'000'000'000'000'000LL}});
        auto const& [issuer, owner, depositor, asset] = accounts;
        Account const borrower{"borrower"};
        fundIouHolder(env, borrower, accounts, kTrustLimit, Number{1});

        Number const installment{1, -1};
        auto const coarsened = coarsenVault(
            env,
            owner,
            depositor,
            asset,
            {
                // 1. Vault at Scale 1 (base unit 0.1) that holds 899,999,000,000,000.
                .scale = 1,
                .depositAmount = Number{899'999'000'000'000LL},
                // 2. Loan A: 700,000,000,000,000 at 0% with the maximum LateInterestRate,
                // 5 x 1 day.
                .loanPrincipal = Number{700'000'000'000'000LL},
                // 3. Loan B: 0.5 at 0% to a separate borrower, 5 installments of 0.1, 1,000 days
                // apart.
                .extraLoans = {ExtraLoan{
                    .principal = installment * 5,
                    .paymentTotal = 5,
                    .paymentInterval = 1'000 * 24 * 60 * 60,
                    .borrower = borrower}},
                // 4. Loan A's first payment, 800 days late. AssetsAvailable is now on a grid of 1.
                .overdueDays = 800,
            });
        expectCoarsened(env, coarsened);
        Keylet const loanB = coarsened.loanKeylets[1];

        // 5. The borrower pays loan B's installment of 0.1 before its due date.
        // BUG: LoanPay returns tecPRECISION_LOSS.
        env(loan::pay(borrower, loanB.key, asset(installment)), Ter(tesSUCCESS));
        env.close();

        // 6. The borrower pays the same installment late, after its due date.
        closePastDue(env, loanB);
        // BUG: LoanPay returns tecPRECISION_LOSS.
        env(loan::pay(borrower, loanB.key, asset(installment), tfLoanLatePayment), Ter(tesSUCCESS));
        env.close();
    }

    // FV_M4_23: the last on-schedule payment of the rounded-up PeriodicPayment plus
    // LoanServiceFee fails with tecINSUFFICIENT_PAYMENT. It is 1 ULP at LoanScale short.
    void
    testLoanLastPaymentExtra()
    {
        testcase("FV_M4_23 LoanLastPaymentExtra");

        using namespace test::jtx;
        using namespace loan;
        using namespace std::chrono_literals;
        Env env{*this, all_ | featureLendingProtocolV1_1};

        // 1. Vault at Scale 8 that holds 381.246. The broker has a ManagementFeeRate of 0.1%.
        Number const principal{190'623, -3};
        auto const [issuer, owner, depositor, asset] =
            setupIou(env, {.depositorTrust = kTrustLimit, .depositorFunds = principal * 3});
        auto const fixture = setupLendingVault(
            env,
            owner,
            depositor,
            asset,
            principal * 2,
            kInvestmentWindow,
            /* scale */ 8,
            /* coverRateMinimum */ TenthBips32(0),
            /* coverRateLiquidation */ TenthBips32(0),
            /* managementFeeRate */ TenthBips16(100));

        // 2. Loan A: 190.623 at 12% with a LoanServiceFee of 1, 36 x 30 days.
        std::uint32_t const paymentTotal = 36;
        Number const loanServiceFee{1};
        Keylet const loanA = keylet::loan(fixture.brokerKeylet.key, SeqProxy::rawSequence(1));
        env(loan::set(depositor, fixture.brokerKeylet.key, principal),
            kInterestRate(TenthBips32(12'000)),
            kLoanServiceFee(loanServiceFee),
            kPaymentTotal(paymentTotal),
            kPaymentInterval(30 * 24 * 60 * 60),
            Sig(sfCounterpartySignature, owner),
            Fee(env.current()->fees().base * 2));
        env.close();

        // 3. An hour before each due date the borrower pays 7.31645546. The first 35 succeed.
        auto const loanSle = env.le(loanA);
        Number const payment =
            roundPeriodicPayment(asset, loanSle->at(sfPeriodicPayment), loanSle->at(sfLoanScale)) +
            loanServiceFee;
        for (std::uint32_t paid = 0; paid < paymentTotal - 1; ++paid)
        {
            env.close(nextPaymentDueDate(env, loanA) - 1h);
            env(loan::pay(depositor, loanA.key, asset(payment)));
            env.close();
        }

        // 4. The last payment. TotalValueOutstanding is 6.31645547.
        env.close(nextPaymentDueDate(env, loanA) - 1h);
        // BUG: LoanPay returns tecINSUFFICIENT_PAYMENT.
        env(loan::pay(depositor, loanA.key, asset(payment)), Ter(tesSUCCESS));
        env.close();
    }

    // FV_M4_29: a regular or late payment fails with tecLIMIT_EXCEEDED on a loan with a tiny
    // InterestRate, because the interest part of the installment is negative.
    void
    testLoanPayNegativeInterest()
    {
        testcase("FV_M4_29 LoanPayNegativeInterest");

        using namespace test::jtx;
        Env env{*this, all_ | featureLendingProtocolV1_1};

        // The vault at Scale 2 holds 1,000,000,000,000.
        auto const [issuer, owner, depositor, asset] = setupIou(
            env, {.depositorTrust = kTrustLimit, .depositorFunds = Number{2'000'000'000'000LL}});
        auto const fixture = setupLendingVault(
            env, owner, depositor, asset, Number{1'000'000'000'000LL}, kInvestmentWindow, 2);

        // 1. Loan A: 5,198,461,379.86 at 6 tenth bips, 30 x 60 s.
        Keylet const loanA =
            openLoan(env, fixture, Number{519'846'137'986LL, -2}, 30, TenthBips32(6), 0, 60);

        // 2. Two regular installments ahead of schedule. 173,282,047 covers one installment.
        Number const installment{173'282'047};
        for (int paid = 0; paid < 2; ++paid)
        {
            env(loan::pay(depositor, loanA.key, asset(installment)));
            env.close();
        }

        // 3. The third regular installment.
        // BUG: LoanPay returns tecLIMIT_EXCEEDED.
        env(loan::pay(depositor, loanA.key, asset(installment)), Ter(tesSUCCESS));
        env.close();

        // 4. The same installment paid late, after the due date and the grace period.
        closePastGrace(env, loanA);
        // BUG: LoanPay returns tecLIMIT_EXCEEDED.
        env(loan::pay(depositor, loanA.key, asset(installment), tfLoanLatePayment),
            Ter(tesSUCCESS));
        env.close();
    }

    // FV_M4_30: on the loan of FV_M4_29 a late payment or an overpayment succeeds and raises
    // the interest the loan still owes.
    void
    testLoanPayInterestDueRises()
    {
        testcase("FV_M4_30 LoanPayInterestDueRises");

        using namespace test::jtx;
        using namespace loan;

        for (bool const overpayment : {false, true})
        {
            Env env{*this, all_ | featureLendingProtocolV1_1};

            // The vault at Scale 2 holds 1,000,000,000,000.
            auto const [issuer, owner, depositor, asset] = setupIou(
                env,
                {.depositorTrust = kTrustLimit, .depositorFunds = Number{2'000'000'000'000LL}});
            auto const fixture = setupLendingVault(
                env, owner, depositor, asset, Number{1'000'000'000'000LL}, kInvestmentWindow, 2);

            // 1. Loan A of FV_M4_29 with a 100% LateInterestRate or a 50% OverpaymentInterestRate.
            Number const principal{519'846'137'986LL, -2};
            std::uint32_t const loanFlags = overpayment ? tfLoanOverpayment : 0;
            Keylet const loanA = keylet::loan(fixture.brokerKeylet.key, SeqProxy::rawSequence(1));
            env(loan::set(depositor, fixture.brokerKeylet.key, principal, loanFlags),
                kInterestRate(TenthBips32(6)),
                kLateInterestRate(percentageToTenthBips(overpayment ? 0 : 100)),
                kOverpaymentInterestRate(percentageToTenthBips(overpayment ? 50 : 0)),
                kPaymentTotal(30),
                kPaymentInterval(60),
                Sig(sfCounterpartySignature, owner),
                Fee(env.current()->fees().base * 2));
            env.close();

            // 2. Two regular installments ahead of schedule.
            Number const installment{173'282'047};
            for (int paid = 0; paid < 2; ++paid)
            {
                env(loan::pay(depositor, loanA.key, asset(installment)));
                env.close();
            }

            // 3. The third installment, paid late after its due date or as an overpayment of
            // the installment + 10.
            if (!overpayment)
                closePastDue(env, loanA);
            Number const interestBefore = constructLoanState(env.le(loanA)).interestDue;
            Number const payment = overpayment ? installment + 10 : Number{180'000'000};
            std::uint32_t const flags = overpayment ? tfLoanOverpayment : tfLoanLatePayment;
            env(loan::pay(depositor, loanA.key, asset(payment), flags));
            env.close();
            Number const interestAfter = constructLoanState(env.le(loanA)).interestDue;

            // BUG: the interest the loan still owes rises from 13.93 to 17.17.
            BEAST_EXPECTS(interestAfter <= interestBefore, to_string(interestAfter));
        }
    }

    // FV_M4_32: with a LoanServiceFee or LatePaymentFee so large that the amount due rounds to
    // the fee, LoanPay credits the vault with an installment nobody paid.
    void
    testLoanPayFeeSwampsInstalment()
    {
        testcase("FV_M4_32 LoanPayFeeSwampsInstalment");

        using namespace test::jtx;
        using namespace loan;

        Number const fee{1, 30};

        for (bool const lateFee : {false, true})
        {
            Env env{*this, all_ | featureLendingProtocolV1_1};

            // The vault at Scale 2 holds 1,000,000,000,000. The borrower holds 10^30.
            auto const accounts = setupIou(
                env,
                {.depositorTrust = kTrustLimit,
                 .ownerTrust = kTrustLimit,
                 .depositorFunds = Number{2'000'000'000'000LL}});
            auto const& [issuer, owner, depositor, asset] = accounts;
            Account const borrower{"borrower"};
            fundIouHolder(env, borrower, accounts, kTrustLimit, fee);
            auto const fixture = setupLendingVault(
                env, owner, depositor, asset, Number{1'000'000'000'000LL}, kInvestmentWindow, 2);

            // 1. Loan A of FV_M4_29 at 1% with a LoanServiceFee or LatePaymentFee of 10^30.
            Keylet const loanA = keylet::loan(fixture.brokerKeylet.key, SeqProxy::rawSequence(1));
            env(loan::set(borrower, fixture.brokerKeylet.key, Number{519'846'137'986LL, -2}),
                kInterestRate(TenthBips32(1'000)),
                kLoanServiceFee(lateFee ? Number{0} : fee),
                kLatePaymentFee(lateFee ? fee : Number{0}),
                kPaymentTotal(30),
                kPaymentInterval(60),
                Sig(sfCounterpartySignature, owner),
                Fee(env.current()->fees().base * 2));
            env.close();

            // 2. The borrower pays the amount due, the 10^30 it holds, on time or after the
            // due date.
            if (lateFee)
                closePastDue(env, loanA);
            auto const before = snapshotVault(env, fixture.vaultKeylet, asset);
            Number const borrowerBefore = env.balance(borrower, asset).value();
            Number const ownerBefore = env.balance(owner, asset).value();
            env(loan::pay(borrower, loanA.key, asset(fee), lateFee ? tfLoanLatePayment : 0));
            env.close();
            auto const after = snapshotVault(env, fixture.vaultKeylet, asset);

            Number const vaultReceived = after.available - before.available;
            Number const borrowerSpent = borrowerBefore - env.balance(borrower, asset).value();
            Number const ownerReceived = env.balance(owner, asset).value() - ownerBefore;
            // BUG: the broker owner receives the 10^30 spent and the vault gains 173,282,097.1.
            BEAST_EXPECTS(vaultReceived <= borrowerSpent - ownerReceived, to_string(vaultReceived));
        }
    }

    // FV_M4_34: a regular or late payment of an installment that is only management fee fails
    // with tecPRECISION_LOSS, so the loan can only be defaulted.
    void
    testLoanPayFeeOnlyInstalment()
    {
        testcase("FV_M4_34 LoanPayFeeOnlyInstalment");

        using namespace test::jtx;
        Env env{*this, all_ | featureLendingProtocolV1_1};

        // 1. Vault at Scale 0 that holds 10^12. The broker has a ManagementFeeRate of 10%.
        auto const [issuer, owner, depositor, asset] = setupIou(
            env, {.depositorTrust = kTrustLimit, .depositorFunds = Number{2'000'000'000'000LL}});
        auto const fixture = setupLendingVault(
            env,
            owner,
            depositor,
            asset,
            Number{1'000'000'000'000LL},
            kInvestmentWindow,
            /* scale */ 0,
            /* coverRateMinimum */ TenthBips32(0),
            /* coverRateLiquidation */ TenthBips32(0),
            /* managementFeeRate */ TenthBips16(10'000));

        // 2. Loan A: 2 at 45.5%, 12 yearly installments of 1.
        Number const installment{1};
        Keylet const loanA =
            openLoan(env, fixture, Number{2}, 12, TenthBips32(45'500), 0, 365 * 24 * 60 * 60);

        // 3. Installments 1 to 8 are 1 of interest each.
        for (int paid = 0; paid < 8; ++paid)
        {
            env(loan::pay(depositor, loanA.key, asset(installment)));
            env.close();
        }

        // 4. Installment 9 is 1 of management fee and nothing else.
        // BUG: LoanPay returns tecPRECISION_LOSS.
        env(loan::pay(depositor, loanA.key, asset(installment)), Ter(tesSUCCESS));
        env.close();

        // 5. The same installment paid late, after its due date.
        closePastDue(env, loanA);
        // BUG: LoanPay returns tecPRECISION_LOSS.
        env(loan::pay(depositor, loanA.key, asset(installment), tfLoanLatePayment),
            Ter(tesSUCCESS));
        env.close();
    }

    // FV_M4_35: a late payment of an installment that takes nothing off the loan fails with
    // tecINVARIANT_FAILED, so the loan can only be defaulted.
    void
    testLoanPayZeroValueInstalment()
    {
        testcase("FV_M4_35 LoanPayZeroValueInstalment");

        using namespace test::jtx;
        using namespace loan;
        Env env{*this, all_ | featureLendingProtocolV1_1};

        // 1. Vault at Scale 0 that holds 1,000,000. The broker has a ManagementFeeRate of 10%.
        auto const [issuer, owner, depositor, asset] =
            setupIou(env, {.depositorTrust = kTrustLimit, .depositorFunds = Number{2'000'000}});
        auto const fixture = setupLendingVault(
            env,
            owner,
            depositor,
            asset,
            Number{1'000'000},
            kInvestmentWindow,
            /* scale */ 0,
            /* coverRateMinimum */ TenthBips32(0),
            /* coverRateLiquidation */ TenthBips32(0),
            /* managementFeeRate */ TenthBips16(10'000));

        // 2. Loan A: 6 at 14.5% with a LateInterestRate of 100%, 16 yearly installments.
        std::uint32_t const oneYear = 365 * 24 * 60 * 60;
        Keylet const loanA = keylet::loan(fixture.brokerKeylet.key, SeqProxy::rawSequence(1));
        env(loan::set(depositor, fixture.brokerKeylet.key, Number{6}),
            kInterestRate(TenthBips32(14'500)),
            kLateInterestRate(percentageToTenthBips(100)),
            kPaymentTotal(16),
            kPaymentInterval(oneYear),
            Sig(sfCounterpartySignature, owner),
            Fee(env.current()->fees().base * 2));
        env.close();

        // 3. Installments 1 to 3 are paid early, 1 of interest each.
        for (int paid = 0; paid < 3; ++paid)
        {
            env(loan::pay(depositor, loanA.key, asset(Number{1})));
            env.close();
        }

        // 4. Installment 4 is paid 0.2 years late: 1 of interest and 1 of late interest.
        env.close(nextPaymentDueDate(env, loanA) + std::chrono::seconds{oneYear / 5});
        env(loan::pay(depositor, loanA.key, asset(Number{2}), tfLoanLatePayment));
        env.close();

        // 5. Installment 5 takes nothing off the loan. Paid 0.2 years late it is 1 of late
        // interest.
        env.close(nextPaymentDueDate(env, loanA) + std::chrono::seconds{oneYear / 5});
        // BUG: LoanInvariant rejects the payment with tecINVARIANT_FAILED.
        env(loan::pay(depositor, loanA.key, asset(Number{1}), tfLoanLatePayment), Ter(tesSUCCESS));
        env.close();
    }

    // FV_M4_39: with a ClosePaymentFee so large that the full payment rounds to the fee, LoanPay
    // credits the vault with principal and interest nobody paid.
    void
    testLoanPayCloseFeeSwampsPayoff()
    {
        testcase("FV_M4_39 LoanPayCloseFeeSwampsPayoff");

        using namespace test::jtx;
        using namespace loan;
        Env env{*this, all_ | featureLendingProtocolV1_1};

        // 1. Vault at Scale 6 that holds 3,000,000,000. The broker has a ManagementFeeRate of 10%.
        Number const borrowerFunds{2, 25};
        auto const accounts = setupIou(
            env,
            {.depositorTrust = kTrustLimit,
             .ownerTrust = kTrustLimit,
             .depositorFunds = Number{3'000'000'000LL}});
        auto const& [issuer, owner, depositor, asset] = accounts;
        Account const borrower{"borrower"};
        fundIouHolder(env, borrower, accounts, kTrustLimit, borrowerFunds);
        auto const fixture = setupLendingVault(
            env,
            owner,
            depositor,
            asset,
            Number{3'000'000'000LL},
            kInvestmentWindow,
            /* scale */ 6,
            /* coverRateMinimum */ TenthBips32(0),
            /* coverRateLiquidation */ TenthBips32(0),
            /* managementFeeRate */ TenthBips16(10'000));

        // 2. Loan A: 1,000 at 10% with a 100% CloseInterestRate and a ClosePaymentFee of 10^25.
        Keylet const loanA = keylet::loan(fixture.brokerKeylet.key, SeqProxy::rawSequence(1));
        env(loan::set(borrower, fixture.brokerKeylet.key, Number{1'000}),
            kInterestRate(percentageToTenthBips(10)),
            kCloseInterestRate(percentageToTenthBips(100)),
            kClosePaymentFee(Number{1, 25}),
            kPaymentTotal(30),
            kPaymentInterval(60),
            Sig(sfCounterpartySignature, owner),
            Fee(env.current()->fees().base * 2));
        env.close();

        // 3. The borrower offers the 2 * 10^25 it holds as a full payment in the next ledger.
        auto const before = snapshotVault(env, fixture.vaultKeylet, asset);
        Number const borrowerBefore = env.balance(borrower, asset).value();
        Number const ownerBefore = env.balance(owner, asset).value();
        env(loan::pay(borrower, loanA.key, asset(borrowerFunds), tfLoanFullPayment));
        env.close();
        auto const after = snapshotVault(env, fixture.vaultKeylet, asset);

        Number const vaultReceived = after.available - before.available;
        Number const borrowerSpent = borrowerBefore - env.balance(borrower, asset).value();
        Number const ownerReceived = env.balance(owner, asset).value() - ownerBefore;
        // BUG: the broker owner receives the 10^25 spent and the vault gains 1,900.
        BEAST_EXPECTS(vaultReceived <= borrowerSpent - ownerReceived, to_string(vaultReceived));
    }

    // FV_M4_40: a late payment that takes AssetsAvailable of a coarsened vault up to a power of
    // ten credits the vault a negative amount, so the vault pays the borrower.
    void
    testLoanPayNegativeCredit()
    {
        testcase("FV_M4_40 LoanPayNegativeCredit");

        using namespace test::jtx;
        using namespace loan;
        using namespace std::chrono_literals;
        Env env{*this, all_ | featureLendingProtocolV1_1};

        // 1. Vault at Scale 10 that holds 500,000.
        auto const accounts = setupIou(
            env, {.depositorTrust = kTrustLimit, .depositorFunds = Number{20'000'000'000LL}});
        auto const& [issuer, owner, depositor, asset] = accounts;
        Account const borrower{"borrower"};
        fundIouHolder(env, borrower, accounts, kTrustLimit, Number{1});
        auto const fixture =
            setupLendingVault(env, owner, depositor, asset, Number{500'000}, kInvestmentWindow, 10);

        // 2. Loan A: 450,000 at 0% with the maximum LateInterestRate, 400 x 60 s.
        std::uint32_t const paymentTotalA = 400;
        Keylet const loanA = keylet::loan(fixture.brokerKeylet.key, SeqProxy::rawSequence(1));
        env(loan::set(depositor, fixture.brokerKeylet.key, Number{450'000}),
            kLateInterestRate(lending::kMaxLateInterestRate),
            kPaymentTotal(paymentTotalA),
            kPaymentInterval(60),
            Sig(sfCounterpartySignature, owner),
            Fee(env.current()->fees().base * 2));
        env.close();

        // 3. Loan B: 0.0000019996 at 0% to a separate borrower, one payment.
        Number const amountB{19'996, -10};
        Keylet const loanB = keylet::loan(fixture.brokerKeylet.key, SeqProxy::rawSequence(2));
        env(loan::set(borrower, fixture.brokerKeylet.key, amountB),
            kPaymentTotal(1),
            kPaymentInterval(24 * 60 * 60),
            Sig(sfCounterpartySignature, owner),
            Fee(env.current()->fees().base * 2));
        env.close();

        // 4. Loan C: 0.00002 at 0% to the same borrower, 20 installments of 0.000001.
        Number const installmentC{1, -6};
        std::uint32_t const paymentTotalC = 20;
        Keylet const loanC = keylet::loan(fixture.brokerKeylet.key, SeqProxy::rawSequence(3));
        env(loan::set(borrower, fixture.brokerKeylet.key, installmentC * paymentTotalC),
            kPaymentTotal(paymentTotalC),
            kPaymentInterval(24 * 60 * 60),
            Sig(sfCounterpartySignature, owner),
            Fee(env.current()->fees().base * 2));
        env.close();

        // 5. About 130 years later loan A's 400 installments are paid late, in one ledger.
        env.close(nextPaymentDueDate(env, loanA) + 4'099'998'939s);
        for (std::uint32_t paid = 0; paid < paymentTotalA; ++paid)
            env(loan::pay(depositor, loanA.key, asset(Number{1'000'000'000}), tfLoanLatePayment));
        env.close();
        expectCoarsened(env, fixture.vaultKeylet);

        // 6. The depositor withdraws until AssetsAvailable is just below 9,999,999,999.999998.
        Number const target{9'999'999'999'999'998LL, -6};
        Number const withdrawal =
            snapshotVault(env, fixture.vaultKeylet, asset).available - target + installmentC * 10;
        env(Vault::withdraw(
            {.depositor = depositor, .id = fixture.vaultKeylet.key, .amount = asset(withdrawal)}));
        env.close();

        // 7. Loan C's installments take AssetsAvailable up to exactly that amount.
        auto before = snapshotVault(env, fixture.vaultKeylet, asset);
        for (std::uint32_t paid = 0; paid < paymentTotalC && before.available < target; ++paid)
        {
            env(loan::pay(borrower, loanC.key, asset(installmentC), tfLoanLatePayment));
            env.close();
            before = snapshotVault(env, fixture.vaultKeylet, asset);
        }
        BEAST_EXPECT(before.available == target);

        // 8. The borrower pays loan B's 0.0000019996 late. The payment succeeds.
        Number const borrowerBefore = env.balance(borrower, asset).value();
        env(loan::pay(borrower, loanB.key, asset(amountB), tfLoanLatePayment));
        env.close();
        auto const after = snapshotVault(env, fixture.vaultKeylet, asset);

        Number const vaultReceived = after.available - before.available;
        Number const borrowerSpent = borrowerBefore - env.balance(borrower, asset).value();
        // BUG: AssetsAvailable falls by 0.000008.
        BEAST_EXPECTS(vaultReceived >= Number{0}, to_string(vaultReceived));
        // BUG: the borrower's balance rises by 0.000008.
        BEAST_EXPECTS(borrowerSpent > Number{0}, to_string(borrowerSpent));
    }

    // FV_M4_41: the late payment that coarsens the vault fails with tecINVARIANT_FAILED while a
    // pending loan's principal has a digit below the new grid.
    void
    testLoanPayPendingSubUnit()
    {
        testcase("FV_M4_41 LoanPayPendingSubUnit");

        using namespace test::jtx;
        using namespace loan;
        using namespace std::chrono_literals;
        Env env{*this, all_ | featureLendingProtocolV1_1};

        // 1. Vault at Scale 6 that holds 8,999,999,000.
        auto const accounts = setupIou(
            env, {.depositorTrust = kTrustLimit, .depositorFunds = Number{20'000'000'000LL}});
        auto const& [issuer, owner, depositor, asset] = accounts;
        Account const borrower{"borrower"};
        fundIouHolder(env, borrower, accounts, kTrustLimit, Number{1});
        auto const fixture = setupLendingVault(
            env, owner, depositor, asset, Number{8'999'999'000LL}, kInvestmentWindow, 6);

        // 2. Loan A: 7,000,000,000 at 0% with the maximum LateInterestRate, one payment.
        Keylet const loanA = keylet::loan(fixture.brokerKeylet.key, SeqProxy::rawSequence(1));
        env(loan::set(depositor, fixture.brokerKeylet.key, Number{7'000'000'000LL}),
            kLateInterestRate(lending::kMaxLateInterestRate),
            kPaymentTotal(1),
            kPaymentInterval(24 * 60 * 60),
            Sig(sfCounterpartySignature, owner),
            Fee(env.current()->fees().base * 2));
        env.close();

        // 3. Loan B: a two-step proposal of 12,345.678901 that starts in a year and stays pending.
        Keylet const loanB = keylet::loan(fixture.brokerKeylet.key, SeqProxy::rawSequence(2));
        env(loan::set(owner, fixture.brokerKeylet.key, Number{12'345'678'901LL, -6}),
            kBorrower(borrower),
            kStartDate((env.now() + 365 * 24h).time_since_epoch().count()),
            kPaymentTotal(1),
            kPaymentInterval(30 * 24 * 60 * 60));
        env.close();

        // 4. Loan A's payment, 60 days late. It would take AssetsAvailable past 10^16 base units.
        Number const latePayment{10'000'000'000LL};
        env.close(nextPaymentDueDate(env, loanA) + 60 * 24h);
        // BUG: the vault invariant rejects the payment with tecINVARIANT_FAILED.
        env(loan::pay(depositor, loanA.key, asset(latePayment), tfLoanLatePayment),
            Ter(tesSUCCESS));
        env.close();

        // 5. Once the broker deletes loan B, the same payment succeeds.
        env(loan::del(owner, loanB.key));
        env.close();
        env(loan::pay(depositor, loanA.key, asset(latePayment), tfLoanLatePayment));
        env.close();
        expectCoarsened(env, fixture.vaultKeylet);
    }

    // FV_M4_47: one late payment clears a loan's impairment although the loan stays two
    // installments late.
    void
    testLoanPayClearsImpairmentWhileLate()
    {
        testcase("FV_M4_47 LoanPayClearsImpairmentWhileLate");

        using namespace test::jtx;
        using namespace std::chrono_literals;
        Env env{*this, all_ | featureLendingProtocolV1_1};

        // 1. Vault that holds 10,000.
        auto const [issuer, owner, depositor, asset] =
            setupIou(env, {.depositorTrust = kTrustLimit, .depositorFunds = Number{100'000}});
        auto const fixture =
            setupLendingVault(env, owner, depositor, asset, Number{10'000}, kInvestmentWindow);

        // 2. Loan A: 1,000 at 0%, 5 payments of 200, 120 s apart.
        Number const installment{200};
        Keylet const loanA = openLoan(env, fixture, Number{1'000}, 5, TenthBips32(0), 0, 120);

        // 3. Three due dates pass without a payment.
        env.close(nextPaymentDueDate(env, loanA) + 2 * 120s + 60s);

        // 4. The broker impairs loan A.
        env(loan::manage(owner, loanA.key, tfLoanImpair));
        env.close();

        // 5. The borrower pays one installment late.
        std::uint32_t const paymentTime = env.now().time_since_epoch().count();
        env(loan::pay(depositor, loanA.key, asset(installment), tfLoanLatePayment));
        env.close();

        auto const loan = env.le(loanA);
        std::uint32_t const dueDate = loan->at(sfNextPaymentDueDate);
        bool const current = loan->isFlag(lsfLoanImpaired) || dueDate >= paymentTime;
        // BUG: loan A is no longer impaired, but its NextPaymentDueDate is still in the past.
        BEAST_EXPECTS(current, std::to_string(dueDate));
    }

    // FV_M4_48: a full payment before StartDate pays no interest, although LoanAccept paid the
    // principal out 29 days earlier.
    void
    testLoanPayBeforeStartDate()
    {
        testcase("FV_M4_48 LoanPayBeforeStartDate");

        using namespace test::jtx;
        using namespace loan;
        using namespace std::chrono_literals;
        Env env{*this, all_ | featureLendingProtocolV1_1};

        // 1. Vault that holds 10,000.
        auto const [issuer, owner, depositor, asset] =
            setupIou(env, {.depositorTrust = kTrustLimit, .depositorFunds = Number{100'000}});
        auto const fixture =
            setupLendingVault(env, owner, depositor, asset, Number{10'000}, kInvestmentWindow);

        // 2. Loan A: a two-step proposal of 1,000 at 10%, 12 x 30 days, that starts in 30 days.
        Number const principal{1'000};
        Keylet const loanA = keylet::loan(fixture.brokerKeylet.key, SeqProxy::rawSequence(1));
        env(loan::set(owner, fixture.brokerKeylet.key, principal),
            kBorrower(depositor),
            kStartDate((env.now() + 30 * 24h).time_since_epoch().count()),
            kInterestRate(percentageToTenthBips(10)),
            kPaymentTotal(12),
            kPaymentInterval(30 * 24 * 60 * 60));
        env.close();

        // 3. The borrower accepts loan A on day 0 and receives the 1,000.
        NetClock::time_point const acceptTime = env.now();
        env(loan::accept(depositor, loanA.key));
        env.close();

        // 4. On day 29, one day before StartDate, the borrower pays loan A off.
        env.close(acceptTime + 29 * 24h);
        Number const borrowerBefore = env.balance(depositor, asset).value();
        env(loan::pay(depositor, loanA.key, asset(Number{1'100}), tfLoanFullPayment));
        env.close();

        Number const borrowerSpent = borrowerBefore - env.balance(depositor, asset).value();
        // BUG: the borrower pays back the 1,000 and no interest for the 29 days.
        BEAST_EXPECTS(borrowerSpent > principal, to_string(borrowerSpent));
    }

    // FV_M4_53: a late payment on an XRP loan returns tefEXCEPTION when the late interest is above
    // 10^17 drops. The late interest is rounded to an XRP amount before the payment check.
    void
    testLoanPayXRPRange()
    {
        testcase("FV_M4_53 LoanPayXRPRange");

        using namespace test::jtx;
        using namespace loan;
        Env env{*this, all_ | featureLendingProtocolV1_1};
        Account const owner{"owner"};
        Account const depositor{"depositor"};
        env.fund(XRP(5'100'000'000LL), owner, depositor);
        env.close();

        // 1. An XRP vault with 5 * 10^15 drops, all of it lent in loan A with one payment and a
        //    LateInterestRate of 100%.
        PrettyAsset const asset{xrpIssue()};
        Number const principal{5'000'000'000'000'000LL};
        auto const fixture = setupLendingVault(
            env, owner, depositor, asset, principal, std::chrono::seconds{946'000'000});
        Keylet const loanA = keylet::loan(
            fixture.brokerKeylet.key,
            SeqProxy::rawSequence(env.le(fixture.brokerKeylet)->at(sfLoanSequence)));
        env(loan::set(depositor, fixture.brokerKeylet.key, principal),
            kLateInterestRate(percentageToTenthBips(100)),
            kGracePeriod(60),
            kPaymentInterval(120),
            kPaymentTotal(1),
            Sig(sfCounterpartySignature, owner),
            Fee(env.current()->fees().base * 2));
        env.close();

        NetClock::time_point const due = nextPaymentDueDate(env, loanA);
        std::chrono::seconds const oneYear{365 * 24 * 60 * 60};
        STAmount const payment = asset(principal).value();

        // 2. Ten years late the late interest is about 5 * 10^16 drops. A payment of the
        //    principal is below the amount due.
        env.close(due + 10 * oneYear);
        env(loan::pay(depositor, loanA.key, payment, tfLoanLatePayment),
            Ter(tecINSUFFICIENT_PAYMENT));
        env.close();

        // 3. Twenty-five years late the late interest is about 1.25 * 10^17 drops.
        // BUG: the result is tefEXCEPTION.
        env.close(due + 25 * oneYear);
        env(loan::pay(depositor, loanA.key, payment, tfLoanLatePayment),
            Ter(tecINSUFFICIENT_PAYMENT));
        env.close();
    }

    // FV_M4_59: a late payment on an XRP loan returns tefEXCEPTION when it takes AssetsTotal above
    // 10^17 drops. AssetsTotal counts principal that is lent out, so the vault holds less.
    void
    testLoanPayAssetsTotalRange()
    {
        testcase("FV_M4_59 LoanPayAssetsTotalRange");

        using namespace test::jtx;
        Env env{*this, all_ | featureLendingProtocolV1_1};
        Account const owner{"owner"};
        Account const depositor{"depositor"};
        env.fund(XRP(1'000'000), owner);
        env.fund(XRP(99'900'000'000LL), depositor);
        env.close();

        // 1. An XRP vault with 9 * 10^15 drops, all of it lent to the depositor in loans A, B
        //    and C.
        PrettyAsset const asset{xrpIssue()};
        auto const fixture = setupLendingVault(
            env,
            owner,
            depositor,
            asset,
            Number{9'000'000'000'000'000LL},
            std::chrono::seconds{946'000'000});
        Keylet const loanA = openLoanWithLateInterest(env, fixture, Number{100'000'000'000'000LL});
        Keylet const loanB =
            openLoanWithLateInterest(env, fixture, Number{4'400'000'000'000'000LL});
        openLoanWithLateInterest(env, fixture, Number{4'500'000'000'000'000LL});

        // 2. The loans are 20.5 years late. Loan A is paid with its late interest, about
        //    2.15 * 10^15 drops in all.
        std::chrono::seconds const late{646'488'000};
        env.close(nextPaymentDueDate(env, loanA) + late);
        env(loan::pay(
            depositor,
            loanA.key,
            asset(Number{3'000'000'000'000'000LL}).value(),
            tfLoanLatePayment));
        env.close();

        // 3. Loan B is due about 9.46 * 10^16 drops, and the depositor holds more than that.
        STAmount const payment = asset(Number{95'000'000'000'000'000LL}).value();
        BEAST_EXPECT(env.balance(depositor).value() > payment);

        // 4. The payment takes AssetsAvailable to 9.68 * 10^16 drops. With the 4.5 * 10^15 that
        //    loan C still owes, AssetsTotal would be 1.01 * 10^17 drops.
        // BUG: the result is tefEXCEPTION.
        env(loan::pay(depositor, loanB.key, payment, tfLoanLatePayment));
        env.close();
    }

public:
    void
    run() override
    {
        // Open bugs. Each call fails until the C++ code is fixed, so it is commented out.
        // clang-format off
        // testLoanPayCoarsenedInstalment();          // FV_M4_21
        // testLoanLastPaymentExtra();                // FV_M4_23
        // testLoanPayNegativeInterest();             // FV_M4_29
        // testLoanPayInterestDueRises();             // FV_M4_30
        // testLoanPayFeeSwampsInstalment();          // FV_M4_32
        // testLoanPayFeeOnlyInstalment();            // FV_M4_34
        // testLoanPayZeroValueInstalment();          // FV_M4_35
        // testLoanPayCloseFeeSwampsPayoff();         // FV_M4_39
        // testLoanPayNegativeCredit();               // FV_M4_40
        // testLoanPayPendingSubUnit();               // FV_M4_41
        // testLoanPayClearsImpairmentWhileLate();    // FV_M4_47
        // testLoanPayBeforeStartDate();              // FV_M4_48
        // testLoanPayXRPRange();                     // FV_M4_53
        // testLoanPayAssetsTotalRange();             // FV_M4_59
        // clang-format on

        // Keeps a run of this suite alone from reporting "No tests run".
        pass();
    }
};

BEAST_DEFINE_TESTSUITE(LoanPayFindings, formal_verification, xrpl);

}  // namespace xrpl
