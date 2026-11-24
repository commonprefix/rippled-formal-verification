#include <test/app/lending/LoanManageFixedPrecisionBase.h>
#include <test/formal_verification/findings/LendingFindingsHelpers.h>
#include <test/jtx/Account.h>
#include <test/jtx/Env.h>
#include <test/jtx/TestHelpers.h>
#include <test/jtx/amount.h>
#include <test/jtx/batch.h>
#include <test/jtx/fee.h>
#include <test/jtx/seq.h>
#include <test/jtx/sig.h>
#include <test/jtx/tags.h>
#include <test/jtx/ter.h>
#include <test/jtx/trust.h>
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
#include <xrpl/protocol/XRPAmount.h>
#include <xrpl/tx/applySteps.h>

#include <chrono>
#include <cmath>
#include <cstdint>
#include <string>

// cspell: words Unpayable

namespace xrpl {

// One test per bug reported in LoanPay. The test of an open bug fails and its call in run() is
// commented out. A fixed bug's test is a regression test.
class LoanPayFindings_test : public LoanManageFixedPrecisionBase
{
    // The trust limit is above every balance. RedemptionDate is after every loan schedule.
    static inline Number const kTrustLimit{1, 31};
    static constexpr std::chrono::seconds kInvestmentWindow = std::chrono::hours{20 * 365 * 24};
    // About 30 years, for the XRP and MPT range tests that pay decades late.
    static constexpr std::chrono::seconds kLongInvestmentWindow{946'000'000};
    // Covers each late instalment of loan A in setupCoarsenedLastInstalment.
    static inline Number const kLatePaymentLimit{2'000'000};
    // Pending loan B of the FV_M4_41 tests. Its last digit is below the grid of the coarse vault.
    static inline Number const kSubGridPrincipal{12'345'678'901LL, -6};

    // The loan's NextPaymentDueDate as a ledger close time.
    static NetClock::time_point
    nextPaymentDueDate(test::jtx::Env const& env, Keylet const& loanKeylet)
    {
        return NetClock::time_point{
            NetClock::duration{env.le(loanKeylet)->at(sfNextPaymentDueDate)}};
    }

    // Pays the loan's next `count` installments, each PeriodicPayment rounded up to LoanScale.
    static void
    payInstallments(
        test::jtx::Env& env,
        test::jtx::Account const& borrower,
        PrettyAsset const& asset,
        Keylet const& loanKeylet,
        std::uint32_t count)
    {
        auto const loanSle = env.le(loanKeylet);
        Number const installment =
            roundPeriodicPayment(asset, loanSle->at(sfPeriodicPayment), loanSle->at(sfLoanScale));
        for (std::uint32_t paid = 0; paid < count; ++paid)
        {
            env(test::jtx::loan::pay(borrower, loanKeylet.key, asset(installment)));
            env.close();
        }
    }

    // FV_M4_1: AssetsTotal stays AssetsAvailable + DebtTotal across a power of ten.
    void
    testLoanConservation()
    {
        testcase("FV_M4_1 LoanConservation");

        using namespace test::jtx;
        Env env{*this, all_ | featureLendingProtocolV1_1};

        // 1. Vault that holds 999,000,000.
        auto const [issuer, owner, depositor, asset] = setupIou(
            env, {.depositorTrust = kTrustLimit, .depositorFunds = Number{2'000'000'000LL}});
        auto const fixture =
            setupLendingVault(env, owner, depositor, asset, Number{999'000'000}, kInvestmentWindow);

        // 2. Loan A: 10,000,000 at 100%, 2 x 1 year.
        Keylet const loanA =
            openLoan(env, fixture, Number{10'000'000}, 2, TenthBips32(100'000), 0, kSecondsInYear);

        // 3. The first installment takes AssetsTotal across 10^9. The second pays loan A off.
        for (int paid = 0; paid < 2; ++paid)
        {
            payInstallments(env, depositor, asset, loanA, 1);
            auto const vault = snapshotVault(env, fixture.vaultKeylet, asset);
            Number const debtTotal = env.le(fixture.brokerKeylet)->at(sfDebtTotal);
            BEAST_EXPECT(vault.total > Number{1'000'000'000});
            BEAST_EXPECTS(vault.total == vault.available + debtTotal, to_string(vault.total));
        }
    }

    // FV_M4_2: the final payment succeeds after AssetsTotal crossed a power of ten.
    void
    testLoanUnpayable()
    {
        testcase("FV_M4_2 LoanUnpayable");

        using namespace test::jtx;
        Env env{*this, all_ | featureLendingProtocolV1_1};

        // 1. Vault that holds 999,000,000.
        auto const [issuer, owner, depositor, asset] = setupIou(
            env, {.depositorTrust = kTrustLimit, .depositorFunds = Number{2'000'000'000LL}});
        auto const fixture =
            setupLendingVault(env, owner, depositor, asset, Number{999'000'000}, kInvestmentWindow);

        // 2. Loan A: 10,000,000 at 71.428%, 4 x 1 year.
        Keylet const loanA =
            openLoan(env, fixture, Number{10'000'000}, 4, TenthBips32(71'428), 0, kSecondsInYear);

        // 3. The first three installments take AssetsTotal across 10^9.
        payInstallments(env, depositor, asset, loanA, 3);
        BEAST_EXPECT(snapshotVault(env, fixture.vaultKeylet, asset).total > Number{1'000'000'000});

        // 4. The final payment, 1,000 above TotalValueOutstanding, closes loan A.
        Number const owed = env.le(loanA)->at(sfTotalValueOutstanding);
        env(loan::pay(depositor, loanA.key, asset(owed + 1'000)));
        env.close();
        BEAST_EXPECT(env.le(loanA)->at(sfPaymentRemaining) == 0);
        BEAST_EXPECT(env.le(fixture.brokerKeylet)->at(sfDebtTotal) == Number{0});
    }

    // FV_M4_3: a loan whose payments leave PrincipalOutstanding unchanged is still paid off.
    void
    testLoanStuck()
    {
        testcase("FV_M4_3 LoanStuck");

        using namespace test::jtx;
        Env env{*this, all_ | featureLendingProtocolV1_1};

        // 1. MPT vault that holds 5,000.
        auto const [issuer, owner, depositor, asset] =
            setupMpt(env, {.maxAmt = 100'000, .withDepositor = true, .holderFunds = 10'000});
        auto const fixture =
            setupLendingVault(env, owner, depositor, asset, Number{5'000}, kInvestmentWindow);

        // 2. Loan A: 1 at 50%, 3 x 1 year. TotalValueOutstanding is 3.
        Keylet const loanA =
            openLoan(env, fixture, Number{1}, 3, TenthBips32(50'000), 0, kSecondsInYear);

        // 3. The first two payments of 1 are interest only. PrincipalOutstanding stays 1.
        for (int paid = 0; paid < 2; ++paid)
        {
            env(loan::pay(depositor, loanA.key, asset(Number{1})));
            env.close();
            BEAST_EXPECT(env.le(loanA)->at(sfPrincipalOutstanding) == Number{1});
        }

        // 4. The third payment of 1 pays the principal and closes loan A.
        env(loan::pay(depositor, loanA.key, asset(Number{1})));
        env.close();
        BEAST_EXPECT(env.le(loanA)->at(sfPaymentRemaining) == 0);
    }

    // FV_M4_5: a loan is paid off after another loan took AssetsTotal across a power of ten.
    void
    testLoanSharedVaultUnpayable()
    {
        testcase("FV_M4_5 LoanSharedVaultUnpayable");

        using namespace test::jtx;
        using namespace loan;
        Env env{*this, all_ | featureLendingProtocolV1_1};

        // 1. Vault that holds 972,000,000.
        auto const accounts = setupIou(
            env, {.depositorTrust = kTrustLimit, .depositorFunds = Number{10'000'000'000LL}});
        auto const& [issuer, owner, depositor, asset] = accounts;
        Account const borrower{"borrower"};
        fundIouHolder(env, borrower, accounts, kTrustLimit, Number{10'000'000'000LL});
        auto const fixture =
            setupLendingVault(env, owner, depositor, asset, Number{972'000'000}, kInvestmentWindow);

        // 2. Loan A: 10,000,000 at 10%, 4 x 1 year.
        Keylet const loanA =
            openLoan(env, fixture, Number{10'000'000}, 4, TenthBips32(10'000), 0, kSecondsInYear);

        // 3. Loan B: 200,000,000 at 10% to a separate borrower, 2 x 1 year.
        Keylet const loanB = keylet::loan(fixture.brokerKeylet.key, SeqProxy::rawSequence(2));
        env(loan::set(borrower, fixture.brokerKeylet.key, Number{200'000'000}),
            kInterestRate(TenthBips32(10'000)),
            kPaymentTotal(2),
            kPaymentInterval(kSecondsInYear),
            Sig(sfCounterpartySignature, owner),
            Fee(env.current()->fees().base * 2));
        env.close();

        // 4. Loan B is paid off. Its interest takes AssetsTotal across 10^9.
        payInstallments(env, borrower, asset, loanB, 1);
        Number const owedB = env.le(loanB)->at(sfTotalValueOutstanding);
        env(loan::pay(borrower, loanB.key, asset(owedB + 1'000)));
        env.close();
        BEAST_EXPECT(snapshotVault(env, fixture.vaultKeylet, asset).total > Number{1'000'000'000});

        // 5. Loan A's three installments and its final payment succeed.
        payInstallments(env, depositor, asset, loanA, 3);
        Number const owedA = env.le(loanA)->at(sfTotalValueOutstanding);
        env(loan::pay(depositor, loanA.key, asset(owedA + 1'000)));
        env.close();
        BEAST_EXPECT(env.le(loanA)->at(sfPaymentRemaining) == 0);
    }

    // FV_M4_6: an early full payment succeeds after AssetsTotal crossed a power of ten.
    void
    testLoanFullPayoffStuck()
    {
        testcase("FV_M4_6 LoanFullPayoffStuck");

        using namespace test::jtx;
        using namespace loan;
        using namespace std::chrono_literals;
        Env env{*this, all_ | featureLendingProtocolV1_1};

        // 1. Vault that holds 999,000,000.
        auto const [issuer, owner, depositor, asset] = setupIou(
            env, {.depositorTrust = kTrustLimit, .depositorFunds = Number{2'000'000'000LL}});
        auto const fixture =
            setupLendingVault(env, owner, depositor, asset, Number{999'000'000}, kInvestmentWindow);

        // 2. Loan A: 200,000,000 at 8.15% with a CloseInterestRate of 5%, 36 x 30 days.
        Keylet const loanA = keylet::loan(fixture.brokerKeylet.key, SeqProxy::rawSequence(1));
        env(loan::set(depositor, fixture.brokerKeylet.key, Number{200'000'000}),
            kInterestRate(TenthBips32(8'150)),
            kCloseInterestRate(TenthBips32(5'000)),
            kPaymentTotal(36),
            kPaymentInterval(30 * 24 * 60 * 60),
            Sig(sfCounterpartySignature, owner),
            Fee(env.current()->fees().base * 2));
        env.close();

        // 3. The first installment takes AssetsTotal across 10^9.
        payInstallments(env, depositor, asset, loanA, 1);
        BEAST_EXPECT(snapshotVault(env, fixture.vaultKeylet, asset).total > Number{1'000'000'000});

        // 4. 15 days later a full payment of TotalValueOutstanding + 200,000,000 closes loan A.
        env.close(env.now() + 15 * 24h);
        Number const owed = env.le(loanA)->at(sfTotalValueOutstanding);
        env(loan::pay(depositor, loanA.key, asset(owed + 200'000'000), tfLoanFullPayment));
        env.close();
        BEAST_EXPECT(env.le(loanA)->at(sfPaymentRemaining) == 0);
    }

    // FV_M4_6: a late final payment succeeds after AssetsTotal crossed a power of ten.
    void
    testLoanLatePaymentStuck()
    {
        testcase("FV_M4_6 LoanLatePaymentStuck");

        using namespace test::jtx;
        using namespace loan;
        using namespace std::chrono_literals;
        Env env{*this, all_ | featureLendingProtocolV1_1};

        // 1. Vault that holds 984,675,729.
        auto const [issuer, owner, depositor, asset] = setupIou(
            env, {.depositorTrust = kTrustLimit, .depositorFunds = Number{2'000'000'000LL}});
        auto const fixture =
            setupLendingVault(env, owner, depositor, asset, Number{984'675'729}, kInvestmentWindow);

        // 2. Loan A: 200,000,000 at 6.2% with a LatePaymentFee of 10, 36 x 30 days.
        Keylet const loanA = keylet::loan(fixture.brokerKeylet.key, SeqProxy::rawSequence(1));
        env(loan::set(depositor, fixture.brokerKeylet.key, Number{200'000'000}),
            kInterestRate(TenthBips32(6'200)),
            kLatePaymentFee(Number{10}),
            kPaymentTotal(36),
            kPaymentInterval(30 * 24 * 60 * 60),
            Sig(sfCounterpartySignature, owner),
            Fee(env.current()->fees().base * 2));
        env.close();

        // 3. The first 35 installments take AssetsTotal across 10^9.
        payInstallments(env, depositor, asset, loanA, 35);
        BEAST_EXPECT(snapshotVault(env, fixture.vaultKeylet, asset).total > Number{1'000'000'000});

        // 4. The final payment, a day late and 100,000 above TotalValueOutstanding, closes loan A.
        env.close(nextPaymentDueDate(env, loanA) + 24h);
        Number const owed = env.le(loanA)->at(sfTotalValueOutstanding);
        env(loan::pay(depositor, loanA.key, asset(owed + 100'000), tfLoanLatePayment));
        env.close();
        BEAST_EXPECT(env.le(loanA)->at(sfPaymentRemaining) == 0);
    }

    // FV_M4_6: an overpayment succeeds after AssetsTotal crossed a power of ten.
    void
    testLoanOverpaymentStuck()
    {
        testcase("FV_M4_6 LoanOverpaymentStuck");

        using namespace test::jtx;
        Env env{*this, all_ | featureLendingProtocolV1_1};

        // 1. Vault that holds 986,751,133.
        auto const [issuer, owner, depositor, asset] = setupIou(
            env, {.depositorTrust = kTrustLimit, .depositorFunds = Number{2'000'000'000LL}});
        auto const fixture =
            setupLendingVault(env, owner, depositor, asset, Number{986'751'133}, kInvestmentWindow);

        // 2. Loan A: 200,000,000 at 9.8% with overpayments allowed, 60 x 30 days.
        Keylet const loanA = openLoan(
            env,
            fixture,
            Number{200'000'000},
            60,
            TenthBips32(9'800),
            tfLoanOverpayment,
            30 * 24 * 60 * 60);

        // 3. The first 58 installments take AssetsTotal across 10^9.
        payInstallments(env, depositor, asset, loanA, 58);
        BEAST_EXPECT(snapshotVault(env, fixture.vaultKeylet, asset).total > Number{1'000'000'000});

        // 4. An overpayment of 8,399,489.88053 leaves 0.000001 of principal after installment 59.
        Number const overpayment{839'948'988'053LL, -5};
        Number const baseUnit{1, -6};
        env(loan::pay(depositor, loanA.key, asset(overpayment), tfLoanOverpayment));
        env.close();
        BEAST_EXPECT(env.le(loanA)->at(sfPrincipalOutstanding) == baseUnit);

        // 5. The last payment of 0.000001 closes loan A.
        env(loan::pay(depositor, loanA.key, asset(baseUnit)));
        env.close();
        BEAST_EXPECT(env.le(loanA)->at(sfPaymentRemaining) == 0);
    }

    // FV_M4_21: on a coarsened vault an installment below the vault's ULP can't be paid.
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
                // 2. Loan A: 700,000,000,000,000 at the maximum LateInterestRate, 5 x 1 day.
                .loanPrincipal = Number{700'000'000'000'000LL},
                // 3. Loan B: 0.5 to a separate borrower, 5 installments of 0.1, 1,000 days apart.
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

    // FV_M4_23: the last on-schedule payment of PeriodicPayment + LoanServiceFee is 1 ULP short.
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

    // FV_M4_25: on a coarsened vault LoanPay credits AssetsAvailable less than the principal paid.
    void
    testLoanPayForgivesPrincipal()
    {
        testcase("FV_M4_25 LoanPayForgivesPrincipal");

        using namespace test::jtx;
        using namespace std::chrono_literals;
        Env env{*this, all_ | featureLendingProtocolV1_1};
        auto const accounts =
            setupIou(env, {.depositorTrust = kTrustLimit, .depositorFunds = Number{10'000'000}});
        auto const& [issuer, owner, depositor, asset] = accounts;
        Account const borrower{"borrower"};
        fundIouHolder(env, borrower, accounts, kTrustLimit, Number{1});

        Number const installment{20'000'000'000'009LL, -10};
        std::uint32_t const paymentTotal = 5;
        Number const principal = installment * paymentTotal;
        auto const coarsened = coarsenVault(
            env,
            owner,
            depositor,
            asset,
            {
                // 1. Vault at Scale 10 that holds 899,999.
                .scale = 10,
                .depositAmount = Number{899'999},
                // 2. Loan A: 700,000 at the maximum LateInterestRate, 5 x 1 day.
                .loanPrincipal = Number{700'000},
                // 3. Loan B: 10,000.0000000045 to a separate borrower, 5 installments of
                // 2,000.0000000009, 1,000 days apart.
                .extraLoans = {ExtraLoan{
                    .principal = principal,
                    .paymentTotal = paymentTotal,
                    .paymentInterval = 1'000 * 24 * 60 * 60,
                    .borrower = borrower}},
                // 4. Loan A is paid 800 days late. AssetsAvailable is now on a grid of 10^-9.
                .overdueDays = 800,
            });
        expectCoarsened(env, coarsened);
        Keylet const vaultKeylet = coarsened.fixture.vaultKeylet;
        Keylet const loanB = coarsened.loanKeylets[1];

        // 5. The borrower pays loan B's 5 installments, each an hour before its due date.
        Number vaultReceived{0};
        for (std::uint32_t paid = 0; paid < paymentTotal; ++paid)
        {
            env.close(nextPaymentDueDate(env, loanB) - 1h);
            Number const principalBefore = env.le(loanB)->at(sfPrincipalOutstanding);
            Number const availableBefore = snapshotVault(env, vaultKeylet, asset).available;
            env(loan::pay(borrower, loanB.key, asset(installment)));
            env.close();
            Number const principalPaid =
                principalBefore - env.le(loanB)->at(sfPrincipalOutstanding);
            Number const credit =
                snapshotVault(env, vaultKeylet, asset).available - availableBefore;
            vaultReceived += credit;
            // BUG: AssetsAvailable rises by 2,000 for 2,000.0000000009 of principal paid.
            BEAST_EXPECTS(credit == principalPaid, to_string(credit));
        }

        // BUG: the vault receives 10,000 for the 10,000.0000000045 it lent.
        BEAST_EXPECTS(vaultReceived >= principal, to_string(vaultReceived));
    }

    // FV_M4_29: at a tiny InterestRate a payment fails because its interest part is negative.
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

    // FV_M4_30: on the loan of FV_M4_29 a late payment or an overpayment raises the interest due.
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

            // 3. The third installment, paid late or as an overpayment of the installment + 10.
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

    // FV_M4_31: at 60 tenth bips PrincipalOutstanding is up to 0.78 away from the schedule.
    void
    testLoanPayPrincipalSplit()
    {
        testcase("FV_M4_31 LoanPayPrincipalSplit");

        using namespace test::jtx;
        Env env{*this, all_ | featureLendingProtocolV1_1};

        // 1. Vault at Scale 2 that holds 1,000,000,000,000.
        auto const [issuer, owner, depositor, asset] = setupIou(
            env, {.depositorTrust = kTrustLimit, .depositorFunds = Number{2'000'000'000'000LL}});
        auto const fixture = setupLendingVault(
            env, owner, depositor, asset, Number{1'000'000'000'000LL}, kInvestmentWindow, 2);

        // 2. Loan A of FV_M4_29 at 60 tenth bips: 5,198,461,379.86, 30 x 60 s.
        std::uint32_t const paymentTotal = 30;
        std::uint32_t const paymentInterval = 60;
        Keylet const loanA = openLoan(
            env,
            fixture,
            Number{519'846'137'986LL, -2},
            paymentTotal,
            TenthBips32(60),
            0,
            paymentInterval);

        // 3. The schedule: after k installments PrincipalOutstanding is
        //    principal * (growth(30) - growth(k)) / growth(30), growth(k) = (1 + rate)^k - 1.
        double const principal = 5'198'461'379.86;
        double const rate = 60.0 / 100'000 * paymentInterval / kSecondsInYear;
        double const logGrowth = std::log1p(rate);
        double const totalGrowth = std::expm1(paymentTotal * logGrowth);

        // 4. The borrower pays the 30 installments. 173,282,050 covers one installment.
        Number const installment{173'282'050};
        Number largestDrift{0};
        for (std::uint32_t paid = 1; paid <= paymentTotal; ++paid)
        {
            env(loan::pay(depositor, loanA.key, asset(installment)));
            env.close();
            double const scheduled =
                principal * (totalGrowth - std::expm1(paid * logGrowth)) / totalGrowth;
            Number const drift = env.le(loanA)->at(sfPrincipalOutstanding) -
                Number{std::llround(scheduled * 100), -2};
            if (abs(drift) > abs(largestDrift))
                largestDrift = drift;
        }

        Number const baseUnit{1, -2};
        // BUG: PrincipalOutstanding is up to 0.78 away from the schedule.
        BEAST_EXPECTS(abs(largestDrift) <= baseUnit, to_string(largestDrift));
    }

    // FV_M4_32: with a huge LoanServiceFee or LatePaymentFee the vault gets what nobody paid.
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

            // 2. The borrower pays the 10^30 it holds, on time or after the due date.
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

    // FV_M4_34: an installment that is only management fee can't be paid.
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

    // FV_M4_35: a late installment that takes nothing off the loan fails with tecINVARIANT_FAILED.
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

        // 5. Installment 5, 0.2 years late, is 1 of late interest and takes nothing off the loan.
        env.close(nextPaymentDueDate(env, loanA) + std::chrono::seconds{oneYear / 5});
        // BUG: LoanInvariant rejects the payment with tecINVARIANT_FAILED.
        env(loan::pay(depositor, loanA.key, asset(Number{1}), tfLoanLatePayment), Ter(tesSUCCESS));
        env.close();
    }

    // FV_M4_39: with a huge ClosePaymentFee a full payment credits the vault what nobody paid.
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

    // FV_M4_40: a late payment that takes AssetsAvailable to a power of ten pays the borrower.
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
        Keylet const loanA =
            openLoanWithLateInterest(env, fixture, Number{450'000}, paymentTotalA, 60);

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

    // FV_M4_41: a coarsening late payment fails while a pending loan has a digit below the grid.
    void
    testLoanPayPendingSubUnit()
    {
        testcase("FV_M4_41 LoanPayPendingSubUnit");

        using namespace test::jtx;
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
        Keylet const loanA =
            openLoanWithLateInterest(env, fixture, Number{7'000'000'000LL}, 1, 24 * 60 * 60);

        // 3. Loan B: a two-step proposal of 12,345.678901 that starts in a year and stays pending.
        Keylet const loanB = proposeLoan(
            env, fixture, borrower, kSubGridPrincipal, env.now() + 365 * 24h, 30 * 24 * 60 * 60);

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

    // FV_M4_41: a coarsening full payment fails while a pending loan has a digit below the grid.
    void
    testLoanPayoffPendingSubUnit()
    {
        testcase("FV_M4_41 LoanPayoffPendingSubUnit");

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

        // 2. Loan A: 7,000,000,000 at 0% in 2 daily payments, CloseInterestRate 30%.
        Keylet const loanA = keylet::loan(fixture.brokerKeylet.key, SeqProxy::rawSequence(1));
        env(loan::set(depositor, fixture.brokerKeylet.key, Number{7'000'000'000LL}),
            kCloseInterestRate(percentageToTenthBips(30)),
            kPaymentTotal(2),
            kPaymentInterval(24 * 60 * 60),
            Sig(sfCounterpartySignature, owner),
            Fee(env.current()->fees().base * 2));
        env.close();

        // 3. Loan B, pending: 12,345.678901.
        Keylet const loanB = proposeLoan(
            env, fixture, borrower, kSubGridPrincipal, env.now() + 365 * 24h, 30 * 24 * 60 * 60);

        // 4. An hour later A's payoff interest takes AssetsAvailable past 10^16 base units.
        env.close(env.now() + 1h);
        STAmount const payoff = asset(Number{9'100'000'000LL}).value();
        // BUG: the vault invariant rejects the payment with tecINVARIANT_FAILED.
        env(loan::pay(depositor, loanA.key, payoff, tfLoanFullPayment), Ter(tesSUCCESS));
        env.close();

        // 5. Once the broker deletes B, the same payment succeeds and coarsens the vault.
        env(loan::del(owner, loanB.key));
        env.close();
        env(loan::pay(depositor, loanA.key, payoff, tfLoanFullPayment));
        env.close();
        expectCoarsened(env, fixture.vaultKeylet);
    }

    // FV_M4_41: once an overpayment coarsened the vault, the next payment fails the same way.
    void
    testLoanOverpaymentPendingSubUnit()
    {
        testcase("FV_M4_41 LoanOverpaymentPendingSubUnit");

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

        // 2. Loan A: 7,000,000,000 in 2 daily payments, OverpaymentInterestRate 60%.
        Keylet const loanA = keylet::loan(fixture.brokerKeylet.key, SeqProxy::rawSequence(1));
        env(loan::set(
                depositor, fixture.brokerKeylet.key, Number{7'000'000'000LL}, tfLoanOverpayment),
            kOverpaymentInterestRate(percentageToTenthBips(60)),
            kPaymentTotal(2),
            kPaymentInterval(24 * 60 * 60),
            Sig(sfCounterpartySignature, owner),
            Fee(env.current()->fees().base * 2));
        env.close();

        // 3. Loan B, pending: 12,345.678901.
        proposeLoan(
            env, fixture, borrower, kSubGridPrincipal, env.now() + 365 * 24h, 30 * 24 * 60 * 60);

        // 4. An hour later an overpayment of 6,900,000,000 takes AssetsTotal to 11,039,999,000.
        env.close(env.now() + 1h);
        env(loan::pay(depositor, loanA.key, asset(Number{6'900'000'000LL}), tfLoanOverpayment));
        env.close();
        expectCoarsened(env, fixture.vaultKeylet);

        // 5. The borrower pays the remaining 2,140,000,000.
        // BUG: the vault invariant rejects the payment with tecINVARIANT_FAILED.
        env(loan::pay(depositor, loanA.key, asset(Number{2'140'000'000LL})), Ter(tesSUCCESS));
        env.close();
    }

    // A coarsened IOU vault at Scale 10. Loan A has one instalment left and pending loan B has a
    // digit below the coarse grid.
    LendingFixture
    setupCoarsenedLastInstalment(test::jtx::Env& env, AssetAccounts const& accounts)
    {
        using namespace test::jtx;
        using namespace std::chrono_literals;
        auto const& [issuer, owner, depositor, asset] = accounts;

        // 1. Vault at Scale 10 with 899,999.
        auto const fixture =
            setupLendingVault(env, owner, depositor, asset, Number{899'999}, 15 * 365 * 24h, 10);

        // 2. Loan A: 700,000 in 5 daily installments with the maximum LateInterestRate. Loan B,
        //    pending: 100,000.0000000007 with a StartDate in 900 days.
        Keylet const loanA =
            openLoanWithLateInterest(env, fixture, Number{700'000}, 5, 24 * 60 * 60);
        Number const principalB{1'000'000'000'000'007LL, -10};
        proposeLoan(env, fixture, principalB, env.now() + 900 * 24h, 30 * 24 * 60 * 60);

        // 3. 800 days after A's grace period, 4 late installments of A coarsen the vault.
        closePastGrace(env, loanA);
        env.close(env.now() + 800 * 24h);
        for (int paid = 0; paid < 4; ++paid)
        {
            env(loan::pay(
                depositor, loanA.key, asset(kLatePaymentLimit).value(), tfLoanLatePayment));
            env.close();
        }
        BEAST_EXPECT(env.le(loanA)->at(sfPaymentRemaining) == 1);
        expectCoarsened(env, fixture.vaultKeylet);
        return fixture;
    }

    // FV_M4_41: on a coarsened vault the last instalment of the last loan fails the same way.
    void
    testLoanLastPaymentPendingSubUnit()
    {
        testcase("FV_M4_41 LoanLastPaymentPendingSubUnit");

        using namespace test::jtx;
        Env env{*this, all_ | featureLendingProtocolV1_1};
        auto const accounts = setupCoarsenIou(env);
        auto const fixture = setupCoarsenedLastInstalment(env, accounts);
        Keylet const loanA = keylet::loan(fixture.brokerKeylet.key, SeqProxy::rawSequence(1));

        // 4. The borrower pays A's last instalment late.
        STAmount const limit = accounts.asset(kLatePaymentLimit).value();
        // BUG: the vault invariant rejects the payment with tecINVARIANT_FAILED.
        env(loan::pay(accounts.depositor, loanA.key, limit, tfLoanLatePayment), Ter(tesSUCCESS));
        env.close();
    }

    // FV_M4_41: on a coarsened vault the default of the last loan fails the same way.
    void
    testLoanDefaultPendingSubUnit()
    {
        testcase("FV_M4_41 LoanDefaultPendingSubUnit");

        using namespace test::jtx;
        Env env{*this, all_ | featureLendingProtocolV1_1};
        auto const accounts = setupCoarsenIou(env);
        auto const fixture = setupCoarsenedLastInstalment(env, accounts);
        Keylet const loanA = keylet::loan(fixture.brokerKeylet.key, SeqProxy::rawSequence(1));
        Keylet const loanB = keylet::loan(fixture.brokerKeylet.key, SeqProxy::rawSequence(2));

        // 4. The broker defaults A.
        // BUG: the vault invariant rejects the default with tecINVARIANT_FAILED.
        env(loan::manage(accounts.owner, loanA.key, tfLoanDefault), Ter(tesSUCCESS));
        env.close();

        // 5. AssetsTotal is above the Open limit, so the borrower can't accept B. The broker
        //    can't delete it either, tecINVARIANT_FAILED is FV_M4_22.
        env(loan::accept(accounts.depositor, loanB.key), Ter(tecLIMIT_EXCEEDED));
        env.close();
        env(loan::del(accounts.owner, loanB.key), Ter(tecINVARIANT_FAILED));
        env.close();
    }

    // FV_M4_45: without fixCleanup3_1_3 the base fee of a LoanPay with a huge Amount overflows.
    void
    testLoanPayFeeOverflow()
    {
        testcase("FV_M4_45 LoanPayFeeOverflow");

        using namespace test::jtx;
        Env env{*this, (all_ | featureLendingProtocolV1_1) - fixCleanup3_1_3};

        // 1. Vault that holds 10,000.
        auto const [issuer, owner, depositor, asset] =
            setupIou(env, {.depositorTrust = kTrustLimit, .depositorFunds = Number{100'000}});
        auto const fixture =
            setupLendingVault(env, owner, depositor, asset, Number{10'000}, kInvestmentWindow);

        // 2. Loan A: 100 at 0%, 100 installments of 1.
        Keylet const loanA = openLoan(env, fixture, Number{100}, 100);

        // 3. A LoanPay of 5 * 10^18 counts as 5 * 10^18 installments, at one base fee per 5.
        STAmount const amount = asset(Number{5, 18}).value();
        XRPAmount const baseFee = env.current()->fees().base;
        auto const loanPayFee =
            calculateBaseFee(*env.current(), *env.jt(loan::pay(depositor, loanA.key, amount)).stx);
        if (!BEAST_EXPECT(loanPayFee))
            return;
        // BUG: the base fee of the LoanPay is -8,446,744,073,709,551,616 drops.
        BEAST_EXPECTS(*loanPayFee >= baseFee, to_string(*loanPayFee));

        // 4. The LoanPay is submitted with one base fee.
        // BUG: LoanPay returns tefEXCEPTION.
        env(loan::pay(depositor, loanA.key, amount), Fee(baseFee), Ter(telINSUF_FEE_P));
    }

    // FV_M4_47: one late payment clears the impairment of a loan that stays two installments late.
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

    // FV_M4_48: a full payment before StartDate pays no interest for the days since LoanAccept.
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

    // FV_M4_53: an XRP late payment whose late interest is above 10^17 drops returns tefEXCEPTION.
    void
    testLoanPayXRPRange()
    {
        testcase("FV_M4_53 LoanPayXRPRange");

        using namespace test::jtx;
        Env env{*this, all_ | featureLendingProtocolV1_1};
        Account const owner{"owner"};
        Account const depositor{"depositor"};
        env.fund(XRP(5'100'000'000LL), owner, depositor);
        env.close();

        // 1. An XRP vault with 5 * 10^15 drops, all lent in loan A at LateInterestRate 100%.
        PrettyAsset const asset{xrpIssue()};
        Number const principal{5'000'000'000'000'000LL};
        auto const fixture =
            setupLendingVault(env, owner, depositor, asset, principal, kLongInvestmentWindow);
        Keylet const loanA = openLoanWithLateInterest(env, fixture, principal);

        NetClock::time_point const due = nextPaymentDueDate(env, loanA);
        std::chrono::seconds const oneYear{365 * 24 * 60 * 60};
        STAmount const payment = asset(principal).value();

        // 2. Ten years late, with 5 * 10^16 drops of late interest, the principal is not enough.
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

    // FV_M4_54: in a Batch after the LoanSet of its loan, a large LoanPay costs one base fee.
    void
    testLoanPayBatchFee()
    {
        testcase("FV_M4_54 LoanPayBatchFee");

        using namespace test::jtx;
        using namespace loan;
        Env env{*this, all_ | featureLendingProtocolV1_1};
        Account const owner{"owner"};
        Account const depositor{"depositor"};
        env.fund(XRP(10'000'000), owner, depositor);
        env.close();

        // 1. An XRP vault that holds 1,000,000 XRP.
        PrettyAsset const asset{xrpIssue()};
        auto const fixture = setupLendingVault(
            env, owner, depositor, asset, XRP(1'000'000).number(), kInvestmentWindow);
        XRPAmount const baseFee = env.current()->fees().base;

        // 2. Loan A: 1,000 XRP at 0%, 200 installments of 5 XRP.
        Number const principal = XRP(1'000).number();
        std::uint32_t const paymentTotal = 200;
        Keylet const loanA = keylet::loan(fixture.brokerKeylet.key, SeqProxy::rawSequence(1));
        env(loan::set(depositor, fixture.brokerKeylet.key, principal),
            kPaymentTotal(paymentTotal),
            Sig(sfCounterpartySignature, owner),
            Fee(baseFee * 2));
        env.close();

        // 3. A LoanPay of 500 XRP pays 100 installments. 19 base fees do not cover it.
        STAmount const payment = XRP(500);
        env(loan::pay(depositor, loanA.key, payment), Fee(baseFee * 19), Ter(telINSUF_FEE_P));

        // 4. A Batch with the same LoanSet, for loan B, and the same LoanPay on loan B. The Batch
        //    fee counts one base fee for the LoanPay.
        Keylet const loanB = keylet::loan(fixture.brokerKeylet.key, SeqProxy::rawSequence(2));
        std::uint32_t const seq = env.seq(depositor);
        // BUG: the Batch returns tesSUCCESS.
        env(batch::outer(depositor, seq, batch::calcBatchFee(env, 1, 2), tfAllOrNothing),
            batch::Inner(
                env.json(
                    loan::set(depositor, fixture.brokerKeylet.key, principal),
                    kCounterparty(owner.id()),
                    kPaymentTotal(paymentTotal),
                    Sig(kNone),
                    Fee(kNone),
                    Seq(kNone)),
                seq + 1),
            batch::Inner(loan::pay(depositor, loanB.key, payment), seq + 2),
            batch::Sig(owner),
            Ter(telINSUF_FEE_P));
        env.close();
    }

    // FV_M4_55: a fee-free LoanPay fails with tecFROZEN when the broker is deep frozen.
    void
    testLoanPayZeroFeeBrokerDeepFrozen()
    {
        testcase("FV_M4_55 LoanPayZeroFeeBrokerDeepFrozen");

        using namespace test::jtx;
        Env env{*this, all_ | featureLendingProtocolV1_1};

        // 1. Vault that holds 1,000,000. The broker has no ManagementFeeRate and 1,000 of cover.
        auto const [issuer, owner, depositor, asset] = setupIou(
            env,
            {.depositorTrust = kTrustLimit,
             .depositorFunds = Number{2'000'000},
             .ownerFunds = Number{1'000}});
        auto const fixture =
            setupLendingVault(env, owner, depositor, asset, Number{1'000'000}, kInvestmentWindow);
        env(loan_broker::coverDeposit(owner, fixture.brokerKeylet.key, asset(1'000).value()));
        env.close();

        // 2. Loan A: 1,000 at 10% with no fees, 12 installments.
        Keylet const loanA = openLoan(env, fixture, Number{1'000}, 12, TenthBips32(10'000));

        // 3. The issuer deep freezes the trust lines of the broker owner and the broker account.
        Account const brokerAccount{"broker", env.le(fixture.brokerKeylet)->at(sfAccount)};
        env(trust(issuer, owner["USD"](0), tfSetFreeze | tfSetDeepFreeze));
        env(trust(issuer, brokerAccount["USD"](0), tfSetFreeze | tfSetDeepFreeze));
        env.close();

        // 4. The borrower pays the first installment.
        auto const loanSle = env.le(loanA);
        Number const installment =
            roundPeriodicPayment(asset, loanSle->at(sfPeriodicPayment), loanSle->at(sfLoanScale));
        // BUG: LoanPay returns tecFROZEN.
        env(loan::pay(depositor, loanA.key, asset(installment)), Ter(tesSUCCESS));
        env.close();
        // BUG: PaymentRemaining is still 12.
        BEAST_EXPECT(env.le(loanA)->at(sfPaymentRemaining) == 11);
    }

    // FV_M4_59: an XRP late payment that takes AssetsTotal above 10^17 drops returns tefEXCEPTION.
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

        // 1. An XRP vault with 9 * 10^15 drops, all lent to the depositor in loans A, B and C.
        PrettyAsset const asset{xrpIssue()};
        auto const fixture = setupLendingVault(
            env, owner, depositor, asset, Number{9'000'000'000'000'000LL}, kLongInvestmentWindow);
        Keylet const loanA = openLoanWithLateInterest(env, fixture, Number{100'000'000'000'000LL});
        Keylet const loanB =
            openLoanWithLateInterest(env, fixture, Number{4'400'000'000'000'000LL});
        openLoanWithLateInterest(env, fixture, Number{4'500'000'000'000'000LL});

        // 2. 20.5 years late, loan A is paid with its late interest, about 2.15 * 10^15 drops.
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
        env(loan::pay(depositor, loanB.key, payment, tfLoanLatePayment), Ter(tesSUCCESS));
        env.close();
    }

    // FV_M4_59: an MPT late payment that takes AssetsTotal above 2^63 - 1 returns tefEXCEPTION.
    void
    testLoanPayAssetsTotalMPTRange()
    {
        testcase("FV_M4_59 LoanPayAssetsTotalMPTRange");

        using namespace test::jtx;
        Env env{*this, all_ | featureLendingProtocolV1_1};

        // 1. An MPT with the largest supply, all of it held by the depositor. The vault holds
        //    9 * 10^15 of it, all lent to the depositor in loan A.
        auto const [issuer, owner, depositor, asset] = setupMpt(
            env,
            {.maxAmt = kMaxMpTokenAmount, .withDepositor = true, .holderFunds = kMaxMpTokenAmount});
        auto const fixture = setupLendingVault(
            env, owner, depositor, asset, Number{9'000'000'000'000'000LL}, kLongInvestmentWindow);
        Keylet const loanA =
            openLoanWithLateInterest(env, fixture, Number{9'000'000'000'000'000LL}, 1000, 60);

        // 2. Eight late installments, 3,552,303,357 seconds after the first due date. They take
        //    AssetsAvailable to 8,081,967,283,287,671,231.
        env.close(nextPaymentDueDate(env, loanA) + std::chrono::seconds{3'552'303'357});
        for (int paid = 0; paid < 8; ++paid)
        {
            env(loan::pay(
                depositor, loanA.key, env.balance(depositor, asset).value(), tfLoanLatePayment));
            env.close();
        }
        BEAST_EXPECT(
            env.le(fixture.vaultKeylet)->at(sfAssetsAvailable) ==
            Number{8'081'967'283'287'671'231LL});

        // 3. At time 4,015,937,045 the next instalment takes AssetsAvailable to 9.219 * 10^18 and
        //    AssetsTotal, with the 8.928 * 10^15 A still owes, to 9.228 * 10^18, above 2^63 - 1.
        env.close(NetClock::time_point{NetClock::duration{4'015'937'045}});
        // BUG: the result is tefEXCEPTION.
        env(loan::pay(
                depositor, loanA.key, env.balance(depositor, asset).value(), tfLoanLatePayment),
            Ter(tesSUCCESS));
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
        // testLoanPayForgivesPrincipal();            // FV_M4_25, by design
        // testLoanPayNegativeInterest();             // FV_M4_29
        // testLoanPayInterestDueRises();             // FV_M4_30
        // testLoanPayPrincipalSplit();               // FV_M4_31, by design
        // testLoanPayFeeSwampsInstalment();          // FV_M4_32
        // testLoanPayFeeOnlyInstalment();            // FV_M4_34
        // testLoanPayZeroValueInstalment();          // FV_M4_35
        // testLoanPayCloseFeeSwampsPayoff();         // FV_M4_39
        // testLoanPayNegativeCredit();               // FV_M4_40
        // testLoanPayPendingSubUnit();               // FV_M4_41
        // testLoanPayoffPendingSubUnit();            // FV_M4_41
        // testLoanOverpaymentPendingSubUnit();       // FV_M4_41
        // testLoanLastPaymentPendingSubUnit();       // FV_M4_41
        // testLoanDefaultPendingSubUnit();           // FV_M4_41
        // testLoanPayFeeOverflow();                  // FV_M4_45, without fixCleanup3_1_3
        // testLoanPayClearsImpairmentWhileLate();    // FV_M4_47
        // testLoanPayBeforeStartDate();              // FV_M4_48
        // testLoanPayXRPRange();                     // FV_M4_53
        // testLoanPayBatchFee();                     // FV_M4_54
        // testLoanPayZeroFeeBrokerDeepFrozen();      // FV_M4_55
        // testLoanPayAssetsTotalRange();             // FV_M4_59
        // testLoanPayAssetsTotalMPTRange();          // FV_M4_59

        // Cases that pass today, kept as regression tests.
        testLoanConservation();                       // FV_M4_1
        testLoanUnpayable();                          // FV_M4_2
        testLoanStuck();                              // FV_M4_3
        testLoanSharedVaultUnpayable();               // FV_M4_5
        testLoanFullPayoffStuck();                    // FV_M4_6
        testLoanLatePaymentStuck();                   // FV_M4_6
        testLoanOverpaymentStuck();                   // FV_M4_6
        // clang-format on
    }
};

BEAST_DEFINE_TESTSUITE(LoanPayFindings, formal_verification, xrpl);

}  // namespace xrpl
