#include <test/app/lending/LoanManageFixedPrecisionBase.h>
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
#include <xrpl/beast/utility/Zero.h>
#include <xrpl/ledger/helpers/LendingHelpers.h>
#include <xrpl/ledger/helpers/VaultHelpers.h>
#include <xrpl/protocol/Feature.h>
#include <xrpl/protocol/Indexes.h>
#include <xrpl/protocol/Issue.h>
#include <xrpl/protocol/Keylet.h>
#include <xrpl/protocol/Protocol.h>
#include <xrpl/protocol/SField.h>
#include <xrpl/protocol/STAmount.h>
#include <xrpl/protocol/SeqProxy.h>
#include <xrpl/protocol/TER.h>
#include <xrpl/protocol/TxFlags.h>
#include <xrpl/protocol/Units.h>

#include <chrono>
#include <cstdint>
#include <optional>

namespace xrpl {

// One failing test per open bug in LoanSet, LoanAccept, LoanDelete and LoanManage. A test is
// enabled by uncommenting its call in run().
class LoanFindings_test : public LoanManageFixedPrecisionBase
{
    // Proposes a two-step loan of the fixture's owner to its depositor and returns its keylet.
    // The loan stays pending until the depositor accepts it.
    static Keylet
    proposeLoan(
        test::jtx::Env& env,
        LendingFixture const& fixture,
        Number const& principal,
        NetClock::time_point startDate,
        std::uint32_t paymentInterval,
        TenthBips32 interestRate = TenthBips32{0})
    {
        using namespace test::jtx;

        Keylet const& broker = fixture.brokerKeylet;
        Keylet const loanKeylet =
            keylet::loan(broker.key, SeqProxy::rawSequence(env.le(broker)->at(sfLoanSequence)));
        env(loan::set(fixture.owner, broker.key, principal),
            loan::kBorrower(fixture.depositor),
            loan::kStartDate(startDate.time_since_epoch().count()),
            loan::kInterestRate(interestRate),
            loan::kPaymentInterval(paymentInterval));
        env.close();
        return loanKeylet;
    }

    // Creates the loan whose late payment coarsens the vault: 5 daily installments at the
    // maximum LateInterestRate.
    static Keylet
    openCoarseningLoan(test::jtx::Env& env, LendingFixture const& fixture, Number const& principal)
    {
        using namespace test::jtx;

        Keylet const& broker = fixture.brokerKeylet;
        Keylet const loanKeylet =
            keylet::loan(broker.key, SeqProxy::rawSequence(env.le(broker)->at(sfLoanSequence)));
        env(loan::set(fixture.depositor, broker.key, principal),
            loan::kLateInterestRate(lending::kMaxLateInterestRate),
            loan::kPaymentTotal(5),
            loan::kPaymentInterval(24 * 60 * 60),
            Sig(sfCounterpartySignature, fixture.owner),
            Fee(env.current()->fees().base * 2));
        env.close();
        return loanKeylet;
    }

    // Pays the loan's first installment 800 days after its grace period. The late interest
    // takes AssetsAvailable past 16 digits, so the vault coarsens.
    void
    payCoarseningLoanLate(
        test::jtx::Env& env,
        LendingFixture const& fixture,
        PrettyAsset const& asset,
        Keylet const& loan)
    {
        using namespace test::jtx;
        using namespace std::chrono_literals;

        auto const sle = env.le(loan);
        std::uint32_t const graceEnd = sle->at(sfNextPaymentDueDate) + sle->at(sfGracePeriod);
        env.close(NetClock::time_point{NetClock::duration{graceEnd}} + 800 * 24h);
        // Ten times the principal is enough for the installment and its late interest.
        Number const limit = Number{sle->at(sfPrincipalOutstanding)} * 10;
        env(loan::pay(fixture.depositor, loan.key, asset(limit).value(), tfLoanLatePayment));
        env.close();
        expectCoarsened(env, fixture.vaultKeylet);
    }

    // Takes AssetsAvailable to 999,999,999,999,999.9, one base unit below 10^15. Loan A's late
    // payment coarsens the vault. In Redemption a withdrawal and installments of 0.1 follow.
    void
    moveAvailableBelowPowerOfTen(
        test::jtx::Env& env,
        AssetAccounts const& accounts,
        LendingFixture const& fixture,
        Keylet const& loanA)
    {
        using namespace test::jtx;
        using namespace std::chrono_literals;

        PrettyAsset const& asset = accounts.asset;
        Keylet const& vault = fixture.vaultKeylet;
        Keylet const& broker = fixture.brokerKeylet;

        // 1. Loan C: 2 in 20 installments of 0.1. Its borrower holds only 1, so that a payment
        //    of 0.1 fits the 16 digits of its balance.
        Account const topUpBorrower{"topUpBorrower"};
        fundIouHolder(env, topUpBorrower, accounts, Number{1'000}, Number{1});
        Keylet const loanC =
            keylet::loan(broker.key, SeqProxy::rawSequence(env.le(broker)->at(sfLoanSequence)));
        env(loan::set(topUpBorrower, broker.key, Number{2}),
            loan::kPaymentTotal(20),
            loan::kPaymentInterval(24 * 60 * 60),
            Sig(sfCounterpartySignature, fixture.owner),
            Fee(env.current()->fees().base * 2));
        env.close();

        // 2. A's late payment coarsens the vault.
        payCoarseningLoanLate(env, fixture, asset, loanA);

        // 3. After RedemptionDate the depositor withdraws to 0.9 below the target. C's first 9
        //    installments of 0.1 add the rest.
        Number const target{9'999'999'999'999'999LL, -1};
        env.close(fixture.redemptionDate + 1s);
        Number const withdrawal = Number{env.le(vault)->at(sfAssetsAvailable)} - target + 1;
        env(fixture.vault.withdraw(
            {.depositor = fixture.depositor, .id = vault.key, .amount = asset(withdrawal)}));
        env.close();
        for (int paid = 0; paid < 9; ++paid)
        {
            env(loan::pay(
                topUpBorrower, loanC.key, asset(Number{1, -1}).value(), tfLoanLatePayment));
            env.close();
        }
        BEAST_EXPECT(env.le(vault)->at(sfAssetsAvailable) == target);
    }

    // A coarsened Scale 1 vault in Redemption with AssetsAvailable at 999,999,999,999,999.9. The
    // returned fixture has its second broker, which holds the given cover and lends loan B of 1.
    LendingFixture
    setupVaultBelowPowerOfTen(
        test::jtx::Env& env,
        TenthBips32 coverRateMinimum,
        Number const& cover)
    {
        using namespace test::jtx;
        using namespace std::chrono_literals;

        auto const accounts = setupIou(
            env,
            {.depositorTrust = Number{30'000'000'000'000'000LL},
             .depositorFunds = Number{10'000'000'000'000'000LL},
             .ownerFunds = Number{100}});
        auto const& [issuer, owner, depositor, asset] = accounts;

        // 1. Vault at Scale 1 with 899,999,000,000,000, just under its Open limit.
        auto const fixture = setupLendingVault(
            env, owner, depositor, asset, Number{899'999'000'000'000LL}, 900 * 24h, 1);

        // 2. A second broker with a CoverRateLiquidation of 100% and the given cover.
        LendingFixture coverFixture = fixture;
        coverFixture.brokerKeylet =
            keylet::loanBroker(owner.id(), SeqProxy::rawSequence(env.seq(owner)));
        env(loan_broker::set(owner, fixture.vaultKeylet.key),
            loan_broker::kCoverRateMinimum(coverRateMinimum),
            loan_broker::kCoverRateLiquidation(percentageToTenthBips(100)));
        env.close();
        env(loan_broker::coverDeposit(owner, coverFixture.brokerKeylet.key, asset(cover).value()));
        env.close();

        // 3. Loan A: 700,000,000,000,000 with the maximum LateInterestRate. Loan B: 1 on the
        //    second broker.
        Keylet const loanA = openCoarseningLoan(env, fixture, Number{700'000'000'000'000LL});
        openLoan(env, coverFixture, Number{1}, 1, TenthBips32{0}, 0, 24 * 60 * 60);

        // 4. Loan C and A's late payment take AssetsAvailable to 999,999,999,999,999.9.
        moveAvailableBelowPowerOfTen(env, accounts, fixture, loanA);
        return coverFixture;
    }

    // FV_M4_18: the cover a default pays is based on DebtTotal before the default, so the loss
    // from defaulting the same two loans depends on their order.
    void
    testLoanDefaultOrder()
    {
        testcase("FV_M4_18 LoanDefaultOrder");

        using namespace test::jtx;
        using namespace std::chrono_literals;

        // The drop of AssetsTotal when A is defaulted first and when B is defaulted first.
        Number lossAFirst;
        Number lossBFirst;
        for (bool const defaultAFirst : {true, false})
        {
            Env env{*this, all_ | featureLendingProtocolV1_1};
            auto const [issuer, owner, depositor, asset] = setupIou(
                env,
                {.depositorTrust = Number{2'000'000},
                 .ownerTrust = Number{20'000},
                 .ownerFunds = Number{10'000}});

            // 1. Vault with 1,000,000. Broker: CoverRateMinimum 10%, CoverRateLiquidation 25%,
            //    cover 10,000.
            auto const fixture = setupLendingVault(
                env,
                owner,
                depositor,
                asset,
                Number{1'000'000},
                10 * 365 * 24h,
                std::nullopt,
                percentageToTenthBips(10),
                percentageToTenthBips(25));
            Keylet const& vault = fixture.vaultKeylet;
            env(loan_broker::coverDeposit(owner, fixture.brokerKeylet.key, asset(10'000).value()));
            env.close();

            // 2. Loan A: 1,000. Loan B: 9,000. Both at 10% in one payment after 36.5 days.
            TenthBips32 const interestRate = percentageToTenthBips(10);
            Keylet const loanA =
                openLoan(env, fixture, Number{1'000}, 1, interestRate, 0, 3'153'600);
            Keylet const loanB =
                openLoan(env, fixture, Number{9'000}, 1, interestRate, 0, 3'153'600);

            // 3. Both loans miss their payment and the broker owner defaults them.
            Number const assetsTotalBefore = env.le(vault)->at(sfAssetsTotal);
            env.close(env.now() + 40 * 24h);
            Keylet const& first = defaultAFirst ? loanA : loanB;
            Keylet const& second = defaultAFirst ? loanB : loanA;
            env(loan::manage(owner, first.key, tfLoanDefault));
            env.close();
            env(loan::manage(owner, second.key, tfLoanDefault));
            env.close();
            Number& loss = defaultAFirst ? lossAFirst : lossBFirst;
            loss = assetsTotalBefore - Number{env.le(vault)->at(sfAssetsTotal)};
        }

        // BUG: the vault loses 9,525 with A first and 9,725 with B first.
        BEAST_EXPECTS(
            lossAFirst == lossBFirst,
            "the vault loses " + to_string(lossAFirst) + " with A first and " +
                to_string(lossBFirst) + " with B first");
    }

    // FV_M4_19: for a very small InterestRate LoanSet computes an interest many times too high,
    // or below zero and then returns tecPRECISION_LOSS.
    void
    testLoanPeriodicPaymentPrecision()
    {
        testcase("FV_M4_19 LoanPeriodicPaymentPrecision");

        using namespace test::jtx;
        Env env{*this, all_ | featureLendingProtocolV1_1};
        auto const [issuer, owner, depositor, asset] =
            setupIou(env, {.depositorTrust = Number{2'000'000}});

        // 1. Vault with 1,000,000. Broker without cover or fees.
        auto const fixture = setupLendingVault(env, owner, depositor, asset, Number{1'000'000});

        // 2. Loan A: 1,000 at InterestRate 2 (0.002% a year), 50 x 60 s. Its exact interest is
        //    0.00000097, which rounds up to 0.000001 at LoanScale.
        Keylet const loanA = openLoan(env, fixture, Number{1'000}, 50, TenthBips32{2}, 0, 60);
        Number const expectedInterestA{1, -6};
        auto const loanASle = env.le(loanA);
        Number const interestA = Number{loanASle->at(sfTotalValueOutstanding)} -
            Number{loanASle->at(sfPrincipalOutstanding)};

        // BUG: A's interest is 0.000012, twelve times too high.
        BEAST_EXPECTS(interestA == expectedInterestA, "A's interest is " + to_string(interestA));

        // 3. Loan B: the same at InterestRate 3. Its exact interest is 0.00000146.
        // BUG: LoanSet computes a negative interest for B and returns tecPRECISION_LOSS.
        env(loan::set(depositor, fixture.brokerKeylet.key, Number{1'000}),
            loan::kInterestRate(TenthBips32{3}),
            loan::kPaymentTotal(50),
            loan::kPaymentInterval(60),
            Sig(sfCounterpartySignature, owner),
            Fee(env.current()->fees().base * 2),
            Ter(tesSUCCESS));
        env.close();
    }

    // FV_M4_22: a pending loan proposed before its vault coarsens can't be deleted. LoanDelete
    // returns tecINVARIANT_FAILED and the principal stays in AssetsReserved.
    void
    testLoanPendingCoarsened()
    {
        testcase("FV_M4_22 LoanPendingCoarsened");

        using namespace test::jtx;
        using namespace std::chrono_literals;
        Env env{*this, all_ | featureLendingProtocolV1_1};
        auto const [issuer, owner, depositor, asset] = setupCoarsenIou(env);

        // 1. Vault at Scale 10 with 899,999, just under its Open limit of 900,000.
        auto const fixture =
            setupLendingVault(env, owner, depositor, asset, Number{899'999}, 15 * 365 * 24h, 10);

        // 2. Loan A: 700,000 in 5 daily installments with the maximum LateInterestRate.
        Keylet const loanA = openCoarseningLoan(env, fixture, Number{700'000});

        // 3. Loan B, two-step and left pending: 100,000.0000000007 with a StartDate in 900 days.
        Number const principalB{1'000'000'000'000'007LL, -10};
        Keylet const loanB =
            proposeLoan(env, fixture, principalB, env.now() + 900 * 24h, 30 * 24 * 60 * 60);

        // 4. A's late payment takes AssetsAvailable to 1,774,247.129122271, on a grid of 10^-9.
        payCoarseningLoanLate(env, fixture, asset, loanA);
        BEAST_EXPECT(
            env.le(fixture.vaultKeylet)->at(sfAssetsAvailable) ==
            (Number{1'774'247'129'122'271LL, -9}));

        // 5. AssetsTotal is above the Open limit, so the borrower can't accept B.
        env(loan::accept(depositor, loanB.key), Ter(tecLIMIT_EXCEEDED));
        env.close();

        // 6. The broker owner deletes B.
        // BUG: LoanDelete returns tecINVARIANT_FAILED.
        env(loan::del(owner, loanB.key), Ter(tesSUCCESS));
        env.close();
    }

    // FV_M4_27: a default fails with tecINTERNAL when AssetsAvailable plus the cover rounds up to
    // a power of ten, because the amount the cover pays to the vault comes out negative.
    void
    testLoanDefaultNegativeCover()
    {
        testcase("FV_M4_27 LoanDefaultNegativeCover");

        using namespace test::jtx;
        Env env{*this, all_ | featureLendingProtocolV1_1};

        // 1. AssetsAvailable is 999,999,999,999,999.9. Loan B of 1 is on a broker with a
        //    CoverRateMinimum of 9.999% that holds its minimum cover of 0.1.
        auto const fixture = setupVaultBelowPowerOfTen(env, TenthBips32{9'999}, Number{1, -1});
        Keylet const loanB = keylet::loan(fixture.brokerKeylet.key, SeqProxy::rawSequence(1));

        // 2. B's default cover is 1 x 9.999% x 100% = 0.09999. This is the amount LoanManage
        //    credits to the vault for it.
        Number const defaultCover{9'999, -5};
        STAmount const vaultCredit = creditToPosteriorAvailableScale(
            env.le(fixture.vaultKeylet), defaultCover, Number::RoundingMode::Downward);

        // BUG: creditToPosteriorAvailableScale returns -0.9.
        BEAST_EXPECTS(
            vaultCredit >= beast::kZero, "the vault is credited " + to_string(vaultCredit));

        // 3. The broker owner defaults B.
        // BUG: LoanManage returns tecINTERNAL.
        env(loan::manage(fixture.owner, loanB.key, tfLoanDefault), Ter(tesSUCCESS));
        env.close();
    }

    // FV_M4_28: on a coarsened vault, a default whose cover is enough to repay the loan in full
    // pays the vault less than the principal, and the vault absorbs the difference.
    void
    testLoanDefaultCoveredLoss()
    {
        testcase("FV_M4_28 LoanDefaultCoveredLoss");

        using namespace test::jtx;
        Env env{*this, all_ | featureLendingProtocolV1_1};

        // 1. AssetsAvailable is 999,999,999,999,999.9. Loan B of 1 is on a broker with a
        //    CoverRateMinimum of 100% and a cover of 5, so its default cover is the principal.
        auto const fixture = setupVaultBelowPowerOfTen(env, percentageToTenthBips(100), Number{5});
        Keylet const& vault = fixture.vaultKeylet;
        Keylet const& broker = fixture.brokerKeylet;
        Keylet const loanB = keylet::loan(broker.key, SeqProxy::rawSequence(1));
        Number const coverBefore = env.le(broker)->at(sfCoverAvailable);
        // getAssetsTotal is AssetsAvailable + AssetsDeployed.
        Number const assetsBefore = getAssetsTotal(env.le(vault));

        // 2. The broker owner defaults B.
        env(loan::manage(fixture.owner, loanB.key, tfLoanDefault));
        env.close();
        Number const coverPaid = coverBefore - env.le(broker)->at(sfCoverAvailable);
        Number const assetsLost = assetsBefore - getAssetsTotal(env.le(vault));

        // BUG: the cover pays 0.1 of B's principal of 1.
        BEAST_EXPECTS(coverPaid >= Number{1}, "the cover paid " + to_string(coverPaid));

        // BUG: AssetsAvailable + AssetsDeployed drops by 0.9.
        BEAST_EXPECTS(
            assetsLost <= beast::kZero,
            "AssetsAvailable + AssetsDeployed dropped by " + to_string(assetsLost));
    }

    // FV_M4_33: two pending loans each pass LoanSet's Open limit check, but once one is accepted
    // LoanAccept of the other returns tecLIMIT_EXCEEDED.
    void
    testLoanAcceptOpenLimit()
    {
        testcase("FV_M4_33 LoanAcceptOpenLimit");

        using namespace test::jtx;
        using namespace std::chrono_literals;
        Env env{*this, all_ | featureLendingProtocolV1_1};
        auto const [issuer, owner, depositor, asset] = setupIou(
            env, {.depositorTrust = Number{2'000'000}, .depositorFunds = Number{1'000'000}});

        // 1. Vault at Scale 10 with 880,000. Its Open limit is 900,000.
        auto const fixture =
            setupLendingVault(env, owner, depositor, asset, Number{880'000}, 2 * 365 * 24h, 10);

        // 2. Loans A and B, two-step: 50,000 at 30% for one year each, so 15,000 of interest
        //    each. LoanSet checks 880,000 + 15,000 against the Open limit for both.
        NetClock::time_point const startDate = env.now() + 30 * 24h;
        std::uint32_t const oneYear = 365 * 24 * 60 * 60;
        TenthBips32 const interestRate = percentageToTenthBips(30);
        Keylet const loanA =
            proposeLoan(env, fixture, Number{50'000}, startDate, oneYear, interestRate);
        Keylet const loanB =
            proposeLoan(env, fixture, Number{50'000}, startDate, oneYear, interestRate);

        // 3. The borrower accepts A. Its interest of 15,000 moves into YieldUnrealized.
        env(loan::accept(depositor, loanA.key));
        env.close();

        // 4. The borrower accepts B.
        // BUG: LoanAccept returns tecLIMIT_EXCEEDED, so B can only be deleted.
        env(loan::accept(depositor, loanB.key), Ter(tesSUCCESS));
        env.close();
    }

    // FV_M4_42: LoanSet stores a ManagementFeeOutstanding 1 ULP at LoanScale above the broker's
    // share of the interest rounded down.
    void
    testLoanSetManagementFeeRoundsUp()
    {
        testcase("FV_M4_42 LoanSetManagementFeeRoundsUp");

        using namespace test::jtx;
        Env env{*this, all_ | featureLendingProtocolV1_1};
        auto const [issuer, owner, depositor, asset] = setupIou(
            env,
            {.depositorTrust = Number{1'000'000'000'000LL}, .depositorFunds = Number{620'000'000}});

        // 1. Vault at Scale 6 with 620,000,000. Broker with a ManagementFeeRate of 9.999%.
        auto const fixture = setupLendingVault(
            env,
            owner,
            depositor,
            asset,
            Number{620'000'000},
            std::chrono::seconds{900'000'000},
            6,
            TenthBips32{0},
            TenthBips32{0},
            TenthBips16{9'999});

        // 2. Loan A: 615,000,000.00667 at 100% in one payment after 15 years. Its interest is
        //    9,225,000,000.10005 and 9.999% of that is 922,407,750.0100039995.
        Number const principal{61'500'000'000'667LL, -5};
        std::uint32_t const fifteenYears = 15 * 365 * 24 * 60 * 60;
        Keylet const loanA =
            openLoan(env, fixture, principal, 1, percentageToTenthBips(100), 0, fifteenYears);
        Number const expectedFee{922'407'750'010'003LL, -6};
        Number const fee = env.le(loanA)->at(sfManagementFeeOutstanding);

        // BUG: ManagementFeeOutstanding is 922,407,750.010004, 1 ULP at LoanScale too high.
        BEAST_EXPECTS(fee == expectedFee, "ManagementFeeOutstanding is " + to_string(fee));
    }

    // FV_M4_46: LoanAccept pays out a pending loan while CoverAvailable is below the minimum
    // cover, where LoanSet returns tecINSUFFICIENT_FUNDS.
    void
    testLoanAcceptBelowMinimumCover()
    {
        testcase("FV_M4_46 LoanAcceptBelowMinimumCover");

        using namespace test::jtx;
        using namespace std::chrono_literals;
        Env env{*this, all_ | featureLendingProtocolV1_1};
        auto const [issuer, owner, depositor, asset] =
            setupIou(env, {.depositorTrust = Number{100'000}, .ownerFunds = Number{1'000}});

        // 1. Vault with 10,000. Broker: CoverRateMinimum 10%, CoverRateLiquidation 100%, cover
        //    200.
        auto const fixture = setupLendingVault(
            env,
            owner,
            depositor,
            asset,
            Number{10'000},
            std::chrono::seconds{1'000'000},
            std::nullopt,
            percentageToTenthBips(10),
            percentageToTenthBips(100));
        Keylet const& broker = fixture.brokerKeylet;
        env(loan_broker::coverDeposit(owner, broker.key, asset(200).value()));
        env.close();

        // 2. Loan A: 1,000 due in 120 s. Loan B, two-step and left pending: 1,000 with a
        //    StartDate in one hour. DebtTotal is 2,000 and the minimum cover is 200.
        Keylet const loanA = openLoan(env, fixture, Number{1'000}, 1);
        Keylet const loanB = proposeLoan(env, fixture, Number{1'000}, env.now() + 1h, 120);

        // 3. The broker owner defaults A. The cover pays 200 and drops to 0, below its minimum
        //    of 100 for B.
        defaultAfterGrace(env, owner, loanA);
        Number const minimum = minimumBrokerCover(
            env.le(broker)->at(sfDebtTotal),
            percentageToTenthBips(10),
            env.le(fixture.vaultKeylet));
        BEAST_EXPECT(Number{env.le(broker)->at(sfCoverAvailable)} < minimum);

        // 4. LoanSet refuses a new one-step loan of 1,000 with this cover.
        env(loan::set(depositor, broker.key, Number{1'000}),
            loan::kPaymentInterval(120),
            Sig(sfCounterpartySignature, owner),
            Fee(env.current()->fees().base * 2),
            Ter(tecINSUFFICIENT_FUNDS));
        env.close();

        // 5. The borrower accepts B.
        // BUG: LoanAccept returns tesSUCCESS and pays B out.
        env(loan::accept(depositor, loanB.key), Ter(tecINSUFFICIENT_FUNDS));
        env.close();
    }

    // FV_M4_49: LoanSet's schedule check ignores GracePeriod, so it accepts a loan that can be
    // defaulted only after RedemptionDate.
    void
    testLoanDefaultInRedemption()
    {
        testcase("FV_M4_49 LoanDefaultInRedemption");

        using namespace test::jtx;
        Env env{*this, all_ | featureLendingProtocolV1_1};
        auto const [issuer, owner, depositor, asset] =
            setupIou(env, {.depositorTrust = Number{100'000}});

        // 1. Vault with 10,000 in its Investment phase.
        auto const fixture = setupLendingVault(env, owner, depositor, asset, Number{10'000});
        Keylet const& broker = fixture.brokerKeylet;
        std::uint32_t const redemptionDate = fixture.redemptionDate.time_since_epoch().count();

        // 2. Loan A: 1,000 in one payment due kLoanRedemptionBuffer before RedemptionDate, with
        //    a GracePeriod equal to its PaymentInterval. It starts at the next close time.
        auto const lastClosed = env.closed()->header();
        std::uint32_t const startDate =
            (lastClosed.closeTime + lastClosed.closeTimeResolution).time_since_epoch().count();
        std::uint32_t const paymentInterval = redemptionDate - kLoanRedemptionBuffer - startDate;
        Keylet const loanA = keylet::loan(broker.key, SeqProxy::rawSequence(1));
        // BUG: LoanSet returns tesSUCCESS.
        env(loan::set(depositor, broker.key, Number{1'000}),
            loan::kPaymentInterval(paymentInterval),
            loan::kGracePeriod(paymentInterval),
            Sig(sfCounterpartySignature, owner),
            Fee(env.current()->fees().base * 2),
            Ter(tecNO_PERMISSION));
        env.close();

        // A fixed LoanSet creates no loan, and there is nothing more to show.
        auto const loanSle = env.le(loanA);
        if (!loanSle)
            return;
        BEAST_EXPECT(loanSle->at(sfNextPaymentDueDate) + kLoanRedemptionBuffer == redemptionDate);

        // 3. At RedemptionDate the default is still too soon. It succeeds only later, inside
        //    the Redemption phase.
        env.close(fixture.redemptionDate);
        env(loan::manage(owner, loanA.key, tfLoanDefault), Ter(tecTOO_SOON));
        env.close();
        defaultAfterGrace(env, owner, loanA);
    }

    // FV_M4_51: a LoanSet on an XRP vault returns tefEXCEPTION when the loan's principal plus its
    // interest is above 10^17 drops. The loan is computed before the Open limit check.
    void
    testLoanSetXRPRange()
    {
        testcase("FV_M4_51 LoanSetXRPRange");

        using namespace test::jtx;
        Env env{*this, all_ | featureLendingProtocolV1_1};
        Account const owner{"owner"};
        Account const depositor{"depositor"};
        env.fund(XRP(4'000'000'000LL), owner, depositor);
        env.close();

        // 1. An XRP vault with 3.3 * 10^15 drops and a broker with no cover requirement.
        PrettyAsset const asset{xrpIssue()};
        auto const fixture = setupLendingVault(
            env,
            owner,
            depositor,
            asset,
            Number{3'300'000'000'000'000LL},
            std::chrono::seconds{946'000'000});

        // 2. A loan of 3.2 * 10^15 drops at 100% with one payment after 943,000,000 seconds.
        //    Its total value is below 10^17 drops and its interest is above the Open limit.
        std::uint32_t const paymentInterval = 943'000'000;
        env(loan::set(depositor, fixture.brokerKeylet.key, Number{3'200'000'000'000'000LL}),
            loan::kInterestRate(percentageToTenthBips(100)),
            loan::kGracePeriod(60),
            loan::kPaymentInterval(paymentInterval),
            loan::kPaymentTotal(1),
            Sig(sfCounterpartySignature, owner),
            Fee(env.current()->fees().base * 2),
            Ter(tecLIMIT_EXCEEDED));
        env.close();

        // 3. The same loan for 3.3 * 10^15 drops has a total value above 10^17 drops.
        // BUG: the result is tefEXCEPTION.
        env(loan::set(depositor, fixture.brokerKeylet.key, Number{3'300'000'000'000'000LL}),
            loan::kInterestRate(percentageToTenthBips(100)),
            loan::kGracePeriod(60),
            loan::kPaymentInterval(paymentInterval),
            loan::kPaymentTotal(1),
            Sig(sfCounterpartySignature, owner),
            Fee(env.current()->fees().base * 2),
            Ter(tecLIMIT_EXCEEDED));
        env.close();
    }

    // FV_M4_61: a LoanSet on an MPT vault returns tefEXCEPTION when the loan's principal plus its
    // interest is above 2^63 - 1. The loan is computed before the Open limit check.
    void
    testLoanSetMPTRange()
    {
        testcase("FV_M4_61 LoanSetMPTRange");

        using namespace test::jtx;
        Env env{*this, all_ | featureLendingProtocolV1_1};

        // 1. An MPT that allows 2^63 - 1 units, all of them held by the depositor.
        auto const [issuer, owner, depositor, asset] = setupMpt(
            env,
            {.maxAmt = kMaxMpTokenAmount, .withDepositor = true, .holderFunds = kMaxMpTokenAmount});

        // 2. A vault with 9 * 10^15 units, all of it lent in loan A: ten payments and a
        //    LateInterestRate of 100%.
        auto const fixture = setupLendingVault(
            env,
            owner,
            depositor,
            asset,
            Number{9'000'000'000'000'000LL},
            std::chrono::seconds{946'000'000});
        Keylet const loanA = keylet::loan(
            fixture.brokerKeylet.key,
            SeqProxy::rawSequence(env.le(fixture.brokerKeylet)->at(sfLoanSequence)));
        env(loan::set(depositor, fixture.brokerKeylet.key, Number{9'000'000'000'000'000LL}),
            loan::kLateInterestRate(percentageToTenthBips(100)),
            loan::kGracePeriod(60),
            loan::kPaymentInterval(60),
            loan::kPaymentTotal(10),
            Sig(sfCounterpartySignature, owner),
            Fee(env.current()->fees().base * 2));
        env.close();

        // 3. Loan A is paid 15 years late. Its late interest takes AssetsAvailable to about
        //    7.5 * 10^17 units, far above the Open limit.
        std::uint32_t const dueDate = env.le(loanA)->at(sfNextPaymentDueDate);
        std::chrono::seconds const fifteenYears{15 * 365 * 24 * 60 * 60};
        env.close(NetClock::time_point{NetClock::duration{dueDate}} + fifteenYears);
        for (int payment = 0; payment < 10; ++payment)
        {
            env(loan::pay(
                depositor, loanA.key, asset(Number{200'000'000'000'000'000LL}), tfLoanLatePayment));
            env.close();
        }

        // 4. A loan of 5.79 * 10^17 units at 100% with one payment after 470,000,000 seconds has
        //    a total value of 9.21 * 10^18 units, below 2^63 - 1.
        std::uint32_t const paymentInterval = 470'000'000;
        env(loan::set(depositor, fixture.brokerKeylet.key, Number{579'000'000'000'000'000LL}),
            loan::kInterestRate(percentageToTenthBips(100)),
            loan::kGracePeriod(60),
            loan::kPaymentInterval(paymentInterval),
            loan::kPaymentTotal(1),
            Sig(sfCounterpartySignature, owner),
            Fee(env.current()->fees().base * 2),
            Ter(tecLIMIT_EXCEEDED));
        env.close();

        // 5. The same loan for 5.81 * 10^17 units has a total value of 9.24 * 10^18 units, above
        //    2^63 - 1.
        // BUG: the result is tefEXCEPTION.
        env(loan::set(depositor, fixture.brokerKeylet.key, Number{581'000'000'000'000'000LL}),
            loan::kInterestRate(percentageToTenthBips(100)),
            loan::kGracePeriod(60),
            loan::kPaymentInterval(paymentInterval),
            loan::kPaymentTotal(1),
            Sig(sfCounterpartySignature, owner),
            Fee(env.current()->fees().base * 2),
            Ter(tecLIMIT_EXCEEDED));
        env.close();
    }

public:
    void
    run() override
    {
        // Open bugs. Each call fails until the C++ code is fixed, so it is commented out.
        // clang-format off
        // testLoanDefaultOrder();                    // FV_M4_18
        // testLoanPeriodicPaymentPrecision();        // FV_M4_19
        // testLoanPendingCoarsened();                // FV_M4_22
        // testLoanDefaultNegativeCover();            // FV_M4_27
        // testLoanDefaultCoveredLoss();              // FV_M4_28
        // testLoanAcceptOpenLimit();                 // FV_M4_33
        // testLoanSetManagementFeeRoundsUp();        // FV_M4_42
        // testLoanAcceptBelowMinimumCover();         // FV_M4_46
        // testLoanDefaultInRedemption();             // FV_M4_49
        // testLoanSetXRPRange();                     // FV_M4_51
        // testLoanSetMPTRange();                     // FV_M4_61
        // clang-format on

        // Keeps a run of this suite alone from reporting "No tests run".
        pass();
    }
};

BEAST_DEFINE_TESTSUITE(LoanFindings, formal_verification, xrpl);

}  // namespace xrpl
