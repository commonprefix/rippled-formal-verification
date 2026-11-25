#include <test/app/lending/LoanManageFixedPrecisionBase.h>
#include <test/formal_verification/findings/LendingFindingsHelpers.h>
#include <test/jtx/Account.h>
#include <test/jtx/Env.h>
#include <test/jtx/TestHelpers.h>
#include <test/jtx/amount.h>
#include <test/jtx/fee.h>
#include <test/jtx/permissioned_domains.h>
#include <test/jtx/sig.h>
#include <test/jtx/ter.h>
#include <test/jtx/vault.h>

#include <xrpl/basics/Number.h>
#include <xrpl/basics/base_uint.h>
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
#include <limits>
#include <optional>

// cspell: words unimpairs

namespace xrpl {

// One test per bug reported in LoanSet, LoanAccept, LoanDelete and LoanManage. The test of an
// open bug fails and its call in run() is commented out. A fixed bug's test is a regression test.
class LoanFindings_test : public LoanManageFixedPrecisionBase
{
    // Pays the loan's first installment 800 days after its grace period, which coarsens the vault.
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

    // Coarsens the vault with loan A's late payment and takes AssetsAvailable to 10^15 - 0.1.
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

        // 1. Loan C: 2 in 20 installments of 0.1. Its borrower holds 1, so 0.1 fits in 16 digits.
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

        // 3. After RedemptionDate a withdrawal leaves 0.9 to go, which 9 installments of C add.
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

    // A coarsened Scale 1 vault in Redemption with AssetsAvailable 999,999,999,999,999.9. Returns
    // the fixture of its second broker, which holds `cover` and lent loan B of 1.
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

        // 3. Loan A: 700,000,000,000,000 at LateInterestRate 100%. Loan B: 1 on the second broker.
        Keylet const loanA =
            openLoanWithLateInterest(env, fixture, Number{700'000'000'000'000LL}, 5, 24 * 60 * 60);
        openLoan(env, coverFixture, Number{1}, 1, TenthBips32{0}, 0, 24 * 60 * 60);

        // 4. Loan C and A's late payment take AssetsAvailable to 999,999,999,999,999.9.
        moveAvailableBelowPowerOfTen(env, accounts, fixture, loanA);
        return coverFixture;
    }

    // Pays the next installment late with PeriodicPayment + 1, of which LoanPay takes what is due.
    static void
    payInstallmentLate(
        test::jtx::Env& env,
        LendingFixture const& fixture,
        PrettyAsset const& asset,
        Keylet const& loan)
    {
        using namespace test::jtx;

        Number const installment = env.le(loan)->at(sfPeriodicPayment);
        env(loan::pay(
            fixture.depositor, loan.key, asset(installment + 1).value(), tfLoanLatePayment));
        env.close();
    }

    // FV_M4_4: a default after most of the vault was withdrawn clears the loan's debt.
    void
    testLoanDefaultStuck()
    {
        testcase("FV_M4_4 LoanDefaultStuck");

        using namespace test::jtx;
        using namespace std::chrono_literals;
        Env env{*this, all_ | featureLendingProtocolV1_1};
        auto const [issuer, owner, depositor, asset] = setupIou(
            env,
            {.depositorTrust = Number{1'000'000'000'000LL},
             .ownerTrust = Number{1'000'000'000'000LL},
             .depositorFunds = Number{50'000'000'000LL},
             .ownerFunds = Number{15'000'000}});

        // 1. Vault at Scale 5 with 9,999,000,000 and a RedemptionDate 7 months later. Broker:
        //    CoverRateMinimum 10%, CoverRateLiquidation 25%, cover 15,000,000.
        std::uint32_t const month = 30 * 24 * 60 * 60;
        auto const fixture = setupLendingVault(
            env,
            owner,
            depositor,
            asset,
            Number{9'999'000'000LL},
            std::chrono::seconds{7 * month},
            5,
            percentageToTenthBips(10),
            percentageToTenthBips(25));
        Keylet const& vault = fixture.vaultKeylet;
        Keylet const& broker = fixture.brokerKeylet;
        env(loan_broker::coverDeposit(owner, broker.key, asset(15'000'000).value()));
        env.close();

        // 2. Loan A: 100,000,000 at 10% in 6 monthly installments.
        Keylet const loanA =
            openLoan(env, fixture, Number{100'000'000}, 6, percentageToTenthBips(10), 0, month);

        // 3. Five payments of an installment + 1,000 take AssetsTotal across 10,000,000,000.
        Number const installment = env.le(loanA)->at(sfPeriodicPayment);
        for (int paid = 0; paid < 5; ++paid)
        {
            env(loan::pay(depositor, loanA.key, asset(installment + 1'000).value()));
            env.close();
        }
        BEAST_EXPECT(Number{env.le(vault)->at(sfAssetsTotal)} > Number{10'000'000'000LL});

        // 4. After RedemptionDate the depositor withdraws down to AssetsAvailable 50,000,000.
        env.close(fixture.redemptionDate + 1s);
        Number const withdrawal = Number{env.le(vault)->at(sfAssetsAvailable)} - 50'000'000;
        env(fixture.vault.withdraw(
            {.depositor = depositor, .id = vault.key, .amount = asset(withdrawal)}));
        env.close();

        // 5. The broker owner defaults A, whose last installment was missed.
        env(loan::manage(owner, loanA.key, tfLoanDefault));
        env.close();
        auto const vaultSle = env.le(vault);
        BEAST_EXPECT(vaultSle->at(sfAssetsAvailable) == vaultSle->at(sfAssetsTotal));
        BEAST_EXPECT(env.le(broker)->at(sfDebtTotal) == Number{0});
    }

    // FV_M4_7: after AssetsTotal crossed a power of ten a default credits what the cover pays.
    void
    testLoanDefaultTransferMismatch()
    {
        testcase("FV_M4_7 LoanDefaultTransferMismatch");

        using namespace test::jtx;
        Env env{*this, all_ | featureLendingProtocolV1_1};
        auto const [issuer, owner, depositor, asset] = setupIou(
            env,
            {.depositorTrust = Number{1'000'000'000'000LL},
             .ownerTrust = Number{1'000'000'000'000LL},
             .depositorFunds = Number{2'000'000'000LL},
             .ownerFunds = Number{30'000'000}});

        // 1. Vault with 986,751,133 and a RedemptionDate 70 months later. Broker:
        //    CoverRateMinimum 10%, CoverRateLiquidation 25%, cover 30,000,000.
        std::uint32_t const month = 30 * 24 * 60 * 60;
        auto const fixture = setupLendingVault(
            env,
            owner,
            depositor,
            asset,
            Number{986'751'133},
            std::chrono::seconds{70 * month},
            std::nullopt,
            percentageToTenthBips(10),
            percentageToTenthBips(25));
        Keylet const& vault = fixture.vaultKeylet;
        Keylet const& broker = fixture.brokerKeylet;
        env(loan_broker::coverDeposit(owner, broker.key, asset(30'000'000).value()));
        env.close();

        // 2. Loan A: 200,000,000 at 9.8% in 60 monthly installments.
        Keylet const loanA =
            openLoan(env, fixture, Number{200'000'000}, 60, TenthBips32{9'800}, 0, month);

        // 3. 51 payments of an installment + 1,000 take AssetsAvailable across 1,000,000,000.
        Number const installment = env.le(loanA)->at(sfPeriodicPayment);
        for (int paid = 0; paid < 51; ++paid)
        {
            env(loan::pay(depositor, loanA.key, asset(installment + 1'000).value()));
            env.close();
        }
        auto const before = snapshotVault(env, vault, asset);
        Number const coverBefore = env.le(broker)->at(sfCoverAvailable);
        BEAST_EXPECT(before.available > Number{1'000'000'000});

        // 4. The broker owner defaults A after its grace period.
        defaultAfterGrace(env, owner, loanA);
        auto const after = snapshotVault(env, vault, asset);
        Number const coverPaid = coverBefore - Number{env.le(broker)->at(sfCoverAvailable)};
        Number const credited = after.available - before.available;
        Number const received = after.vaultBalance - before.vaultBalance;
        BEAST_EXPECT(coverPaid > beast::kZero);
        BEAST_EXPECTS(
            credited == coverPaid,
            "the cover paid " + to_string(coverPaid) + " and AssetsAvailable grew by " +
                to_string(credited));
        BEAST_EXPECTS(
            received == coverPaid,
            "the cover paid " + to_string(coverPaid) + " and the vault received " +
                to_string(received));
    }

    // FV_M4_8: on a coarsened vault an impair adds exactly the loan's principal to LossUnrealized.
    void
    testLoanImpairStuck()
    {
        testcase("FV_M4_8 LoanImpairStuck");

        using namespace test::jtx;
        using namespace std::chrono_literals;

        for (bool const payB : {true, false})
        {
            Env env{*this, all_ | featureLendingProtocolV1_1};
            auto const [issuer, owner, depositor, asset] = setupCoarsenIou(env);

            // 1. Vault at Scale 10 with 899,000, under its Open limit of 900,000.
            auto const fixture = setupLendingVault(
                env, owner, depositor, asset, Number{899'000}, 15 * 365 * 24h, 10);
            Keylet const& vault = fixture.vaultKeylet;

            // 2. Loan A: 50,000 in 5 daily installments with the maximum LateInterestRate.
            //    Loan B: 100.0000000004 at 10% in one payment after 30 days.
            Keylet const loanA =
                openLoanWithLateInterest(env, fixture, Number{50'000}, 5, 24 * 60 * 60);
            Number const principalB{1'000'000'000'004LL, -10};
            Keylet const loanB = openLoan(
                env, fixture, principalB, 1, percentageToTenthBips(10), 0, 30 * 24 * 60 * 60);

            // 3. A's late payment coarsens the vault to 10^-9, above B's last digit.
            payCoarseningLoanLate(env, fixture, asset, loanA);

            // 4. B is late and the broker owner impairs it.
            env(loan::manage(owner, loanB.key, tfLoanImpair));
            env.close();
            BEAST_EXPECT(env.le(vault)->at(sfLossUnrealized) == principalB);

            // 5. The broker owner unimpairs B and impairs it again.
            env(loan::manage(owner, loanB.key, tfLoanUnimpair));
            env.close();
            BEAST_EXPECT(env.le(vault)->at(sfLossUnrealized) == Number{0});
            env(loan::manage(owner, loanB.key, tfLoanImpair));
            env.close();

            // 6. B is paid late in one run and defaulted in the other.
            if (payB)
            {
                payInstallmentLate(env, fixture, asset, loanB);
            }
            else
            {
                env(loan::manage(owner, loanB.key, tfLoanDefault));
                env.close();
            }
            BEAST_EXPECT(env.le(loanB)->at(sfPaymentRemaining) == 0);
            BEAST_EXPECT(env.le(vault)->at(sfLossUnrealized) == Number{0});
        }
    }

    // FV_M4_9: DebtTotal is 0 once the broker's last loan, a pending one, is deleted.
    void
    testLoanBrokerDebtResidue()
    {
        testcase("FV_M4_9 LoanBrokerDebtResidue");

        using namespace test::jtx;
        using namespace std::chrono_literals;
        Env env{*this, all_ | featureLendingProtocolV1_1};
        auto const [issuer, owner, depositor, asset] = setupIou(
            env,
            {.clawback = true,
             .depositorTrust = Number{10'000'000},
             .depositorFunds = Number{2'000'000}});

        // 1. Vault at Scale 9 with 999,999.5.
        auto const fixture =
            setupLendingVault(env, owner, depositor, asset, Number{9'999'995, -1}, 365 * 24h, 9);
        Keylet const& vault = fixture.vaultKeylet;
        Keylet const& broker = fixture.brokerKeylet;

        // 2. Loan A: 1,000 at 10% in 2 monthly installments.
        std::uint32_t const month = 30 * 24 * 60 * 60;
        Keylet const loanA =
            openLoan(env, fixture, Number{1'000}, 2, percentageToTenthBips(10), 0, month);

        // 3. Pending loan B: 100.000000009. One more digit, below the base unit, fails.
        NetClock::time_point const startDate = env.now() + 24h;
        env(loan::set(owner, broker.key, Number{1'000'000'000'009LL, -10}),
            loan::kBorrower(depositor),
            loan::kStartDate(startDate.time_since_epoch().count()),
            loan::kPaymentInterval(month),
            Ter(tecPRECISION_LOSS));
        env.close();
        Number const principalB{100'000'000'009LL, -9};
        Keylet const loanB = proposeLoan(env, fixture, principalB, startDate, month);
        BEAST_EXPECT(env.le(broker)->at(sfDebtTotal) == Number{1'000} + principalB);

        // 4. A's first payment of 600 takes AssetsTotal across 1,000,000. Its second pays A off.
        env(loan::pay(depositor, loanA.key, asset(600).value()));
        env.close();
        BEAST_EXPECT(Number{env.le(vault)->at(sfAssetsTotal)} > Number{1'000'000});
        env(loan::pay(depositor, loanA.key, asset(600).value()));
        env.close();
        BEAST_EXPECT(env.le(broker)->at(sfDebtTotal) == principalB);

        // 5. The issuer claws back 20, which takes AssetsTotal back below 1,000,000.
        env(fixture.vault.clawback(
            {.issuer = issuer, .id = vault.key, .holder = depositor, .amount = asset(20).value()}));
        env.close();
        BEAST_EXPECT(Number{env.le(vault)->at(sfAssetsTotal)} < Number{1'000'000});

        // 6. The broker owner deletes A and then the pending B, the broker's last loan.
        env(loan::del(owner, loanA.key));
        env.close();
        env(loan::del(owner, loanB.key));
        env.close();
        BEAST_EXPECT(env.le(broker)->at(sfOwnerCount) == 0);
        BEAST_EXPECT(env.le(broker)->at(sfDebtTotal) == Number{0});

        // 7. The broker owner deletes the broker.
        env(loan_broker::del(owner, broker.key));
        env.close();
        BEAST_EXPECT(!env.le(broker));
    }

    // FV_M4_10: an XRP LoanSet with a principal or LoanServiceFee above 10^17 drops is rejected.
    void
    testLoanSetXrpPrincipal()
    {
        testcase("FV_M4_10 LoanSetXrpPrincipal");

        using namespace test::jtx;
        Env env{*this, all_ | featureLendingProtocolV1_1};
        Account const owner{"owner"};
        Account const depositor{"depositor"};
        env.fund(XRP(10'000'000), owner, depositor);
        env.close();

        // 1. An XRP vault with 1,000 XRP.
        PrettyAsset const asset{xrpIssue()};
        auto const fixture = setupLendingVault(env, owner, depositor, asset, Number{1'000'000'000});
        Number const aboveMaxDrops{1, 18};

        // 2. A loan of 10^18 drops, which is not an XRP amount.
        env(loan::set(depositor, fixture.brokerKeylet.key, aboveMaxDrops),
            Sig(sfCounterpartySignature, owner),
            Fee(env.current()->fees().base * 2),
            Ter(tecPRECISION_LOSS));
        env.close();

        // 3. A loan of 1 XRP with a LoanServiceFee of 10^18 drops.
        env(loan::set(depositor, fixture.brokerKeylet.key, Number{1'000'000}),
            loan::kLoanServiceFee(aboveMaxDrops),
            Sig(sfCounterpartySignature, owner),
            Fee(env.current()->fees().base * 2),
            Ter(tecPRECISION_LOSS));
        env.close();
    }

    // FV_M4_11: on a coarsened vault an impair leaves LossUnrealized at the loan's principal.
    void
    testLoanImpairRoundUp()
    {
        testcase("FV_M4_11 LoanImpairRoundUp");

        using namespace test::jtx;
        using namespace std::chrono_literals;

        for (bool const defaultB : {true, false})
        {
            Env env{*this, all_ | featureLendingProtocolV1_1};
            auto const [issuer, owner, depositor, asset] = setupCoarsenIou(env);

            // 1. Vault at Scale 10 with 899,000, under its Open limit of 900,000.
            auto const fixture = setupLendingVault(
                env, owner, depositor, asset, Number{899'000}, 15 * 365 * 24h, 10);
            Keylet const& vault = fixture.vaultKeylet;

            // 2. Loan A: 100.0000000006 at 10% in one payment after 30 days. Loan B: 50,000 in 5
            //    daily installments with the maximum LateInterestRate.
            Number const principalA{1'000'000'000'006LL, -10};
            Keylet const loanA = openLoan(
                env, fixture, principalA, 1, percentageToTenthBips(10), 0, 30 * 24 * 60 * 60);
            Keylet const loanB =
                openLoanWithLateInterest(env, fixture, Number{50'000}, 5, 24 * 60 * 60);

            // 3. B's late payment coarsens the vault to 10^-9, above A's last digit.
            payCoarseningLoanLate(env, fixture, asset, loanB);

            // 4. A is late and the broker owner impairs it.
            env(loan::manage(owner, loanA.key, tfLoanImpair));
            env.close();
            BEAST_EXPECT(env.le(vault)->at(sfLossUnrealized) == principalA);

            // 5. AssetsTotal goes back below 1,000,000. In one run the broker owner defaults B.
            if (defaultB)
            {
                env(loan::manage(owner, loanB.key, tfLoanDefault));
                env.close();
            }
            else
            {
                // In the other run B is paid off late and the depositor withdraws 300,000.
                for (int paid = 0; paid < 4; ++paid)
                {
                    env(loan::pay(depositor, loanB.key, asset(500'000).value(), tfLoanLatePayment));
                    env.close();
                }
                BEAST_EXPECT(env.le(loanB)->at(sfPaymentRemaining) == 0);
                env.close(fixture.redemptionDate + 1s);
                env(fixture.vault.withdraw(
                    {.depositor = depositor, .id = vault.key, .amount = asset(300'000)}));
                env.close();
            }
            BEAST_EXPECT(Number{env.le(vault)->at(sfAssetsTotal)} < Number{1'000'000});
            BEAST_EXPECT(env.le(vault)->at(sfLossUnrealized) == principalA);
        }
    }

    // FV_M4_12: an impair and an unimpair at different vault scales leave LossUnrealized at 0.
    void
    testLoanLossResidue()
    {
        testcase("FV_M4_12 LoanLossResidue");

        using namespace test::jtx;
        using namespace std::chrono_literals;

        for (bool const payD : {true, false})
        {
            Env env{*this, all_ | featureLendingProtocolV1_1};
            auto const [issuer, owner, depositor, asset] = setupCoarsenIou(env);

            // 1. Vault at Scale 10 with 899,000, under its Open limit of 900,000.
            auto const fixture = setupLendingVault(
                env, owner, depositor, asset, Number{899'000}, 15 * 365 * 24h, 10);
            Keylet const& vault = fixture.vaultKeylet;

            // 2. Loans at 10% in one payment: A 100.0000000006 and C 20,000 after 36.5 days, D
            //    1,000 after 73 days. Loan B: 50,000 in one payment, LateInterestRate 100%.
            std::uint32_t const interval = 3'153'600;
            TenthBips32 const interestRate = percentageToTenthBips(10);
            Number const principalA{1'000'000'000'006LL, -10};
            Keylet const loanA = openLoan(env, fixture, principalA, 1, interestRate, 0, interval);
            Keylet const loanB = openLoanWithLateInterest(env, fixture, Number{50'000});
            Keylet const loanC =
                openLoan(env, fixture, Number{20'000}, 1, interestRate, 0, interval);
            Keylet const loanD =
                openLoan(env, fixture, Number{1'000}, 1, interestRate, 0, 2 * interval);

            // 3. B is paid off 800 days late, which coarsens the vault to 10^-9, above A's digit.
            payCoarseningLoanLate(env, fixture, asset, loanB);

            // 4. A is late and the broker owner impairs it on the coarsened vault.
            env(loan::manage(owner, loanA.key, tfLoanImpair));
            env.close();
            BEAST_EXPECT(env.le(vault)->at(sfLossUnrealized) == principalA);

            // 5. The broker owner defaults C, which takes the vault back to its base unit 10^-10.
            env(loan::manage(owner, loanC.key, tfLoanDefault));
            env.close();
            BEAST_EXPECT(Number{env.le(vault)->at(sfAssetsTotal)} < Number{1'000'000});

            // 6. The broker owner unimpairs A at the base unit. A is then paid late.
            env(loan::manage(owner, loanA.key, tfLoanUnimpair));
            env.close();
            BEAST_EXPECT(env.le(vault)->at(sfLossUnrealized) == Number{0});
            payInstallmentLate(env, fixture, asset, loanA);

            // 7. D, the last loan, is paid late in one run, impaired and defaulted in the other.
            if (payD)
            {
                payInstallmentLate(env, fixture, asset, loanD);
            }
            else
            {
                env(loan::manage(owner, loanD.key, tfLoanImpair));
                env.close();
                env(loan::manage(owner, loanD.key, tfLoanDefault));
                env.close();
            }
            auto const vaultSle = env.le(vault);
            BEAST_EXPECT(env.le(loanD)->at(sfPaymentRemaining) == 0);
            BEAST_EXPECT(vaultSle->at(sfLossUnrealized) == Number{0});
            BEAST_EXPECT(vaultSle->at(sfAssetsAvailable) == vaultSle->at(sfAssetsTotal));
        }
    }

    // FV_M4_13: on a coarsened vault an unimpair leaves the other impaired loan's principal.
    void
    testLoanUnimpairNeighbor()
    {
        testcase("FV_M4_13 LoanUnimpairNeighbor");

        using namespace test::jtx;
        using namespace std::chrono_literals;

        for (bool const payB : {true, false})
        {
            Env env{*this, all_ | featureLendingProtocolV1_1};
            auto const [issuer, owner, depositor, asset] = setupCoarsenIou(env);

            // 1. Vault at Scale 10 with 899,000, under its Open limit of 900,000.
            auto const fixture = setupLendingVault(
                env, owner, depositor, asset, Number{899'000}, 15 * 365 * 24h, 10);
            Keylet const& vault = fixture.vaultKeylet;

            // 2. Loans A 100.0000000006 and B 200.0000000004 at 10% in one payment after 36.5
            //    days. Loan C: 50,000 in 5 daily installments with the maximum LateInterestRate.
            std::uint32_t const interval = 3'153'600;
            TenthBips32 const interestRate = percentageToTenthBips(10);
            Number const principalA{1'000'000'000'006LL, -10};
            Number const principalB{2'000'000'000'004LL, -10};
            Keylet const loanA = openLoan(env, fixture, principalA, 1, interestRate, 0, interval);
            Keylet const loanB = openLoan(env, fixture, principalB, 1, interestRate, 0, interval);
            Keylet const loanC =
                openLoanWithLateInterest(env, fixture, Number{50'000}, 5, 24 * 60 * 60);

            // 3. A and B are late and the broker owner impairs both at the base unit of 10^-10.
            closePastDue(env, loanB);
            env(loan::manage(owner, loanA.key, tfLoanImpair));
            env.close();
            env(loan::manage(owner, loanB.key, tfLoanImpair));
            env.close();
            BEAST_EXPECT(env.le(vault)->at(sfLossUnrealized) == principalA + principalB);

            // 4. C's late payment coarsens the vault to 10^-9, above the last digit of A and B.
            payCoarseningLoanLate(env, fixture, asset, loanC);

            // 5. The broker owner unimpairs A.
            env(loan::manage(owner, loanA.key, tfLoanUnimpair));
            env.close();
            BEAST_EXPECT(env.le(vault)->at(sfLossUnrealized) == principalB);

            // 6. The broker owner unimpairs B and impairs it again.
            env(loan::manage(owner, loanB.key, tfLoanUnimpair));
            env.close();
            BEAST_EXPECT(env.le(vault)->at(sfLossUnrealized) == Number{0});
            env(loan::manage(owner, loanB.key, tfLoanImpair));
            env.close();

            // 7. B is paid late in one run and defaulted in the other.
            if (payB)
            {
                payInstallmentLate(env, fixture, asset, loanB);
            }
            else
            {
                env(loan::manage(owner, loanB.key, tfLoanDefault));
                env.close();
            }
            BEAST_EXPECT(env.le(loanB)->at(sfPaymentRemaining) == 0);
            BEAST_EXPECT(env.le(vault)->at(sfLossUnrealized) == Number{0});
        }
    }

    // FV_M4_14: after AssetsTotal crossed a power of ten the vault's only loan can be impaired.
    void
    testLoanImpairLimit()
    {
        testcase("FV_M4_14 LoanImpairLimit");

        using namespace test::jtx;
        using namespace std::chrono_literals;
        Env env{*this, all_ | featureLendingProtocolV1_1};
        auto const [issuer, owner, depositor, asset] = setupCoarsenIou(env);

        // 1. Vault at Scale 10 with 890,500.
        auto const fixture =
            setupLendingVault(env, owner, depositor, asset, Number{890'500}, 15 * 365 * 24h, 10);
        Keylet const& vault = fixture.vaultKeylet;

        // 2. Loan A: 100.0000000006 at 10% due in 36.5 days. Loan B: 50,000, LateInterestRate 100%.
        Number const principalA{1'000'000'000'006LL, -10};
        Keylet const loanA =
            openLoan(env, fixture, principalA, 1, percentageToTenthBips(10), 0, 3'153'600);
        Keylet const loanB = openLoanWithLateInterest(env, fixture, Number{50'000});

        // 3. B is paid 800 days late. The vault coarsens to 10^-9, AssetsAvailable stays below.
        payCoarseningLoanLate(env, fixture, asset, loanB);
        BEAST_EXPECT(Number{env.le(vault)->at(sfAssetsAvailable)} < Number{1'000'000});

        // 4. A is late and the vault's only loan. The broker owner impairs it.
        env(loan::manage(owner, loanA.key, tfLoanImpair));
        env.close();
        BEAST_EXPECT(env.le(vault)->at(sfAssetsDeployed) == principalA);
        BEAST_EXPECT(env.le(vault)->at(sfLossUnrealized) == principalA);

        // 5. The broker owner defaults A.
        env(loan::manage(owner, loanA.key, tfLoanDefault));
        env.close();
        BEAST_EXPECT(env.le(vault)->at(sfLossUnrealized) == Number{0});
    }

    // FV_M4_15: two pending loans that take AssetsReserved across a power of ten can be accepted.
    void
    testLoanReservedLock()
    {
        testcase("FV_M4_15 LoanReservedLock");

        using namespace test::jtx;
        using namespace std::chrono_literals;

        for (bool const acceptB : {true, false})
        {
            Env env{*this, all_ | featureLendingProtocolV1_1};
            auto const [issuer, owner, depositor, asset] = setupIou(
                env, {.depositorTrust = Number{10'000'000}, .depositorFunds = Number{2'000'000}});

            // 1. Vault at Scale 9 with 999,999.
            auto const fixture =
                setupLendingVault(env, owner, depositor, asset, Number{999'999}, 365 * 24h, 9);
            Keylet const& vault = fixture.vaultKeylet;

            // 2. Loan A: 10,000 at 100% in one payment after 1 day.
            std::uint32_t const day = 24 * 60 * 60;
            Keylet const loanA =
                openLoan(env, fixture, Number{10'000}, 1, percentageToTenthBips(100), 0, day);

            // 3. Pending loan B: 400,000.000000004. One more digit, below the base unit, fails.
            NetClock::time_point const startDate = env.now() + 30 * 24h;
            env(loan::set(owner, fixture.brokerKeylet.key, Number{4'000'000'000'000'004LL, -10}),
                loan::kBorrower(depositor),
                loan::kStartDate(startDate.time_since_epoch().count()),
                loan::kPaymentInterval(30 * day),
                Ter(tecPRECISION_LOSS));
            env.close();
            Number const principalB{400'000'000'000'004LL, -9};
            Keylet const loanB = proposeLoan(env, fixture, principalB, startDate, 30 * day);

            // 4. A is paid off. Its interest takes AssetsTotal across 1,000,000.
            Number const owedA = env.le(loanA)->at(sfTotalValueOutstanding);
            env(loan::pay(depositor, loanA.key, asset(owedA).value()));
            env.close();
            BEAST_EXPECT(Number{env.le(vault)->at(sfAssetsTotal)} > Number{1'000'000});

            // 5. Loan C, two-step: 600,000. AssetsReserved is 1,000,000.000000004.
            Number const principalC{600'000};
            Keylet const loanC = proposeLoan(env, fixture, principalC, startDate, 30 * day);
            BEAST_EXPECT(env.le(vault)->at(sfAssetsReserved) == principalB + principalC);

            // 6. The borrower accepts C.
            env(loan::accept(depositor, loanC.key));
            env.close();
            BEAST_EXPECT(env.le(vault)->at(sfAssetsReserved) == principalB);

            // 7. The borrower accepts B in one run and deletes it in the other.
            if (acceptB)
            {
                env(loan::accept(depositor, loanB.key));
            }
            else
            {
                env(loan::del(depositor, loanB.key));
            }
            env.close();
            BEAST_EXPECT(env.le(vault)->at(sfAssetsReserved) == Number{0});
        }
    }

    // FV_M4_16: after a default on a coarsened vault the vault can be emptied and deleted.
    void
    testLoanDefaultResidue()
    {
        testcase("FV_M4_16 LoanDefaultResidue");

        using namespace test::jtx;
        using namespace std::chrono_literals;
        Env env{*this, all_ | featureLendingProtocolV1_1};
        auto const [issuer, owner, depositor, asset] = setupCoarsenIou(env);

        // 1. Vault at Scale 10 with 890,500.
        auto const fixture =
            setupLendingVault(env, owner, depositor, asset, Number{890'500}, 15 * 365 * 24h, 10);
        Keylet const& vault = fixture.vaultKeylet;

        // 2. Loan A: 100.0000000001 at 10% due in 36.5 days. Loan B: 50,000, LateInterestRate 100%.
        Keylet const loanA = openLoan(
            env,
            fixture,
            Number{1'000'000'000'001LL, -10},
            1,
            percentageToTenthBips(10),
            0,
            3'153'600);
        Keylet const loanB = openLoanWithLateInterest(env, fixture, Number{50'000});

        // 3. B is paid 800 days late. The vault coarsens to 10^-9, AssetsAvailable stays below.
        payCoarseningLoanLate(env, fixture, asset, loanB);
        BEAST_EXPECT(Number{env.le(vault)->at(sfAssetsAvailable)} < Number{1'000'000});

        // 4. The broker owner defaults A, the vault's last loan.
        env(loan::manage(owner, loanA.key, tfLoanDefault));
        env.close();
        Number const assetsTotal = env.le(vault)->at(sfAssetsTotal);
        BEAST_EXPECT(env.le(vault)->at(sfAssetsAvailable) == assetsTotal);

        // 5. After RedemptionDate the depositor, the only holder, withdraws AssetsTotal.
        env.close(fixture.redemptionDate + 1s);
        env(fixture.vault.withdraw(
            {.depositor = depositor, .id = vault.key, .amount = asset(assetsTotal)}));
        env.close();

        // 6. The owner deletes both loans, the broker and the vault.
        env(loan::del(owner, loanA.key));
        env(loan::del(owner, loanB.key));
        env.close();
        env(loan_broker::del(owner, fixture.brokerKeylet.key));
        env.close();
        env(fixture.vault.del({.owner = owner, .id = vault.key}));
        env.close();
        BEAST_EXPECT(!env.le(vault));
    }

    // FV_M4_17: a LoanSet that takes DebtTotal to exactly DebtMaximum stores that value.
    void
    testLoanSetDebtRounding()
    {
        testcase("FV_M4_17 LoanSetDebtRounding");

        using namespace test::jtx;
        using namespace std::chrono_literals;
        Env env{*this, all_ | featureLendingProtocolV1_1};
        auto const [issuer, owner, depositor, asset] = setupIou(
            env,
            {.depositorTrust = Number{10'000'000},
             .ownerTrust = Number{10'000},
             .depositorFunds = Number{2'000'000},
             .ownerFunds = Number{1'000}});

        // 1. Vault at Scale 9 with 999,999.5. Its first broker has no limits.
        auto const fixture =
            setupLendingVault(env, owner, depositor, asset, Number{9'999'995, -1}, 365 * 24h, 9);
        Keylet const& vault = fixture.vaultKeylet;

        // 2. A second broker: DebtMaximum 1,100.000000256, CoverRateMinimum 15.625% and a cover
        //    of 171.87500004, its minimum cover at DebtMaximum.
        Number const debtMaximum{1'100'000'000'256LL, -9};
        TenthBips32 const coverRateMinimum{15'625};
        LendingFixture limitedFixture = fixture;
        limitedFixture.brokerKeylet =
            keylet::loanBroker(owner.id(), SeqProxy::rawSequence(env.seq(owner)));
        Keylet const& limitedBroker = limitedFixture.brokerKeylet;
        env(loan_broker::set(owner, vault.key),
            loan_broker::kDebtMaximum(debtMaximum),
            loan_broker::kCoverRateMinimum(coverRateMinimum),
            loan_broker::kCoverRateLiquidation(percentageToTenthBips(10)));
        env.close();
        env(loan_broker::coverDeposit(
            owner, limitedBroker.key, asset(Number{17'187'500'004LL, -8}).value()));
        env.close();

        // 3. Loan A on the second broker, at 10% in one payment after 36.5 days. A principal of
        //    100.0000000256 has a digit below the base unit of 10^-9. 100.000000256 is lent.
        std::uint32_t const interval = 3'153'600;
        TenthBips32 const interestRate = percentageToTenthBips(10);
        env(loan::set(depositor, limitedBroker.key, Number{1'000'000'000'256LL, -10}),
            loan::kInterestRate(interestRate),
            loan::kPaymentInterval(interval),
            Sig(sfCounterpartySignature, owner),
            Fee(env.current()->fees().base * 2),
            Ter(tecPRECISION_LOSS));
        env.close();
        openLoan(env, limitedFixture, Number{100'000'000'256LL, -9}, 1, interestRate, 0, interval);

        // 4. Loan B: 500,000 on the first broker. Its payoff takes AssetsTotal across 1,000,000.
        Keylet const loanB = openLoan(env, fixture, Number{500'000}, 1, interestRate, 0, interval);
        Number const owedB = env.le(loanB)->at(sfTotalValueOutstanding);
        env(loan::pay(depositor, loanB.key, asset(owedB).value()));
        env.close();
        BEAST_EXPECT(Number{env.le(vault)->at(sfAssetsTotal)} > Number{1'000'000});

        // 5. Loan C: 1,000 on the second broker. DebtTotal hits DebtMaximum, the cover its minimum.
        openLoan(env, limitedFixture, Number{1'000}, 1, interestRate, 0, interval);
        auto const brokerSle = env.le(limitedBroker);
        Number const debtTotal = brokerSle->at(sfDebtTotal);
        Number const cover = brokerSle->at(sfCoverAvailable);
        Number const minimum = minimumBrokerCover(debtTotal, coverRateMinimum, env.le(vault));
        BEAST_EXPECTS(debtTotal == debtMaximum, "DebtTotal is " + to_string(debtTotal));
        BEAST_EXPECTS(
            cover >= minimum,
            "the cover is " + to_string(cover) + " and its minimum " + to_string(minimum));
    }

    // FV_M4_18: the vault's loss from defaulting two loans depends on their order.
    void
    testLoanDefaultOrder()
    {
        testcase("FV_M4_18 LoanDefaultOrder");

        using namespace test::jtx;
        using namespace std::chrono_literals;

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

    // FV_M4_19: for a tiny InterestRate LoanSet computes an interest far too high or below zero.
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

    // FV_M4_20: two loans paid off on a coarsened vault leave DebtTotal at exactly 0.
    void
    testLoanDeleteDebtResidue()
    {
        testcase("FV_M4_20 LoanDeleteDebtResidue");

        using namespace test::jtx;
        using namespace std::chrono_literals;
        Env env{*this, all_ | featureLendingProtocolV1_1};
        auto const [issuer, owner, depositor, asset] = setupCoarsenIou(env);

        // 1. Vault at Scale 10 with 899,000, under its Open limit of 900,000. A second broker.
        auto const fixture =
            setupLendingVault(env, owner, depositor, asset, Number{899'000}, 15 * 365 * 24h, 10);
        Keylet const& broker = fixture.brokerKeylet;
        LendingFixture otherFixture = fixture;
        otherFixture.brokerKeylet =
            keylet::loanBroker(owner.id(), SeqProxy::rawSequence(env.seq(owner)));
        env(loan_broker::set(owner, fixture.vaultKeylet.key));
        env.close();

        // 2. Loan A 52.7018338136 at 10% and loan B 80.8939642807 at 0%, in 2 monthly installments.
        //    Loan C on the second broker: 50,000 in 5 daily installments, maximum LateInterestRate.
        std::uint32_t const month = 30 * 24 * 60 * 60;
        Number const principalA{527'018'338'136LL, -10};
        Number const principalB{808'939'642'807LL, -10};
        Keylet const loanA =
            openLoan(env, fixture, principalA, 2, percentageToTenthBips(10), 0, month);
        Keylet const loanB = openLoan(env, fixture, principalB, 2, TenthBips32{0}, 0, month);
        Keylet const loanC =
            openLoanWithLateInterest(env, otherFixture, Number{50'000}, 5, 24 * 60 * 60);
        BEAST_EXPECT(env.le(broker)->at(sfDebtTotal) == principalA + principalB);

        // 3. C's late payment coarsens the vault to 10^-9, above the installments' last digit.
        payCoarseningLoanLate(env, otherFixture, asset, loanC);

        // 4. A and B pay their 2 installments in turn.
        for (int round = 0; round < 2; ++round)
        {
            payInstallmentLate(env, fixture, asset, loanA);
            payInstallmentLate(env, fixture, asset, loanB);
        }
        BEAST_EXPECT(env.le(loanA)->at(sfPaymentRemaining) == 0);
        BEAST_EXPECT(env.le(loanB)->at(sfPaymentRemaining) == 0);
        BEAST_EXPECT(env.le(broker)->at(sfDebtTotal) == Number{0});

        // 5. The borrower deletes A and then B, the broker's last loan.
        env(loan::del(depositor, loanA.key));
        env.close();
        env(loan::del(depositor, loanB.key));
        env.close();
        BEAST_EXPECT(env.le(broker)->at(sfOwnerCount) == 0);
        BEAST_EXPECT(env.le(broker)->at(sfDebtTotal) == Number{0});
    }

    // FV_M4_22: a pending loan proposed before its vault coarsens can't be deleted.
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
        Keylet const loanA =
            openLoanWithLateInterest(env, fixture, Number{700'000}, 5, 24 * 60 * 60);

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

    // FV_M4_27: a default fails with tecINTERNAL when the cover's credit to the vault is negative.
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

        // 2. LoanManage credits the vault B's default cover of 1 x 9.999% x 100% = 0.09999.
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

    // FV_M4_28: on a coarsened vault a fully covered default pays the vault less than principal.
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

    // FV_M4_33: of two pending loans that passed the Open limit check only one can be accepted.
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

    // FV_M4_42: LoanSet stores a ManagementFeeOutstanding 1 ULP at LoanScale too high.
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

    // FV_M4_44: without fixCleanup3_4_0 a default is allowed decades before the grace period ends.
    void
    testLoanDefaultDueDateWrap()
    {
        testcase("FV_M4_44 LoanDefaultDueDateWrap");

        using namespace test::jtx;
        Env env{*this, (all_ | featureLendingProtocolV1_1) - fixCleanup3_4_0};
        Account const owner{"owner"};
        Account const depositor{"depositor"};
        env.fund(XRP(10'000'000), owner, depositor);
        env.close();

        // 1. The ledger time is 2,900,000,000 s, 44 years before the uint32 time limit. An XRP
        //    vault with 1,000,000 XRP and a RedemptionDate 946,000,000 s later.
        env.close(NetClock::time_point{NetClock::duration{2'900'000'000U}});
        PrettyAsset const asset{xrpIssue()};
        auto const fixture = setupLendingVault(
            env,
            owner,
            depositor,
            asset,
            Number{1'000'000'000'000LL},
            std::chrono::seconds{946'000'000});

        // 2. Loan A: 1,000 XRP in 2 payments with a GracePeriod equal to its PaymentInterval.
        //    StartDate + 2 * PaymentInterval + GracePeriod is about 1,000 s below the limit.
        std::uint64_t const maxTime = std::numeric_limits<std::uint32_t>::max();
        std::uint64_t const startDate = env.now().time_since_epoch().count();
        auto const paymentInterval = static_cast<std::uint32_t>((maxTime - startDate - 1'000) / 3);
        Keylet const loanA = openLoan(
            env,
            fixture,
            Number{1'000'000'000},
            2,
            TenthBips32{0},
            0,
            paymentInterval,
            paymentInterval);
        std::uint32_t const firstDueDate = env.le(loanA)->at(sfNextPaymentDueDate);

        // 3. Past the first due date the broker owner impairs A and then unimpairs it. The
        //    unimpair sets NextPaymentDueDate to the close time plus PaymentInterval.
        env.close(NetClock::time_point{NetClock::duration{firstDueDate + 10'000}});
        env(loan::manage(owner, loanA.key, tfLoanImpair));
        env.close();
        env(loan::manage(owner, loanA.key, tfLoanUnimpair));
        env.close();
        std::uint32_t const nextDueDate = env.le(loanA)->at(sfNextPaymentDueDate);
        BEAST_EXPECT(nextDueDate > env.now().time_since_epoch().count());
        BEAST_EXPECT(std::uint64_t{nextDueDate} + paymentInterval > maxTime);

        // 4. The broker owner defaults A, 14 years before its next due date.
        // BUG: LoanManage returns tesSUCCESS.
        env(loan::manage(owner, loanA.key, tfLoanDefault), Ter(tecTOO_SOON));
        env.close();
    }

    // FV_M4_46: LoanAccept pays out a pending loan while the cover is below its minimum.
    void
    testLoanAcceptBelowMinimumCover()
    {
        testcase("FV_M4_46 LoanAcceptBelowMinimumCover");

        using namespace test::jtx;
        using namespace std::chrono_literals;
        Env env{*this, all_ | featureLendingProtocolV1_1};
        auto const [issuer, owner, depositor, asset] =
            setupIou(env, {.depositorTrust = Number{100'000}, .ownerFunds = Number{1'000}});

        // 1. Vault with 10,000. Broker: CoverRateMinimum 10%, CoverRateLiquidation 100%, cover 200.
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

        // 3. The broker owner defaults A. The cover pays 200, leaving 0 below its minimum of 100.
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

    // FV_M4_49: LoanSet ignores GracePeriod and accepts a loan that defaults after RedemptionDate.
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

        // 3. At RedemptionDate the default is still too soon. It succeeds only later.
        env.close(fixture.redemptionDate);
        env(loan::manage(owner, loanA.key, tfLoanDefault), Ter(tecTOO_SOON));
        env.close();
        defaultAfterGrace(env, owner, loanA);
    }

    // FV_M4_51: an XRP LoanSet whose total value is above 10^17 drops returns tefEXCEPTION.
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

    // FV_M4_56: a pending loan past its StartDate can't be accepted or deleted by a third account.
    void
    testLoanDeleteExpiredPending()
    {
        testcase("FV_M4_56 LoanDeleteExpiredPending");

        using namespace test::jtx;
        using namespace std::chrono_literals;
        Env env{*this, all_ | featureLendingProtocolV1_1};
        Account const owner{"owner"};
        Account const depositor{"depositor"};
        Account const thirdParty{"thirdParty"};
        env.fund(XRP(10'000'000), owner, depositor, thirdParty);
        env.close();

        // 1. An XRP vault with 1,000,000 XRP.
        PrettyAsset const asset{xrpIssue()};
        auto const fixture =
            setupLendingVault(env, owner, depositor, asset, Number{1'000'000'000'000LL});

        // 2. Loan A, two-step and left pending: 200 XRP with a StartDate in one hour.
        Keylet const loanA = proposeLoan(env, fixture, Number{200'000'000}, env.now() + 1h, 200);

        // 3. Two hours later the borrower can no longer accept A.
        env.close(env.now() + 2h);
        env(loan::accept(depositor, loanA.key), Ter(tecEXPIRED));
        env.close();

        // 4. An account that is neither the broker owner nor the borrower deletes A.
        // BUG: LoanDelete returns tecNO_PERMISSION.
        env(loan::del(thirdParty, loanA.key), Ter(tesSUCCESS));
        env.close();
        Number const reserved = env.le(fixture.vaultKeylet)->at(sfAssetsReserved);

        // BUG: AssetsReserved still holds A's 200 XRP.
        BEAST_EXPECTS(reserved == beast::kZero, "AssetsReserved is " + to_string(reserved));
    }

    // FV_M4_57: a LoanSet through a public broker of a private vault ignores the vault's domain.
    void
    testLoanFromPrivateVaultOutsideDomain()
    {
        testcase("FV_M4_57 LoanFromPrivateVaultOutsideDomain");

        using namespace test::jtx;
        Env env{*this, all_ | featureLendingProtocolV1_1};
        Account const owner{"owner"};
        Account const borrower{"borrower"};
        Account const credentialIssuer{"credentialIssuer"};
        env.fund(XRP(10'000'000), owner, borrower, credentialIssuer);
        env.close();

        // 1. A private XRP vault with 1,000,000 XRP of its owner, and a public broker.
        PrettyAsset const asset{xrpIssue()};
        Vault const vault{env};
        auto [createTx, vaultKeylet, subscriptionDate] = vault.createClosedEnded(
            {.owner = owner,
             .asset = asset,
             .flags = tfVaultPrivate,
             .subscriptionOffset = std::chrono::seconds{60}});
        env(createTx);
        env.close();
        env(vault.deposit(
            {.depositor = owner, .id = vaultKeylet.key, .amount = asset(1'000'000'000'000LL)}));
        env.close();
        vault.closePastSubscription(subscriptionDate);
        Keylet const broker = keylet::loanBroker(owner.id(), SeqProxy::rawSequence(env.seq(owner)));
        env(loan_broker::set(owner, vaultKeylet.key));
        env.close();

        // 2. The vault gets a domain whose credential the borrower does not hold.
        pdomain::Credentials const credentials{{.issuer = credentialIssuer, .credType = "member"}};
        env(pdomain::setTx(credentialIssuer, credentials));
        env.close();
        uint256 const domain = pdomain::getNewDomain(env.meta());
        auto setTx = vault.set({.owner = owner, .id = vaultKeylet.key});
        setTx[sfDomainID] = to_string(domain);
        env(setTx);
        env.close();

        // 3. The borrower takes a loan of 1,000 XRP from the broker.
        // BUG: LoanSet returns tesSUCCESS.
        env(loan::set(borrower, broker.key, Number{1'000'000'000}),
            Sig(sfCounterpartySignature, owner),
            Fee(env.current()->fees().base * 2),
            Ter(tecNO_AUTH));
        env.close();
    }

    // FV_M4_61: an MPT LoanSet whose total value is above 2^63 - 1 returns tefEXCEPTION.
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

        // 2. A vault with 9 * 10^15 units, all lent in loan A: 10 payments, LateInterestRate 100%.
        auto const fixture = setupLendingVault(
            env,
            owner,
            depositor,
            asset,
            Number{9'000'000'000'000'000LL},
            std::chrono::seconds{946'000'000});
        Keylet const loanA =
            openLoanWithLateInterest(env, fixture, Number{9'000'000'000'000'000LL}, 10, 60);

        // 3. Paid 15 years late, A takes AssetsAvailable to 7.5 * 10^17, far above the Open limit.
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

        // 5. The same loan for 5.81 * 10^17 has a total value of 9.24 * 10^18, above 2^63 - 1.
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
        // testLoanDefaultDueDateWrap();              // FV_M4_44, without fixCleanup3_4_0
        // testLoanAcceptBelowMinimumCover();         // FV_M4_46
        // testLoanDefaultInRedemption();             // FV_M4_49
        // testLoanSetXRPRange();                     // FV_M4_51
        // testLoanDeleteExpiredPending();            // FV_M4_56
        // testLoanFromPrivateVaultOutsideDomain();   // FV_M4_57
        // testLoanSetMPTRange();                     // FV_M4_61

        // Cases that pass today, kept as regression tests.
        testLoanDefaultStuck();                       // FV_M4_4
        testLoanDefaultTransferMismatch();            // FV_M4_7
        testLoanImpairStuck();                        // FV_M4_8
        testLoanBrokerDebtResidue();                  // FV_M4_9
        testLoanSetXrpPrincipal();                    // FV_M4_10
        testLoanImpairRoundUp();                      // FV_M4_11
        testLoanLossResidue();                        // FV_M4_12
        testLoanUnimpairNeighbor();                   // FV_M4_13
        testLoanImpairLimit();                        // FV_M4_14
        testLoanReservedLock();                       // FV_M4_15
        testLoanDefaultResidue();                     // FV_M4_16
        testLoanSetDebtRounding();                    // FV_M4_17
        testLoanDeleteDebtResidue();                  // FV_M4_20
        // clang-format on
    }
};

BEAST_DEFINE_TESTSUITE(LoanFindings, formal_verification, xrpl);

}  // namespace xrpl
