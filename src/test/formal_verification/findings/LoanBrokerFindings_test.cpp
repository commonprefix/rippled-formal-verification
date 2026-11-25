#include <test/app/lending/LoanManageFixedPrecisionBase.h>
#include <test/formal_verification/findings/LendingFindingsHelpers.h>
#include <test/jtx/Account.h>
#include <test/jtx/Env.h>
#include <test/jtx/TestHelpers.h>
#include <test/jtx/amount.h>
#include <test/jtx/fee.h>
#include <test/jtx/flags.h>
#include <test/jtx/mpt.h>
#include <test/jtx/pay.h>
#include <test/jtx/sig.h>
#include <test/jtx/ter.h>
#include <test/jtx/trust.h>

#include <xrpl/basics/Number.h>
#include <xrpl/beast/unit_test/suite.h>
#include <xrpl/ledger/helpers/LendingHelpers.h>
#include <xrpl/protocol/Feature.h>
#include <xrpl/protocol/Indexes.h>
#include <xrpl/protocol/Issue.h>
#include <xrpl/protocol/Keylet.h>
#include <xrpl/protocol/Protocol.h>
#include <xrpl/protocol/SField.h>
#include <xrpl/protocol/SeqProxy.h>
#include <xrpl/protocol/TER.h>
#include <xrpl/protocol/TxFlags.h>
#include <xrpl/protocol/Units.h>

#include <chrono>
#include <cstdint>
#include <optional>
#include <tuple>

namespace xrpl {

// One test per bug reported in the LoanBroker transactions. The test of an open bug fails and its
// call in run() is commented out. A fixed bug's test is a regression test.
class LoanBrokerFindings_test : public LoanManageFixedPrecisionBase
{
    // FV_M3_1: a LoanBrokerCoverWithdraw finer than the base unit pays and debits whole base units.
    void
    testLoanBrokerCoverWithdrawRounding()
    {
        testcase("FV_M3_1 LoanBrokerCoverWithdrawRounding");

        using namespace test::jtx;
        Env env{*this, all_ | featureLendingProtocolV1_1};
        auto const [issuer, owner, depositor, asset] = setupIou(
            env, {.ownerTrust = Number{1'000'000'000}, .ownerFunds = Number{1'000'000'000}});

        // 1. Vault at Scale 6 with 1,000. Broker with a cover of 1,000,000,000.
        auto const fixture = setupLendingVault(env, owner, depositor, asset, Number{1'000});
        Keylet const& broker = fixture.brokerKeylet;
        Number const cover{1'000'000'000};
        env(loan_broker::coverDeposit(owner, broker.key, asset(cover).value()));
        env.close();

        // 2. The owner withdraws 1.55 base units to the depositor, who receives 1 base unit.
        Number const baseUnit{1, -6};
        Number const balanceBefore = env.balance(depositor, asset).value();
        env(loan_broker::coverWithdraw(owner, broker.key, asset(Number{155, -8}).value()),
            loan_broker::kDestination(depositor));
        env.close();
        BEAST_EXPECT(env.balance(depositor, asset).value() - balanceBefore == baseUnit);
        BEAST_EXPECT(cover - env.le(broker)->at(sfCoverAvailable) == baseUnit);

        // 3. A withdrawal of 0.55 base units is rejected and leaves the cover unchanged.
        env(loan_broker::coverWithdraw(owner, broker.key, asset(Number{55, -8}).value()),
            loan_broker::kDestination(depositor),
            Ter(tecPRECISION_LOSS));
        env.close();
        BEAST_EXPECT(cover - env.le(broker)->at(sfCoverAvailable) == baseUnit);
    }

    // FV_M3_2: a clawback of all cover above the minimum leaves CoverAvailable below the minimum.
    void
    testLoanBrokerClawbackCoarsenedCover()
    {
        testcase("FV_M3_2 LoanBrokerClawbackCoarsenedCover");

        using namespace test::jtx;
        Env env{*this, all_ | featureLendingProtocolV1_1};
        auto const [issuer, owner, depositor, asset] = setupIou(
            env,
            {.clawback = true,
             .depositorTrust = Number{3'000'000},
             .ownerTrust = Number{20'000},
             .ownerFunds = Number{10'001}});

        // 1. Vault at Scale 10 with 800,000. Broker: CoverRateMinimum 10%, CoverRateLiquidation
        //    100%, cover 10,001.
        auto const fixture = setupLendingVault(
            env,
            owner,
            depositor,
            asset,
            Number{800'000},
            std::chrono::seconds{1'000'000},
            10,
            percentageToTenthBips(10),
            percentageToTenthBips(100));
        Keylet const& broker = fixture.brokerKeylet;
        env(loan_broker::coverDeposit(owner, broker.key, asset(10'001).value()));
        env.close();

        // 2. Loan A: 90,000 due in 60 s. Loan B: 10,000 in 2 daily installments with a
        //    LoanServiceFee of 2,000,000.
        Keylet const loanA = openLoan(env, fixture, Number{90'000}, 1, TenthBips32{0}, 0, 60);
        Keylet const loanB = keylet::loan(broker.key, SeqProxy::rawSequence(2));
        env(loan::set(depositor, broker.key, Number{10'000}),
            loan::kLoanServiceFee(Number{2'000'000}),
            loan::kPaymentTotal(2),
            loan::kPaymentInterval(24 * 60 * 60),
            Sig(sfCounterpartySignature, owner),
            Fee(env.current()->fees().base * 2));
        env.close();

        // 3. Defaulting A takes 10,000 from the cover, leaving 1, below its minimum of 1,000.
        defaultAfterGrace(env, owner, loanA);
        BEAST_EXPECT(env.le(broker)->at(sfCoverAvailable) == Number{1});

        // 4. B's first installment of 5,000 and its fee. The fee goes to the cover, which becomes
        //    2,000,001, past 10^16 base units.
        env(loan::pay(depositor, loanB.key, asset(2'005'000).value()));
        env.close();
        BEAST_EXPECT(env.le(broker)->at(sfCoverAvailable) == Number{2'000'001});

        // 5. Loan C: 1.0000000001. The minimum cover becomes 500.1000000001.
        openLoan(env, fixture, Number{10'000'000'001LL, -10}, 1, TenthBips32{0}, 0, 60);
        Number const minimum = minimumBrokerCover(
            env.le(broker)->at(sfDebtTotal),
            percentageToTenthBips(10),
            env.le(fixture.vaultKeylet));
        BEAST_EXPECT(minimum == (Number{5'001'000'000'001LL, -10}));

        // 6. The issuer claws back all cover above the minimum.
        env(loan_broker::coverClawback(issuer), loan_broker::kLoanBrokerId(broker.key));
        env.close();
        Number const coverAvailable = env.le(broker)->at(sfCoverAvailable);

        // BUG: CoverAvailable is 500.1, below the minimum cover.
        BEAST_EXPECTS(coverAvailable >= minimum, "CoverAvailable is " + to_string(coverAvailable));
    }

    // FV_M3_3: on an XRP vault a DebtMaximum above 10^17 drops returns tecPRECISION_LOSS.
    void
    testLoanBrokerXrpDebtMaximum()
    {
        testcase("FV_M3_3 LoanBrokerXrpDebtMaximum");

        using namespace test::jtx;
        Env env{*this, all_ | featureLendingProtocolV1_1};
        Account const lender{"lender"};
        env.fund(XRP(10'000'000), lender);
        env.close();

        // 1. The lender owns an XRP vault with 1,000 drops and a broker.
        PrettyAsset const xrp{xrpIssue()};
        auto const fixture = setupLendingVault(env, lender, lender, xrp, Number{1'000});
        Keylet const& vault = fixture.vaultKeylet;
        Keylet const& broker = fixture.brokerKeylet;

        // 2. A DebtMaximum of 10^17 drops, the largest XRP amount, is accepted.
        Number const largestXrp{1, 17};
        env(loan_broker::set(lender, vault.key),
            loan_broker::kLoanBrokerId(broker.key),
            loan_broker::kDebtMaximum(largestXrp));
        env.close();

        // 3. A new broker with a DebtMaximum of 10^18 drops is rejected.
        Number const aboveLargestXrp{1, 18};
        env(loan_broker::set(lender, vault.key),
            loan_broker::kDebtMaximum(aboveLargestXrp),
            Ter(tecPRECISION_LOSS));
        env.close();

        // 4. An update of the first broker to a DebtMaximum of 10^18 drops is rejected.
        env(loan_broker::set(lender, vault.key),
            loan_broker::kLoanBrokerId(broker.key),
            loan_broker::kDebtMaximum(aboveLargestXrp),
            Ter(tecPRECISION_LOSS));
        env.close();
        BEAST_EXPECT(env.le(broker)->at(sfDebtMaximum) == largestXrp);
    }

    // FV_M3_4: a cover deposit that crosses a power of ten can be withdrawn right back.
    void
    testLoanBrokerCoverUnwithdrawable()
    {
        testcase("FV_M3_4 LoanBrokerCoverUnwithdrawable");

        using namespace test::jtx;
        Env env{*this, all_ | featureLendingProtocolV1_1};
        auto const [issuer, owner, depositor, asset] = setupIou(
            env, {.ownerTrust = Number{10'000'000'000LL}, .ownerFunds = Number{10'000'000'000LL}});

        // 1. Vault at Scale 6 with 1,000 and a broker. A cover of 9,999,999,999.999999, 1 base
        //    unit below 10^10, is above the Open limit.
        auto const fixture = setupLendingVault(env, owner, depositor, asset, Number{1'000});
        Keylet const& broker = fixture.brokerKeylet;
        Number const aboveOpenLimit{9'999'999'999'999'999LL, -6};
        env(loan_broker::coverDeposit(owner, broker.key, asset(aboveOpenLimit).value()),
            Ter(tecLIMIT_EXCEEDED));
        env.close();

        // 2. A cover of 999,999,999.999999, 1 base unit below 10^9, is accepted.
        Number const cover{999'999'999'999'999LL, -6};
        env(loan_broker::coverDeposit(owner, broker.key, asset(cover).value()));
        env.close();

        // 3. A deposit of 1 base unit takes the cover to 1,000,000,000.
        STAmount const baseUnit = asset(Number{1, -6}).value();
        env(loan_broker::coverDeposit(owner, broker.key, baseUnit));
        env.close();
        BEAST_EXPECT(env.le(broker)->at(sfCoverAvailable) == Number{1'000'000'000});

        // 4. The owner withdraws the same amount.
        env(loan_broker::coverWithdraw(owner, broker.key, baseUnit));
        env.close();
        BEAST_EXPECT(env.le(broker)->at(sfCoverAvailable) == cover);
    }

    // FV_M3_5: a cover deposit that crosses a power of ten credits what the owner pays.
    void
    testLoanBrokerCoverOvercredit()
    {
        testcase("FV_M3_5 LoanBrokerCoverOvercredit");

        using namespace test::jtx;
        Env env{*this, all_ | featureLendingProtocolV1_1};
        auto const [issuer, owner, depositor, asset] = setupIou(
            env, {.ownerTrust = Number{2'000'000'000}, .ownerFunds = Number{1'000'000'001}});

        // 1. Vault at Scale 6 with 1,000. Broker with a cover of 999,999,999.999999.
        auto const fixture = setupLendingVault(env, owner, depositor, asset, Number{1'000});
        Keylet const& broker = fixture.brokerKeylet;
        Number const cover{999'999'999'999'999LL, -6};
        env(loan_broker::coverDeposit(owner, broker.key, asset(cover).value()));
        env.close();

        // 2. 9.8 base units take the cover across 10^9. The owner pays 9 and the cover rises by 9.
        Number const credit{9, -6};
        Number const balanceBefore = env.balance(owner, asset).value();
        env(loan_broker::coverDeposit(owner, broker.key, asset(Number{98, -7}).value()));
        env.close();
        BEAST_EXPECT(balanceBefore - env.balance(owner, asset).value() == credit);
        BEAST_EXPECT(env.le(broker)->at(sfCoverAvailable) - cover == credit);
    }

    // FV_M3_6: a cover clawback finer than the base unit claws and debits whole base units.
    void
    testLoanBrokerClawbackRounding()
    {
        testcase("FV_M3_6 LoanBrokerClawbackRounding");

        using namespace test::jtx;
        Env env{*this, all_ | featureLendingProtocolV1_1};
        auto const [issuer, owner, depositor, asset] = setupIou(
            env,
            {.clawback = true,
             .ownerTrust = Number{1'000'000'000},
             .ownerFunds = Number{1'000'000'000}});

        // 1. Vault at Scale 6 with 1,000. Broker with a cover of 1,000,000,000.
        auto const fixture = setupLendingVault(env, owner, depositor, asset, Number{1'000});
        Keylet const& broker = fixture.brokerKeylet;
        Number const cover{1'000'000'000};
        env(loan_broker::coverDeposit(owner, broker.key, asset(cover).value()));
        env.close();
        Account const pseudoAccount{"broker pseudo-account", env.le(broker)->at(sfAccount)};

        // 2. A clawback of 0.76 base units is rejected and leaves the cover unchanged.
        env(loan_broker::coverClawback(issuer),
            loan_broker::kLoanBrokerId(broker.key),
            kAmount(asset(Number{76, -8}).value()),
            Ter(tecPRECISION_LOSS));
        env.close();
        BEAST_EXPECT(env.le(broker)->at(sfCoverAvailable) == cover);

        // 3. A clawback of 1.76 base units takes 1 from the pseudo-account and from the cover.
        Number const baseUnit{1, -6};
        env(loan_broker::coverClawback(issuer),
            loan_broker::kLoanBrokerId(broker.key),
            kAmount(asset(Number{176, -8}).value()));
        env.close();
        BEAST_EXPECT(cover - env.balance(pseudoAccount, asset).value() == baseUnit);
        BEAST_EXPECT(cover - env.le(broker)->at(sfCoverAvailable) == baseUnit);
    }

    // FV_M3_7: a late payment that coarsens the vault leaves another broker's minimum cover as is.
    void
    testLoanBrokerMinimumCoverVaultScale()
    {
        testcase("FV_M3_7 LoanBrokerMinimumCoverVaultScale");

        using namespace test::jtx;
        Env env{*this, all_ | featureLendingProtocolV1_1};
        auto const [issuer, owner, depositor, asset] = setupIou(
            env,
            {.depositorTrust = Number{2'000'000},
             .ownerTrust = Number{100'000},
             .ownerFunds = Number{70'002}});

        // 1. Vault at Scale 10 with 899,999, shared by brokers A and B at CoverRateMinimum 10%.
        TenthBips32 const coverRateMinimum = percentageToTenthBips(10);
        auto const fixture = setupLendingVault(
            env,
            owner,
            depositor,
            asset,
            Number{899'999},
            std::chrono::hours{2 * 365 * 24},
            10,
            coverRateMinimum,
            percentageToTenthBips(25));
        Keylet const& vault = fixture.vaultKeylet;
        Keylet const& brokerA = fixture.brokerKeylet;
        LendingFixture fixtureB = fixture;
        fixtureB.brokerKeylet =
            keylet::loanBroker(owner.id(), SeqProxy::rawSequence(env.seq(owner)));
        Keylet const& brokerB = fixtureB.brokerKeylet;
        env(loan_broker::set(owner, vault.key),
            loan_broker::kCoverRateMinimum(coverRateMinimum),
            loan_broker::kCoverRateLiquidation(percentageToTenthBips(25)));
        env.close();

        // 2. Broker A: a cover of 1.2345678902, exactly the minimum for loan A of 12.3456789012
        //    due in one year.
        Number const coverA{12'345'678'902LL, -10};
        env(loan_broker::coverDeposit(owner, brokerA.key, asset(coverA).value()));
        env.close();
        openLoan(
            env,
            fixture,
            Number{123'456'789'012LL, -10},
            1,
            percentageToTenthBips(5),
            0,
            365 * 24 * 60 * 60);
        Number const debtA = env.le(brokerA)->at(sfDebtTotal);
        BEAST_EXPECT(minimumBrokerCover(debtA, coverRateMinimum, env.le(vault)) == coverA);

        // 3. Broker B: a cover of 70,000. Loan B: 700,000 due in one day, LateInterestRate 100%.
        env(loan_broker::coverDeposit(owner, brokerB.key, asset(70'000).value()));
        env.close();
        Keylet const loanB =
            openLoanWithLateInterest(env, fixtureB, Number{700'000}, 1, 24 * 60 * 60);

        // 4. Loan B is paid 60 days late. Its late interest takes AssetsTotal past 1,000,000.
        closePastDue(env, loanB);
        env.close(std::chrono::hours{60 * 24});
        env(loan::pay(depositor, loanB.key, asset(1'000'000).value(), tfLoanLatePayment));
        env.close();
        expectCoarsened(env, vault);

        // 5. Broker A is unchanged, and its minimum cover is still its CoverAvailable.
        BEAST_EXPECT(env.le(brokerA)->at(sfDebtTotal) == debtA);
        BEAST_EXPECT(env.le(brokerA)->at(sfCoverAvailable) == coverA);
        BEAST_EXPECT(minimumBrokerCover(debtA, coverRateMinimum, env.le(vault)) == coverA);
    }

    // FV_M3_8: two cover deposits across a power of ten cost and credit the same in either order.
    void
    testLoanBrokerCoverDepositOrder()
    {
        testcase("FV_M3_8 LoanBrokerCoverDepositOrder");

        using namespace test::jtx;

        // 1 base unit and 1.3 base units.
        Number const amountA{1, -6};
        Number const amountB{13, -7};

        for (bool const amountAFirst : {true, false})
        {
            Env env{*this, all_ | featureLendingProtocolV1_1};
            auto const [issuer, owner, depositor, asset] = setupIou(
                env, {.ownerTrust = Number{2'000'000'000}, .ownerFunds = Number{1'000'000'001}});

            // 1. Vault at Scale 6 with 1,000. Broker with a cover of 999,999,999.999999.
            auto const fixture = setupLendingVault(env, owner, depositor, asset, Number{1'000});
            Keylet const& broker = fixture.brokerKeylet;
            Number const cover{999'999'999'999'999LL, -6};
            env(loan_broker::coverDeposit(owner, broker.key, asset(cover).value()));
            env.close();
            Number const balanceBefore = env.balance(owner, asset).value();

            // 2. The two deposits. The first takes the cover to 1,000,000,000.
            Number const& first = amountAFirst ? amountA : amountB;
            Number const& second = amountAFirst ? amountB : amountA;
            env(loan_broker::coverDeposit(owner, broker.key, asset(first).value()));
            env.close();
            BEAST_EXPECT(env.le(broker)->at(sfCoverAvailable) == Number{1'000'000'000});
            env(loan_broker::coverDeposit(owner, broker.key, asset(second).value()));
            env.close();

            // 3. In either order the owner pays 2 base units and the cover rises by the same.
            Number const total{2, -6};
            BEAST_EXPECT(balanceBefore - env.balance(owner, asset).value() == total);
            BEAST_EXPECT(env.le(broker)->at(sfCoverAvailable) - cover == total);
        }
    }

    // FV_M3_9: LoanBrokerDelete by an unauthorized MPT holder fails with tecINVARIANT_FAILED.
    void
    testLoanBrokerDeleteUnauthorized()
    {
        testcase("FV_M3_9 LoanBrokerDeleteUnauthorized");

        using namespace test::jtx;
        Env env{*this, all_ | featureLendingProtocolV1_1};

        // 1. An MPT that requires authorization. The lender is authorized and holds 20,000.
        Account const issuer{"issuer"};
        Account const lender{"lender"};
        env.fund(XRP(100'000), issuer, lender);
        env.close();
        MPTTester mptt(
            {.env = env,
             .issuer = issuer,
             .holders = {lender},
             .pay = 20'000,
             .flags = tfMPTRequireAuth | tfMPTCanTransfer,
             .authHolder = true});
        PrettyAsset const mpt{mptt.issuanceID()};

        // 2. The lender owns a vault with 1,000 and a broker with a cover of 5,000.
        auto const fixture = setupLendingVault(env, lender, lender, mpt, Number{1'000});
        Keylet const& broker = fixture.brokerKeylet;
        env(loan_broker::coverDeposit(lender, broker.key, mpt(5'000).value()));
        env.close();

        // 3. The issuer unauthorizes the lender. A cover withdrawal to the lender is rejected.
        mptt.authorize({.account = issuer, .holder = lender, .flags = tfMPTUnauthorize});
        env.close();
        env(loan_broker::coverWithdraw(lender, broker.key, mpt(1'000).value()), Ter(tecNO_AUTH));
        env.close();

        // 4. The lender deletes the broker, which pays the cover to the lender.
        env(loan_broker::del(lender, broker.key), Ter(std::ignore));
        env.close();

        // BUG: LoanBrokerDelete returns tecINVARIANT_FAILED.
        BEAST_EXPECTS(
            env.ter() != tecINVARIANT_FAILED, "LoanBrokerDelete returned " + transToken(env.ter()));
    }

    // FV_M3_10: an XRP cover deposit that takes the cover above 10^17 drops returns tefEXCEPTION.
    void
    testLoanBrokerCoverDepositRangeXRP()
    {
        testcase("FV_M3_10 LoanBrokerCoverDepositRange XRP");

        using namespace test::jtx;
        Env env{*this, all_ | featureLendingProtocolV1_1};
        Account const lender{"lender"};
        env.fund(XRP(10'000'000), lender);
        env.close();

        // 1. The lender owns an XRP vault with 1,000 drops and a broker with a cover of 1 drop.
        PrettyAsset const xrp{xrpIssue()};
        auto const fixture = setupLendingVault(env, lender, lender, xrp, Number{1'000});
        Keylet const& broker = fixture.brokerKeylet;
        env(loan_broker::coverDeposit(lender, broker.key, drops(1)));
        env.close();

        // 2. A deposit that takes the cover to 10^17 drops is above the Open limit.
        env(loan_broker::coverDeposit(lender, broker.key, drops(99'999'999'999'999'999)),
            Ter(tecLIMIT_EXCEEDED));
        env.close();

        // 3. One drop more takes the cover to 10^17 + 1 drops.
        // BUG: the result is tefEXCEPTION.
        env(loan_broker::coverDeposit(lender, broker.key, drops(100'000'000'000'000'000)),
            Ter(tecLIMIT_EXCEEDED));
        env.close();
    }

    // FV_M3_10: an MPT cover deposit that takes the cover above 2^63 - 1 returns tefEXCEPTION.
    void
    testLoanBrokerCoverDepositRangeMPT()
    {
        testcase("FV_M3_10 LoanBrokerCoverDepositRange MPT");

        using namespace test::jtx;
        Env env{*this, all_ | featureLendingProtocolV1_1};

        // 1. The lender holds 20,000 of an MPT and owns a vault of 1,000 and a broker with cover 2.
        Account const issuer{"issuer"};
        Account const lender{"lender"};
        env.fund(XRP(100'000), issuer, lender);
        env.close();
        MPTTester const mptt(
            {.env = env,
             .issuer = issuer,
             .holders = {lender},
             .pay = 20'000,
             .flags = tfMPTCanTransfer});
        PrettyAsset const mpt{mptt.issuanceID()};
        auto const fixture = setupLendingVault(env, lender, lender, mpt, Number{1'000});
        Keylet const& broker = fixture.brokerKeylet;
        env(loan_broker::coverDeposit(lender, broker.key, mpt(2).value()));
        env.close();

        // 2. A deposit that takes the cover to 2^63 - 1 units is above the Open limit.
        STAmount const toLargest{mptt.issuanceID(), std::uint64_t{9'223'372'036'854'775'805}};
        env(loan_broker::coverDeposit(lender, broker.key, toLargest), Ter(tecLIMIT_EXCEEDED));
        env.close();

        // 3. Two units more take the cover to 2^63 + 1 units.
        // BUG: the result is tefEXCEPTION.
        STAmount const pastLargest{mptt.issuanceID(), std::uint64_t{9'223'372'036'854'775'807}};
        env(loan_broker::coverDeposit(lender, broker.key, pastLargest), Ter(tecLIMIT_EXCEEDED));
        env.close();
    }

    // FV_M3_11: with RequireAuth, LoanBrokerDelete re-creates the owner's deleted trust line.
    void
    testLoanBrokerDeleteRequireAuthIou()
    {
        testcase("FV_M3_11 LoanBrokerDeleteRequireAuthIou");

        using namespace test::jtx;
        Env env{*this, all_ | featureLendingProtocolV1_1};

        // 1. An IOU with RequireAuth. The lender is authorized and holds 1,001,000.
        Account const issuer{"issuer"};
        Account const lender{"lender"};
        env.fund(XRP(1'000'000), issuer, lender);
        env.close();
        env(fset(issuer, asfRequireAuth));
        env.close();
        PrettyAsset const iou{issuer["USD"]};
        env(trust(lender, iou(10'000'000)));
        env(trust(issuer, iou(0), lender, tfSetfAuth));
        env(pay(issuer, lender, iou(1'001'000)));
        env.close();

        // 2. The lender owns a vault with 1,000,000 and a broker with a cover of 1,000.
        auto const fixture = setupLendingVault(env, lender, lender, iou, Number{1'000'000});
        Keylet const& broker = fixture.brokerKeylet;
        env(loan_broker::coverDeposit(lender, broker.key, iou(1'000).value()));
        env.close();

        // 3. The lender holds nothing and deletes its trust line.
        Keylet const lenderLine = keylet::trustLine(lender, issuer["USD"]);
        env(trust(lender, iou(0)));
        env.close();
        BEAST_EXPECT(!env.le(lenderLine));

        // 4. A cover withdrawal to the lender is rejected.
        env(loan_broker::coverWithdraw(lender, broker.key, iou(1).value()), Ter(tecNO_LINE));
        env.close();

        // 5. The lender deletes the broker, which pays the cover to the lender.
        // BUG: LoanBrokerDelete returns tesSUCCESS.
        env(loan_broker::del(lender, broker.key), Ter(tecNO_LINE));
        env.close();

        // BUG: the lender's trust line exists again and holds the cover of 1,000.
        BEAST_EXPECTS(
            !env.le(lenderLine),
            "the lender's trust line holds " + env.balance(lender, iou).value().getText());
    }

public:
    void
    run() override
    {
        // Open bugs. Each call fails until the C++ code is fixed, so it is commented out.
        // clang-format off
        // testLoanBrokerClawbackCoarsenedCover();    // FV_M3_2
        // testLoanBrokerDeleteUnauthorized();        // FV_M3_9
        // testLoanBrokerCoverDepositRangeXRP();      // FV_M3_10
        // testLoanBrokerCoverDepositRangeMPT();      // FV_M3_10
        // testLoanBrokerDeleteRequireAuthIou();      // FV_M3_11

        // Cases that pass today, kept as regression tests.
        testLoanBrokerCoverWithdrawRounding();        // FV_M3_1
        testLoanBrokerXrpDebtMaximum();               // FV_M3_3
        testLoanBrokerCoverUnwithdrawable();          // FV_M3_4
        testLoanBrokerCoverOvercredit();              // FV_M3_5
        testLoanBrokerClawbackRounding();             // FV_M3_6
        testLoanBrokerMinimumCoverVaultScale();       // FV_M3_7
        testLoanBrokerCoverDepositOrder();            // FV_M3_8
        // clang-format on
    }
};

BEAST_DEFINE_TESTSUITE(LoanBrokerFindings, formal_verification, xrpl);

}  // namespace xrpl
