#include <test/app/lending/LoanManageFixedPrecisionBase.h>
#include <test/jtx/Account.h>
#include <test/jtx/Env.h>
#include <test/jtx/TestHelpers.h>
#include <test/jtx/amount.h>
#include <test/jtx/fee.h>
#include <test/jtx/mpt.h>
#include <test/jtx/sig.h>
#include <test/jtx/ter.h>

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

// One failing test per open bug in the loan broker transactions. A test is enabled by
// uncommenting its call in run().
class LoanBrokerFindings_test : public LoanManageFixedPrecisionBase
{
    // FV_M3_2: a LoanBrokerCoverClawback of all cover above the minimum rounds the clawed amount
    // up and leaves CoverAvailable below the minimum cover.
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

        // 3. The broker owner defaults A. The cover pays 10,000 and drops to 1, below its
        //    minimum of 1,000.
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

    // FV_M3_9: LoanBrokerDelete fails with tecINVARIANT_FAILED when the issuer of an MPT that
    // requires authorization has unauthorized the broker owner.
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

    // FV_M3_10: a LoanBrokerCoverDeposit on an XRP vault returns tefEXCEPTION when CoverAvailable
    // plus the amount is above 10^17 drops. Preclaim builds that sum as an XRP amount.
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

    // FV_M3_10: the same on an MPT vault, when CoverAvailable plus the amount is above 2^63
    // units.
    void
    testLoanBrokerCoverDepositRangeMPT()
    {
        testcase("FV_M3_10 LoanBrokerCoverDepositRange MPT");

        using namespace test::jtx;
        Env env{*this, all_ | featureLendingProtocolV1_1};

        // 1. The lender holds 20,000 of an MPT and owns a vault with 1,000 and a broker with a
        //    cover of 2.
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
        // clang-format on

        // Keeps a run of this suite alone from reporting "No tests run".
        pass();
    }
};

BEAST_DEFINE_TESTSUITE(LoanBrokerFindings, formal_verification, xrpl);

}  // namespace xrpl
