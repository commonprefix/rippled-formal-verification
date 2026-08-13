#include <test/app/lending/LoanTestBase.h>
#include <test/jtx/Account.h>
#include <test/jtx/Env.h>
#include <test/jtx/TestHelpers.h>
#include <test/jtx/amount.h>
#include <test/jtx/fee.h>
#include <test/jtx/flags.h>
#include <test/jtx/mpt.h>
#include <test/jtx/multisign.h>
#include <test/jtx/noop.h>
#include <test/jtx/pay.h>
#include <test/jtx/trust.h>
#include <test/jtx/vault.h>

#include <xrpl/basics/Number.h>
#include <xrpl/basics/chrono.h>
#include <xrpl/beast/unit_test/suite.h>
#include <xrpl/json/json_value.h>
#include <xrpl/ledger/helpers/AccountRootHelpers.h>
#include <xrpl/protocol/Feature.h>
#include <xrpl/protocol/Indexes.h>
#include <xrpl/protocol/Issue.h>
#include <xrpl/protocol/LedgerFormats.h>
#include <xrpl/protocol/MPTIssue.h>
#include <xrpl/protocol/Protocol.h>
#include <xrpl/protocol/SField.h>
#include <xrpl/protocol/STAmount.h>
#include <xrpl/protocol/TER.h>
#include <xrpl/protocol/TxFlags.h>
#include <xrpl/protocol/Units.h>
#include <xrpl/protocol/XRPAmount.h>

#include <array>
#include <chrono>
#include <cstdint>
#include <functional>
#include <utility>
#include <vector>

namespace xrpl::test {

class LoanSet_test : public LoanTestBase
{
private:
    void
    testLoanSet(FeatureBitset features)
    {
        using namespace jtx;

        Account const issuer{"issuer"};
        Account const lender{"lender"};
        Account const borrower{"borrower"};

        struct CaseArgs
        {
            bool requireAuth = false;
            bool authorizeBorrower = false;
            int initialXRP = 1'000'000;
        };

        auto const testCase = [&, this](
                                  std::function<void(Env&, BrokerInfo const&, MPTTester&)> mptTest,
                                  std::function<void(Env&, BrokerInfo const&)> iouTest,
                                  CaseArgs args = {}) {
            Env env(*this, features);
            env.fund(XRP(args.initialXRP), issuer, lender, borrower);
            env.close();
            if (args.requireAuth)
            {
                env(fset(issuer, asfRequireAuth));
                env.close();
            }

            // We need two different asset types, MPT and IOU. Prepare MPT
            // first
            MPTTester mptt{env, issuer, kMptInitNoFund};

            auto const kNone = LedgerSpecificFlags(0);
            mptt.create(
                {.flags = tfMPTCanTransfer | tfMPTCanLock |
                     (args.requireAuth ? tfMPTRequireAuth : kNone)});
            env.close();
            PrettyAsset const mptAsset = mptt.issuanceID();
            mptt.authorize({.account = lender});
            mptt.authorize({.account = borrower});
            env.close();
            if (args.requireAuth)
            {
                mptt.authorize({.account = issuer, .holder = lender});
                if (args.authorizeBorrower)
                    mptt.authorize({.account = issuer, .holder = borrower});
                env.close();
            }

            env(pay(issuer, lender, mptAsset(10'000'000)));
            env.close();

            // Prepare IOU
            PrettyAsset const iouAsset = issuer[iouCurrency_];
            env(trust(lender, iouAsset(10'000'000)));
            env(trust(borrower, iouAsset(10'000'000)));
            env.close();
            if (args.requireAuth)
            {
                env(trust(issuer, iouAsset(0), lender, tfSetfAuth));
                env(pay(issuer, lender, iouAsset(10'000'000)));
                if (args.authorizeBorrower)
                {
                    env(trust(issuer, iouAsset(0), borrower, tfSetfAuth));
                    env(pay(issuer, borrower, iouAsset(10'000)));
                }
            }
            else
            {
                env(pay(issuer, lender, iouAsset(10'000'000)));
                env(pay(issuer, borrower, iouAsset(10'000)));
            }
            env.close();

            // Create vaults and loan brokers
            std::array const assets{mptAsset, iouAsset};
            std::vector<BrokerInfo> brokers;
            brokers.reserve(assets.size());
            for (auto const& asset : assets)
            {
                brokers.emplace_back(createVaultAndBroker(env, asset, lender));
            }

            if (mptTest)
                mptTest(env, brokers[0], mptt);
            if (iouTest)
                iouTest(env, brokers[1]);
        };

        testCase(
            [&, this](Env& env, BrokerInfo const& broker, auto&) {
                using namespace loan;
                Number const principalRequest = broker.asset(1'000).value();

                testcase("MPT issuer is borrower, issuer submits");
                env(set(issuer, broker.brokerID, principalRequest),
                    kCounterparty(lender),
                    Sig(sfCounterpartySignature, lender),
                    Fee(env.current()->fees().base * 5));

                testcase("MPT issuer is borrower, lender submits");
                env(set(lender, broker.brokerID, principalRequest),
                    kCounterparty(issuer),
                    Sig(sfCounterpartySignature, issuer),
                    Fee(env.current()->fees().base * 5));
            },
            [&, this](Env& env, BrokerInfo const& broker) {
                using namespace loan;
                Number const principalRequest = broker.asset(1'000).value();

                testcase("IOU issuer is borrower, issuer submits");
                env(set(issuer, broker.brokerID, principalRequest),
                    kCounterparty(lender),
                    Sig(sfCounterpartySignature, lender),
                    Fee(env.current()->fees().base * 5));

                testcase("IOU issuer is borrower, lender submits");
                env(set(lender, broker.brokerID, principalRequest),
                    kCounterparty(issuer),
                    Sig(sfCounterpartySignature, issuer),
                    Fee(env.current()->fees().base * 5));
            },
            CaseArgs{.requireAuth = true});

        testCase(
            [&, this](Env& env, BrokerInfo const& broker, auto&) {
                using namespace loan;
                Number const principalRequest = broker.asset(1'000).value();

                testcase("MPT unauthorized borrower, borrower submits");
                env(set(borrower, broker.brokerID, principalRequest),
                    kCounterparty(lender),
                    Sig(sfCounterpartySignature, lender),
                    Fee(env.current()->fees().base * 5),
                    Ter{tecNO_AUTH});

                testcase("MPT unauthorized borrower, lender submits");
                env(set(lender, broker.brokerID, principalRequest),
                    kCounterparty(borrower),
                    Sig(sfCounterpartySignature, borrower),
                    Fee(env.current()->fees().base * 5),
                    Ter{tecNO_AUTH});
            },
            [&, this](Env& env, BrokerInfo const& broker) {
                using namespace loan;
                Number const principalRequest = broker.asset(1'000).value();

                testcase("IOU unauthorized borrower, borrower submits");
                env(set(borrower, broker.brokerID, principalRequest),
                    kCounterparty(lender),
                    Sig(sfCounterpartySignature, lender),
                    Fee(env.current()->fees().base * 5),
                    Ter{tecNO_AUTH});

                testcase("IOU unauthorized borrower, lender submits");
                env(set(lender, broker.brokerID, principalRequest),
                    kCounterparty(borrower),
                    Sig(sfCounterpartySignature, borrower),
                    Fee(env.current()->fees().base * 5),
                    Ter{tecNO_AUTH});
            },
            CaseArgs{.requireAuth = true});

        auto const [acctReserve, incReserve] = [this]() -> std::pair<int, int> {
            Env const env{*this, testableAmendments()};
            return {
                env.current()->fees().accountReserve(0, 1).drops() / kDropsPerXrp.drops(),
                env.current()->fees().increment.drops() / kDropsPerXrp.drops()};
        }();

        testCase(
            [&, this](Env& env, BrokerInfo const& broker, MPTTester& mptt) {
                using namespace loan;
                Number const principalRequest = broker.asset(1'000).value();

                testcase(
                    "MPT authorized borrower, borrower submits, borrower has "
                    "no reserve");
                mptt.authorize({.account = borrower, .flags = tfMPTUnauthorize});
                env.close();

                auto const mptoken = keylet::mptoken(mptt.issuanceID(), borrower);
                auto const sleMPT1 = env.le(mptoken);
                BEAST_EXPECT(sleMPT1 == nullptr);

                // Burn some XRP
                env(noop(borrower), Fee(XRP((acctReserve * 2) + (incReserve * 2))));
                env.close();

                // Cannot create loan, not enough reserve to create MPToken
                env(set(borrower, broker.brokerID, principalRequest),
                    kCounterparty(lender),
                    Sig(sfCounterpartySignature, lender),
                    Fee(env.current()->fees().base * 5),
                    Ter{tecINSUFFICIENT_RESERVE});
                env.close();

                // Can create loan now, will implicitly create MPToken
                env(pay(issuer, borrower, XRP(incReserve)));
                env.close();
                env(set(borrower, broker.brokerID, principalRequest),
                    kCounterparty(lender),
                    Sig(sfCounterpartySignature, lender),
                    Fee(env.current()->fees().base * 5));
                env.close();

                auto const sleMPT2 = env.le(mptoken);
                BEAST_EXPECT(sleMPT2 != nullptr);
            },
            {},
            CaseArgs{.initialXRP = (acctReserve * 2) + (incReserve * 8) + 1});

        testCase(
            {},
            [&, this](Env& env, BrokerInfo const& broker) {
                using namespace loan;
                Number const principalRequest = broker.asset(1'000).value();

                testcase(
                    "IOU authorized borrower, borrower submits, borrower has "
                    "no reserve");
                // Remove trust line from borrower to issuer
                env.trust(broker.asset(0), borrower);
                env.close();

                env(pay(borrower, issuer, broker.asset(10'000)));
                env.close();
                auto const trustline = keylet::trustLine(borrower, broker.asset.raw().get<Issue>());
                auto const sleLine1 = env.le(trustline);
                BEAST_EXPECT(sleLine1 == nullptr);

                // Burn some XRP
                env(noop(borrower), Fee(XRP((acctReserve * 2) + (incReserve * 2))));
                env.close();

                // Cannot create loan, not enough reserve to create trust line
                env(set(borrower, broker.brokerID, principalRequest),
                    kCounterparty(lender),
                    Sig(sfCounterpartySignature, lender),
                    Fee(env.current()->fees().base * 5),
                    Ter{tecNO_LINE_INSUF_RESERVE});
                env.close();

                // Can create loan now, will implicitly create trust line
                env(pay(issuer, borrower, XRP(incReserve)));
                env.close();
                env(set(borrower, broker.brokerID, principalRequest),
                    kCounterparty(lender),
                    Sig(sfCounterpartySignature, lender),
                    Fee(env.current()->fees().base * 5));
                env.close();

                auto const sleLine2 = env.le(trustline);
                BEAST_EXPECT(sleLine2 != nullptr);
            },
            CaseArgs{.initialXRP = (acctReserve * 2) + (incReserve * 8) + 1});

        testCase(
            [&, this](Env& env, BrokerInfo const& broker, MPTTester& mptt) {
                using namespace loan;
                Number const principalRequest = broker.asset(1'000).value();

                testcase(
                    "MPT authorized borrower, borrower submits, lender has "
                    "no reserve");
                auto const mptoken = keylet::mptoken(mptt.issuanceID(), lender);
                auto const sleMPT1 = env.le(mptoken);
                BEAST_EXPECT(sleMPT1 != nullptr);

                env(pay(lender, issuer, broker.asset(sleMPT1->at(sfMPTAmount))));
                env.close();

                mptt.authorize({.account = lender, .flags = tfMPTUnauthorize});
                env.close();

                auto const sleMPT2 = env.le(mptoken);
                BEAST_EXPECT(sleMPT2 == nullptr);

                // Burn some XRP
                env(noop(lender), Fee(XRP(incReserve)));
                env.close();

                // Cannot create loan, not enough reserve to create MPToken
                env(set(borrower, broker.brokerID, principalRequest),
                    kLoanOriginationFee(broker.asset(1).value()),
                    kCounterparty(lender),
                    Sig(sfCounterpartySignature, lender),
                    Fee(env.current()->fees().base * 5),
                    Ter{tecINSUFFICIENT_RESERVE});
                env.close();

                // Can create loan now, will implicitly create MPToken
                env(pay(issuer, lender, XRP(incReserve)));
                env.close();
                env(set(borrower, broker.brokerID, principalRequest),
                    kLoanOriginationFee(broker.asset(1).value()),
                    kCounterparty(lender),
                    Sig(sfCounterpartySignature, lender),
                    Fee(env.current()->fees().base * 5));
                env.close();

                auto const sleMPT3 = env.le(mptoken);
                BEAST_EXPECT(sleMPT3 != nullptr);
            },
            {},
            CaseArgs{.initialXRP = (acctReserve * 2) + (incReserve * 8) + 1});

        testCase(
            {},
            [&, this](Env& env, BrokerInfo const& broker) {
                using namespace loan;
                Number const principalRequest = broker.asset(1'000).value();

                testcase(
                    "IOU authorized borrower, borrower submits, lender has no "
                    "reserve");
                // Remove trust line from lender to issuer
                env.trust(broker.asset(0), lender);
                env.close();

                auto const trustline = keylet::trustLine(lender, broker.asset.raw().get<Issue>());
                auto const sleLine1 = env.le(trustline);
                BEAST_EXPECT(sleLine1 != nullptr);

                env(pay(lender, issuer, broker.asset(abs(sleLine1->at(sfBalance).value()))));
                env.close();
                auto const sleLine2 = env.le(trustline);
                BEAST_EXPECT(sleLine2 == nullptr);

                // Burn some XRP
                env(noop(lender), Fee(XRP(incReserve)));
                env.close();

                // Cannot create loan, not enough reserve to create trust line
                env(set(borrower, broker.brokerID, principalRequest),
                    kLoanOriginationFee(broker.asset(1).value()),
                    kCounterparty(lender),
                    Sig(sfCounterpartySignature, lender),
                    Fee(env.current()->fees().base * 5),
                    Ter{tecNO_LINE_INSUF_RESERVE});
                env.close();

                // Can create loan now, will implicitly create trust line
                env(pay(issuer, lender, XRP(incReserve)));
                env.close();
                env(set(borrower, broker.brokerID, principalRequest),
                    kLoanOriginationFee(broker.asset(1).value()),
                    kCounterparty(lender),
                    Sig(sfCounterpartySignature, lender),
                    Fee(env.current()->fees().base * 5));
                env.close();

                auto const sleLine3 = env.le(trustline);
                BEAST_EXPECT(sleLine3 != nullptr);
            },
            CaseArgs{.initialXRP = (acctReserve * 2) + (incReserve * 8) + 1});

        testCase(
            [&, this](Env& env, BrokerInfo const& broker, MPTTester& mptt) {
                using namespace loan;
                Number const principalRequest = broker.asset(1'000).value();

                testcase("MPT authorized borrower, unauthorized lender");
                auto const mptoken = keylet::mptoken(mptt.issuanceID(), lender);
                auto const sleMPT1 = env.le(mptoken);
                BEAST_EXPECT(sleMPT1 != nullptr);

                env(pay(lender, issuer, broker.asset(sleMPT1->at(sfMPTAmount))));
                env.close();

                mptt.authorize({.account = lender, .flags = tfMPTUnauthorize});
                env.close();

                auto const sleMPT2 = env.le(mptoken);
                BEAST_EXPECT(sleMPT2 == nullptr);

                // Cannot create loan, lender not authorized to receive fee
                env(set(borrower, broker.brokerID, principalRequest),
                    kLoanOriginationFee(broker.asset(1).value()),
                    kCounterparty(lender),
                    Sig(sfCounterpartySignature, lender),
                    Fee(env.current()->fees().base * 5),
                    Ter{tecNO_AUTH});
                env.close();

                // Cannot create loan, even without an origination fee
                env(set(borrower, broker.brokerID, principalRequest),
                    kCounterparty(lender),
                    Sig(sfCounterpartySignature, lender),
                    Fee(env.current()->fees().base * 5),
                    Ter{tecNO_AUTH});
                env.close();

                // No MPToken for lender - no authorization and no payment
                auto const sleMPT3 = env.le(mptoken);
                BEAST_EXPECT(sleMPT3 == nullptr);
            },
            {},
            CaseArgs{.requireAuth = true, .authorizeBorrower = true});

        testCase(
            [&, this](Env& env, BrokerInfo const& broker, auto&) {
                using namespace loan;
                Number const principalRequest = broker.asset(1'000).value();

                testcase("MPT authorized borrower, borrower submits");
                env(set(borrower, broker.brokerID, principalRequest),
                    kCounterparty(lender),
                    Sig(sfCounterpartySignature, lender),
                    Fee(env.current()->fees().base * 5));
            },
            [&, this](Env& env, BrokerInfo const& broker) {
                using namespace loan;
                Number const principalRequest = broker.asset(1'000).value();

                testcase("IOU authorized borrower, borrower submits");
                env(set(borrower, broker.brokerID, principalRequest),
                    kCounterparty(lender),
                    Sig(sfCounterpartySignature, lender),
                    Fee(env.current()->fees().base * 5));
            },
            CaseArgs{.requireAuth = true, .authorizeBorrower = true});

        testCase(
            [&, this](Env& env, BrokerInfo const& broker, auto&) {
                using namespace loan;
                Number const principalRequest = broker.asset(1'000).value();

                testcase("MPT authorized borrower, lender submits");
                env(set(lender, broker.brokerID, principalRequest),
                    kCounterparty(borrower),
                    Sig(sfCounterpartySignature, borrower),
                    Fee(env.current()->fees().base * 5));
            },
            [&, this](Env& env, BrokerInfo const& broker) {
                using namespace loan;
                Number const principalRequest = broker.asset(1'000).value();

                testcase("IOU authorized borrower, lender submits");
                env(set(lender, broker.brokerID, principalRequest),
                    kCounterparty(borrower),
                    Sig(sfCounterpartySignature, borrower),
                    Fee(env.current()->fees().base * 5));
            },
            CaseArgs{.requireAuth = true, .authorizeBorrower = true});

        jtx::Account const alice{"alice"};
        jtx::Account const bella{"bella"};
        auto const msigSetup = [&](Env& env, Account const& account) {
            json::Value const tx1 = signers(account, 2, {{alice, 1}, {bella, 1}});
            env(tx1);
            env.close();
        };

        testCase(
            [&, this](Env& env, BrokerInfo const& broker, auto&) {
                using namespace loan;
                msigSetup(env, lender);
                Number const principalRequest = broker.asset(1'000).value();

                testcase(
                    "MPT authorized borrower, borrower submits, lender "
                    "multisign");
                env(set(borrower, broker.brokerID, principalRequest),
                    kCounterparty(lender),
                    Msig(sfCounterpartySignature, alice, bella),
                    Fee(env.current()->fees().base * 5));
            },
            [&, this](Env& env, BrokerInfo const& broker) {
                using namespace loan;
                msigSetup(env, lender);
                Number const principalRequest = broker.asset(1'000).value();

                testcase(
                    "IOU authorized borrower, borrower submits, lender "
                    "multisign");
                env(set(borrower, broker.brokerID, principalRequest),
                    kCounterparty(lender),
                    Msig(sfCounterpartySignature, alice, bella),
                    Fee(env.current()->fees().base * 5));
            },
            CaseArgs{.requireAuth = true, .authorizeBorrower = true});

        testCase(
            [&, this](Env& env, BrokerInfo const& broker, auto&) {
                using namespace loan;
                msigSetup(env, borrower);
                Number const principalRequest = broker.asset(1'000).value();

                testcase(
                    "MPT authorized borrower, lender submits, borrower "
                    "multisign");
                env(set(lender, broker.brokerID, principalRequest),
                    kCounterparty(borrower),
                    Msig(sfCounterpartySignature, alice, bella),
                    Fee(env.current()->fees().base * 5));
            },
            [&, this](Env& env, BrokerInfo const& broker) {
                using namespace loan;
                msigSetup(env, borrower);
                Number const principalRequest = broker.asset(1'000).value();

                testcase(
                    "IOU authorized borrower, lender submits, borrower "
                    "multisign");
                env(set(lender, broker.brokerID, principalRequest),
                    kCounterparty(borrower),
                    Msig(sfCounterpartySignature, alice, bella),
                    Fee(env.current()->fees().base * 5));
            },
            CaseArgs{.requireAuth = true, .authorizeBorrower = true});

        testCase(
            [&, this](Env& env, BrokerInfo const& broker, auto&) {
                using namespace loan;
                Number const principalRequest = broker.asset(1'000).value();
                Vault const vault{env};
                auto tx = vault.set({.owner = lender, .id = broker.vaultID});
                tx[sfAssetsMaximum] = BrokerParameters::defaults().vaultDeposit;
                env(tx);
                env.close();

                testcase("Vault at maximum value");
                env(set(issuer, broker.brokerID, principalRequest),
                    kCounterparty(lender),
                    kInterestRate(TenthBips32(10'000)),
                    Sig(sfCounterpartySignature, lender),
                    Fee(env.current()->fees().base * 5),
                    Ter(tecLIMIT_EXCEEDED));
            },
            nullptr);

        testCase(
            [&, this](Env& env, BrokerInfo const& broker, auto&) {
                using namespace loan;
                Number const principalRequest = broker.asset(1'000).value();
                Vault const vault{env};
                auto tx = vault.set({.owner = lender, .id = broker.vaultID});
                tx[sfAssetsMaximum] =
                    BrokerParameters::defaults().vaultDeposit + broker.asset(1).number();
                env(tx);
                env.close();

                testcase("Vault maximum value exceeded");
                env(set(issuer, broker.brokerID, principalRequest),
                    kCounterparty(lender),
                    kInterestRate(TenthBips32(100'000)),
                    Sig(sfCounterpartySignature, lender),
                    Fee(env.current()->fees().base * 5),
                    kPaymentTotal(2),
                    kPaymentInterval(3600 * 24),
                    Ter(tecLIMIT_EXCEEDED));
            },
            nullptr);
    }

    // Exercises the two-step (LendingProtocolV1_1) flow, where the LoanBroker
    // owner proposes a pending Loan (LoanSet with a Borrower and StartDate) that
    // the Borrower later accepts (LoanAccept) or that either party cancels
    // (LoanDelete). Requires the LendingProtocolV1_1 amendment.
    void
    testTwoStep(FeatureBitset features)
    {
        using namespace jtx;
        using namespace jtx::loan;
        using namespace std::chrono_literals;

        Account const issuer{"issuer"};  // Issues the IOU / MPT assets
        Account const lender{"lender"};  // Vault + LoanBroker owner
        Account const borrower{"borrower"};
        Account const evan{"evan"};  // unrelated third party

        // Loan terms shared across the scenarios. The principal is derived
        // from the broker's asset, so it adapts to XRP, IOU and MPT.
        auto const interest = TenthBips32{50'000};
        std::uint32_t const payTotal = 10;
        std::uint32_t const payInterval = 200;

        auto const assetTypeName = [](AssetType t) -> char const* {
            switch (t)
            {
                case AssetType::XRP:
                    return "XRP";
                case AssetType::IOU:
                    return "IOU";
                case AssetType::MPT:
                    return "MPT";
            }
            return "?";
        };

        // Build a funded environment with a Vault + LoanBroker owned by
        // `lender`, using the requested asset type, and return the broker.
        auto const makeBroker = [&](Env& env, AssetType assetType) -> BrokerInfo {
            env.fund(XRP(100'000'000), noripple(lender));
            env.fund(XRP(1'000'000), borrower, evan);
            if (assetType != AssetType::XRP)
                env.fund(XRP(1'000'000), issuer);
            env.close();
            BrokerParameters const params{};
            auto const asset = createAsset(env, assetType, params, issuer, lender, borrower);
            env.close();
            if (!asset.native())
                env(pay(issuer, lender, asset(params.vaultDeposit + params.coverDeposit)));
            env.close();
            return createVaultAndBroker(env, asset, lender, params);
        };

        // The keylet of the next loan the broker will create.
        auto const nextLoanKeylet = [&](Env& env, BrokerInfo const& broker) -> Keylet {
            auto const brokerSle = env.le(broker.brokerKeylet());
            return keylet::loan(
                broker.brokerID, SeqProxy::rawSequence(brokerSle->at(sfLoanSequence)));
        };

        // Snapshot of the vault's asset accounting.
        struct VaultAmounts
        {
            Number available;
            Number reserved;
            Number total;
        };
        auto const readVault = [&](Env& env, BrokerInfo const& broker) -> VaultAmounts {
            auto const v = env.le(broker.vaultKeylet());
            return {
                .available = v->at(sfAssetsAvailable),
                .reserved = v->at(sfAssetsReserved),
                .total = v->at(sfAssetsTotal)};
        };

        // Submit a valid two-step proposal from `proposer` on behalf of
        // `theBorrower`, with the supplied StartDate and any extra functors.
        auto const propose = [&](Env& env,
                                 BrokerInfo const& broker,
                                 Account const& proposer,
                                 Account const& theBorrower,
                                 std::uint32_t startDate,
                                 auto const&... extra) {
            env(set(proposer, broker.brokerID, broker.asset(200).number()),
                kBorrower(theBorrower),
                kStartDate(startDate),
                kInterestRate(interest),
                kPaymentTotal(payTotal),
                kPaymentInterval(payInterval),
                extra...);
        };

        auto const featureEnabled = (features & featureLendingProtocolV1_1).any();

        if (!featureEnabled)
        {
            testcase("Two-step: rejected as before");

            Env env(*this, features);
            auto const broker = makeBroker(env, AssetType::XRP);
            // A StartDate comfortably in the future. With the amendment
            // disabled, the Borrower/StartDate fields are gated off in
            // checkExtraFeatures, so the tx is rejected with temDISABLED.
            propose(
                env,
                broker,
                lender,
                borrower,
                (env.now() + 1h).time_since_epoch().count(),
                Ter(temDISABLED));

            // A LoanSet with no CounterpartySignature, not inside a Batch
            // inner transaction, and with no Borrower field is rejected as
            // before, because the immediate flow still requires a
            // CounterpartySignature.
            env(set(lender, broker.brokerID, broker.asset(200).number()), Ter(temBAD_SIGNER));

            // Rest of the tests are not applicable
            return;
        }

        for (auto const assetType : {AssetType::XRP, AssetType::IOU, AssetType::MPT})
        {
            testcase << "Two-step: propose then accept (" << assetTypeName(assetType) << ")";

            Env env(*this, features);
            auto const broker = makeBroker(env, assetType);
            Number const principal = broker.asset(200).number();

            auto const vault0 = readVault(env, broker);
            auto const lenderOwners0 = env.ownerCount(lender);
            auto const borrowerOwners0 = env.ownerCount(borrower);

            auto const loanKeylet = nextLoanKeylet(env, broker);
            // A StartDate comfortably in the future.
            propose(env, broker, lender, borrower, (env.now() + 1h).time_since_epoch().count());
            env.close();

            // The proposal creates a pending Loan, linked only into the broker
            // pseudo-account's directory.
            if (auto const loan = env.le(loanKeylet); BEAST_EXPECT(loan))
            {
                BEAST_EXPECT(loan->isFlag(lsfLoanPending));
                BEAST_EXPECT(loan->at(sfBorrower) == borrower.id());
                BEAST_EXPECT(loan->isFieldPresent(sfLoanBrokerNode));
                BEAST_EXPECT(!loan->isFieldPresent(sfOwnerNode));
            }

            // The owner reserve is charged to the broker owner, not the
            // borrower.
            BEAST_EXPECT(env.ownerCount(lender) == lenderOwners0 + 1);
            BEAST_EXPECT(env.ownerCount(borrower) == borrowerOwners0);

            // Vault bookkeeping: Available -= P, Reserved += P, Total +=
            // InterestDue.
            auto const vault1 = readVault(env, broker);
            BEAST_EXPECT(vault1.available == vault0.available - principal);
            BEAST_EXPECT(vault1.reserved == vault0.reserved + principal);
            BEAST_EXPECT(vault1.total > vault0.total);
            Number const interestDue = vault1.total - vault0.total;

            // Capture pre-acceptance balances to verify disbursement.
            auto const vaultPseudo = [&]() {
                auto const v = env.le(broker.vaultKeylet());
                return Account("vault pseudo-account", v->at(sfAccount));
            }();
            STAmount const pseudoBal0 = env.balance(vaultPseudo, broker.asset).value();
            STAmount const borrowerBal0 = env.balance(borrower, broker.asset).value();

            env(accept(borrower, loanKeylet.key));
            env.close();

            // The loan is now active and linked into the borrower's directory.
            if (auto const loan = env.le(loanKeylet); BEAST_EXPECT(loan))
            {
                BEAST_EXPECT(!loan->isFlag(lsfLoanPending));
                BEAST_EXPECT(loan->isFieldPresent(sfLoanBrokerNode));
                BEAST_EXPECT(loan->isFieldPresent(sfOwnerNode));
            }

            // The reserve is swapped from the broker owner to the borrower.
            BEAST_EXPECT(env.ownerCount(lender) == lenderOwners0);
            BEAST_EXPECT(env.ownerCount(borrower) == borrowerOwners0 + 1);

            // Reserved principal is released; Available and Total are unchanged
            // from the proposal.
            auto const vault2 = readVault(env, broker);
            BEAST_EXPECT(vault2.reserved == vault0.reserved);
            BEAST_EXPECT(vault2.available == vault0.available - principal);
            BEAST_EXPECT(vault2.total == vault0.total + interestDue);

            // The principal is disbursed from the vault pseudo-account to the
            // borrower (origination fee is zero, so the borrower receives it
            // all, less the transaction fee it paid).
            BEAST_EXPECT(
                env.balance(vaultPseudo, broker.asset).value() ==
                pseudoBal0 - broker.asset(200).value());
            BEAST_EXPECT(env.balance(borrower, broker.asset).value() > borrowerBal0);
        }

        {
            testcase("Two-step: propose then accept with origination fee");

            // Use an IOU so the disbursed amounts can be checked exactly,
            // without the borrower's XRP transaction fee getting in the way.
            Env env(*this, features);
            auto const broker = makeBroker(env, AssetType::IOU);
            Number const principal = broker.asset(200).number();
            Number const originationFee = broker.asset(5).number();

            auto const loanKeylet = nextLoanKeylet(env, broker);
            propose(
                env,
                broker,
                lender,
                borrower,
                (env.now() + 1h).time_since_epoch().count(),
                kLoanOriginationFee(originationFee));
            env.close();

            // The pending loan records the origination fee.
            if (auto const loan = env.le(loanKeylet); BEAST_EXPECT(loan))
            {
                BEAST_EXPECT(loan->isFlag(lsfLoanPending));
                BEAST_EXPECT(loan->at(sfLoanOriginationFee) == originationFee);
            }

            auto const vaultPseudo = [&]() {
                auto const v = env.le(broker.vaultKeylet());
                return Account("vault pseudo-account", v->at(sfAccount));
            }();
            STAmount const pseudoBal0 = env.balance(vaultPseudo, broker.asset).value();
            STAmount const borrowerBal0 = env.balance(borrower, broker.asset).value();
            STAmount const lenderBal0 = env.balance(lender, broker.asset).value();

            env(accept(borrower, loanKeylet.key));
            env.close();

            STAmount const netToBorrower{broker.asset, principal - originationFee};
            STAmount const feeToOwner{broker.asset, originationFee};

            // The full principal leaves the vault pseudo-account.
            BEAST_EXPECT(
                env.balance(vaultPseudo, broker.asset).value() ==
                pseudoBal0 - broker.asset(200).value());
            // The borrower receives the principal net of the origination fee.
            BEAST_EXPECT(
                env.balance(borrower, broker.asset).value() == borrowerBal0 + netToBorrower);
            // The broker owner receives the origination fee.
            BEAST_EXPECT(env.balance(lender, broker.asset).value() == lenderBal0 + feeToOwner);
        }

        {
            testcase("Two-step: proposal failures");

            Env env(*this, features);
            auto const epoch = env.now();
            auto const broker = makeBroker(env, AssetType::XRP);

            // The submitter must be the LoanBroker owner.
            // A StartDate comfortably in the future.
            propose(
                env,
                broker,
                evan,
                borrower,
                (env.now() + 1h).time_since_epoch().count(),
                Ter(tecNO_PERMISSION));

            // The StartDate must be in the future.
            std::uint32_t const pastDate = epoch.time_since_epoch().count();
            propose(env, broker, lender, borrower, pastDate, Ter(tecEXPIRED));

            // A LoanSet with no CounterpartySignature, not inside a Batch
            // inner transaction, and with no Borrower field matches neither
            // the one-step nor the two-step (Borrower) flow.
            env(set(lender, broker.brokerID, broker.asset(200).number()), Ter(temINVALID));
        }

        {
            testcase("Two-step: LoanAccept validation");

            Env env(*this, features);
            auto const broker = makeBroker(env, AssetType::XRP);

            // Zero LoanID fails preflight.
            env(accept(borrower, uint256{}), Ter(temINVALID));

            // A LoanID that does not resolve to a Loan object.
            env(accept(borrower, keylet::loan(broker.brokerID, SeqProxy::rawSequence(999)).key),
                Ter(tecNO_ENTRY));

            auto const loanKeylet = nextLoanKeylet(env, broker);
            // A StartDate comfortably in the future.
            propose(env, broker, lender, borrower, (env.now() + 1h).time_since_epoch().count());
            env.close();

            // Only the borrower may accept.
            env(accept(evan, loanKeylet.key), Ter(tecNO_PERMISSION));
            env(accept(lender, loanKeylet.key), Ter(tecNO_PERMISSION));

            // The borrower accepts successfully.
            env(accept(borrower, loanKeylet.key));
            env.close();

            // The loan is no longer pending, so it cannot be accepted again.
            env(accept(borrower, loanKeylet.key), Ter(tecNO_PERMISSION));
        }

        {
            testcase("Two-step: pending loan rejects other transactions");

            // While a loan is pending acceptance it may only be accepted
            // (LoanAccept) or cancelled (LoanDelete, covered separately). Every
            // other loan transaction must reject it.
            Env env(*this, features);
            auto const broker = makeBroker(env, AssetType::XRP);

            auto const loanKeylet = nextLoanKeylet(env, broker);
            propose(env, broker, lender, borrower, (env.now() + 1h).time_since_epoch().count());
            env.close();

            // The loan is pending.
            if (auto const loan = env.le(loanKeylet); BEAST_EXPECT(loan))
                BEAST_EXPECT(loan->isFlag(lsfLoanPending));

            // LoanManage can not impair, unimpair, or default a pending loan.
            env(manage(lender, loanKeylet.key, tfLoanImpair), Ter(tecNO_PERMISSION));
            env(manage(lender, loanKeylet.key, tfLoanUnimpair), Ter(tecNO_PERMISSION));
            env(manage(lender, loanKeylet.key, tfLoanDefault), Ter(tecNO_PERMISSION));

            // LoanPay can not pay a pending loan, even from the borrower.
            env(pay(borrower, loanKeylet.key, broker.asset(50)), Ter(tecNO_PERMISSION));
            env(pay(borrower, loanKeylet.key, broker.asset(50), tfLoanFullPayment),
                Ter(tecNO_PERMISSION));

            // The borrower can still accept the pending loan.
            env(accept(borrower, loanKeylet.key));
            env.close();
            if (auto const loan = env.le(loanKeylet); BEAST_EXPECT(loan))
                BEAST_EXPECT(!loan->isFlag(lsfLoanPending));
        }

        {
            testcase("Two-step: LoanAccept after expiry");

            Env env(*this, features);
            auto const broker = makeBroker(env, AssetType::XRP);

            auto const loanKeylet = nextLoanKeylet(env, broker);
            std::uint32_t const startDate = (env.now() + 1h).time_since_epoch().count();
            propose(env, broker, lender, borrower, startDate);
            env.close();

            // Advance the ledger beyond the StartDate.
            env.close(NetClock::time_point{NetClock::duration{startDate}} + 1h);

            env(accept(borrower, loanKeylet.key), Ter(tecEXPIRED));
        }

        {
            testcase("Two-step: LoanDelete of pending loan after StartDate expired");

            // A pending loan whose StartDate has passed can no longer be
            // accepted (LoanAccept returns tecEXPIRED), but it can still be
            // cleaned up with LoanDelete, releasing the reserve and reversing
            // the vault bookkeeping.
            Env env(*this, features);
            auto const broker = makeBroker(env, AssetType::XRP);

            auto const vault0 = readVault(env, broker);
            auto const lenderOwners0 = env.ownerCount(lender);
            auto const borrowerOwners0 = env.ownerCount(borrower);

            auto const loanKeylet = nextLoanKeylet(env, broker);
            std::uint32_t const startDate = (env.now() + 1h).time_since_epoch().count();
            propose(env, broker, lender, borrower, startDate);
            env.close();

            BEAST_EXPECT(env.le(loanKeylet));
            BEAST_EXPECT(env.ownerCount(lender) == lenderOwners0 + 1);

            // Advance the ledger beyond the StartDate.
            env.close(NetClock::time_point{NetClock::duration{startDate}} + 1h);

            // The proposal has expired, so it can no longer be accepted.
            env(accept(borrower, loanKeylet.key), Ter(tecEXPIRED));

            // But it can still be deleted.
            env(del(lender, loanKeylet.key));
            env.close();

            // The loan is gone, the reserve is released, and the vault
            // bookkeeping is fully reversed.
            BEAST_EXPECT(!env.le(loanKeylet));
            BEAST_EXPECT(env.ownerCount(lender) == lenderOwners0);
            BEAST_EXPECT(env.ownerCount(borrower) == borrowerOwners0);

            auto const vault1 = readVault(env, broker);
            BEAST_EXPECT(vault1.available == vault0.available);
            BEAST_EXPECT(vault1.reserved == vault0.reserved);
            BEAST_EXPECT(vault1.total == vault0.total);
        }

        {
            testcase("Two-step: LoanSet with insufficient reserve");

            // Use an IOU so the lender's XRP balance is only relevant to
            // the owner reserve for the Loan object created by LoanSet.
            Env env(*this, features);
            auto const broker = makeBroker(env, AssetType::IOU);

            // Drain the lender's XRP down to its current reserve, leaving
            // nothing to cover the additional owner reserve for the Loan
            // object that LoanSet creates on the LoanBroker owner.
            auto const amt =
                env.balance(lender) - accountReserve(*env.current(), lender.id(), env.journal);
            env(pay(lender, issuer, amt));
            env.close();

            propose(
                env,
                broker,
                lender,
                borrower,
                (env.now() + 1h).time_since_epoch().count(),
                Ter(tecINSUFFICIENT_RESERVE));
        }

        {
            testcase("Two-step: LoanAccept with insufficient reserve");

            // Use an IOU so the borrower's XRP balance is only relevant to
            // the owner reserve, not to receiving the loan asset.
            Env env(*this, features);
            auto const broker = makeBroker(env, AssetType::IOU);

            auto const loanKeylet = nextLoanKeylet(env, broker);
            propose(env, broker, lender, borrower, (env.now() + 1h).time_since_epoch().count());
            env.close();

            // Drain the borrower's XRP down to its current reserve, leaving
            // nothing to cover the additional owner reserve for the Loan
            // object that acceptance transfers to the borrower.
            auto const amt =
                env.balance(borrower) - accountReserve(*env.current(), borrower.id(), env.journal);
            env(pay(borrower, issuer, amt));
            env.close();

            env(accept(borrower, loanKeylet.key), Ter(tecINSUFFICIENT_RESERVE));
        }

        // Between the LoanSet proposal and the LoanAccept, the issuer
        // freezes the trust line (IOU) or locks the MPToken (MPT) on the
        // vault pseudo-account, which is about to disburse the principal.
        // Acceptance must be rejected. XRP cannot be frozen, so it is
        // excluded.
        for (auto const assetType : {AssetType::IOU, AssetType::MPT})
        {
            testcase << "Two-step: LoanAccept with frozen vault pseudo-account ("
                     << assetTypeName(assetType) << ")";

            Env env(*this, features);
            auto const broker = makeBroker(env, assetType);

            auto const loanKeylet = nextLoanKeylet(env, broker);
            propose(env, broker, lender, borrower, (env.now() + 1h).time_since_epoch().count());
            env.close();

            auto const vaultPseudo = [&]() {
                auto const v = env.le(broker.vaultKeylet());
                return Account("vault pseudo-account", v->at(sfAccount));
            }();

            TER expected = tesSUCCESS;
            if (assetType == AssetType::IOU)
            {
                env(trust(issuer, vaultPseudo[iouCurrency_](0), tfSetFreeze));
                env.close();
                expected = TER{tecFROZEN};
            }
            else
            {
                MPTTester mptt{env, issuer, broker.asset.raw().get<MPTIssue>().getMptID()};
                mptt.set({.account = issuer, .holder = vaultPseudo, .flags = tfMPTLock});
                env.close();
                expected = TER{tecLOCKED};
            }

            env(accept(borrower, loanKeylet.key), Ter(expected));
        }

        // Between the LoanSet proposal and the LoanAccept, the issuer deep
        // freezes the trust line (IOU) or locks the MPToken (MPT) on the
        // LoanBroker pseudo-account, which is the fallback recipient of
        // LoanPay fees. Acceptance must be rejected. XRP cannot be frozen,
        // so it is excluded.
        for (auto const assetType : {AssetType::IOU, AssetType::MPT})
        {
            testcase << "Two-step: LoanAccept with deep frozen broker pseudo-account ("
                     << assetTypeName(assetType) << ")";

            Env env(*this, features);
            auto const broker = makeBroker(env, assetType);

            auto const loanKeylet = nextLoanKeylet(env, broker);
            propose(env, broker, lender, borrower, (env.now() + 1h).time_since_epoch().count());
            env.close();

            auto const brokerPseudo = [&]() {
                auto const b = env.le(broker.brokerKeylet());
                return Account("broker pseudo-account", b->at(sfAccount));
            }();

            TER expected = tesSUCCESS;
            if (assetType == AssetType::IOU)
            {
                env(trust(issuer, brokerPseudo[iouCurrency_](0), tfSetFreeze | tfSetDeepFreeze));
                env.close();
                expected = TER{tecFROZEN};
            }
            else
            {
                MPTTester mptt{env, issuer, broker.asset.raw().get<MPTIssue>().getMptID()};
                mptt.set({.account = issuer, .holder = brokerPseudo, .flags = tfMPTLock});
                env.close();
                expected = TER{tecLOCKED};
            }

            env(accept(borrower, loanKeylet.key), Ter(expected));
        }

        // Between the LoanSet proposal and the LoanAccept, the issuer
        // freezes the trust line (IOU) or locks the MPToken (MPT) on the
        // borrower, who is about to receive the principal. Acceptance must
        // be rejected. XRP cannot be frozen, so it is excluded.
        for (auto const assetType : {AssetType::IOU, AssetType::MPT})
        {
            testcase << "Two-step: LoanAccept with frozen borrower (" << assetTypeName(assetType)
                     << ")";

            Env env(*this, features);
            auto const broker = makeBroker(env, assetType);

            auto const loanKeylet = nextLoanKeylet(env, broker);
            propose(env, broker, lender, borrower, (env.now() + 1h).time_since_epoch().count());
            env.close();

            TER expected = tesSUCCESS;
            if (assetType == AssetType::IOU)
            {
                env(trust(issuer, borrower[iouCurrency_](0), tfSetFreeze));
                env.close();
                expected = TER{tecFROZEN};
            }
            else
            {
                MPTTester mptt{env, issuer, broker.asset.raw().get<MPTIssue>().getMptID()};
                mptt.set({.account = issuer, .holder = borrower, .flags = tfMPTLock});
                env.close();
                expected = TER{tecLOCKED};
            }

            env(accept(borrower, loanKeylet.key), Ter(expected));
        }

        // Between the LoanSet proposal and the LoanAccept, the issuer deep
        // freezes the trust line (IOU) or locks the MPToken (MPT) on the
        // LoanBroker owner, who receives the origination fee. Acceptance
        // must be rejected. XRP cannot be frozen, so it is excluded.
        for (auto const assetType : {AssetType::IOU, AssetType::MPT})
        {
            testcase << "Two-step: LoanAccept with deep frozen broker owner ("
                     << assetTypeName(assetType) << ")";

            Env env(*this, features);
            auto const broker = makeBroker(env, assetType);

            auto const loanKeylet = nextLoanKeylet(env, broker);
            propose(env, broker, lender, borrower, (env.now() + 1h).time_since_epoch().count());
            env.close();

            TER expected = tesSUCCESS;
            if (assetType == AssetType::IOU)
            {
                env(trust(issuer, lender[iouCurrency_](0), tfSetFreeze | tfSetDeepFreeze));
                env.close();
                expected = TER{tecFROZEN};
            }
            else
            {
                MPTTester mptt{env, issuer, broker.asset.raw().get<MPTIssue>().getMptID()};
                mptt.set({.account = issuer, .holder = lender, .flags = tfMPTLock});
                env.close();
                expected = TER{tecLOCKED};
            }

            env(accept(borrower, loanKeylet.key), Ter(expected));
        }

        {
            testcase("Two-step: LoanAccept when a holding cannot be added");

            // Between the LoanSet proposal and the LoanAccept, the IOU
            // issuer clears asfDefaultRipple, so a fresh holding for the
            // vault asset can no longer be established. Acceptance must be
            // rejected by the canAddHolding check in checkLoanFreeze. Only
            // the IOU path is reachable: for MPT, MPTCanTransfer is required
            // to create the vault/broker and MPT flags are immutable.
            Env env(*this, features);
            auto const broker = makeBroker(env, AssetType::IOU);

            auto const loanKeylet = nextLoanKeylet(env, broker);
            propose(env, broker, lender, borrower, (env.now() + 1h).time_since_epoch().count());
            env.close();

            env(fclear(issuer, asfDefaultRipple));
            env.close();

            env(accept(borrower, loanKeylet.key), Ter(terNO_RIPPLE));
        }

        {
            testcase("Two-step: LoanAccept with unauthorized borrower (MPT)");

            // The MPT requires holder authorization. The borrower is
            // authorized at LoanSet proposal time so the proposal succeeds,
            // then the issuer revokes the borrower's MPToken authorization
            // before LoanAccept. Disbursement in doApply fails the
            // requireAuth(StrongAuth) check. Only the MPT path is
            // reachable: XRP has no authorization concept, and IOU trust
            // line authorization cannot be revoked once granted.
            Env env(*this, features);

            env.fund(XRP(1'000'000), issuer, noripple(lender), borrower);
            env.close();

            MPTTester asset(
                {.env = env,
                 .issuer = issuer,
                 .holders = {lender, borrower},
                 .flags = kMptDexFlags | tfMPTRequireAuth | tfMPTCanClawback | tfMPTCanLock,
                 .authHolder = true});

            env(pay(issuer, lender, asset(2'000'000)));
            env.close();

            auto const broker = createVaultAndBroker(env, asset, lender);

            auto const loanKeylet = nextLoanKeylet(env, broker);
            propose(env, broker, lender, borrower, (env.now() + 1h).time_since_epoch().count());
            env.close();

            // Issuer revokes the borrower's MPToken authorization.
            asset.authorize({.account = issuer, .holder = borrower, .flags = tfMPTUnauthorize});
            env.close();

            env(accept(borrower, loanKeylet.key), Ter(tecNO_AUTH));
        }

        {
            testcase("Two-step: LoanAccept with unauthorized broker owner (MPT)");

            // Same rationale as the unauthorized-borrower case, but this
            // time the issuer revokes the broker owner's MPToken
            // authorization between proposal and accept. disburseLoan's
            // requireAuth(brokerOwner, StrongAuth) check fails.
            Env env(*this, features);

            env.fund(XRP(1'000'000), issuer, noripple(lender), borrower);
            env.close();

            MPTTester asset(
                {.env = env,
                 .issuer = issuer,
                 .holders = {lender, borrower},
                 .flags = kMptDexFlags | tfMPTRequireAuth | tfMPTCanClawback | tfMPTCanLock,
                 .authHolder = true});

            env(pay(issuer, lender, asset(2'000'000)));
            env.close();

            auto const broker = createVaultAndBroker(env, asset, lender);

            auto const loanKeylet = nextLoanKeylet(env, broker);
            propose(env, broker, lender, borrower, (env.now() + 1h).time_since_epoch().count());
            env.close();

            // Issuer revokes the broker owner's MPToken authorization.
            asset.authorize({.account = issuer, .holder = lender, .flags = tfMPTUnauthorize});
            env.close();

            env(accept(borrower, loanKeylet.key), Ter(tecNO_AUTH));
        }

        // Deleting a pending loan reverses the proposal-time bookkeeping and
        // releases the broker owner's reserve. It can be done by either the
        // broker owner or the borrower.
        auto const testDeletePending = [&](AssetType assetType, Account const& deleter) {
            Env env(*this, features);
            auto const broker = makeBroker(env, assetType);

            auto const vault0 = readVault(env, broker);
            auto const lenderOwners0 = env.ownerCount(lender);
            auto const borrowerOwners0 = env.ownerCount(borrower);

            auto const loanKeylet = nextLoanKeylet(env, broker);
            // A StartDate comfortably in the future.
            propose(env, broker, lender, borrower, (env.now() + 1h).time_since_epoch().count());
            env.close();

            BEAST_EXPECT(env.le(loanKeylet));
            BEAST_EXPECT(env.ownerCount(lender) == lenderOwners0 + 1);

            // An unrelated account cannot delete the loan.
            env(del(evan, loanKeylet.key), Ter(tecNO_PERMISSION));

            env(del(deleter, loanKeylet.key));
            env.close();

            // The loan is gone, the reserve is released, and the vault
            // bookkeeping is fully reversed.
            BEAST_EXPECT(!env.le(loanKeylet));
            BEAST_EXPECT(env.ownerCount(lender) == lenderOwners0);
            BEAST_EXPECT(env.ownerCount(borrower) == borrowerOwners0);

            auto const vault1 = readVault(env, broker);
            BEAST_EXPECT(vault1.available == vault0.available);
            BEAST_EXPECT(vault1.reserved == vault0.reserved);
            BEAST_EXPECT(vault1.total == vault0.total);
        };

        for (auto const assetType : {AssetType::XRP, AssetType::IOU, AssetType::MPT})
        {
            testcase << "Two-step: LoanDelete of pending loan by broker owner ("
                     << assetTypeName(assetType) << ")";
            testDeletePending(assetType, lender);

            testcase << "Two-step: LoanDelete of pending loan by borrower ("
                     << assetTypeName(assetType) << ")";
            testDeletePending(assetType, borrower);
        }
    }

    // LoanSet in a closed-ended vault — phase gating and maturity bound.
    void
    testLoanSetClosedEnded()
    {
        testcase("LoanSet closed-ended: phase and maturity bound");
        using namespace jtx;
        using namespace loan;

        Account const issuer{"issuer"};
        Account const lender{"lender"};
        Account const borrower{"borrower"};

        // Common loan schedule used by the phase-rejection cases below.
        constexpr std::uint32_t kInterval = 3600u * 24u;  // 1 day
        constexpr std::uint32_t kTotal = 2u;

        // featureLendingProtocolV1_1 is excluded from `all_` by convention (see the comment on
        // `all_`), so callers must opt in. Closed-ended vaults are gated on this amendment; without
        // it VaultCreate returns temDISABLED and every follow-on txn sees tecNO_ENTRY.
        auto const withEnv = [&, this](auto&& body) {
            Env env(*this, testableAmendments() | featureLendingProtocolV1_1);
            env.fund(XRP(1'000'000'000), issuer, lender, borrower);
            env.close();
            PrettyAsset const asset{xrpIssue(), 1'000'000};
            body(env, asset);
        };

        auto const setLoan = [&](Env& env, BrokerInfo const& broker, TER expected) {
            env(set(lender, broker.brokerID, broker.asset(100).value()),
                kCounterparty(borrower),
                Sig(sfCounterpartySignature, borrower),
                Fee(env.current()->fees().base * 5),
                kPaymentTotal(kTotal),
                kPaymentInterval(kInterval),
                Ter(expected));
            env.close();
        };

        // 1. Rejected during Subscription: the broker is created in Subscription (skipPhaseAdvance
        // = true), then LoanSet is attempted before advancing past SubscriptionDate.
        withEnv([&](Env& env, PrettyAsset const& asset) {
            auto const broker = createVaultAndBroker(
                env,
                asset,
                lender,
                BrokerParameters{.vaultKind = VaultKind::ClosedEnded, .skipPhaseAdvance = true});
            setLoan(env, broker, tecTOO_SOON);
        });

        // 2. Rejected during Redemption: broker is set up normally (which lands the vault in
        // Investment), then advance the clock past RedemptionDate before attempting LoanSet.
        withEnv([&](Env& env, PrettyAsset const& asset) {
            auto const broker = createVaultAndBroker(
                env, asset, lender, BrokerParameters{.vaultKind = VaultKind::ClosedEnded});
            BEAST_EXPECT(broker.redemptionDate.has_value());
            using d = NetClock::duration;
            using tp = NetClock::time_point;
            env.close(tp{d{*broker.redemptionDate + 1}});
            setLoan(env, broker, tecEXPIRED);
        });

        // 3. Accepted during Investment when the schedule comfortably fits before RedemptionDate.
        withEnv([&](Env& env, PrettyAsset const& asset) {
            auto const broker = createVaultAndBroker(
                env, asset, lender, BrokerParameters{.vaultKind = VaultKind::ClosedEnded});
            setLoan(env, broker, tesSUCCESS);
        });

        // 4. Rejected during Investment when the loan's final payment would land on or after
        // RedemptionDate. Use a tight redemptionOffset and a schedule whose final payment is well
        // past that boundary.
        withEnv([&](Env& env, PrettyAsset const& asset) {
            constexpr std::uint32_t kRedemptionOffset = 3u * 24u * 3600u;
            auto const broker = createVaultAndBroker(
                env,
                asset,
                lender,
                BrokerParameters{
                    .vaultKind = VaultKind::ClosedEnded, .redemptionOffset = kRedemptionOffset});
            env(set(lender, broker.brokerID, broker.asset(100).value()),
                kCounterparty(borrower),
                Sig(sfCounterpartySignature, borrower),
                Fee(env.current()->fees().base * 5),
                kPaymentTotal(10u),
                kPaymentInterval(kInterval),
                Ter(tecNO_PERMISSION));
            env.close();
        });

        // 5. Boundary: schedule whose finalPayment lands exactly (RedemptionDate - 1) is accepted,
        // and one second later (== RedemptionDate) is rejected. Uses payTotal = 1 so the arithmetic
        // is simple: finalPayment = startDate + interval.
        withEnv([&](Env& env, PrettyAsset const& asset) {
            auto const broker = createVaultAndBroker(
                env, asset, lender, BrokerParameters{.vaultKind = VaultKind::ClosedEnded});
            BEAST_EXPECT(broker.redemptionDate.has_value());

            auto const startDate = env.now().time_since_epoch().count();
            auto const acceptInterval = *broker.redemptionDate - 1 - startDate;
            env(set(lender, broker.brokerID, broker.asset(100).value()),
                kCounterparty(borrower),
                Sig(sfCounterpartySignature, borrower),
                Fee(env.current()->fees().base * 5),
                kPaymentTotal(1u),
                kPaymentInterval(acceptInterval),
                Ter(tesSUCCESS));
            env.close();

            auto const rejectInterval =
                *broker.redemptionDate - env.now().time_since_epoch().count();
            env(set(lender, broker.brokerID, broker.asset(100).value()),
                kCounterparty(borrower),
                Sig(sfCounterpartySignature, borrower),
                Fee(env.current()->fees().base * 5),
                kPaymentTotal(1u),
                kPaymentInterval(rejectInterval),
                Ter(tecNO_PERMISSION));
            env.close();
        });
    }

public:
    void
    run() override
    {
        for (auto const& features : jtx::amendmentCombinations(
                 {fixCleanup3_1_3, fixCleanup3_2_0, featureMPTokensV2}, all_))
            testLoanSet(features);
        for (auto const& features : jtx::amendmentCombinations(
                 {fixCleanup3_1_3, fixCleanup3_2_0, featureMPTokensV2, featureLendingProtocolV1_1},
                 all_))
            testTwoStep(features);

        testLoanSetClosedEnded();
    }
};

BEAST_DEFINE_TESTSUITE(LoanSet, tx, xrpl);

}  // namespace xrpl::test
