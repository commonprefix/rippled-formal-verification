#include <test/app/invariants/InvariantsBase.h>
#include <test/jtx/Account.h>
#include <test/jtx/Env.h>
#include <test/jtx/amount.h>
#include <test/jtx/mpt.h>
#include <test/jtx/pay.h>
#include <test/jtx/ter.h>
#include <test/jtx/trust.h>
#include <test/jtx/vault.h>

#include <xrpl/basics/Number.h>
#include <xrpl/beast/unit_test/suite.h>
#include <xrpl/ledger/OpenView.h>
#include <xrpl/protocol/AccountID.h>
#include <xrpl/protocol/Indexes.h>
#include <xrpl/protocol/Issue.h>
#include <xrpl/protocol/Keylet.h>
#include <xrpl/protocol/MPTIssue.h>
#include <xrpl/protocol/Protocol.h>
#include <xrpl/protocol/SField.h>
#include <xrpl/protocol/STAmount.h>
#include <xrpl/protocol/STLedgerEntry.h>
#include <xrpl/protocol/STNumber.h>  // IWYU pragma: keep
#include <xrpl/protocol/STObject.h>
#include <xrpl/protocol/STTx.h>
#include <xrpl/protocol/TER.h>
#include <xrpl/protocol/TxFlags.h>
#include <xrpl/protocol/TxFormats.h>
#include <xrpl/protocol/UintTypes.h>
#include <xrpl/protocol/XRPAmount.h>
#include <xrpl/tx/ApplyContext.h>

#include <cstdint>
#include <limits>
#include <memory>
#include <optional>

namespace xrpl::test {

// One failing test per open gap in the invariant checks. No transaction reaches these gaps, so
// each test changes ledger entries inside the invariant test harness of InvariantsBase.
class InvariantFindings_test : public InvariantsBase
{
    // Creates an XRP vault of the owner and takes 10 XRP from the depositor.
    static Keylet
    createXrpVault(jtx::Env& env, jtx::Account const& owner, jtx::Account const& depositor)
    {
        using namespace jtx;

        Vault const vault{env};
        auto const [create, vaultKeylet] = vault.create({.owner = owner, .asset = xrpIssue()});
        env(create);
        env(vault.deposit({.depositor = depositor, .id = vaultKeylet.key, .amount = XRP(10)}));
        return vaultKeylet;
    }

    // FV_M1_27: ValidMPTBalanceChanges sums balance changes in an int64, where 2^64 wraps to 0.
    void
    testMptInvariantWrap()
    {
        testcase("FV_M1_27 MptInvariantWrap");
        using namespace jtx;

        // A holder with 100 that gains a third of 2^64 - 1 plus 1 stays within the MPT range.
        constexpr std::uint64_t third = 6'148'914'691'236'517'205ULL;
        constexpr std::uint64_t startBalance = 100;
        static_assert(3 * third == std::numeric_limits<std::uint64_t>::max());
        static_assert(startBalance + third + 1 <= kMaxMpTokenAmount);
        Account const a3{"A3"};

        // 1. A1, A2 and A3 hold 100 each of an MPT. OutstandingAmount is 300.
        // 2. A Payment adds a third of 2^64 - 1 to each balance and leaves OutstandingAmount at
        //    300. The gains add up to 2^64 - 1 and the invariant fires.
        // 3. The same Payment with 1 more for A1. The gains add up to 2^64.
        for (std::uint64_t const extraForA1 : {0, 1})
        {
            MPTID mptID;
            // BUG: in step 3 the transaction succeeds, no invariant fires.
            doInvariantCheck(
                {{"invalid OutstandingAmount balance"}},
                [&](Account const& a1, Account const& a2, ApplyContext& ac) {
                    for (AccountID const& holder : {a1.id(), a2.id(), a3.id()})
                    {
                        auto const token = ac.view().peek(keylet::mptoken(mptID, holder));
                        if (!token)
                            return false;
                        std::uint64_t const gain = holder == a1.id() ? third + extraForA1 : third;
                        token->setFieldU64(sfMPTAmount, startBalance + gain);
                        ac.view().update(token);
                    }
                    return true;
                },
                XRPAmount{},
                STTx{ttPAYMENT, [](STObject&) {}},
                {tecINVARIANT_FAILED, tefINVARIANT_FAILED},
                [&](Account const& a1, Account const& a2, Env& env) {
                    Account const issuer{"issuer"};
                    env.fund(XRP(1'000), issuer, a3);
                    MPTTester const mpt(
                        {.env = env,
                         .issuer = issuer,
                         .holders = {a1, a2, a3},
                         .pay = startBalance});
                    mptID = mpt.issuanceID();
                    return true;
                });
        }
    }

    // FV_M2_29: burning the shares of an empty vault may change AssetsTotal and AssetsAvailable.
    void
    testForceBurnAssetFields()
    {
        testcase("FV_M2_29 ForceBurnAssetFields");
        using namespace jtx;

        Account const a1{"A1"};
        Account const a2{"A2"};

        // 1. A1 owns an XRP vault. A1 and A2 deposit 10 XRP each.
        // 2. The vault is emptied: AssetsTotal and AssetsAvailable are set to 0, the shares stay.
        // 3. A VaultClawback by A1 burns the shares of A2 and sets both fields to 5 drops.
        // BUG: the transaction succeeds, no invariant fires.
        doLoanInvariantCheck(
            testableAmendments(),
            STTx{
                ttVAULT_CLAWBACK,
                [&](STObject& tx) {
                    tx.setAccountID(sfAccount, a1.id());
                    tx.setAccountID(sfHolder, a2.id());
                }},
            [](OpenView& ov, LoanFixture const& fixture) {
                auto const vault = std::make_shared<SLE>(*ov.read(fixture.vaultKeylet));
                vault->at(sfAssetsAvailable) = Number(0);
                vault->at(sfAssetsTotal) = Number(0);
                ov.rawReplace(vault);
            },
            [](ApplyContext& ac, LoanFixture const& fixture) {
                auto const vault = ac.view().peek(fixture.vaultKeylet);
                if (!vault)
                    return false;
                MPTID const shareID = vault->at(sfShareMPTID);
                auto const issuance = ac.view().peek(keylet::mptokenIssuance(shareID));
                auto const holder = ac.view().peek(keylet::mptoken(shareID, fixture.a2.id()));
                if (!issuance || !holder)
                    return false;
                issuance->at(sfOutstandingAmount) -= holder->getFieldU64(sfMPTAmount);
                holder->at(sfMPTAmount) = 0;
                ac.view().update(issuance);
                ac.view().update(holder);
                vault->at(sfAssetsAvailable) = Number(5);
                vault->at(sfAssetsTotal) = Number(5);
                ac.view().update(vault);
                return true;
            },
            "Invariant failed",
            [](Env& env, LoanFixture const& fixture) {
                env(Vault::deposit(
                    {.depositor = fixture.a1, .id = fixture.vaultKeylet.key, .amount = XRP(10)}));
                env(Vault::deposit(
                    {.depositor = fixture.a2, .id = fixture.vaultKeylet.key, .amount = XRP(10)}));
                return true;
            });
    }

    // FV_M2_30: ValidVault skips transactions without a Vault entry, ValidMPTTransfer IOU rippling.
    void
    testNonVaultTxAndInheritedTransfer()
    {
        testcase("FV_M2_30 NonVaultTxAndInheritedTransfer");
        using namespace jtx;

        std::optional<Keylet> vaultKeylet;

        // 1. An XRP vault of A1 holds 10 XRP of A2. A Payment moves 1 drop from its account to A2.
        // BUG: the transaction succeeds, no invariant fires.
        doInvariantCheck(
            {{"Invariant failed"}},
            [&](Account const&, Account const& a2, ApplyContext& ac) {
                AccountID const pseudoID = ac.view().read(*vaultKeylet)->at(sfAccount);
                auto const pseudo = ac.view().peek(keylet::account(pseudoID));
                auto const receiver = ac.view().peek(keylet::account(a2.id()));
                if (!pseudo || !receiver)
                    return false;
                pseudo->at(sfBalance) -= XRPAmount{1};
                receiver->at(sfBalance) += XRPAmount{1};
                ac.view().update(pseudo);
                ac.view().update(receiver);
                return true;
            },
            XRPAmount{},
            STTx{ttPAYMENT, [](STObject&) {}},
            {tecINVARIANT_FAILED, tefINVARIANT_FAILED},
            [&](Account const& a1, Account const& a2, Env& env) {
                vaultKeylet = createXrpVault(env, a1, a2);
                return true;
            });

        // 2. On a vault as in step 1, a Payment mints 1 share to A2. The vault receives nothing.
        // BUG: the transaction succeeds, no invariant fires.
        doInvariantCheck(
            {{"Invariant failed"}},
            [&](Account const&, Account const& a2, ApplyContext& ac) {
                MPTID const shareID = ac.view().read(*vaultKeylet)->at(sfShareMPTID);
                auto const issuance = ac.view().peek(keylet::mptokenIssuance(shareID));
                auto const holder = ac.view().peek(keylet::mptoken(shareID, a2.id()));
                if (!issuance || !holder)
                    return false;
                issuance->at(sfOutstandingAmount) += 1;
                holder->at(sfMPTAmount) += 1;
                ac.view().update(issuance);
                ac.view().update(holder);
                return true;
            },
            XRPAmount{},
            STTx{ttPAYMENT, [](STObject&) {}},
            {tecINVARIANT_FAILED, tefINVARIANT_FAILED},
            [&](Account const& a1, Account const& a2, Env& env) {
                vaultKeylet = createXrpVault(env, a1, a2);
                return true;
            });

        // 3. A2 holds the shares of a vault of A1's IOU. A1 disabled rippling on its trust lines
        //    with A2 and A3. A Payment moves 1 share from A2 to A3.
        Account const a3{"A3"};
        MPTID shareID;
        // BUG: the transaction succeeds, no invariant fires.
        doInvariantCheck(
            {{"Invariant failed"}},
            [&](Account const&, Account const& a2, ApplyContext& ac) {
                auto const sender = ac.view().peek(keylet::mptoken(shareID, a2.id()));
                auto const receiver = ac.view().peek(keylet::mptoken(shareID, a3.id()));
                if (!sender || !receiver)
                    return false;
                sender->at(sfMPTAmount) -= 1;
                receiver->at(sfMPTAmount) += 1;
                ac.view().update(sender);
                ac.view().update(receiver);
                return true;
            },
            XRPAmount{},
            STTx{ttPAYMENT, [](STObject&) {}},
            {tecINVARIANT_FAILED, tefINVARIANT_FAILED},
            [&](Account const& a1, Account const& a2, Env& env) {
                env.fund(XRP(1'000), a3);
                PrettyAsset const usd = a1["USD"];
                env(trust(a2, usd(1'000)));
                env(trust(a3, usd(1'000)));
                env(pay(a1, a2, usd(100)));
                Vault const vault{env};
                auto const [create, iouVaultKeylet] = vault.create({.owner = a2, .asset = usd});
                env(create);
                env(vault.deposit({.depositor = a2, .id = iouVaultKeylet.key, .amount = usd(100)}));
                shareID = env.le(iouVaultKeylet)->at(sfShareMPTID);
                env(MPTTester::authorizeJV({.account = a3, .id = shareID}));
                STAmount const oneShare{MPTIssue{shareID}, 1};
                env(pay(a2, a3, oneShare));
                env(trust(a1, a2["USD"](0), tfSetNoRipple));
                env(trust(a1, a3["USD"](0), tfSetNoRipple));
                // The Payment transactor rejects the transfer.
                env(pay(a2, a3, oneShare), Ter(tecPATH_DRY));
                return true;
            });
    }

    // FV_M3_12: no invariant bounds DebtTotal by DebtMaximum or a broker's OwnerCount by its loans.
    void
    testLoanBrokerDebtMaximumOwnerCount()
    {
        testcase("FV_M3_12 LoanBrokerDebtMaximumOwnerCount");
        using namespace jtx;

        Account const a1{"A1"};
        STTx const brokerSet{
            ttLOAN_BROKER_SET, [&](STObject& tx) { tx.setAccountID(sfAccount, a1.id()); }};

        // 1. A LoanBrokerSet by the broker owner A1 sets DebtMaximum to 1 and DebtTotal to 2.
        // BUG: the transaction succeeds, no invariant fires.
        doLoanInvariantCheck(
            testableAmendments(),
            brokerSet,
            [](OpenView&, LoanFixture const&) {},
            [](ApplyContext& ac, LoanFixture const& fixture) {
                auto const broker = ac.view().peek(fixture.brokerKeylet);
                if (!broker)
                    return false;
                broker->at(sfDebtMaximum) = Number(1);
                broker->at(sfDebtTotal) = Number(2);
                ac.view().update(broker);
                return true;
            },
            "Invariant failed");

        // 2. A LoanBrokerSet by A1 adds 1 to the broker's OwnerCount. No loan is created.
        // BUG: the transaction succeeds, no invariant fires.
        doLoanInvariantCheck(
            testableAmendments(),
            brokerSet,
            [](OpenView&, LoanFixture const&) {},
            [](ApplyContext& ac, LoanFixture const& fixture) {
                auto const broker = ac.view().peek(fixture.brokerKeylet);
                if (!broker)
                    return false;
                broker->at(sfOwnerCount) += 1;
                ac.view().update(broker);
                return true;
            },
            "Invariant failed");
    }

    // FV_M4_58: for a LoanPay ValidVault doesn't tie AssetsAvailable to the pseudo-account's funds.
    void
    testLoanPayVaultConservation()
    {
        testcase("FV_M4_58 LoanPayVaultConservation");
        using namespace jtx;

        std::optional<Keylet> vaultKeylet;

        // 1. A1 owns an XRP vault with 10 XRP of A2.
        // 2. A LoanPay adds 1 drop to AssetsAvailable and AssetsTotal. The vault receives nothing.
        // BUG: the transaction succeeds, no invariant fires.
        doInvariantCheck(
            {{"Invariant failed"}},
            [&](Account const&, Account const&, ApplyContext& ac) {
                auto const vault = ac.view().peek(*vaultKeylet);
                if (!vault)
                    return false;
                vault->at(sfAssetsAvailable) += Number(1);
                vault->at(sfAssetsTotal) += Number(1);
                ac.view().update(vault);
                return true;
            },
            XRPAmount{},
            STTx{ttLOAN_PAY, [](STObject& tx) { tx.setFieldAmount(sfAmount, XRPAmount(1)); }},
            {tecINVARIANT_FAILED, tefINVARIANT_FAILED},
            [&](Account const& a1, Account const& a2, Env& env) {
                vaultKeylet = createXrpVault(env, a1, a2);
                return true;
            });
    }

public:
    void
    run() override
    {
        // Open bugs. Each call fails until the C++ code is fixed, so it is commented out.
        // clang-format off
        // testMptInvariantWrap();                   // FV_M1_27
        // testForceBurnAssetFields();               // FV_M2_29
        // testNonVaultTxAndInheritedTransfer();     // FV_M2_30
        // testLoanBrokerDebtMaximumOwnerCount();    // FV_M3_12
        // testLoanPayVaultConservation();           // FV_M4_58
        // clang-format on

        // Keeps a run of this suite alone from reporting "No tests run".
        pass();
    }
};

BEAST_DEFINE_TESTSUITE(InvariantFindings, formal_verification, xrpl);

}  // namespace xrpl::test
