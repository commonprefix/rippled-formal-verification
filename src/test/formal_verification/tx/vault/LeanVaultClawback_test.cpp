#include <test/formal_verification/common/LeanSuite.h>
#include <test/formal_verification/ffi/vault/VaultClawbackFFI.h>
#include <test/formal_verification/ffi/vault/VaultFFI.h>
#include <test/formal_verification/tx/vault/VaultTestHelpers.h>
#include <test/jtx/Account.h>
#include <test/jtx/Env.h>
#include <test/jtx/amount.h>
#include <test/jtx/flags.h>
#include <test/jtx/mpt.h>
#include <test/jtx/pay.h>
#include <test/jtx/ter.h>
#include <test/jtx/trust.h>

#include <xrpl/basics/Number.h>
#include <xrpl/beast/utility/Journal.h>
#include <xrpl/protocol/Indexes.h>
#include <xrpl/protocol/MPTIssue.h>
#include <xrpl/protocol/SField.h>
#include <xrpl/protocol/STNumber.h>
#include <xrpl/protocol/TER.h>

#include <cstdint>
#include <optional>
#include <string>

namespace xrpl::test::formal_verification {

class LeanVaultClawback_test : public LeanSuite
{
    static MPTIssue
    shareIssue(jtx::Env& env, Keylet const& vaultKeylet)
    {
        return MPTIssue{env.le(vaultKeylet)->at(sfShareMPTID)};
    }

    void
    compareClawbackAsset(
        jtx::Env& env,
        Keylet const& vaultKeylet,
        jtx::Account const& issuer,
        jtx::Account const& holder,
        Asset const& asset,
        STAmount const& amount,
        TER expected)
    {
        using namespace jtx;
        Vault const state = readVaultState(env, vaultKeylet, asset);
        STAmount const holderShares = fetchHolderShares(env, vaultKeylet, holder);
        bool const waiveUnrealizedLoss = holderOwnsAllShares(env, vaultKeylet, holder);
        LeanVaultResult const clawback =
            leanVaultClawback(state, amount, holderShares, waiveUnrealizedLoss);
        expectLawful(clawback);

        env(jtx::Vault::clawback(
                {.issuer = issuer, .id = vaultKeylet.key, .holder = holder, .amount = amount}),
            jtx::Ter(std::ignore));
        TER const cppTer = env.ter();
        // Read before closing: a close discards state staged on the open ledger.
        Vault const cpp = readVaultState(env, vaultKeylet, asset);
        env.close();

        BEAST_EXPECTS(
            cppTer == expected,
            std::string("cpp=") + transToken(cppTer) + " expected " + transToken(expected));
        BEAST_EXPECTS(!clawback.leanError.has_value(), "lean clawback error");

        TER const leanTer = clawback.error.value_or(tesSUCCESS);
        BEAST_EXPECTS(
            leanTer == expected,
            std::string("lean=") + transToken(leanTer) + " expected " + transToken(expected));

        if (cppTer != tesSUCCESS)
            return;

        Number const& cppAssetsTotal = cpp.assetsTotal;
        Number const& cppAssetsAvailable = cpp.assetsAvailable;
        Number const& cppSharesTotal = cpp.sharesTotal;
        BEAST_EXPECTS(
            clawback.vault.assetsTotal == cppAssetsTotal,
            "assetsTotal lean=" + to_string(clawback.vault.assetsTotal) +
                " cpp=" + to_string(cppAssetsTotal));
        BEAST_EXPECTS(
            clawback.vault.assetsAvailable == cppAssetsAvailable,
            "assetsAvailable lean=" + to_string(clawback.vault.assetsAvailable) +
                " cpp=" + to_string(cppAssetsAvailable));
        BEAST_EXPECTS(
            clawback.vault.sharesTotal == cppSharesTotal,
            "sharesTotal lean=" + to_string(clawback.vault.sharesTotal) +
                " cpp=" + to_string(cppSharesTotal));
        Number const& cppLossUnrealized = cpp.lossUnrealized;
        BEAST_EXPECTS(
            clawback.vault.lossUnrealized == cppLossUnrealized,
            "lossUnrealized lean=" + to_string(clawback.vault.lossUnrealized) +
                " cpp=" + to_string(cppLossUnrealized));
    }

    void
    testClawbackAsset(std::int64_t seed, std::int64_t amount, TER expected)
    {
        using namespace jtx;
        testcase("clawback MPT asset " + std::to_string(amount) + " from " + std::to_string(seed));

        Env env(*this);
        Account const owner{"owner"};
        Account const issuer{"issuer"};
        Account const holder{"holder"};
        env.fund(XRP(1'000'000), owner, issuer, holder);
        env.close();

        MPTTester mptt{env, issuer, kMptInitNoFund};
        mptt.create({.flags = tfMPTCanTransfer | tfMPTCanClawback});
        PrettyAsset const asset = mptt.issuanceID();
        mptt.authorize({.account = holder});
        env.close();
        env(pay(issuer, holder, asset(seed)));
        env.close();

        auto const vaultKeylet = createVault(env, owner, asset.raw());
        env(jtx::Vault::deposit(
                {.depositor = holder, .id = vaultKeylet.key, .amount = asset(seed)}),
            jtx::Ter(tesSUCCESS));
        env.close();

        compareClawbackAsset(
            env, vaultKeylet, issuer, holder, asset.raw(), asset(amount), expected);
    }

    // MPT vault where the owner donates assets without shares, drifting NAV off 1:1 so the
    // clawback conversions round. The issuer then claws `clawAmount` from the holder.
    void
    testClawbackDrifted(
        std::int64_t deposit,
        std::int64_t donation,
        std::int64_t clawAmount,
        TER expected)
    {
        using namespace jtx;
        testcase(
            "clawback drifted MPT claw " + std::to_string(clawAmount) + " (deposit=" +
            std::to_string(deposit) + ", donation=" + std::to_string(donation) + ")");

        Env env(*this);
        Account const owner{"owner"};
        Account const issuer{"issuer"};
        Account const holder{"holder"};
        env.fund(XRP(1'000'000), owner, issuer, holder);
        env.close();

        MPTTester mptt{env, issuer, kMptInitNoFund};
        mptt.create({.flags = tfMPTCanTransfer | tfMPTCanClawback});
        PrettyAsset const asset = mptt.issuanceID();
        mptt.authorize({.account = holder});
        mptt.authorize({.account = owner});
        env.close();
        env(pay(issuer, holder, asset(deposit)));
        env(pay(issuer, owner, asset(donation)));
        env.close();

        auto const vaultKeylet = createVault(env, owner, asset.raw());
        env(jtx::Vault::deposit(
                {.depositor = holder, .id = vaultKeylet.key, .amount = asset(deposit)}),
            jtx::Ter(tesSUCCESS));
        env.close();
        env(jtx::Vault::deposit(
                {.depositor = owner,
                 .id = vaultKeylet.key,
                 .amount = asset(donation),
                 .flags = tfVaultDonate}),
            jtx::Ter(tesSUCCESS));
        env.close();

        compareClawbackAsset(
            env, vaultKeylet, issuer, holder, asset.raw(), asset(clawAmount), expected);
    }

    // Force an extreme vault state a real clawback cannot reach, then clawback the asset.
    void
    testUpdatedStateClawback(
        Number const& assetsTotal,
        Number const& assetsAvailable,
        std::uint64_t sharesTotal,
        std::int64_t clawAmount,
        TER expected)
    {
        using namespace jtx;
        testcase(
            "clawback updated-state amount=" + std::to_string(clawAmount) + " (assetsTotal=" +
            to_string(assetsTotal) + ", assetsAvailable=" + to_string(assetsAvailable) +
            ", sharesTotal=" + std::to_string(sharesTotal) + ")");

        Env env(*this);
        Account const owner{"owner"};
        Account const issuer{"issuer"};
        Account const holder{"holder"};
        env.fund(XRP(1'000'000), owner, issuer, holder);
        env.close();

        MPTTester mptt{env, issuer, kMptInitNoFund};
        mptt.create({.flags = tfMPTCanTransfer | tfMPTCanClawback});
        PrettyAsset const asset = mptt.issuanceID();
        mptt.authorize({.account = holder});
        env.close();
        env(pay(issuer, holder, asset(1'000)));
        env.close();

        auto const vaultKeylet = createVault(env, owner, asset.raw());
        env(jtx::Vault::deposit(
                {.depositor = holder, .id = vaultKeylet.key, .amount = asset(1'000)}),
            jtx::Ter(tesSUCCESS));
        env.close();

        BEAST_EXPECT(updateVaultState(env, vaultKeylet, assetsTotal, assetsAvailable, sharesTotal));
        compareClawbackAsset(
            env, vaultKeylet, issuer, holder, asset.raw(), asset(clawAmount), expected);
    }

    // canBurnShares preclaim
    void
    compareCanBurnShares(
        jtx::Env& env,
        Keylet const& vaultKeylet,
        jtx::Account const& owner,
        jtx::Account const& holder,
        Asset const& asset,
        TER expected,
        std::optional<std::int64_t> shareAmount = std::nullopt)
    {
        using namespace jtx;
        Vault const state = readVaultState(env, vaultKeylet, asset);
        STAmount const amount{shareIssue(env, vaultKeylet), shareAmount.value_or(0)};
        LeanAmountResult const lean =
            leanCanBurnShares(state, amount, fetchHolderShares(env, vaultKeylet, holder));
        expectLawful(lean);
        BEAST_EXPECTS(!lean.leanError.has_value(), "lean canBurnShares error");

        jtx::Vault::ClawbackArgs args{.issuer = owner, .id = vaultKeylet.key, .holder = holder};
        if (shareAmount)
            args.amount = amount;
        env(jtx::Vault::clawback(args), jtx::Ter(std::ignore));
        TER const cppTer = env.ter();
        env.close();

        std::optional<TER> const expectedError =
            expected == tesSUCCESS ? std::nullopt : std::optional<TER>{expected};
        if (shareAmount)
            BEAST_EXPECTS(
                cppTer == expected,
                std::string("cpp=") + transToken(cppTer) + " expected " + transToken(expected));
        else
            BEAST_EXPECTS(
                (cppTer == tecNO_PERMISSION) == expectedError.has_value(),
                std::string("cpp=") + transToken(cppTer) + " expected " + transToken(expected));
        BEAST_EXPECTS(
            lean.error == expectedError,
            std::string("error lean=") + (lean.error ? transToken(*lean.error) : "none") +
                " expected " + (expectedError ? transToken(*expectedError) : "none"));
    }

    // An owner burn with an explicit share amount must name the holder's whole balance.
    void
    testBurnSharesPartialAmount()
    {
        using namespace jtx;
        testcase("canBurnShares with a partial share amount");

        Env env(*this);
        Account const owner{"owner"};
        Account const issuer{"issuer"};
        Account const holder{"holder"};
        env.fund(XRP(1'000'000), owner, issuer, holder);
        env.close();

        PrettyAsset const asset = issuer["USD"];
        env(trust(holder, asset(1'000'000)));
        env.close();
        env(pay(issuer, holder, asset(1'000)));
        env.close();
        auto const vaultKeylet = createVault(env, owner, asset.raw());
        env(jtx::Vault::deposit(
                {.depositor = holder, .id = vaultKeylet.key, .amount = asset(1'000)}),
            jtx::Ter(tesSUCCESS));
        env.close();
        // Insolvent: no assets, shares outstanding.
        std::uint64_t const outstanding =
            env.le(keylet::mptokenIssuance(env.le(vaultKeylet)->at(sfShareMPTID)))
                ->at(sfOutstandingAmount);
        BEAST_EXPECT(updateVaultState(env, vaultKeylet, Number{0}, Number{0}, outstanding));
        compareCanBurnShares(env, vaultKeylet, owner, holder, asset.raw(), tecLIMIT_EXCEEDED, 5);
    }

    void
    testCanBurnShares(
        Number const& assetsTotal,
        Number const& assetsAvailable,
        std::uint64_t sharesTotal,
        TER expected)
    {
        using namespace jtx;
        testcase(
            "canBurnShares total=" + to_string(assetsTotal) +
            " avail=" + to_string(assetsAvailable) + " shares=" + std::to_string(sharesTotal));

        Env env(*this);
        Account const owner{"owner"};
        Account const issuer{"issuer"};
        Account const holder{"holder"};
        env.fund(XRP(1'000'000), owner, issuer, holder);
        env.close();

        PrettyAsset const asset = issuer["USD"];
        auto const vaultKeylet = createVault(env, owner, asset.raw());
        BEAST_EXPECT(updateVaultState(env, vaultKeylet, assetsTotal, assetsAvailable, sharesTotal));
        compareCanBurnShares(env, vaultKeylet, owner, holder, asset.raw(), expected);
    }

    // Vault.burnShares models the owner burning a holder's shares
    void
    testBurnShares(std::int64_t deposit, std::uint64_t stagedOutstanding)
    {
        using namespace jtx;
        testcase(
            "burnShares held=" + std::to_string(deposit) +
            " outstanding=" + std::to_string(stagedOutstanding));

        Env env(*this);
        Account const owner{"owner"};
        Account const issuer{"issuer"};
        Account const holder{"holder"};
        env.fund(XRP(1'000'000), owner, issuer, holder);
        env.close();

        MPTTester mptt{env, issuer, kMptInitNoFund};
        mptt.create({.flags = tfMPTCanTransfer});
        PrettyAsset const asset = mptt.issuanceID();
        mptt.authorize({.account = holder});
        env.close();
        env(pay(issuer, holder, asset(deposit)));
        env.close();

        auto const vaultKeylet = createVault(env, owner, asset.raw());
        env(jtx::Vault::deposit(
                {.depositor = holder, .id = vaultKeylet.key, .amount = asset(deposit)}),
            jtx::Ter(tesSUCCESS));
        env.close();
        // Empty the vault of assets (staged) so the owner may burn the remaining shares.
        BEAST_EXPECT(updateVaultState(env, vaultKeylet, Number{0}, Number{0}, stagedOutstanding));

        // The holder's actual share balance is what C++ burns and what the model is given.
        auto const shareMptId = env.le(vaultKeylet)->at(sfShareMPTID);
        auto const holderToken = env.le(keylet::mptoken(shareMptId, holder));
        if (!BEAST_EXPECTS(holderToken, "holder has no vault shares"))
            return;
        std::int64_t const held = static_cast<std::int64_t>(holderToken->at(sfMPTAmount));
        Vault const state = readVaultState(env, vaultKeylet, asset.raw());
        LeanBurnResult const burn =
            leanBurnShares(state, STAmount{shareIssue(env, vaultKeylet), held});
        expectLawful(burn);

        env(jtx::Vault::clawback({.issuer = owner, .id = vaultKeylet.key, .holder = holder}),
            jtx::Ter(std::ignore));
        TER const cppTer = env.ter();
        auto const newVaultSle = env.le(vaultKeylet);
        Number const cppAssetsTotal = getAssetsTotal(newVaultSle);
        Number const cppAssetsAvailable = newVaultSle->at(sfAssetsAvailable);
        Number const cppSharesTotal{static_cast<std::int64_t>(
            env.le(keylet::mptokenIssuance(shareMptId))->at(sfOutstandingAmount))};
        env.close();

        BEAST_EXPECTS(cppTer == tesSUCCESS, std::string("cpp=") + transToken(cppTer));
        BEAST_EXPECTS(!burn.leanError.has_value(), "lean burnShares error");
        BEAST_EXPECTS(
            burn.vault.sharesTotal == cppSharesTotal,
            "sharesTotal lean=" + to_string(burn.vault.sharesTotal) +
                " cpp=" + to_string(cppSharesTotal));
        BEAST_EXPECT(burn.vault.assetsTotal == cppAssetsTotal);
        BEAST_EXPECT(burn.vault.assetsAvailable == cppAssetsAvailable);
    }

    // FV_M2_3 (regression): on a 5:3 NAV-drifted vault, clawing 2 assets burns 1 share worth
    // 1.667. C++ used to recover round(1.667) = 2; both sides now recover 1 (the payout rounds
    // down).
    void
    testClawbackOvervaluedShares()
    {
        testClawbackDrifted(3, 2, 2, tesSUCCESS);
    }

    // FV_M2_12 (regression): a clawback too small to debit assetsTotal (the debit rounds back to
    // the old value) used to burn shares for nothing; both sides now reject it with
    // tecPRECISION_LOSS. A ~1e10 total is past the open limit (9e9 at scale 6), so it is staged.
    void
    testClawbackPrecisionLossStaged(Number const& assetsTotal)
    {
        using namespace jtx;
        testcase("STAGED clawback 1e-6 from total " + to_string(assetsTotal));

        Env env(*this);
        Account const owner{"owner"};
        Account const issuer{"issuer"};
        Account const holder{"holder"};
        env.fund(XRP(1'000'000), owner, issuer, holder);
        env.close();
        env(fset(issuer, asfAllowTrustLineClawback));
        env.close();

        PrettyAsset const asset = issuer["USD"];
        env(trust(holder, asset(20'000'000'000)));
        env.close();
        env(pay(issuer, holder, asset(11'000'000'000)));
        env.close();

        auto const vaultKeylet = createVault(env, owner, asset.raw());
        // A deposit stops at the 9e9 open limit, so seed small and stage the ~1e10 total.
        env(jtx::Vault::deposit(
                {.depositor = holder, .id = vaultKeylet.key, .amount = asset(Number{1'000})}),
            jtx::Ter(tesSUCCESS));
        env.close();

        BEAST_EXPECT(updateVaultState(
            env, vaultKeylet, assetsTotal, assetsTotal, 10'000'000'000'000'009ULL));
        compareClawbackAsset(
            env, vaultKeylet, issuer, holder, asset.raw(), asset(Number{1, -6}), tecPRECISION_LOSS);
    }

    // Finding (FV_M2_12, regression): a clawback too small to change the stored assetsTotal
    // used to burn a share (c++ -> tecINVARIANT_FAILED). Both sides now return tecPRECISION_LOSS.
    void
    testClawbackDustDebit(Number const& assetsTotal, std::uint64_t sharesTotal)
    {
        using namespace jtx;
        testcase("clawback one dust share (total " + to_string(assetsTotal) + ")");

        Env env(*this);
        Account const owner{"owner"};
        Account const issuer{"issuer"};
        Account const holder{"holder"};
        env.fund(XRP(1'000'000), owner, issuer, holder);
        env.close();
        env(fset(issuer, asfAllowTrustLineClawback));
        env.close();

        PrettyAsset const asset = issuer["USD"];
        env(trust(holder, asset(Number{1, 15})));
        env.close();
        env(pay(issuer, holder, asset(Number{1, 12})));
        env.close();

        auto const vaultKeylet = createVault(env, owner, asset.raw());
        env(jtx::Vault::deposit(
                {.depositor = holder, .id = vaultKeylet.key, .amount = asset(Number{1, 6})}),
            jtx::Ter(tesSUCCESS));
        env.close();

        // Stage so one share is worth less than the assetsTotal precision step
        BEAST_EXPECT(updateVaultState(env, vaultKeylet, assetsTotal, assetsTotal, sharesTotal));
        compareClawbackAsset(
            env, vaultKeylet, issuer, holder, asset.raw(), asset(Number{2, -6}), tecPRECISION_LOSS);
    }

    // Finding (FV_M2_17/18, c++): a final clawback (amount 0) leaves a nonzero sfAssetsTotal with 0
    // shares (tecINVARIANT_FAILED) because VaultClawback lacks VaultWithdraw's final-share rule.
    void
    testClawbackAllLeavesAssets(
        Number const& assetsTotal,
        Number const& lossUnrealized,
        std::uint64_t sharesTotal,
        TER expected)
    {
        using namespace jtx;
        testcase("clawback all leaves assets (total " + to_string(assetsTotal) + ")");

        Env env(*this);
        Account const owner{"owner"};
        Account const issuer{"issuer"};
        Account const holder{"holder"};
        env.fund(XRP(1'000'000), owner, issuer, holder);
        env.close();
        env(fset(issuer, asfAllowTrustLineClawback));
        env.close();

        PrettyAsset const asset = issuer["USD"];
        env(trust(holder, asset(Number{2, 6})));
        env.close();
        env(pay(issuer, holder, asset(Number{1, 6})));
        env.close();

        auto const vaultKeylet = createVault(env, owner, asset.raw());
        env(jtx::Vault::deposit(
                {.depositor = holder, .id = vaultKeylet.key, .amount = asset(Number{1, 6})}),
            jtx::Ter(tesSUCCESS));
        env.close();

        BEAST_EXPECT(stageSoleHolderVault(
            env, vaultKeylet, holder, assetsTotal, lossUnrealized, sharesTotal));

        // Amount 0 claws back everything the holder can be paid for.
        env(jtx::Vault::clawback(
                {.issuer = issuer, .id = vaultKeylet.key, .holder = holder, .amount = asset(0)}),
            jtx::Ter(std::ignore));

        BEAST_EXPECTS(
            env.ter() == expected, std::string("clawback returned ") + transToken(env.ter()));

        if (env.ter() != tesSUCCESS)
            return;

        // Read before closing: stageSoleHolderVault edits the open ledger directly and those
        // edits are discarded on close.
        //
        // A sole holder's shares are priced at full value, so the recovery clamps to
        // sfAssetsAvailable and the share count is re-derived from it. What survives is exactly
        // the impaired portion, still backed by shares: no zero-share vault holding assets.
        auto const sleVault = env.le(vaultKeylet);
        Number const afterTotal = sleVault->at(sfAssetsTotal);
        Number const afterAvailable = sleVault->at(sfAssetsAvailable);
        Number const afterLoss = sleVault->at(sfLossUnrealized);
        Number const afterShares{static_cast<std::int64_t>(
            env.le(keylet::mptokenIssuance(sleVault->at(sfShareMPTID)))->at(sfOutstandingAmount))};

        // Everything available was recovered; only the unrealized loss remains.
        BEAST_EXPECTS(afterAvailable == Number{0}, "assetsAvailable " + to_string(afterAvailable));
        BEAST_EXPECTS(afterTotal == lossUnrealized, "assetsTotal " + to_string(afterTotal));
        BEAST_EXPECTS(afterLoss == lossUnrealized, "lossUnrealized " + to_string(afterLoss));

        // Shares survive in proportion to the assets that survive. The bug this covers burned
        // every share while leaving assets behind, so the count must stay above zero.
        Number const expectedShares =
            Number{static_cast<std::int64_t>(sharesTotal)} * lossUnrealized / assetsTotal;
        BEAST_EXPECTS(afterShares > Number{0}, "sharesTotal " + to_string(afterShares));
        BEAST_EXPECTS(
            afterShares == expectedShares,
            "sharesTotal " + to_string(afterShares) + " expected " + to_string(expectedShares));
    }

    // Finding (FV_M2_10, regression vs develop): an issuer VaultClawback with amount 0 should claw
    // the holder's full balance, but this branch does not.
    // C++-only: the model treats amount 0 literally (tecPRECISION_LOSS), so there is no Lean bug.
    void
    testClawbackZeroAmountFullBalance()
    {
        using namespace jtx;
        testcase("issuer clawback with amount 0 claws the full balance");

        Env env(*this);
        Account const owner{"owner"};
        Account const issuer{"issuer"};
        Account const holder{"holder"};
        env.fund(XRP(1'000'000), owner, issuer, holder);
        env.close();

        MPTTester mptt{env, issuer, kMptInitNoFund};
        mptt.create({.flags = tfMPTCanTransfer | tfMPTCanClawback});
        PrettyAsset const asset = mptt.issuanceID();
        mptt.authorize({.account = holder});
        env.close();
        env(pay(issuer, holder, asset(1'000)));
        env.close();

        auto const vaultKeylet = createVault(env, owner, asset.raw());
        env(jtx::Vault::deposit(
                {.depositor = holder, .id = vaultKeylet.key, .amount = asset(1'000)}),
            jtx::Ter(tesSUCCESS));
        env.close();

        // Amount 0 should mean "claw the holder's entire balance"
        env(jtx::Vault::clawback(
                {.issuer = issuer, .id = vaultKeylet.key, .holder = holder, .amount = asset(0)}),
            jtx::Ter(tesSUCCESS));
        env.close();
        auto const shareMptId = env.le(vaultKeylet)->at(sfShareMPTID);
        BEAST_EXPECT(env.le(keylet::mptokenIssuance(shareMptId))->at(sfOutstandingAmount) == 0);
    }

    // FV_M2_11 (regression): an issuer clawback used to recover more than requested because the
    // share count rounded up (on a 7-asset / 5-share vault, clawing 4 burned 3 shares worth 4.2).
    // The share count now truncates on both sides, so the recovery does not exceed the request.
    void
    testClawbackOverRecover()
    {
        using namespace jtx;
        testcase("issuer clawback recovers more than requested");

        Env env(*this);
        Account const owner{"owner"};
        Account const issuer{"issuer"};
        Account const holder{"holder"};
        env.fund(XRP(1'000'000), owner, issuer, holder);
        env.close();
        env(fset(issuer, asfAllowTrustLineClawback));
        env.close();

        PrettyAsset const asset = issuer["USD"];
        env(trust(holder, asset(1'000)));
        env(trust(owner, asset(1'000)));
        env.close();
        env(pay(issuer, holder, asset(5)));
        env(pay(issuer, owner, asset(2)));
        env.close();

        // Scale 0: 1 share == 1 asset. Holder deposits 5 (5 shares), owner donates 2, so the vault
        // holds 7 assets against 5 shares.
        jtx::Vault vault{env};
        auto [createTx, vaultKeylet] = vault.create({.owner = owner, .asset = asset.raw()});
        createTx[sfScale] = 0;
        env(createTx);
        env.close();
        env(jtx::Vault::deposit({.depositor = holder, .id = vaultKeylet.key, .amount = asset(5)}),
            jtx::Ter(tesSUCCESS));
        env.close();
        env(jtx::Vault::deposit(
                {.depositor = owner,
                 .id = vaultKeylet.key,
                 .amount = asset(2),
                 .flags = tfVaultDonate}),
            jtx::Ter(tesSUCCESS));
        env.close();

        // Claw 4: both burn 3 shares (5*4/7 = 2.857 rounds up) and recover 7*3/5 = 4.2 > 4.
        Vault const before = readVaultState(env, vaultKeylet, asset.raw());
        STAmount const request = asset(4);
        STAmount const holderShares = fetchHolderShares(env, vaultKeylet, holder);
        LeanVaultResult const lean = leanVaultClawback(
            before, request, holderShares, holderOwnsAllShares(env, vaultKeylet, holder));
        expectLawful(lean);
        BEAST_EXPECTS(!lean.leanError.has_value(), "lean clawback error");

        env(jtx::Vault::clawback(
                {.issuer = issuer, .id = vaultKeylet.key, .holder = holder, .amount = request}),
            jtx::Ter(tesSUCCESS));
        env.close();
        Vault const after = readVaultState(env, vaultKeylet, asset.raw());

        BEAST_EXPECTS(
            before.assetsTotal - after.assetsTotal <= Number{4},
            "C++ clawback recovered more than requested");
        BEAST_EXPECTS(
            static_cast<Number>(lean.assets) <= Number{4},
            "model clawback recovered more than requested");
    }

    // Finding (FV_M2_8, both sides): clawback pricing rounds in the vault's favor, but the
    // sfAssetsTotal -= update rounds again, dropping the exact difference's low digits from the
    // vault and lowering the share price. Both C++ and the model dilute.
    void
    testClawbackDilution()
    {
        using namespace jtx;
        testcase("clawback lowers the share price (dilution)");

        Env env(*this);
        Account const owner{"owner"};
        Account const issuer{"issuer"};
        Account const holder{"holder"};
        PrettyAsset const asset = issuer["USD"];
        auto const vaultKeylet = createDilutionVault(env, owner, issuer, holder, asset);

        Vault const before = readVaultState(env, vaultKeylet, asset.raw());
        STAmount const amount = asset(Number{1'000'917, -3});  // 1000.917
        STAmount const holderShares = fetchHolderShares(env, vaultKeylet, holder);
        LeanVaultResult const lean = leanVaultClawback(
            before, amount, holderShares, holderOwnsAllShares(env, vaultKeylet, holder));
        expectLawful(lean);
        BEAST_EXPECTS(!lean.leanError.has_value(), "lean clawback error");

        env(jtx::Vault::clawback(
                {.issuer = issuer, .id = vaultKeylet.key, .holder = holder, .amount = amount}),
            jtx::Ter(tesSUCCESS));
        env.close();
        Vault const after = readVaultState(env, vaultKeylet, asset.raw());

        BEAST_EXPECTS(
            priceNotBelow(
                after.assetsTotal, after.sharesTotal, before.assetsTotal, before.sharesTotal),
            "C++ clawback lowered the share price");
        BEAST_EXPECTS(
            priceNotBelow(
                lean.vault.assetsTotal,
                lean.vault.sharesTotal,
                before.assetsTotal,
                before.sharesTotal),
            "model clawback lowered the share price");
    }

    // The round-trip recovery is now re-rounded to the vault scale by the clamp, so the total
    // moves by exactly what the issuer recovers (both C++ and the model).
    void
    testClawbackAppliedDelta()
    {
        using namespace jtx;
        testcase("clawback moves the vault total by exactly the recovery");

        Env env(*this);
        Account const owner{"owner"};
        Account const issuer{"issuer"};
        Account const holder{"holder"};
        PrettyAsset const asset = issuer["USD"];
        auto const vaultKeylet = createAppliedDeltaVault(env, owner, issuer, holder, asset);

        Vault const before = readVaultState(env, vaultKeylet, asset.raw());
        BEAST_EXPECT(before.assetsTotal == Number{3});

        // Claw 0.0001 of the asset from the holder.
        STAmount const amount = asset(Number{1, -4});
        LeanVaultResult const lean = leanVaultClawback(
            before,
            amount,
            fetchHolderShares(env, vaultKeylet, holder),
            holderOwnsAllShares(env, vaultKeylet, holder));
        expectLawful(lean);
        BEAST_EXPECTS(!lean.leanError.has_value() && !lean.error, "lean clawback failed");
        // Model and C++ agree on the recovery, so it stands in for the accountSend amount.
        Number const recovery{lean.assets};
        BEAST_EXPECTS((recovery == Number{999'857, -10}), to_string(recovery));

        env(jtx::Vault::clawback(
                {.issuer = issuer, .id = vaultKeylet.key, .holder = holder, .amount = amount}),
            jtx::Ter(tesSUCCESS));
        env.close();
        Vault const after = readVaultState(env, vaultKeylet, asset.raw());

        // C++: the vault must lose exactly the recovery.
        Number const cppDelta = before.assetsTotal - after.assetsTotal;
        BEAST_EXPECTS(
            cppDelta == recovery,
            "C++ booked " + to_string(cppDelta) + " but recovered " + to_string(recovery));

        // Model: the same, on its own stored total.
        Number const leanDelta = before.assetsTotal - lean.vault.assetsTotal;
        BEAST_EXPECTS(
            leanDelta == recovery,
            "model booked " + to_string(leanDelta) + " but recovered " + to_string(recovery));

        // The recovery must be on the vault scale, on both sides: they share the value here.
        STAmount const recoveryRounded =
            roundToVaultGrid(asset, before.scale, before.assetsAvailable, -recovery);
        BEAST_EXPECTS(
            Number{recoveryRounded} == recovery,
            "the recovery " + to_string(recovery) + " re-rounds to " +
                to_string(Number{recoveryRounded}));
    }

    void
    runTests() override
    {
        using namespace jtx;

        Number const iouMax{9'999'999'999'999'999LL, 80};

        // Asset clawback by the issuer: partial, full, and over-seed (clamped to available).
        testClawbackAsset(1'000, 400, tesSUCCESS);
        testClawbackAsset(1'000, 1'000, tesSUCCESS);
        testClawbackAsset(1'000, 1'001, tesSUCCESS);

        // canBurnShares over VALID (assetsTotal, assetsAvailable, sharesTotal) states
        testCanBurnShares(Number{0}, Number{0}, 0, tecNO_PERMISSION);
        testCanBurnShares(Number{0}, Number{0}, 1'000, tesSUCCESS);
        testCanBurnShares(Number{1'000}, Number{0}, 1'000, tecNO_PERMISSION);
        testCanBurnShares(Number{1'000}, Number{1'000}, 1'000, tecNO_PERMISSION);
        testCanBurnShares(Number{0}, Number{0}, kMaxMpTokenAmount, tesSUCCESS);
        // Per-field extremes: huge assets deny
        testCanBurnShares(iouMax, iouMax, 1'000, tecNO_PERMISSION);
        testCanBurnShares(iouMax, Number{0}, 1'000, tecNO_PERMISSION);
        testBurnSharesPartialAmount();

        // Vault.burnShares
        testBurnShares(1'000'000'000, 1'000'000'000);
        testBurnShares(1'000'000'000, 2'000'000'000);
        testBurnShares(kOpenLimitUnits, kOpenLimitUnits);
        testBurnShares(1, kMaxMpTokenAmount);
        testBurnShares(1, 1);

        testClawbackAsset(kOpenLimitUnits, kOpenLimitUnits, tesSUCCESS);
        testClawbackAsset(kOpenLimitUnits, kOpenLimitUnits / 2, tesSUCCESS);
        testClawbackAsset(kOpenLimitUnits, 1, tesSUCCESS);
        testClawbackAsset(1, 1, tesSUCCESS);

        testClawbackAsset(1'000, 0, tesSUCCESS);

        // NAV-drifted vault (owner donation)
        testClawbackDrifted(3, 2, 3, tesSUCCESS);
        testClawbackDrifted(7, 5, 4, tesSUCCESS);

        testUpdatedStateClawback(iouMax, iouMax, 1'000, 1, tecPRECISION_LOSS);
        testUpdatedStateClawback(iouMax, iouMax, kMaxMpTokenAmount, 1, tecPRECISION_LOSS);
        testUpdatedStateClawback(Number{1'000}, Number{0}, 1'000, 400, tecPRECISION_LOSS);

        // Open discrepancy, disabled until the C++ code is fixed.
        // clang-format off
        // testClawbackAllLeavesAssets(Number{3'141'592'653'589'793'238LL, -18}, Number{0}, 7'000'025, tecPRECISION_LOSS);  // FV_M2_18 (>16 digit dust)

        // Properties both sides now satisfy, kept as regression tests.
        testClawbackOvervaluedShares();  // FV_M2_3: a one-share recovery rounds down
        testClawbackDilution();          // FV_M2_8: the share price does not fall
        testClawbackOverRecover();       // FV_M2_11: the recovery does not exceed the request
        testClawbackAppliedDelta();      // total moves by exactly the recovery

        // Fixed discrepancies, kept as regression tests.
        // FV_M2_17: a sole holder's shares are now priced at full value, so the recovery clamps to
        // sfAssetsAvailable instead of burning every share against a smaller payout.
        testClawbackAllLeavesAssets(Number{1'000'000}, Number{1'000}, 1'000'000, tesSUCCESS);
        testClawbackZeroAmountFullBalance();  // FV_M2_10: amount 0 claws the full balance
        testClawbackDustDebit(Number{2, 12}, 1'000'000'000'000'000'000ULL);   // FV_M2_12 (2e12)
        testClawbackDustDebit(Number{15, 12}, 9'200'000'000'000'000'000ULL);  // FV_M2_12 (1.5e13)
        // FV_M2_12: a 1e-6 clawback below the 1e-5 ULP of a staged ~1e10 total.
        testClawbackPrecisionLossStaged(Number{1'000'000'000'000'001LL, -5});
        testClawbackPrecisionLossStaged(Number{1'000'000'000'000'000LL, -5});
        // clang-format on
    }
};

BEAST_DEFINE_TESTSUITE(LeanVaultClawback, formal_verification, xrpl);

}  // namespace xrpl::test::formal_verification
