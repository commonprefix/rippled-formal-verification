#include <test/formal_verification/common/LeanSuite.h>
#include <test/formal_verification/ffi/vault/VaultClawbackFFI.h>
#include <test/formal_verification/ffi/vault/VaultFFI.h>
#include <test/formal_verification/tx/vault/ClawbackSweepCases.h>
#include <test/formal_verification/tx/vault/DepositSweepCases.h>
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
#include <vector>

namespace xrpl::test::formal_verification {

using namespace clawback_sweep;

class LeanVaultClawback_test : public LeanSuite
{
    // The accounts of the shared staging ledger built in runTests: the vault owner, the issuer of
    // both clawback-enabled assets, and the one holder every staged state is about.
    jtx::Account const owner_{"owner"};
    jtx::Account const issuer_{"issuer"};
    jtx::Account const holder_{"holder"};

    static MPTIssue
    shareIssue(jtx::Env& env, Keylet const& vaultKeylet)
    {
        return MPTIssue{env.le(vaultKeylet)->at(sfShareMPTID)};
    }

    // `n` of the vault's asset, as a Number (not on the vault grid).
    static STAmount
    assetAmount(jtx::Env& env, Keylet const& vault, Number const& n)
    {
        return STAmount{Asset{env.le(vault)->at(sfAsset)}, n};
    }

    struct StagedClawback
    {
        AppliedVaultTx cpp;
        LeanVaultResult lean;
    };

    // One issuer clawback from holder_: C++ on a throwaway view and the model on the same staged
    // vault must agree on the verdict and, when both succeed, on the post-state and the recovery.
    // The holder owns every share unless `staged` says otherwise.
    StagedClawback
    checkClawback(
        jtx::Env& env,
        Keylet const& vault,
        StagedVault staged,
        STAmount const& amount,
        bool omitAmount = false)
    {
        if (!staged.holderShares)
            staged.holderShares = staged.sharesTotal;
        jtx::Vault::ClawbackArgs args{.issuer = issuer_, .id = vault.key, .holder = holder_};
        if (!omitAmount)
            args.amount = amount;
        AppliedVaultTx const cpp =
            applyStaged(env, vault, holder_, staged, jtx::Vault::clawback(args));
        std::uint64_t const held = *staged.holderShares;
        LeanVaultResult const lean = leanVaultClawback(
            cpp.pre,
            amount,
            STAmount{shareIssue(env, vault), held},
            staged.sharesTotal != 0 && held == staged.sharesTotal);
        std::string const at = sampleText(staged, amount);
        if (expectAgree(*this, at, cpp, lean) == tesSUCCESS && !lean.leanError && !lean.error)
        {
            Number const recovered = cpp.pre.assetsAvailable - cpp.post.assetsAvailable;
            BEAST_EXPECTS(
                Number{lean.assets} == recovered,
                at + "recovered lean=" + to_string(Number{lean.assets}) +
                    " cpp=" + to_string(recovered));
        }
        return {.cpp = cpp, .lean = lean};
    }

    void
    expectStagedClawback(
        jtx::Env& env,
        Keylet const& vault,
        StagedVault const& staged,
        STAmount const& amount,
        TER expected,
        bool omitAmount = false)
    {
        TER const ter = checkClawback(env, vault, staged, amount, omitAmount).cpp.ter;
        BEAST_EXPECTS(
            ter == expected,
            std::string("cpp=") + transToken(ter) + " expected " + transToken(expected));
    }

    // One owner burn of holder_'s shares (`amount` in shares, 0 for all), checked like
    // checkClawback: the model runs canBurnShares, then burnShares on the holder's balance.
    TER
    checkBurn(jtx::Env& env, Keylet const& vault, StagedVault const& staged, std::int64_t amount)
    {
        MPTIssue const shares = shareIssue(env, vault);
        STAmount const requested{shares, amount};
        STAmount const held{shares, staged.holderShares.value_or(0)};
        AppliedVaultTx const cpp = applyStaged(
            env,
            vault,
            holder_,
            staged,
            jtx::Vault::clawback(
                {.issuer = owner_, .id = vault.key, .holder = holder_, .amount = requested}));
        std::string const at = sampleText(staged, requested);
        LeanAmountResult const can = leanCanBurnShares(cpp.pre, requested, held);
        BEAST_EXPECTS(can.leanError != LeanError::notLawful, at + "model: staged state not lawful");
        TER leanTer = can.leanError ? TER{tefEXCEPTION} : can.error.value_or(tesSUCCESS);
        LeanBurnResult burn;
        if (leanTer == tesSUCCESS)
        {
            burn = leanBurnShares(cpp.pre, held);
            leanTer = burn.leanError ? TER{tefEXCEPTION} : burn.error.value_or(tesSUCCESS);
        }
        BEAST_EXPECTS(
            leanTer == cpp.ter, at + "lean=" + transToken(leanTer) + " cpp=" + transToken(cpp.ter));
        if (cpp.ter == tesSUCCESS && leanTer == tesSUCCESS)
            expectSameVault(*this, at, burn.vault, cpp.post);
        return cpp.ter;
    }

    void
    compareClawbackAsset(
        jtx::Env& env,
        Keylet const& vaultKeylet,
        jtx::Account const& issuer,
        jtx::Account const& holder,
        Asset const& asset,
        STAmount const& amount,
        TER expected,
        bool omitAmount = false)
    {
        using namespace jtx;
        Vault const state = readVaultState(env, vaultKeylet, asset);
        STAmount const holderShares = fetchHolderShares(env, vaultKeylet, holder);
        bool const waiveUnrealizedLoss = holderOwnsAllShares(env, vaultKeylet, holder);
        LeanVaultResult const clawback =
            leanVaultClawback(state, amount, holderShares, waiveUnrealizedLoss);
        expectLawful(clawback);

        // An omitted amount is a zero asset amount for the model.
        env(jtx::Vault::clawback(
                {.issuer = issuer,
                 .id = vaultKeylet.key,
                 .holder = holder,
                 .amount = omitAmount ? std::nullopt : std::optional<STAmount>{amount}}),
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

    // Claw everything from a holder beside the owner's own shares: the holder is not the sole
    // shareholder, so the loss is not waived and the holder's balance bounds the recovery.
    void
    testClawbackAllNotSole(jtx::Env& env, Keylet const& vault, bool omitAmount)
    {
        testcase(
            std::string("clawback all from one of two holders, amount ") +
            (omitAmount ? "omitted" : "zero"));
        // The holder deposited 1'000 and the owner 500.
        StagedVault const staged{
            .available = gridUnits(env, vault, 1'500),
            .sharesTotal = 1'500,
            .holderShares = 1'000,
            .pseudoHolding = true};
        expectStagedClawback(env, vault, staged, gridUnits(env, vault, 0), tesSUCCESS, omitAmount);
    }

    // A coarsened IOU vault whose deployed assets round away against the total: clawing every
    // share would leave the deployed assets without shares. Covered by testCoarseClawAllSweep.
    void
    testClawbackAllWhileDeployed(jtx::Env& env, Keylet const& vault)
    {
        testcase("clawback all shares while assets are deployed");
        StagedVault const staged{
            .available = assetAmount(env, vault, Number{99'999'999'999'999'990LL}),
            .deployed = assetAmount(env, vault, Number{4}),
            .loss = assetAmount(env, vault, Number{4}),
            .sharesTotal = 1'000,
            .pseudoHolding = true};
        expectStagedClawback(
            env, vault, staged, assetAmount(env, vault, Number{0}), tecHAS_OBLIGATIONS);
    }

    void
    testClawbackAsset(
        jtx::Env& env,
        Keylet const& vault,
        std::int64_t seed,
        std::int64_t amount,
        TER expected)
    {
        testcase("clawback MPT asset " + std::to_string(amount) + " from " + std::to_string(seed));
        StagedVault const staged{
            .available = gridUnits(env, vault, seed),
            .sharesTotal = static_cast<std::uint64_t>(seed),
            .pseudoHolding = true};
        expectStagedClawback(env, vault, staged, gridUnits(env, vault, amount), expected);
    }

    // MPT vault where the owner donates assets without shares, drifting NAV off 1:1 so the
    // clawback conversions round. The issuer then claws `clawAmount` from the holder.
    void
    testClawbackDrifted(
        jtx::Env& env,
        Keylet const& vault,
        std::int64_t deposit,
        std::int64_t donation,
        std::int64_t clawAmount,
        TER expected)
    {
        testcase(
            "clawback drifted MPT claw " + std::to_string(clawAmount) + " (deposit=" +
            std::to_string(deposit) + ", donation=" + std::to_string(donation) + ")");
        StagedVault const staged{
            .available = gridUnits(env, vault, deposit + donation),
            .sharesTotal = static_cast<std::uint64_t>(deposit),
            .pseudoHolding = true};
        expectStagedClawback(env, vault, staged, gridUnits(env, vault, clawAmount), expected);
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

    // canBurnShares preclaim, on `staged`. Without a share amount C++ continues past the preclaim
    // check, so only its tecNO_PERMISSION is compared.
    void
    compareCanBurnShares(
        jtx::Env& env,
        Keylet const& vault,
        StagedVault const& staged,
        TER expected,
        std::optional<std::int64_t> shareAmount = std::nullopt)
    {
        STAmount const amount{shareIssue(env, vault), shareAmount.value_or(0)};
        jtx::Vault::ClawbackArgs args{.issuer = owner_, .id = vault.key, .holder = holder_};
        if (shareAmount)
            args.amount = amount;
        AppliedVaultTx const cpp =
            applyStaged(env, vault, holder_, staged, jtx::Vault::clawback(args));
        LeanAmountResult const lean = leanCanBurnShares(
            cpp.pre, amount, STAmount{shareIssue(env, vault), staged.holderShares.value_or(0)});
        expectLawful(lean);
        BEAST_EXPECTS(!lean.leanError.has_value(), "lean canBurnShares error");

        TER const cppTer = cpp.ter;
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

    // An owner burn with an explicit share amount must name the holder's whole balance. Covered by
    // testBurnSweep.
    void
    testBurnSharesPartialAmount(jtx::Env& env, Keylet const& vault)
    {
        testcase("canBurnShares with a partial share amount");
        // Insolvent: no assets, the 1'000 deposited (1e9 shares at scale 6) still outstanding.
        StagedVault const staged{
            .available = gridUnits(env, vault, 0),
            .sharesTotal = 1'000'000'000,
            .holderShares = 1'000'000'000};
        compareCanBurnShares(env, vault, staged, tecLIMIT_EXCEEDED, 5);
    }

    void
    testCanBurnShares(
        jtx::Env& env,
        Keylet const& vault,
        Number const& assetsTotal,
        Number const& assetsAvailable,
        std::uint64_t sharesTotal,
        TER expected)
    {
        testcase(
            "canBurnShares total=" + to_string(assetsTotal) +
            " avail=" + to_string(assetsAvailable) + " shares=" + std::to_string(sharesTotal));
        // The holder owns no shares.
        StagedVault const staged{
            .available = assetAmount(env, vault, assetsAvailable),
            .deployed = assetAmount(env, vault, assetsTotal - assetsAvailable),
            .sharesTotal = sharesTotal,
            .holderShares = 0};
        compareCanBurnShares(env, vault, staged, expected);
    }

    // Vault.burnShares models the owner burning a holder's shares
    void
    testBurnShares(
        jtx::Env& env,
        Keylet const& vault,
        std::int64_t deposit,
        std::uint64_t stagedOutstanding)
    {
        testcase(
            "burnShares held=" + std::to_string(deposit) +
            " outstanding=" + std::to_string(stagedOutstanding));
        // An emptied vault, so the owner may burn the holder's remaining shares.
        StagedVault const staged{
            .available = gridUnits(env, vault, 0),
            .sharesTotal = stagedOutstanding,
            .holderShares = static_cast<std::uint64_t>(deposit)};
        // The holder's actual share balance is what C++ burns and what the model is given.
        AppliedVaultTx const cpp = applyStaged(
            env,
            vault,
            holder_,
            staged,
            jtx::Vault::clawback({.issuer = owner_, .id = vault.key, .holder = holder_}));
        LeanBurnResult const burn =
            leanBurnShares(cpp.pre, STAmount{shareIssue(env, vault), deposit});
        expectLawful(burn);

        BEAST_EXPECTS(cpp.ter == tesSUCCESS, std::string("cpp=") + transToken(cpp.ter));
        BEAST_EXPECTS(!burn.leanError.has_value(), "lean burnShares error");
        BEAST_EXPECTS(
            burn.vault.sharesTotal == cpp.post.sharesTotal,
            "sharesTotal lean=" + to_string(burn.vault.sharesTotal) +
                " cpp=" + to_string(cpp.post.sharesTotal));
        BEAST_EXPECT(burn.vault.assetsTotal == cpp.post.assetsTotal);
        BEAST_EXPECT(burn.vault.assetsAvailable == cpp.post.assetsAvailable);
    }

    // FV_M2_3 (regression): on a 5:3 NAV-drifted vault, clawing 2 assets burns 1 share worth
    // 1.667. C++ used to recover round(1.667) = 2; both sides now recover 1 (the payout rounds
    // down).
    void
    testClawbackOvervaluedShares(jtx::Env& env, Keylet const& vault)
    {
        testClawbackDrifted(env, vault, 3, 2, 2, tesSUCCESS);
    }

    // FV_M2_12 (regression): a clawback too small to debit assetsTotal (the debit rounds back to
    // the old value) used to burn shares for nothing; both sides now reject it with
    // tecPRECISION_LOSS. A ~1e10 total is past the open limit (9e9 at scale 6), so it is staged.
    void
    testClawbackPrecisionLossStaged(jtx::Env& env, Keylet const& vault, Number const& assetsTotal)
    {
        testcase("STAGED clawback 1e-6 from total " + to_string(assetsTotal));
        // The holder deposited 1'000 (1e9 shares at scale 6).
        StagedVault const staged{
            .available = assetAmount(env, vault, assetsTotal),
            .sharesTotal = 10'000'000'000'000'009ULL,
            .holderShares = 1'000'000'000,
            .pseudoHolding = true};
        expectStagedClawback(
            env, vault, staged, assetAmount(env, vault, Number{1, -6}), tecPRECISION_LOSS);
    }

    // Finding (FV_M2_12, regression): a clawback too small to change the stored assetsTotal
    // used to burn a share (c++ -> tecINVARIANT_FAILED). Both sides now return tecPRECISION_LOSS.
    void
    testClawbackDustDebit(
        jtx::Env& env,
        Keylet const& vault,
        Number const& assetsTotal,
        std::uint64_t sharesTotal)
    {
        testcase("clawback one dust share (total " + to_string(assetsTotal) + ")");
        // One share is worth less than the assets total precision step; the holder deposited 1
        // (1e6 shares at scale 6).
        StagedVault const staged{
            .available = assetAmount(env, vault, assetsTotal),
            .sharesTotal = sharesTotal,
            .holderShares = 1'000'000,
            .pseudoHolding = true};
        expectStagedClawback(
            env, vault, staged, assetAmount(env, vault, Number{2, -6}), tecPRECISION_LOSS);
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
    testClawbackZeroAmountFullBalance(jtx::Env& env, Keylet const& vault)
    {
        testcase("issuer clawback with amount 0 claws the full balance");
        StagedVault const staged{
            .available = gridUnits(env, vault, 1'000), .sharesTotal = 1'000, .pseudoHolding = true};
        // Amount 0 should mean "claw the holder's entire balance"
        StagedClawback const r = checkClawback(env, vault, staged, gridUnits(env, vault, 0));
        BEAST_EXPECTS(r.cpp.ter == tesSUCCESS, std::string("cpp=") + transToken(r.cpp.ter));
        BEAST_EXPECT(r.cpp.post.sharesTotal == Number{0});
    }

    // FV_M2_11 (regression): an issuer clawback used to recover more than requested because the
    // share count rounded up (on a 7-asset / 5-share vault, clawing 4 burned 3 shares worth 4.2).
    // The share count now truncates on both sides, so the recovery does not exceed the request.
    void
    testClawbackOverRecover(jtx::Env& env, Keylet const& vault)
    {
        testcase("issuer clawback recovers more than requested");
        // Scale 0: the holder deposited 5 (5 shares) and the owner donated 2, so the vault holds 7
        // assets against 5 shares.
        StagedVault const staged{
            .available = gridUnits(env, vault, 7), .sharesTotal = 5, .pseudoHolding = true};
        // Claw 4: both burn 3 shares (5*4/7 = 2.857 rounds up) and recover 7*3/5 = 4.2 > 4.
        StagedClawback const r = checkClawback(env, vault, staged, gridUnits(env, vault, 4));
        BEAST_EXPECTS(r.cpp.ter == tesSUCCESS, std::string("cpp=") + transToken(r.cpp.ter));
        BEAST_EXPECTS(!r.lean.leanError.has_value(), "lean clawback error");
        BEAST_EXPECTS(
            r.cpp.pre.assetsTotal - r.cpp.post.assetsTotal <= Number{4},
            "C++ clawback recovered more than requested");
        BEAST_EXPECTS(
            static_cast<Number>(r.lean.assets) <= Number{4},
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

    // ---- Sweeps -------------------------------------------------------------------------------

    // The vaults a sweep runs on; holder_ holds their shares.
    using SweepVaults = std::vector<Keylet>;

    // A sole holder of price row `c` (assets total, shares total) claws back its amount.
    TER
    checkPriceCase(jtx::Env& env, Keylet const& vault, PriceCusp const& c)
    {
        StagedVault const staged{
            .available = gridUnits(env, vault, c.total),
            .sharesTotal = static_cast<std::uint64_t>(c.sharesTotal),
            .pseudoHolding = true};
        return checkClawback(env, vault, staged, gridUnits(env, vault, c.amount)).cpp.ter;
    }

    // Holder value: a clawback from one of several holders burns trunc(shares total * amount /
    // assets total) shares; C++ refuses (tecINSUFFICIENT_FUNDS) once that exceeds the holder's
    // shares. At price 1 the cusp is amount == the holder's shares.
    void
    testHolderValueSweep(jtx::Env& env, SweepVaults const& vaults)
    {
        for (Keylet const& vault : vaults)
        {
            beginCase(("clawback " + vaultName(env, vault) + " holder value-Sweep").c_str());
            runAroundCusp(kHolderValueCases, [&](HolderValueCusp const& c) {
                StagedVault const staged{
                    .available = gridUnits(env, vault, c.sharesTotal),
                    .sharesTotal = static_cast<std::uint64_t>(c.sharesTotal),
                    .holderShares = static_cast<std::uint64_t>(c.holderShares),
                    .pseudoHolding = true};
                return checkClawback(env, vault, staged, gridUnits(env, vault, c.amount)).cpp.ter;
            });
        }
    }

    // Owner burn: the owner may burn a holder's shares only in an insolvent vault (shares, no
    // assets; else tecNO_PERMISSION), only all of them (amount equal to the holder's shares or 0;
    // else tecLIMIT_EXCEEDED), and not when the holder has none (tecPRECISION_LOSS).
    void
    testBurnSweep(jtx::Env& env, SweepVaults const& vaults)
    {
        for (Keylet const& vault : vaults)
        {
            beginCase(("clawback " + vaultName(env, vault) + " owner burn-Sweep").c_str());
            auto const check = [&](BurnCusp const& c) {
                StagedVault const staged{
                    .available = gridUnits(env, vault, c.available),
                    .sharesTotal = static_cast<std::uint64_t>(c.sharesTotal),
                    .holderShares = static_cast<std::uint64_t>(c.holderShares),
                    .pseudoHolding = true};
                return checkBurn(env, vault, staged, c.amount);
            };
            runAroundCusp(kBurnCases, check);
            runAroundCusp(kBurnNoSharesCases, check);
        }
    }

    // Zero shares: a clawback burning trunc(shares total * amount / assets total) = 0 shares is
    // refused (tecPRECISION_LOSS). Each row of kZeroSharesCases burns exactly one share.
    void
    testZeroSharesSweep(jtx::Env& env, SweepVaults const& vaults)
    {
        for (Keylet const& vault : vaults)
        {
            beginCase(("clawback " + vaultName(env, vault) + " zero shares-Sweep").c_str());
            runAroundCusp(kZeroSharesCases, [&](PriceCusp const& c) {
                return checkPriceCase(env, vault, c);
            });
        }
    }

    // Clamp to zero: a recovery that floors to zero on the vault grid is refused
    // (tecPRECISION_LOSS). Each row of kClampToZeroCases recovers exactly one unit; one share
    // more or less recovers less than a unit.
    void
    testClampToZeroSweep(jtx::Env& env, SweepVaults const& vaults)
    {
        for (Keylet const& vault : vaults)
        {
            beginCase(("clawback " + vaultName(env, vault) + " clamp to zero-Sweep").c_str());
            runAroundCusp(kClampToZeroCases, [&](PriceCusp const& c) {
                return checkPriceCase(env, vault, c);
            });
        }
    }

    // Clamp to available: with assets deployed, a sole holder's clawback above the available
    // assets is reduced to them and the shares re-derived. Both sides succeed on every case; the
    // post-states and recoveries are compared.
    void
    testClampToAvailableSweep(jtx::Env& env, SweepVaults const& vaults)
    {
        for (Keylet const& vault : vaults)
        {
            beginCase(("clawback " + vaultName(env, vault) + " clamp to available-Sweep").c_str());
            runAroundCusp(
                kAvailableCases,
                [&](AvailableCusp const& c) {
                    StagedVault const staged{
                        .available = gridUnits(env, vault, c.available),
                        .deployed = gridUnits(env, vault, c.deployed),
                        .sharesTotal = static_cast<std::uint64_t>(c.available + c.deployed),
                        .pseudoHolding = true};
                    return checkClawback(env, vault, staged, gridUnits(env, vault, c.amount))
                        .cpp.ter;
                },
                false);
        }
    }

    // Coarse claw-all: a sole holder's claw-all on coarse available assets converts available +
    // deployed to 16 digits. When the deployed assets round away (below half a mantissa ULP, or
    // the tie on an even mantissa) every share would be burned with assets still deployed:
    // tecHAS_OBLIGATIONS. Otherwise the recovery clamps to the available assets and succeeds.
    void
    testCoarseClawAllSweep(jtx::Env& env, SweepVaults const& vaults)
    {
        for (Keylet const& vault : vaults)
        {
            beginCase(("clawback " + vaultName(env, vault) + " coarse claw-all-Sweep").c_str());
            Asset const asset = env.le(vault)->at(sfAsset);
            int const base = -static_cast<int>(env.le(vault)->at(sfScale));
            runAroundCusp(kCoarseClawAllCases, [&](CoarseClawAllCusp const& c) {
                StagedVault const staged{
                    .available =
                        STAmount{asset, static_cast<std::uint64_t>(c.mantissa), base + c.exponent},
                    .deployed = gridUnits(env, vault, c.deployed),
                    .sharesTotal = kCoarseShares,
                    .pseudoHolding = true};
                return checkClawback(env, vault, staged, gridUnits(env, vault, 0)).cpp.ter;
            });
        }
    }

    // Share overflow: a clawback whose share count trunc(shares total * amount / assets total)
    // reaches 2^63 is tecPATH_DRY. Each row is the largest share count that still fits.
    void
    testShareOverflowSweep(jtx::Env& env, SweepVaults const& vaults)
    {
        for (Keylet const& vault : vaults)
        {
            beginCase(("clawback " + vaultName(env, vault) + " share overflow-Sweep").c_str());
            runAroundCusp(clawback_sweep::kShareOverflowCases, [&](PriceCusp const& c) {
                return checkPriceCase(env, vault, c);
            });
        }
    }

    void
    runTests() override
    {
        using namespace jtx;

        // One ledger holding a vault per clawback-enabled asset; every staged clawback (old tests
        // and sweeps) runs on a throwaway view of it. holder_ is not the issuer.
        Env env{*this};
        env.fund(XRP(1'000'000), owner_, issuer_, holder_);
        env.close();
        env(fset(issuer_, asfAllowTrustLineClawback));
        env.close();
        PrettyAsset const iou = issuer_["USD"];
        env(trust(holder_, iou(1'000'000)));
        env(pay(issuer_, holder_, iou(1'000)));
        MPTTester mptt{env, issuer_, kMptInitNoFund};
        mptt.create({.flags = tfMPTCanTransfer | tfMPTCanClawback});
        mptt.authorize({.account = holder_});
        PrettyAsset const mpt = mptt.issuanceID();
        // Outstanding MPT covers any staged holding the issuer claws back.
        env(pay(issuer_, holder_, mpt(9'200'000'000'000'000)));
        env.close();

        Keylet const mptVault = createSweepVault(env, owner_, holder_, mpt);
        // IOU at the smallest, the default and the largest vault scale.
        Keylet const iouScale0Vault = createSweepVault(env, owner_, holder_, iou, 0);
        Keylet const iouScale6Vault = createSweepVault(env, owner_, holder_, iou, 6);
        Keylet const iouScale10Vault = createSweepVault(env, owner_, holder_, iou, 10);
        SweepVaults const all{mptVault, iouScale0Vault, iouScale6Vault, iouScale10Vault};
        SweepVaults const ious{iouScale0Vault, iouScale6Vault, iouScale10Vault};

        Number const iouMax{9'999'999'999'999'999LL, 80};

        // Asset clawback by the issuer: partial, full, and over-seed (clamped to available).
        testClawbackAsset(env, mptVault, 1'000, 400, tesSUCCESS);
        testClawbackAsset(env, mptVault, 1'000, 1'000, tesSUCCESS);
        testClawbackAsset(
            env, mptVault, 1'000, 1'001, tesSUCCESS);  // covered by testClampToAvailableSweep

        // canBurnShares over VALID (assetsTotal, assetsAvailable, sharesTotal) states
        // Covered by testBurnSweep.
        testCanBurnShares(env, iouScale6Vault, Number{0}, Number{0}, 0, tecNO_PERMISSION);
        testCanBurnShares(env, iouScale6Vault, Number{0}, Number{0}, 1'000, tesSUCCESS);
        testCanBurnShares(env, iouScale6Vault, Number{1'000}, Number{0}, 1'000, tecNO_PERMISSION);
        testCanBurnShares(
            env, iouScale6Vault, Number{1'000}, Number{1'000}, 1'000, tecNO_PERMISSION);
        testCanBurnShares(env, iouScale6Vault, Number{0}, Number{0}, kMaxMpTokenAmount, tesSUCCESS);
        // Per-field extremes: huge assets deny
        testCanBurnShares(env, iouScale6Vault, iouMax, iouMax, 1'000, tecNO_PERMISSION);
        testCanBurnShares(env, iouScale6Vault, iouMax, Number{0}, 1'000, tecNO_PERMISSION);
        testBurnSharesPartialAmount(env, iouScale6Vault);

        // Vault.burnShares. Covered by testBurnSweep.
        testBurnShares(env, mptVault, 1'000'000'000, 1'000'000'000);
        testBurnShares(env, mptVault, 1'000'000'000, 2'000'000'000);
        testBurnShares(env, mptVault, kOpenLimitUnits, kOpenLimitUnits);
        testBurnShares(env, mptVault, 1, kMaxMpTokenAmount);
        testBurnShares(env, mptVault, 1, 1);

        testClawbackAsset(env, mptVault, kOpenLimitUnits, kOpenLimitUnits, tesSUCCESS);
        testClawbackAsset(env, mptVault, kOpenLimitUnits, kOpenLimitUnits / 2, tesSUCCESS);
        testClawbackAsset(env, mptVault, kOpenLimitUnits, 1, tesSUCCESS);
        testClawbackAsset(env, mptVault, 1, 1, tesSUCCESS);

        testClawbackAsset(env, mptVault, 1'000, 0, tesSUCCESS);
        testClawbackAllNotSole(env, mptVault, false);
        testClawbackAllNotSole(env, mptVault, true);
        testClawbackAllWhileDeployed(env, iouScale6Vault);

        // NAV-drifted vault (owner donation)
        testClawbackDrifted(env, mptVault, 3, 2, 3, tesSUCCESS);
        testClawbackDrifted(env, mptVault, 7, 5, 4, tesSUCCESS);

        // Own ledgers: these stage values an MPT amount cannot hold.
        testUpdatedStateClawback(iouMax, iouMax, 1'000, 1, tecPRECISION_LOSS);
        testUpdatedStateClawback(iouMax, iouMax, kMaxMpTokenAmount, 1, tecPRECISION_LOSS);
        testUpdatedStateClawback(Number{1'000}, Number{0}, 1'000, 400, tecPRECISION_LOSS);

        // Open discrepancy, disabled until the C++ code is fixed.
        // clang-format off
        // testClawbackAllLeavesAssets(Number{3'141'592'653'589'793'238LL, -18}, Number{0}, 7'000'025, tecPRECISION_LOSS);  // FV_M2_18 (>16 digit dust)

        // Properties both sides now satisfy, kept as regression tests.
        testClawbackOvervaluedShares(env, mptVault);  // FV_M2_3: a one-share recovery rounds down
        testClawbackDilution();          // FV_M2_8: the share price does not fall
        testClawbackOverRecover(env, iouScale0Vault);  // FV_M2_11: the recovery does not exceed the request
        testClawbackAppliedDelta();      // total moves by exactly the recovery

        // Fixed discrepancies, kept as regression tests.
        // FV_M2_17: a sole holder's shares are now priced at full value, so the recovery clamps to
        // sfAssetsAvailable instead of burning every share against a smaller payout.
        testClawbackAllLeavesAssets(Number{1'000'000}, Number{1'000}, 1'000'000, tesSUCCESS);
        testClawbackZeroAmountFullBalance(env, mptVault);  // FV_M2_10: amount 0 claws the full balance
        testClawbackDustDebit(env, iouScale6Vault, Number{2, 12}, 1'000'000'000'000'000'000ULL);   // FV_M2_12 (2e12)
        testClawbackDustDebit(env, iouScale6Vault, Number{15, 12}, 9'200'000'000'000'000'000ULL);  // FV_M2_12 (1.5e13)
        // FV_M2_12: a 1e-6 clawback below the 1e-5 ULP of a staged ~1e10 total.
        testClawbackPrecisionLossStaged(env, iouScale6Vault, Number{1'000'000'000'000'001LL, -5});
        testClawbackPrecisionLossStaged(env, iouScale6Vault, Number{1'000'000'000'000'000LL, -5});
        // clang-format on

        testBurnSweep(env, all);
        testZeroSharesSweep(env, all);
        testClampToZeroSweep(env, ious);
        testClampToAvailableSweep(env, all);
        testCoarseClawAllSweep(env, ious);
        testShareOverflowSweep(env, all);

        // Clawing back more than a non-sole holder's shares are worth is tecINSUFFICIENT_FUNDS
        // on both sides (C++ at the share transfer).
        testHolderValueSweep(env, all);
    }
};

BEAST_DEFINE_TESTSUITE(LeanVaultClawback, formal_verification, xrpl);

}  // namespace xrpl::test::formal_verification
