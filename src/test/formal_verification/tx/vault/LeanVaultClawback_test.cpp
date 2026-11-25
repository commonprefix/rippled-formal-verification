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
#include <xrpl/protocol/MPTIssue.h>
#include <xrpl/protocol/Protocol.h>
#include <xrpl/protocol/SField.h>
#include <xrpl/protocol/STNumber.h>
#include <xrpl/protocol/TER.h>

#include <chrono>
#include <cstddef>
#include <cstdint>
#include <limits>
#include <optional>
#include <span>
#include <string>
#include <vector>

namespace xrpl::test::formal_verification {

struct ClawbackCase
{
    StagedVault vault;
    std::int64_t amount;
    TER expected;
    // The vault owner burns the holder's shares (amount in shares); otherwise the asset issuer
    // claws back vault assets.
    bool burn{};
    // Set: the available assets are vault.available * 10^availableExponent vault grid units, to
    // reach past the vault grid.
    std::optional<int> availableExponent{};
    // The transaction carries no amount (the model gets a zero amount).
    bool omitAmount{};
};

class LeanVaultClawback_test : public LeanSuite
{
    // The accounts of the shared staging ledger: the vault owner, the issuer of both
    // clawback-enabled assets, and the one holder every staged state is about.
    // Staged states may be unreachable by any transaction: a verdict compares model and C++ on the
    // same pre-state and does not claim the state is reachable (see stageVault).
    jtx::Account const owner_{"owner"};
    jtx::Account const issuer_{"issuer"};
    jtx::Account const holder_{"holder"};

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
    // vault both return `expected`, with every vault field and the recovery equal when both
    // succeed. The holder owns every share unless `staged` says otherwise.
    StagedClawback
    expectStagedClawback(
        jtx::Env& env,
        Keylet const& vault,
        StagedAmounts const& staged,
        STAmount const& amount,
        TER expected,
        bool omitAmount = false)
    {
        AppliedVaultTx const cpp = applyClawback(
            env,
            vault,
            issuer_,
            holder_,
            staged,
            omitAmount ? std::nullopt : std::optional<STAmount>{amount});
        LeanVaultResult const lean = leanClawback(cpp, staged, amount, shareIssue(env, vault));
        expectLawful(lean);
        expectSame(*this, sampleText(staged, amount), cpp, lean, expected);
        return {.cpp = cpp, .lean = lean};
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
        env(jtx::Vault::clawback({
                .issuer = issuer,
                .id = vaultKeylet.key,
                .holder = holder,
                .amount = omitAmount ? std::nullopt : std::optional<STAmount>{amount},
            }),
            jtx::Ter(std::ignore));
        TER const cppTer = env.ter();
        // Read before closing: a close discards state staged on the open ledger.
        Vault const post = readVaultState(env, vaultKeylet, asset);
        Number const storedTotal = env.le(vaultKeylet)->at(sfAssetsTotal);
        env.close();

        AppliedVaultTx const cpp{
            .pre = state,
            .ter = cppTer,
            .post = post,
            .assets = state.assetsAvailable - post.assetsAvailable,
            .shares = state.sharesTotal - post.sharesTotal,
            .asset = asset,
            .storedTotal = storedTotal,
        };
        expectSame(*this, "", cpp, clawback, expected);
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
        StagedAmounts const staged{
            .available = vaultUnits(env, vault, 1'500),
            .sharesTotal = 1'500,
            .holderShares = 1'000,
            .pseudoHolding = true,
        };
        expectStagedClawback(env, vault, staged, vaultUnits(env, vault, 0), tesSUCCESS, omitAmount);
    }

    // A coarsened IOU vault whose deployed assets round away against the total: clawing every
    // share would leave the deployed assets without shares. Covered by testClawbackBoundaries.
    void
    testClawbackAllWhileDeployed(jtx::Env& env, Keylet const& vault)
    {
        testcase("clawback all shares while assets are deployed");
        StagedAmounts const staged{
            .available = assetAmount(env, vault, Number{99'999'999'999'999'990LL}),
            .deployed = assetAmount(env, vault, Number{4}),
            .loss = assetAmount(env, vault, Number{4}),
            .sharesTotal = 1'000,
            .pseudoHolding = true,
        };
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
        StagedAmounts const staged{
            .available = vaultUnits(env, vault, seed),
            .sharesTotal = static_cast<std::uint64_t>(seed),
            .pseudoHolding = true,
        };
        expectStagedClawback(env, vault, staged, vaultUnits(env, vault, amount), expected);
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
        StagedAmounts const staged{
            .available = vaultUnits(env, vault, deposit + donation),
            .sharesTotal = static_cast<std::uint64_t>(deposit),
            .pseudoHolding = true,
        };
        expectStagedClawback(env, vault, staged, vaultUnits(env, vault, clawAmount), expected);
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

        Env env{*this, vaultTestAmendments()};
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
        StagedAmounts const& staged,
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
    // testClawbackBoundaries.
    void
    testBurnSharesPartialAmount(jtx::Env& env, Keylet const& vault)
    {
        testcase("canBurnShares with a partial share amount");
        // Insolvent: no assets, the 1'000 deposited (1e9 shares at scale 6) still outstanding.
        StagedAmounts const staged{
            .available = vaultUnits(env, vault, 0),
            .sharesTotal = 1'000'000'000,
            .holderShares = 1'000'000'000,
        };
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
        StagedAmounts const staged{
            .available = assetAmount(env, vault, assetsAvailable),
            .deployed = assetAmount(env, vault, assetsTotal - assetsAvailable),
            .sharesTotal = sharesTotal,
            .holderShares = 0,
        };
        compareCanBurnShares(env, vault, staged, expected);
    }

    // The owner burns all of the holder's shares (no amount) in an emptied vault.
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
        StagedAmounts const staged{
            .available = vaultUnits(env, vault, 0),
            .sharesTotal = stagedOutstanding,
            .holderShares = static_cast<std::uint64_t>(deposit),
        };
        AppliedVaultTx const cpp = applyClawback(env, vault, owner_, holder_, staged, std::nullopt);
        // No amount is a zero share amount for the model.
        STAmount const all{shareIssue(env, vault), 0};
        LeanVaultResult const lean = leanOwnerBurn(cpp, staged, all);
        expectLawful(lean);
        expectSame(*this, sampleText(staged, all), cpp, lean, tesSUCCESS);
    }

    // Early-exit fee rates in tenth-bips.
    static constexpr std::uint32_t kFee5Pct = 5'000;

    // The vaults a case list runs on; holder_ holds their shares.
    using TestVaults = std::vector<Keylet>;

    // What every test runs on: a vault per asset, the clawback-enabled ones issued by issuer_.
    // Every staged clawback runs on a throwaway view of this one ledger.
    struct Setup
    {
        Keylet mptVault;
        Keylet iouMinScaleVault;
        Keylet iouDefaultScaleVault;
        TestVaults xrp;
        TestVaults mpt;
        TestVaults ious;
        // Vaults whose asset the issuer can claw back (MPT and IOU).
        TestVaults clawable;
        TestVaults all;
    };

    Setup
    setup(jtx::Env& env)
    {
        using namespace jtx;
        using namespace std::chrono_literals;

        env.fund(XRP(1'000'000), owner_, issuer_, holder_);
        env.close();
        // Staged dates reach far before the parent close time, which starts near 0.
        env.close(env.now() + 1'000'000'000s);
        env(fset(issuer_, asfAllowTrustLineClawback));
        env.close();
        PrettyAsset const iou = issuer_["USD"];
        env(trust(holder_, iou(1'000'000)));
        env(pay(issuer_, holder_, iou(1'000)));
        MPTTester mptt{env, issuer_, kMptInitNoFund};
        mptt.create({.flags = tfMPTCanTransfer | tfMPTCanClawback});
        mptt.authorize({.account = holder_});
        PrettyAsset const mpt = mptt.issuanceID();
        // Outstanding MPT (the cap) covers any staged holding the issuer claws back.
        env(pay(issuer_, holder_, mpt(std::numeric_limits<std::int64_t>::max())));
        env.close();

        Keylet const xrpVault = createVault(env, owner_, xrpIssue());
        Keylet const mptVault = createVault(env, owner_, mpt);
        // IOU at the smallest, the default and the largest vault scale.
        Keylet const iouMinScaleVault = createVault(env, owner_, iou, kVaultMinimumIouScale);
        Keylet const iouDefaultScaleVault = createVault(env, owner_, iou, kVaultDefaultIouScale);
        Keylet const iouMaxScaleVault =
            createVault(env, owner_, iou, kFixedPrecisionVaultMaximumIouScale);
        TestVaults const ious{iouMinScaleVault, iouDefaultScaleVault, iouMaxScaleVault};
        TestVaults clawable{mptVault};
        clawable.insert(clawable.end(), ious.begin(), ious.end());
        TestVaults all{xrpVault};
        all.insert(all.end(), clawable.begin(), clawable.end());
        // One unit each: the holder gets its share MPToken and an IOU vault its pseudo-account
        // trust line, which staging state on the vault needs.
        for (Keylet const& vault : all)
        {
            env(jtx::Vault::deposit(
                {.depositor = holder_, .id = vault.key, .amount = vaultUnits(env, vault, 1)}));
        }
        env.close();
        return {
            .mptVault = mptVault,
            .iouMinScaleVault = iouMinScaleVault,
            .iouDefaultScaleVault = iouDefaultScaleVault,
            .xrp = {xrpVault},
            .mpt = {mptVault},
            .ious = ious,
            .clawable = clawable,
            .all = all,
        };
    }

    // Clawback has no phase or fee logic: the issuer recovers the full amount during Investment.
    void
    testClawbackInInvestment(jtx::Env& env, Setup const& s)
    {
        testcase("clawback in investment with a fee");
        Keylet const& vault = s.iouDefaultScaleVault;
        StagedAmounts staged = depositedVault(env, vault, kInitialDepositUnits);
        stagePhase(staged, parentCloseTime(env), VaultPhase::Investment, kFee5Pct);
        StagedClawback const r =
            expectStagedClawback(env, vault, staged, issuer_["USD"](400), tesSUCCESS);
        Number const recovered = r.cpp.pre.assetsAvailable - r.cpp.post.assetsAvailable;
        BEAST_EXPECTS(recovered == Number{400}, "recovered " + to_string(recovered));
    }

    // Each case stages its vault (the holder owns every share unless the row sets holderShares) and
    // either has the asset issuer claw back `amount` vault units from the holder or, with `burn`,
    // has the vault owner burn `amount` of the holder's shares, and expects its verdict on both
    // sides.
    // A group comment names a boundary value (the cusp); its rows step those values around it.
    // - Owner burn: the owner may burn a holder's shares only in an insolvent vault (shares, no
    //   assets; else tecNO_PERMISSION) and only all of them (amount equal to the holder's shares,
    //   or 0; else tecLIMIT_EXCEEDED). Each cusp burns exactly the holder's shares.
    //   Deployed assets with nothing available also refuse the burn (tecNO_PERMISSION).
    // - Owner burn, no shares: burning all of a holder that has none is refused
    //   (tecPRECISION_LOSS).
    // - Zero shares: a clawback burning trunc(shares total * amount / assets total) = 0 shares is
    //   refused (tecPRECISION_LOSS). Each cusp burns exactly one share. Where that share is worth
    //   less than one unit, MPT rounds its recovery up to one unit and an IOU floors it to zero
    //   (tecPRECISION_LOSS), so those rows are split by vault set.
    // - Clamp to zero (IOU): a recovery that floors to zero on the vault grid is refused
    //   (tecPRECISION_LOSS). Each cusp recovers exactly one unit.
    // - Clamp to available: with assets deployed, a sole holder's clawback above the available
    //   assets is reduced to them and the shares re-derived; a clawback at or below them is
    //   recovered as asked, which the rows below each cusp pin. Every row succeeds; it shows in
    //   the post-state and the recovery. Each cusp claws exactly the available assets, at price 1.
    // - Coarse claw-all (IOU): a sole holder's claw-all of coarse available assets (mantissa at
    //   exponent above the grid) converts available + deployed to 16 digits; when the deployed
    //   assets round away every share would be burned with assets still deployed
    //   (tecHAS_OBLIGATIONS), otherwise the recovery clamps to the available assets. Each cusp
    //   deploys exactly half a mantissa step.
    // - Decade crossing (IOU): the recovery is truncated to the grid of available - amount, ten
    //   units from 10^16 units up, so there a one-unit clawback truncates to zero
    //   (tecPRECISION_LOSS). Each cusp leaves exactly 10^16 - 1 or 10^16 units.
    // - Loss waiver: a holder of every share is priced at the assets total, any other at assets
    //   total - loss unrealized. Every row succeeds; it shows in the shares burned.
    // - Share overflow: a clawback whose share count trunc(shares total * amount / assets total)
    //   passes 2^63 - 1 fails (tecPATH_DRY). Each cusp converts to exactly 2^63 - 1 shares.
    // - Holder value: a clawback from one of several holders burning more shares than the holder
    //   owns is refused (tecINSUFFICIENT_FUNDS). Each cusp claws exactly the holder's shares'
    //   worth, at price 1.
    // - Native: XRP cannot be clawed back (tecNO_PERMISSION). The issuer omits the amount, since
    //   an XRP amount is refused in preflight.
    // clang-format off
    static constexpr ClawbackCase kBurn[] = {
        // available 0, sharesTotal 1, holderShares 1, amount 1
        {.vault = {.sharesTotal = 1, .holderShares = 1}, .amount = 0, .expected = tesSUCCESS, .burn = true},
        {.vault = {.available = 1, .sharesTotal = 1, .holderShares = 1}, .amount = 0, .expected = tecNO_PERMISSION, .burn = true},
        {.vault = {.available = 2, .sharesTotal = 1, .holderShares = 1}, .amount = 0, .expected = tecNO_PERMISSION, .burn = true},
        {.vault = {.sharesTotal = 1, .holderShares = 1}, .amount = 1, .expected = tesSUCCESS, .burn = true},
        {.vault = {.available = 1, .sharesTotal = 1, .holderShares = 1}, .amount = 1, .expected = tecNO_PERMISSION, .burn = true},
        {.vault = {.available = 2, .sharesTotal = 1, .holderShares = 1}, .amount = 1, .expected = tecNO_PERMISSION, .burn = true},
        {.vault = {.sharesTotal = 1, .holderShares = 1}, .amount = 2, .expected = tecLIMIT_EXCEEDED, .burn = true},
        {.vault = {.available = 1, .sharesTotal = 1, .holderShares = 1}, .amount = 2, .expected = tecNO_PERMISSION, .burn = true},
        {.vault = {.available = 2, .sharesTotal = 1, .holderShares = 1}, .amount = 2, .expected = tecNO_PERMISSION, .burn = true},
        {.vault = {.sharesTotal = 1, .holderShares = 1}, .amount = 3, .expected = tecLIMIT_EXCEEDED, .burn = true},
        {.vault = {.available = 1, .sharesTotal = 1, .holderShares = 1}, .amount = 3, .expected = tecNO_PERMISSION, .burn = true},
        {.vault = {.available = 2, .sharesTotal = 1, .holderShares = 1}, .amount = 3, .expected = tecNO_PERMISSION, .burn = true},
        // available 0, sharesTotal 1'000'000'000, holderShares 1'000'000'000, amount 1'000'000'000
        {.vault = {.sharesTotal = 1'000'000'000, .holderShares = 1'000'000'000}, .amount = 999'999'998, .expected = tecLIMIT_EXCEEDED, .burn = true},
        {.vault = {.available = 1, .sharesTotal = 1'000'000'000, .holderShares = 1'000'000'000}, .amount = 999'999'998, .expected = tecNO_PERMISSION, .burn = true},
        {.vault = {.available = 2, .sharesTotal = 1'000'000'000, .holderShares = 1'000'000'000}, .amount = 999'999'998, .expected = tecNO_PERMISSION, .burn = true},
        {.vault = {.sharesTotal = 1'000'000'000, .holderShares = 1'000'000'000}, .amount = 999'999'999, .expected = tecLIMIT_EXCEEDED, .burn = true},
        {.vault = {.available = 1, .sharesTotal = 1'000'000'000, .holderShares = 1'000'000'000}, .amount = 999'999'999, .expected = tecNO_PERMISSION, .burn = true},
        {.vault = {.available = 2, .sharesTotal = 1'000'000'000, .holderShares = 1'000'000'000}, .amount = 999'999'999, .expected = tecNO_PERMISSION, .burn = true},
        {.vault = {.sharesTotal = 1'000'000'000, .holderShares = 1'000'000'000}, .amount = 1'000'000'000, .expected = tesSUCCESS, .burn = true},
        {.vault = {.available = 1, .sharesTotal = 1'000'000'000, .holderShares = 1'000'000'000}, .amount = 1'000'000'000, .expected = tecNO_PERMISSION, .burn = true},
        {.vault = {.available = 2, .sharesTotal = 1'000'000'000, .holderShares = 1'000'000'000}, .amount = 1'000'000'000, .expected = tecNO_PERMISSION, .burn = true},
        {.vault = {.sharesTotal = 1'000'000'000, .holderShares = 1'000'000'000}, .amount = 1'000'000'001, .expected = tecLIMIT_EXCEEDED, .burn = true},
        {.vault = {.available = 1, .sharesTotal = 1'000'000'000, .holderShares = 1'000'000'000}, .amount = 1'000'000'001, .expected = tecNO_PERMISSION, .burn = true},
        {.vault = {.available = 2, .sharesTotal = 1'000'000'000, .holderShares = 1'000'000'000}, .amount = 1'000'000'001, .expected = tecNO_PERMISSION, .burn = true},
        {.vault = {.sharesTotal = 1'000'000'000, .holderShares = 1'000'000'000}, .amount = 1'000'000'002, .expected = tecLIMIT_EXCEEDED, .burn = true},
        {.vault = {.available = 1, .sharesTotal = 1'000'000'000, .holderShares = 1'000'000'000}, .amount = 1'000'000'002, .expected = tecNO_PERMISSION, .burn = true},
        {.vault = {.available = 2, .sharesTotal = 1'000'000'000, .holderShares = 1'000'000'000}, .amount = 1'000'000'002, .expected = tecNO_PERMISSION, .burn = true},
        // available 0, sharesTotal 9'223'372'036'854'775'807, holderShares 9'223'372'036'854'775'807, amount 9'223'372'036'854'775'807
        {.vault = {.sharesTotal = 9'223'372'036'854'775'807, .holderShares = 9'223'372'036'854'775'807}, .amount = 9'223'372'036'854'775'805, .expected = tecLIMIT_EXCEEDED, .burn = true},
        {.vault = {.available = 1, .sharesTotal = 9'223'372'036'854'775'807, .holderShares = 9'223'372'036'854'775'807}, .amount = 9'223'372'036'854'775'805, .expected = tecNO_PERMISSION, .burn = true},
        {.vault = {.available = 2, .sharesTotal = 9'223'372'036'854'775'807, .holderShares = 9'223'372'036'854'775'807}, .amount = 9'223'372'036'854'775'805, .expected = tecNO_PERMISSION, .burn = true},
        {.vault = {.sharesTotal = 9'223'372'036'854'775'807, .holderShares = 9'223'372'036'854'775'807}, .amount = 9'223'372'036'854'775'806, .expected = tecLIMIT_EXCEEDED, .burn = true},
        {.vault = {.available = 1, .sharesTotal = 9'223'372'036'854'775'807, .holderShares = 9'223'372'036'854'775'807}, .amount = 9'223'372'036'854'775'806, .expected = tecNO_PERMISSION, .burn = true},
        {.vault = {.available = 2, .sharesTotal = 9'223'372'036'854'775'807, .holderShares = 9'223'372'036'854'775'807}, .amount = 9'223'372'036'854'775'806, .expected = tecNO_PERMISSION, .burn = true},
        {.vault = {.sharesTotal = 9'223'372'036'854'775'807, .holderShares = 9'223'372'036'854'775'807}, .amount = 9'223'372'036'854'775'807, .expected = tesSUCCESS, .burn = true},
        {.vault = {.available = 1, .sharesTotal = 9'223'372'036'854'775'807, .holderShares = 9'223'372'036'854'775'807}, .amount = 9'223'372'036'854'775'807, .expected = tecNO_PERMISSION, .burn = true},
        {.vault = {.available = 2, .sharesTotal = 9'223'372'036'854'775'807, .holderShares = 9'223'372'036'854'775'807}, .amount = 9'223'372'036'854'775'807, .expected = tecNO_PERMISSION, .burn = true},
        // available 0, sharesTotal 1'000'000'000, holderShares 1, amount 1
        {.vault = {.sharesTotal = 1'000'000'000, .holderShares = 1}, .amount = 0, .expected = tesSUCCESS, .burn = true},
        {.vault = {.available = 1, .sharesTotal = 1'000'000'000, .holderShares = 1}, .amount = 0, .expected = tecNO_PERMISSION, .burn = true},
        {.vault = {.available = 2, .sharesTotal = 1'000'000'000, .holderShares = 1}, .amount = 0, .expected = tecNO_PERMISSION, .burn = true},
        {.vault = {.sharesTotal = 1'000'000'000, .holderShares = 1}, .amount = 1, .expected = tesSUCCESS, .burn = true},
        {.vault = {.available = 1, .sharesTotal = 1'000'000'000, .holderShares = 1}, .amount = 1, .expected = tecNO_PERMISSION, .burn = true},
        {.vault = {.available = 2, .sharesTotal = 1'000'000'000, .holderShares = 1}, .amount = 1, .expected = tecNO_PERMISSION, .burn = true},
        {.vault = {.sharesTotal = 1'000'000'000, .holderShares = 1}, .amount = 2, .expected = tecLIMIT_EXCEEDED, .burn = true},
        {.vault = {.available = 1, .sharesTotal = 1'000'000'000, .holderShares = 1}, .amount = 2, .expected = tecNO_PERMISSION, .burn = true},
        {.vault = {.available = 2, .sharesTotal = 1'000'000'000, .holderShares = 1}, .amount = 2, .expected = tecNO_PERMISSION, .burn = true},
        {.vault = {.sharesTotal = 1'000'000'000, .holderShares = 1}, .amount = 3, .expected = tecLIMIT_EXCEEDED, .burn = true},
        {.vault = {.available = 1, .sharesTotal = 1'000'000'000, .holderShares = 1}, .amount = 3, .expected = tecNO_PERMISSION, .burn = true},
        {.vault = {.available = 2, .sharesTotal = 1'000'000'000, .holderShares = 1}, .amount = 3, .expected = tecNO_PERMISSION, .burn = true},
        // available 0, deployed > 0, sharesTotal 1, holderShares 1
        {.vault = {.deployed = 1, .sharesTotal = 1, .holderShares = 1}, .amount = 0, .expected = tecNO_PERMISSION, .burn = true},
        {.vault = {.deployed = 1, .sharesTotal = 1, .holderShares = 1}, .amount = 1, .expected = tecNO_PERMISSION, .burn = true},
        {.vault = {.deployed = 1'000'000'000, .loss = 1'000'000'000, .sharesTotal = 1, .holderShares = 1}, .amount = 1, .expected = tecNO_PERMISSION, .burn = true},
    };
    static constexpr ClawbackCase kBurnNoShares[] = {
        // available 0, sharesTotal 1'000'000'000, holderShares 0, amount 0
        {.vault = {.sharesTotal = 1'000'000'000, .holderShares = 0}, .amount = 0, .expected = tecPRECISION_LOSS, .burn = true},
        {.vault = {.available = 1, .sharesTotal = 1'000'000'000, .holderShares = 0}, .amount = 0, .expected = tecNO_PERMISSION, .burn = true},
        {.vault = {.available = 2, .sharesTotal = 1'000'000'000, .holderShares = 0}, .amount = 0, .expected = tecNO_PERMISSION, .burn = true},
        {.vault = {.sharesTotal = 1'000'000'000, .holderShares = 1}, .amount = 0, .expected = tesSUCCESS, .burn = true},
        {.vault = {.available = 1, .sharesTotal = 1'000'000'000, .holderShares = 1}, .amount = 0, .expected = tecNO_PERMISSION, .burn = true},
        {.vault = {.available = 2, .sharesTotal = 1'000'000'000, .holderShares = 1}, .amount = 0, .expected = tecNO_PERMISSION, .burn = true},
        {.vault = {.sharesTotal = 1'000'000'000, .holderShares = 2}, .amount = 0, .expected = tesSUCCESS, .burn = true},
        {.vault = {.available = 1, .sharesTotal = 1'000'000'000, .holderShares = 2}, .amount = 0, .expected = tecNO_PERMISSION, .burn = true},
        {.vault = {.available = 2, .sharesTotal = 1'000'000'000, .holderShares = 2}, .amount = 0, .expected = tecNO_PERMISSION, .burn = true},
    };
    static constexpr ClawbackCase kZeroShares[] = {
        // total 2, sharesTotal 1, amount 2
        {.vault = {.available = 2, .sharesTotal = 1}, .amount = 1, .expected = tecPRECISION_LOSS},
        {.vault = {.available = 2, .sharesTotal = 1}, .amount = 2, .expected = tesSUCCESS},
        {.vault = {.available = 2, .sharesTotal = 1}, .amount = 3, .expected = tesSUCCESS},
        {.vault = {.available = 2, .sharesTotal = 1}, .amount = 4, .expected = tesSUCCESS},
        {.vault = {.available = 2, .sharesTotal = 2}, .amount = 1, .expected = tesSUCCESS},
        {.vault = {.available = 2, .sharesTotal = 2}, .amount = 2, .expected = tesSUCCESS},
        {.vault = {.available = 2, .sharesTotal = 2}, .amount = 3, .expected = tesSUCCESS},
        {.vault = {.available = 2, .sharesTotal = 2}, .amount = 4, .expected = tesSUCCESS},
        {.vault = {.available = 2, .sharesTotal = 3}, .amount = 2, .expected = tesSUCCESS},
        {.vault = {.available = 2, .sharesTotal = 3}, .amount = 3, .expected = tesSUCCESS},
        {.vault = {.available = 2, .sharesTotal = 3}, .amount = 4, .expected = tesSUCCESS},
        // total 2, sharesTotal 2, amount 1
        {.vault = {.available = 2, .sharesTotal = 1}, .amount = 1, .expected = tecPRECISION_LOSS},
        {.vault = {.available = 2, .sharesTotal = 1}, .amount = 2, .expected = tesSUCCESS},
        {.vault = {.available = 2, .sharesTotal = 1}, .amount = 3, .expected = tesSUCCESS},
        {.vault = {.available = 2, .sharesTotal = 2}, .amount = 1, .expected = tesSUCCESS},
        {.vault = {.available = 2, .sharesTotal = 2}, .amount = 2, .expected = tesSUCCESS},
        {.vault = {.available = 2, .sharesTotal = 2}, .amount = 3, .expected = tesSUCCESS},
        {.vault = {.available = 2, .sharesTotal = 3}, .amount = 2, .expected = tesSUCCESS},
        {.vault = {.available = 2, .sharesTotal = 3}, .amount = 3, .expected = tesSUCCESS},
        {.vault = {.available = 2, .sharesTotal = 4}, .amount = 1, .expected = tesSUCCESS},
        {.vault = {.available = 2, .sharesTotal = 4}, .amount = 2, .expected = tesSUCCESS},
        {.vault = {.available = 2, .sharesTotal = 4}, .amount = 3, .expected = tesSUCCESS},
        // total 1'000'000'000, sharesTotal 1, amount 1'000'000'000
        {.vault = {.available = 1'000'000'000, .sharesTotal = 1}, .amount = 999'999'998, .expected = tecPRECISION_LOSS},
        {.vault = {.available = 1'000'000'000, .sharesTotal = 1}, .amount = 999'999'999, .expected = tecPRECISION_LOSS},
        {.vault = {.available = 1'000'000'000, .sharesTotal = 1}, .amount = 1'000'000'000, .expected = tesSUCCESS},
        {.vault = {.available = 1'000'000'000, .sharesTotal = 1}, .amount = 1'000'000'001, .expected = tesSUCCESS},
        {.vault = {.available = 1'000'000'000, .sharesTotal = 1}, .amount = 1'000'000'002, .expected = tesSUCCESS},
        {.vault = {.available = 1'000'000'000, .sharesTotal = 2}, .amount = 999'999'998, .expected = tesSUCCESS},
        {.vault = {.available = 1'000'000'000, .sharesTotal = 2}, .amount = 999'999'999, .expected = tesSUCCESS},
        {.vault = {.available = 1'000'000'000, .sharesTotal = 2}, .amount = 1'000'000'000, .expected = tesSUCCESS},
        {.vault = {.available = 1'000'000'000, .sharesTotal = 2}, .amount = 1'000'000'001, .expected = tesSUCCESS},
        {.vault = {.available = 1'000'000'000, .sharesTotal = 2}, .amount = 1'000'000'002, .expected = tesSUCCESS},
        {.vault = {.available = 1'000'000'000, .sharesTotal = 3}, .amount = 999'999'998, .expected = tesSUCCESS},
        {.vault = {.available = 1'000'000'000, .sharesTotal = 3}, .amount = 999'999'999, .expected = tesSUCCESS},
        {.vault = {.available = 1'000'000'000, .sharesTotal = 3}, .amount = 1'000'000'000, .expected = tesSUCCESS},
        {.vault = {.available = 1'000'000'000, .sharesTotal = 3}, .amount = 1'000'000'001, .expected = tesSUCCESS},
        {.vault = {.available = 1'000'000'000, .sharesTotal = 3}, .amount = 1'000'000'002, .expected = tesSUCCESS},
        // total 1'000'000'000, sharesTotal 1'000'000'000, amount 1
        {.vault = {.available = 1'000'000'000, .sharesTotal = 999'999'998}, .amount = 1, .expected = tecPRECISION_LOSS},
        {.vault = {.available = 1'000'000'000, .sharesTotal = 999'999'998}, .amount = 2, .expected = tesSUCCESS},
        {.vault = {.available = 1'000'000'000, .sharesTotal = 999'999'998}, .amount = 3, .expected = tesSUCCESS},
        {.vault = {.available = 1'000'000'000, .sharesTotal = 999'999'999}, .amount = 1, .expected = tecPRECISION_LOSS},
        {.vault = {.available = 1'000'000'000, .sharesTotal = 999'999'999}, .amount = 2, .expected = tesSUCCESS},
        {.vault = {.available = 1'000'000'000, .sharesTotal = 999'999'999}, .amount = 3, .expected = tesSUCCESS},
        {.vault = {.available = 1'000'000'000, .sharesTotal = 1'000'000'000}, .amount = 1, .expected = tesSUCCESS},
        {.vault = {.available = 1'000'000'000, .sharesTotal = 1'000'000'000}, .amount = 2, .expected = tesSUCCESS},
        {.vault = {.available = 1'000'000'000, .sharesTotal = 1'000'000'000}, .amount = 3, .expected = tesSUCCESS},
        {.vault = {.available = 1'000'000'000, .sharesTotal = 1'000'000'001}, .amount = 2, .expected = tesSUCCESS},
        {.vault = {.available = 1'000'000'000, .sharesTotal = 1'000'000'001}, .amount = 3, .expected = tesSUCCESS},
        {.vault = {.available = 1'000'000'000, .sharesTotal = 1'000'000'002}, .amount = 2, .expected = tesSUCCESS},
        {.vault = {.available = 1'000'000'000, .sharesTotal = 1'000'000'002}, .amount = 3, .expected = tesSUCCESS},
        // total 1'000'000'000, sharesTotal 31'250, amount 32'000
        {.vault = {.available = 1'000'000'000, .sharesTotal = 31'248}, .amount = 31'998, .expected = tecPRECISION_LOSS},
        {.vault = {.available = 1'000'000'000, .sharesTotal = 31'248}, .amount = 31'999, .expected = tecPRECISION_LOSS},
        {.vault = {.available = 1'000'000'000, .sharesTotal = 31'248}, .amount = 32'000, .expected = tecPRECISION_LOSS},
        {.vault = {.available = 1'000'000'000, .sharesTotal = 31'248}, .amount = 32'001, .expected = tecPRECISION_LOSS},
        {.vault = {.available = 1'000'000'000, .sharesTotal = 31'248}, .amount = 32'002, .expected = tecPRECISION_LOSS},
        {.vault = {.available = 1'000'000'000, .sharesTotal = 31'249}, .amount = 31'998, .expected = tecPRECISION_LOSS},
        {.vault = {.available = 1'000'000'000, .sharesTotal = 31'249}, .amount = 31'999, .expected = tecPRECISION_LOSS},
        {.vault = {.available = 1'000'000'000, .sharesTotal = 31'249}, .amount = 32'000, .expected = tecPRECISION_LOSS},
        {.vault = {.available = 1'000'000'000, .sharesTotal = 31'249}, .amount = 32'001, .expected = tecPRECISION_LOSS},
        {.vault = {.available = 1'000'000'000, .sharesTotal = 31'249}, .amount = 32'002, .expected = tesSUCCESS},
        {.vault = {.available = 1'000'000'000, .sharesTotal = 31'250}, .amount = 31'998, .expected = tecPRECISION_LOSS},
        {.vault = {.available = 1'000'000'000, .sharesTotal = 31'250}, .amount = 31'999, .expected = tecPRECISION_LOSS},
        {.vault = {.available = 1'000'000'000, .sharesTotal = 31'250}, .amount = 32'000, .expected = tesSUCCESS},
        {.vault = {.available = 1'000'000'000, .sharesTotal = 31'250}, .amount = 32'001, .expected = tesSUCCESS},
        {.vault = {.available = 1'000'000'000, .sharesTotal = 31'250}, .amount = 32'002, .expected = tesSUCCESS},
        {.vault = {.available = 1'000'000'000, .sharesTotal = 31'251}, .amount = 31'998, .expected = tecPRECISION_LOSS},
        {.vault = {.available = 1'000'000'000, .sharesTotal = 31'251}, .amount = 31'999, .expected = tesSUCCESS},
        {.vault = {.available = 1'000'000'000, .sharesTotal = 31'251}, .amount = 32'000, .expected = tesSUCCESS},
        {.vault = {.available = 1'000'000'000, .sharesTotal = 31'251}, .amount = 32'001, .expected = tesSUCCESS},
        {.vault = {.available = 1'000'000'000, .sharesTotal = 31'251}, .amount = 32'002, .expected = tesSUCCESS},
        {.vault = {.available = 1'000'000'000, .sharesTotal = 31'252}, .amount = 31'998, .expected = tesSUCCESS},
        {.vault = {.available = 1'000'000'000, .sharesTotal = 31'252}, .amount = 31'999, .expected = tesSUCCESS},
        {.vault = {.available = 1'000'000'000, .sharesTotal = 31'252}, .amount = 32'000, .expected = tesSUCCESS},
        {.vault = {.available = 1'000'000'000, .sharesTotal = 31'252}, .amount = 32'001, .expected = tesSUCCESS},
        {.vault = {.available = 1'000'000'000, .sharesTotal = 31'252}, .amount = 32'002, .expected = tesSUCCESS},
    };
    static constexpr ClawbackCase kZeroSharesMpt[] = {
        // total 2, sharesTotal 1, amount 2
        {.vault = {.available = 2, .sharesTotal = 3}, .amount = 1, .expected = tesSUCCESS},
        // total 2, sharesTotal 2, amount 1
        {.vault = {.available = 2, .sharesTotal = 3}, .amount = 1, .expected = tesSUCCESS},
        // total 1'000'000'000, sharesTotal 1'000'000'000, amount 1
        {.vault = {.available = 1'000'000'000, .sharesTotal = 1'000'000'001}, .amount = 1, .expected = tesSUCCESS},
        {.vault = {.available = 1'000'000'000, .sharesTotal = 1'000'000'002}, .amount = 1, .expected = tesSUCCESS},
    };
    static constexpr ClawbackCase kZeroSharesIou[] = {
        // total 2, sharesTotal 1, amount 2
        {.vault = {.available = 2, .sharesTotal = 3}, .amount = 1, .expected = tecPRECISION_LOSS},
        // total 2, sharesTotal 2, amount 1
        {.vault = {.available = 2, .sharesTotal = 3}, .amount = 1, .expected = tecPRECISION_LOSS},
        // total 1'000'000'000, sharesTotal 1'000'000'000, amount 1
        {.vault = {.available = 1'000'000'000, .sharesTotal = 1'000'000'001}, .amount = 1, .expected = tecPRECISION_LOSS},
        {.vault = {.available = 1'000'000'000, .sharesTotal = 1'000'000'002}, .amount = 1, .expected = tecPRECISION_LOSS},
    };
    static constexpr ClawbackCase kClampToZero[] = {
        // total 2, sharesTotal 2, amount 1
        {.vault = {.available = 2, .sharesTotal = 1}, .amount = 1, .expected = tecPRECISION_LOSS},
        {.vault = {.available = 2, .sharesTotal = 1}, .amount = 2, .expected = tesSUCCESS},
        {.vault = {.available = 2, .sharesTotal = 1}, .amount = 3, .expected = tesSUCCESS},
        {.vault = {.available = 2, .sharesTotal = 2}, .amount = 1, .expected = tesSUCCESS},
        {.vault = {.available = 2, .sharesTotal = 2}, .amount = 2, .expected = tesSUCCESS},
        {.vault = {.available = 2, .sharesTotal = 2}, .amount = 3, .expected = tesSUCCESS},
        {.vault = {.available = 2, .sharesTotal = 3}, .amount = 1, .expected = tecPRECISION_LOSS},
        {.vault = {.available = 2, .sharesTotal = 3}, .amount = 2, .expected = tesSUCCESS},
        {.vault = {.available = 2, .sharesTotal = 3}, .amount = 3, .expected = tesSUCCESS},
        {.vault = {.available = 2, .sharesTotal = 4}, .amount = 1, .expected = tesSUCCESS},
        {.vault = {.available = 2, .sharesTotal = 4}, .amount = 2, .expected = tesSUCCESS},
        {.vault = {.available = 2, .sharesTotal = 4}, .amount = 3, .expected = tesSUCCESS},
        // total 2, sharesTotal 2'000, amount 1
        {.vault = {.available = 2, .sharesTotal = 1'998}, .amount = 1, .expected = tesSUCCESS},
        {.vault = {.available = 2, .sharesTotal = 1'998}, .amount = 2, .expected = tesSUCCESS},
        {.vault = {.available = 2, .sharesTotal = 1'998}, .amount = 3, .expected = tesSUCCESS},
        {.vault = {.available = 2, .sharesTotal = 1'999}, .amount = 1, .expected = tecPRECISION_LOSS},
        {.vault = {.available = 2, .sharesTotal = 1'999}, .amount = 2, .expected = tesSUCCESS},
        {.vault = {.available = 2, .sharesTotal = 1'999}, .amount = 3, .expected = tesSUCCESS},
        {.vault = {.available = 2, .sharesTotal = 2'000}, .amount = 1, .expected = tesSUCCESS},
        {.vault = {.available = 2, .sharesTotal = 2'000}, .amount = 2, .expected = tesSUCCESS},
        {.vault = {.available = 2, .sharesTotal = 2'000}, .amount = 3, .expected = tesSUCCESS},
        {.vault = {.available = 2, .sharesTotal = 2'001}, .amount = 1, .expected = tecPRECISION_LOSS},
        {.vault = {.available = 2, .sharesTotal = 2'001}, .amount = 2, .expected = tesSUCCESS},
        {.vault = {.available = 2, .sharesTotal = 2'001}, .amount = 3, .expected = tesSUCCESS},
        {.vault = {.available = 2, .sharesTotal = 2'002}, .amount = 1, .expected = tesSUCCESS},
        {.vault = {.available = 2, .sharesTotal = 2'002}, .amount = 2, .expected = tesSUCCESS},
        {.vault = {.available = 2, .sharesTotal = 2'002}, .amount = 3, .expected = tesSUCCESS},
        // total 2, sharesTotal 9'999'999'999'999'996, amount 1
        {.vault = {.available = 2, .sharesTotal = 9'999'999'999'999'994}, .amount = 1, .expected = tesSUCCESS},
        {.vault = {.available = 2, .sharesTotal = 9'999'999'999'999'994}, .amount = 2, .expected = tesSUCCESS},
        {.vault = {.available = 2, .sharesTotal = 9'999'999'999'999'994}, .amount = 3, .expected = tesSUCCESS},
        {.vault = {.available = 2, .sharesTotal = 9'999'999'999'999'995}, .amount = 1, .expected = tecPRECISION_LOSS},
        {.vault = {.available = 2, .sharesTotal = 9'999'999'999'999'995}, .amount = 2, .expected = tesSUCCESS},
        {.vault = {.available = 2, .sharesTotal = 9'999'999'999'999'995}, .amount = 3, .expected = tesSUCCESS},
        {.vault = {.available = 2, .sharesTotal = 9'999'999'999'999'996}, .amount = 1, .expected = tesSUCCESS},
        {.vault = {.available = 2, .sharesTotal = 9'999'999'999'999'996}, .amount = 2, .expected = tesSUCCESS},
        {.vault = {.available = 2, .sharesTotal = 9'999'999'999'999'996}, .amount = 3, .expected = tesSUCCESS},
        {.vault = {.available = 2, .sharesTotal = 9'999'999'999'999'997}, .amount = 1, .expected = tecPRECISION_LOSS},
        {.vault = {.available = 2, .sharesTotal = 9'999'999'999'999'997}, .amount = 2, .expected = tesSUCCESS},
        {.vault = {.available = 2, .sharesTotal = 9'999'999'999'999'997}, .amount = 3, .expected = tesSUCCESS},
        {.vault = {.available = 2, .sharesTotal = 9'999'999'999'999'998}, .amount = 1, .expected = tesSUCCESS},
        {.vault = {.available = 2, .sharesTotal = 9'999'999'999'999'998}, .amount = 2, .expected = tesSUCCESS},
        {.vault = {.available = 2, .sharesTotal = 9'999'999'999'999'998}, .amount = 3, .expected = tesSUCCESS},
        // total 1'000'000'000, sharesTotal 1'000'000'000, amount 1
        {.vault = {.available = 1'000'000'000, .sharesTotal = 999'999'998}, .amount = 1, .expected = tecPRECISION_LOSS},
        {.vault = {.available = 1'000'000'000, .sharesTotal = 999'999'998}, .amount = 2, .expected = tesSUCCESS},
        {.vault = {.available = 1'000'000'000, .sharesTotal = 999'999'998}, .amount = 3, .expected = tesSUCCESS},
        {.vault = {.available = 1'000'000'000, .sharesTotal = 999'999'999}, .amount = 1, .expected = tecPRECISION_LOSS},
        {.vault = {.available = 1'000'000'000, .sharesTotal = 999'999'999}, .amount = 2, .expected = tesSUCCESS},
        {.vault = {.available = 1'000'000'000, .sharesTotal = 999'999'999}, .amount = 3, .expected = tesSUCCESS},
        {.vault = {.available = 1'000'000'000, .sharesTotal = 1'000'000'000}, .amount = 1, .expected = tesSUCCESS},
        {.vault = {.available = 1'000'000'000, .sharesTotal = 1'000'000'000}, .amount = 2, .expected = tesSUCCESS},
        {.vault = {.available = 1'000'000'000, .sharesTotal = 1'000'000'000}, .amount = 3, .expected = tesSUCCESS},
        {.vault = {.available = 1'000'000'000, .sharesTotal = 1'000'000'001}, .amount = 1, .expected = tecPRECISION_LOSS},
        {.vault = {.available = 1'000'000'000, .sharesTotal = 1'000'000'001}, .amount = 2, .expected = tesSUCCESS},
        {.vault = {.available = 1'000'000'000, .sharesTotal = 1'000'000'001}, .amount = 3, .expected = tesSUCCESS},
        {.vault = {.available = 1'000'000'000, .sharesTotal = 1'000'000'002}, .amount = 1, .expected = tecPRECISION_LOSS},
        {.vault = {.available = 1'000'000'000, .sharesTotal = 1'000'000'002}, .amount = 2, .expected = tesSUCCESS},
        {.vault = {.available = 1'000'000'000, .sharesTotal = 1'000'000'002}, .amount = 3, .expected = tesSUCCESS},
        // total 1'000'000'000, sharesTotal 1'000'000'000'000, amount 1
        {.vault = {.available = 1'000'000'000, .sharesTotal = 999'999'999'998}, .amount = 1, .expected = tecPRECISION_LOSS},
        {.vault = {.available = 1'000'000'000, .sharesTotal = 999'999'999'998}, .amount = 2, .expected = tesSUCCESS},
        {.vault = {.available = 1'000'000'000, .sharesTotal = 999'999'999'998}, .amount = 3, .expected = tesSUCCESS},
        {.vault = {.available = 1'000'000'000, .sharesTotal = 999'999'999'999}, .amount = 1, .expected = tecPRECISION_LOSS},
        {.vault = {.available = 1'000'000'000, .sharesTotal = 999'999'999'999}, .amount = 2, .expected = tesSUCCESS},
        {.vault = {.available = 1'000'000'000, .sharesTotal = 999'999'999'999}, .amount = 3, .expected = tesSUCCESS},
        {.vault = {.available = 1'000'000'000, .sharesTotal = 1'000'000'000'000}, .amount = 1, .expected = tesSUCCESS},
        {.vault = {.available = 1'000'000'000, .sharesTotal = 1'000'000'000'000}, .amount = 2, .expected = tesSUCCESS},
        {.vault = {.available = 1'000'000'000, .sharesTotal = 1'000'000'000'000}, .amount = 3, .expected = tesSUCCESS},
        {.vault = {.available = 1'000'000'000, .sharesTotal = 1'000'000'000'001}, .amount = 1, .expected = tecPRECISION_LOSS},
        {.vault = {.available = 1'000'000'000, .sharesTotal = 1'000'000'000'001}, .amount = 2, .expected = tesSUCCESS},
        {.vault = {.available = 1'000'000'000, .sharesTotal = 1'000'000'000'001}, .amount = 3, .expected = tesSUCCESS},
        {.vault = {.available = 1'000'000'000, .sharesTotal = 1'000'000'000'002}, .amount = 1, .expected = tecPRECISION_LOSS},
        {.vault = {.available = 1'000'000'000, .sharesTotal = 1'000'000'000'002}, .amount = 2, .expected = tesSUCCESS},
        {.vault = {.available = 1'000'000'000, .sharesTotal = 1'000'000'000'002}, .amount = 3, .expected = tesSUCCESS},
        // total 1'000'000'000, sharesTotal 9'999'999'000'000'000, amount 1
        {.vault = {.available = 1'000'000'000, .sharesTotal = 9'999'998'999'999'998}, .amount = 1, .expected = tecPRECISION_LOSS},
        {.vault = {.available = 1'000'000'000, .sharesTotal = 9'999'998'999'999'998}, .amount = 2, .expected = tesSUCCESS},
        {.vault = {.available = 1'000'000'000, .sharesTotal = 9'999'998'999'999'998}, .amount = 3, .expected = tesSUCCESS},
        {.vault = {.available = 1'000'000'000, .sharesTotal = 9'999'998'999'999'999}, .amount = 1, .expected = tecPRECISION_LOSS},
        {.vault = {.available = 1'000'000'000, .sharesTotal = 9'999'998'999'999'999}, .amount = 2, .expected = tesSUCCESS},
        {.vault = {.available = 1'000'000'000, .sharesTotal = 9'999'998'999'999'999}, .amount = 3, .expected = tesSUCCESS},
        {.vault = {.available = 1'000'000'000, .sharesTotal = 9'999'999'000'000'000}, .amount = 1, .expected = tesSUCCESS},
        {.vault = {.available = 1'000'000'000, .sharesTotal = 9'999'999'000'000'000}, .amount = 2, .expected = tesSUCCESS},
        {.vault = {.available = 1'000'000'000, .sharesTotal = 9'999'999'000'000'000}, .amount = 3, .expected = tesSUCCESS},
        {.vault = {.available = 1'000'000'000, .sharesTotal = 9'999'999'000'000'001}, .amount = 1, .expected = tecPRECISION_LOSS},
        {.vault = {.available = 1'000'000'000, .sharesTotal = 9'999'999'000'000'001}, .amount = 2, .expected = tesSUCCESS},
        {.vault = {.available = 1'000'000'000, .sharesTotal = 9'999'999'000'000'001}, .amount = 3, .expected = tesSUCCESS},
        {.vault = {.available = 1'000'000'000, .sharesTotal = 9'999'999'000'000'002}, .amount = 1, .expected = tecPRECISION_LOSS},
        {.vault = {.available = 1'000'000'000, .sharesTotal = 9'999'999'000'000'002}, .amount = 2, .expected = tesSUCCESS},
        {.vault = {.available = 1'000'000'000, .sharesTotal = 9'999'999'000'000'002}, .amount = 3, .expected = tesSUCCESS},
    };
    static constexpr ClawbackCase kAvailable[] = {
        // available 3, deployed 1, amount 3
        {.vault = {.available = 1, .deployed = 1, .sharesTotal = 2}, .amount = 1, .expected = tesSUCCESS},
        {.vault = {.available = 2, .deployed = 1, .sharesTotal = 3}, .amount = 1, .expected = tesSUCCESS},
        {.vault = {.available = 3, .deployed = 1, .sharesTotal = 4}, .amount = 1, .expected = tesSUCCESS},
        {.vault = {.available = 4, .deployed = 1, .sharesTotal = 5}, .amount = 1, .expected = tesSUCCESS},
        {.vault = {.available = 5, .deployed = 1, .sharesTotal = 6}, .amount = 1, .expected = tesSUCCESS},
        {.vault = {.available = 1, .deployed = 1, .sharesTotal = 2}, .amount = 2, .expected = tesSUCCESS},
        {.vault = {.available = 2, .deployed = 1, .sharesTotal = 3}, .amount = 2, .expected = tesSUCCESS},
        {.vault = {.available = 3, .deployed = 1, .sharesTotal = 4}, .amount = 2, .expected = tesSUCCESS},
        {.vault = {.available = 4, .deployed = 1, .sharesTotal = 5}, .amount = 2, .expected = tesSUCCESS},
        {.vault = {.available = 5, .deployed = 1, .sharesTotal = 6}, .amount = 2, .expected = tesSUCCESS},
        {.vault = {.available = 1, .deployed = 1, .sharesTotal = 2}, .amount = 3, .expected = tesSUCCESS},
        {.vault = {.available = 2, .deployed = 1, .sharesTotal = 3}, .amount = 3, .expected = tesSUCCESS},
        {.vault = {.available = 3, .deployed = 1, .sharesTotal = 4}, .amount = 3, .expected = tesSUCCESS},
        {.vault = {.available = 4, .deployed = 1, .sharesTotal = 5}, .amount = 3, .expected = tesSUCCESS},
        {.vault = {.available = 5, .deployed = 1, .sharesTotal = 6}, .amount = 3, .expected = tesSUCCESS},
        {.vault = {.available = 1, .deployed = 1, .sharesTotal = 2}, .amount = 4, .expected = tesSUCCESS},
        {.vault = {.available = 2, .deployed = 1, .sharesTotal = 3}, .amount = 4, .expected = tesSUCCESS},
        {.vault = {.available = 3, .deployed = 1, .sharesTotal = 4}, .amount = 4, .expected = tesSUCCESS},
        {.vault = {.available = 4, .deployed = 1, .sharesTotal = 5}, .amount = 4, .expected = tesSUCCESS},
        {.vault = {.available = 5, .deployed = 1, .sharesTotal = 6}, .amount = 4, .expected = tesSUCCESS},
        {.vault = {.available = 1, .deployed = 1, .sharesTotal = 2}, .amount = 5, .expected = tesSUCCESS},
        {.vault = {.available = 2, .deployed = 1, .sharesTotal = 3}, .amount = 5, .expected = tesSUCCESS},
        {.vault = {.available = 3, .deployed = 1, .sharesTotal = 4}, .amount = 5, .expected = tesSUCCESS},
        {.vault = {.available = 4, .deployed = 1, .sharesTotal = 5}, .amount = 5, .expected = tesSUCCESS},
        {.vault = {.available = 5, .deployed = 1, .sharesTotal = 6}, .amount = 5, .expected = tesSUCCESS},
        // available 1'000'000'000, deployed 1, amount 1'000'000'000
        {.vault = {.available = 999'999'998, .deployed = 1, .sharesTotal = 999'999'999}, .amount = 999'999'998, .expected = tesSUCCESS},
        {.vault = {.available = 999'999'999, .deployed = 1, .sharesTotal = 1'000'000'000}, .amount = 999'999'998, .expected = tesSUCCESS},
        {.vault = {.available = 1'000'000'000, .deployed = 1, .sharesTotal = 1'000'000'001}, .amount = 999'999'998, .expected = tesSUCCESS},
        {.vault = {.available = 1'000'000'001, .deployed = 1, .sharesTotal = 1'000'000'002}, .amount = 999'999'998, .expected = tesSUCCESS},
        {.vault = {.available = 1'000'000'002, .deployed = 1, .sharesTotal = 1'000'000'003}, .amount = 999'999'998, .expected = tesSUCCESS},
        {.vault = {.available = 999'999'998, .deployed = 1, .sharesTotal = 999'999'999}, .amount = 999'999'999, .expected = tesSUCCESS},
        {.vault = {.available = 999'999'999, .deployed = 1, .sharesTotal = 1'000'000'000}, .amount = 999'999'999, .expected = tesSUCCESS},
        {.vault = {.available = 1'000'000'000, .deployed = 1, .sharesTotal = 1'000'000'001}, .amount = 999'999'999, .expected = tesSUCCESS},
        {.vault = {.available = 1'000'000'001, .deployed = 1, .sharesTotal = 1'000'000'002}, .amount = 999'999'999, .expected = tesSUCCESS},
        {.vault = {.available = 1'000'000'002, .deployed = 1, .sharesTotal = 1'000'000'003}, .amount = 999'999'999, .expected = tesSUCCESS},
        {.vault = {.available = 999'999'998, .deployed = 1, .sharesTotal = 999'999'999}, .amount = 1'000'000'000, .expected = tesSUCCESS},
        {.vault = {.available = 999'999'999, .deployed = 1, .sharesTotal = 1'000'000'000}, .amount = 1'000'000'000, .expected = tesSUCCESS},
        {.vault = {.available = 1'000'000'000, .deployed = 1, .sharesTotal = 1'000'000'001}, .amount = 1'000'000'000, .expected = tesSUCCESS},
        {.vault = {.available = 1'000'000'001, .deployed = 1, .sharesTotal = 1'000'000'002}, .amount = 1'000'000'000, .expected = tesSUCCESS},
        {.vault = {.available = 1'000'000'002, .deployed = 1, .sharesTotal = 1'000'000'003}, .amount = 1'000'000'000, .expected = tesSUCCESS},
        {.vault = {.available = 999'999'998, .deployed = 1, .sharesTotal = 999'999'999}, .amount = 1'000'000'001, .expected = tesSUCCESS},
        {.vault = {.available = 999'999'999, .deployed = 1, .sharesTotal = 1'000'000'000}, .amount = 1'000'000'001, .expected = tesSUCCESS},
        {.vault = {.available = 1'000'000'000, .deployed = 1, .sharesTotal = 1'000'000'001}, .amount = 1'000'000'001, .expected = tesSUCCESS},
        {.vault = {.available = 1'000'000'001, .deployed = 1, .sharesTotal = 1'000'000'002}, .amount = 1'000'000'001, .expected = tesSUCCESS},
        {.vault = {.available = 1'000'000'002, .deployed = 1, .sharesTotal = 1'000'000'003}, .amount = 1'000'000'001, .expected = tesSUCCESS},
        {.vault = {.available = 999'999'998, .deployed = 1, .sharesTotal = 999'999'999}, .amount = 1'000'000'002, .expected = tesSUCCESS},
        {.vault = {.available = 999'999'999, .deployed = 1, .sharesTotal = 1'000'000'000}, .amount = 1'000'000'002, .expected = tesSUCCESS},
        {.vault = {.available = 1'000'000'000, .deployed = 1, .sharesTotal = 1'000'000'001}, .amount = 1'000'000'002, .expected = tesSUCCESS},
        {.vault = {.available = 1'000'000'001, .deployed = 1, .sharesTotal = 1'000'000'002}, .amount = 1'000'000'002, .expected = tesSUCCESS},
        {.vault = {.available = 1'000'000'002, .deployed = 1, .sharesTotal = 1'000'000'003}, .amount = 1'000'000'002, .expected = tesSUCCESS},
        // available 1'000'000'000, deployed 1'000'000'000, amount 1'000'000'000
        {.vault = {.available = 999'999'998, .deployed = 1'000'000'000, .sharesTotal = 1'999'999'998}, .amount = 999'999'998, .expected = tesSUCCESS},
        {.vault = {.available = 999'999'999, .deployed = 1'000'000'000, .sharesTotal = 1'999'999'999}, .amount = 999'999'998, .expected = tesSUCCESS},
        {.vault = {.available = 1'000'000'000, .deployed = 1'000'000'000, .sharesTotal = 2'000'000'000}, .amount = 999'999'998, .expected = tesSUCCESS},
        {.vault = {.available = 1'000'000'001, .deployed = 1'000'000'000, .sharesTotal = 2'000'000'001}, .amount = 999'999'998, .expected = tesSUCCESS},
        {.vault = {.available = 1'000'000'002, .deployed = 1'000'000'000, .sharesTotal = 2'000'000'002}, .amount = 999'999'998, .expected = tesSUCCESS},
        {.vault = {.available = 999'999'998, .deployed = 1'000'000'000, .sharesTotal = 1'999'999'998}, .amount = 999'999'999, .expected = tesSUCCESS},
        {.vault = {.available = 999'999'999, .deployed = 1'000'000'000, .sharesTotal = 1'999'999'999}, .amount = 999'999'999, .expected = tesSUCCESS},
        {.vault = {.available = 1'000'000'000, .deployed = 1'000'000'000, .sharesTotal = 2'000'000'000}, .amount = 999'999'999, .expected = tesSUCCESS},
        {.vault = {.available = 1'000'000'001, .deployed = 1'000'000'000, .sharesTotal = 2'000'000'001}, .amount = 999'999'999, .expected = tesSUCCESS},
        {.vault = {.available = 1'000'000'002, .deployed = 1'000'000'000, .sharesTotal = 2'000'000'002}, .amount = 999'999'999, .expected = tesSUCCESS},
        {.vault = {.available = 999'999'998, .deployed = 1'000'000'000, .sharesTotal = 1'999'999'998}, .amount = 1'000'000'000, .expected = tesSUCCESS},
        {.vault = {.available = 999'999'999, .deployed = 1'000'000'000, .sharesTotal = 1'999'999'999}, .amount = 1'000'000'000, .expected = tesSUCCESS},
        {.vault = {.available = 1'000'000'000, .deployed = 1'000'000'000, .sharesTotal = 2'000'000'000}, .amount = 1'000'000'000, .expected = tesSUCCESS},
        {.vault = {.available = 1'000'000'001, .deployed = 1'000'000'000, .sharesTotal = 2'000'000'001}, .amount = 1'000'000'000, .expected = tesSUCCESS},
        {.vault = {.available = 1'000'000'002, .deployed = 1'000'000'000, .sharesTotal = 2'000'000'002}, .amount = 1'000'000'000, .expected = tesSUCCESS},
        {.vault = {.available = 999'999'998, .deployed = 1'000'000'000, .sharesTotal = 1'999'999'998}, .amount = 1'000'000'001, .expected = tesSUCCESS},
        {.vault = {.available = 999'999'999, .deployed = 1'000'000'000, .sharesTotal = 1'999'999'999}, .amount = 1'000'000'001, .expected = tesSUCCESS},
        {.vault = {.available = 1'000'000'000, .deployed = 1'000'000'000, .sharesTotal = 2'000'000'000}, .amount = 1'000'000'001, .expected = tesSUCCESS},
        {.vault = {.available = 1'000'000'001, .deployed = 1'000'000'000, .sharesTotal = 2'000'000'001}, .amount = 1'000'000'001, .expected = tesSUCCESS},
        {.vault = {.available = 1'000'000'002, .deployed = 1'000'000'000, .sharesTotal = 2'000'000'002}, .amount = 1'000'000'001, .expected = tesSUCCESS},
        {.vault = {.available = 999'999'998, .deployed = 1'000'000'000, .sharesTotal = 1'999'999'998}, .amount = 1'000'000'002, .expected = tesSUCCESS},
        {.vault = {.available = 999'999'999, .deployed = 1'000'000'000, .sharesTotal = 1'999'999'999}, .amount = 1'000'000'002, .expected = tesSUCCESS},
        {.vault = {.available = 1'000'000'000, .deployed = 1'000'000'000, .sharesTotal = 2'000'000'000}, .amount = 1'000'000'002, .expected = tesSUCCESS},
        {.vault = {.available = 1'000'000'001, .deployed = 1'000'000'000, .sharesTotal = 2'000'000'001}, .amount = 1'000'000'002, .expected = tesSUCCESS},
        {.vault = {.available = 1'000'000'002, .deployed = 1'000'000'000, .sharesTotal = 2'000'000'002}, .amount = 1'000'000'002, .expected = tesSUCCESS},
        // available 3, deployed 1'000'000'000, amount 3
        {.vault = {.available = 1, .deployed = 1'000'000'000, .sharesTotal = 1'000'000'001}, .amount = 1, .expected = tesSUCCESS},
        {.vault = {.available = 2, .deployed = 1'000'000'000, .sharesTotal = 1'000'000'002}, .amount = 1, .expected = tesSUCCESS},
        {.vault = {.available = 3, .deployed = 1'000'000'000, .sharesTotal = 1'000'000'003}, .amount = 1, .expected = tesSUCCESS},
        {.vault = {.available = 4, .deployed = 1'000'000'000, .sharesTotal = 1'000'000'004}, .amount = 1, .expected = tesSUCCESS},
        {.vault = {.available = 5, .deployed = 1'000'000'000, .sharesTotal = 1'000'000'005}, .amount = 1, .expected = tesSUCCESS},
        {.vault = {.available = 1, .deployed = 1'000'000'000, .sharesTotal = 1'000'000'001}, .amount = 2, .expected = tesSUCCESS},
        {.vault = {.available = 2, .deployed = 1'000'000'000, .sharesTotal = 1'000'000'002}, .amount = 2, .expected = tesSUCCESS},
        {.vault = {.available = 3, .deployed = 1'000'000'000, .sharesTotal = 1'000'000'003}, .amount = 2, .expected = tesSUCCESS},
        {.vault = {.available = 4, .deployed = 1'000'000'000, .sharesTotal = 1'000'000'004}, .amount = 2, .expected = tesSUCCESS},
        {.vault = {.available = 5, .deployed = 1'000'000'000, .sharesTotal = 1'000'000'005}, .amount = 2, .expected = tesSUCCESS},
        {.vault = {.available = 1, .deployed = 1'000'000'000, .sharesTotal = 1'000'000'001}, .amount = 3, .expected = tesSUCCESS},
        {.vault = {.available = 2, .deployed = 1'000'000'000, .sharesTotal = 1'000'000'002}, .amount = 3, .expected = tesSUCCESS},
        {.vault = {.available = 3, .deployed = 1'000'000'000, .sharesTotal = 1'000'000'003}, .amount = 3, .expected = tesSUCCESS},
        {.vault = {.available = 4, .deployed = 1'000'000'000, .sharesTotal = 1'000'000'004}, .amount = 3, .expected = tesSUCCESS},
        {.vault = {.available = 5, .deployed = 1'000'000'000, .sharesTotal = 1'000'000'005}, .amount = 3, .expected = tesSUCCESS},
        {.vault = {.available = 1, .deployed = 1'000'000'000, .sharesTotal = 1'000'000'001}, .amount = 4, .expected = tesSUCCESS},
        {.vault = {.available = 2, .deployed = 1'000'000'000, .sharesTotal = 1'000'000'002}, .amount = 4, .expected = tesSUCCESS},
        {.vault = {.available = 3, .deployed = 1'000'000'000, .sharesTotal = 1'000'000'003}, .amount = 4, .expected = tesSUCCESS},
        {.vault = {.available = 4, .deployed = 1'000'000'000, .sharesTotal = 1'000'000'004}, .amount = 4, .expected = tesSUCCESS},
        {.vault = {.available = 5, .deployed = 1'000'000'000, .sharesTotal = 1'000'000'005}, .amount = 4, .expected = tesSUCCESS},
        {.vault = {.available = 1, .deployed = 1'000'000'000, .sharesTotal = 1'000'000'001}, .amount = 5, .expected = tesSUCCESS},
        {.vault = {.available = 2, .deployed = 1'000'000'000, .sharesTotal = 1'000'000'002}, .amount = 5, .expected = tesSUCCESS},
        {.vault = {.available = 3, .deployed = 1'000'000'000, .sharesTotal = 1'000'000'003}, .amount = 5, .expected = tesSUCCESS},
        {.vault = {.available = 4, .deployed = 1'000'000'000, .sharesTotal = 1'000'000'004}, .amount = 5, .expected = tesSUCCESS},
        {.vault = {.available = 5, .deployed = 1'000'000'000, .sharesTotal = 1'000'000'005}, .amount = 5, .expected = tesSUCCESS},
        // available 3, deployed 9'999'999'999'999'994, amount 3
        {.vault = {.available = 1, .deployed = 9'999'999'999'999'994, .sharesTotal = 9'999'999'999'999'995}, .amount = 1, .expected = tesSUCCESS},
        {.vault = {.available = 2, .deployed = 9'999'999'999'999'994, .sharesTotal = 9'999'999'999'999'996}, .amount = 1, .expected = tesSUCCESS},
        {.vault = {.available = 3, .deployed = 9'999'999'999'999'994, .sharesTotal = 9'999'999'999'999'997}, .amount = 1, .expected = tesSUCCESS},
        {.vault = {.available = 4, .deployed = 9'999'999'999'999'994, .sharesTotal = 9'999'999'999'999'998}, .amount = 1, .expected = tesSUCCESS},
        {.vault = {.available = 5, .deployed = 9'999'999'999'999'994, .sharesTotal = 9'999'999'999'999'999}, .amount = 1, .expected = tesSUCCESS},
        {.vault = {.available = 1, .deployed = 9'999'999'999'999'994, .sharesTotal = 9'999'999'999'999'995}, .amount = 2, .expected = tesSUCCESS},
        {.vault = {.available = 2, .deployed = 9'999'999'999'999'994, .sharesTotal = 9'999'999'999'999'996}, .amount = 2, .expected = tesSUCCESS},
        {.vault = {.available = 3, .deployed = 9'999'999'999'999'994, .sharesTotal = 9'999'999'999'999'997}, .amount = 2, .expected = tesSUCCESS},
        {.vault = {.available = 4, .deployed = 9'999'999'999'999'994, .sharesTotal = 9'999'999'999'999'998}, .amount = 2, .expected = tesSUCCESS},
        {.vault = {.available = 5, .deployed = 9'999'999'999'999'994, .sharesTotal = 9'999'999'999'999'999}, .amount = 2, .expected = tesSUCCESS},
        {.vault = {.available = 1, .deployed = 9'999'999'999'999'994, .sharesTotal = 9'999'999'999'999'995}, .amount = 3, .expected = tesSUCCESS},
        {.vault = {.available = 2, .deployed = 9'999'999'999'999'994, .sharesTotal = 9'999'999'999'999'996}, .amount = 3, .expected = tesSUCCESS},
        {.vault = {.available = 3, .deployed = 9'999'999'999'999'994, .sharesTotal = 9'999'999'999'999'997}, .amount = 3, .expected = tesSUCCESS},
        {.vault = {.available = 4, .deployed = 9'999'999'999'999'994, .sharesTotal = 9'999'999'999'999'998}, .amount = 3, .expected = tesSUCCESS},
        {.vault = {.available = 5, .deployed = 9'999'999'999'999'994, .sharesTotal = 9'999'999'999'999'999}, .amount = 3, .expected = tesSUCCESS},
        {.vault = {.available = 1, .deployed = 9'999'999'999'999'994, .sharesTotal = 9'999'999'999'999'995}, .amount = 4, .expected = tesSUCCESS},
        {.vault = {.available = 2, .deployed = 9'999'999'999'999'994, .sharesTotal = 9'999'999'999'999'996}, .amount = 4, .expected = tesSUCCESS},
        {.vault = {.available = 3, .deployed = 9'999'999'999'999'994, .sharesTotal = 9'999'999'999'999'997}, .amount = 4, .expected = tesSUCCESS},
        {.vault = {.available = 4, .deployed = 9'999'999'999'999'994, .sharesTotal = 9'999'999'999'999'998}, .amount = 4, .expected = tesSUCCESS},
        {.vault = {.available = 5, .deployed = 9'999'999'999'999'994, .sharesTotal = 9'999'999'999'999'999}, .amount = 4, .expected = tesSUCCESS},
        {.vault = {.available = 1, .deployed = 9'999'999'999'999'994, .sharesTotal = 9'999'999'999'999'995}, .amount = 5, .expected = tesSUCCESS},
        {.vault = {.available = 2, .deployed = 9'999'999'999'999'994, .sharesTotal = 9'999'999'999'999'996}, .amount = 5, .expected = tesSUCCESS},
        {.vault = {.available = 3, .deployed = 9'999'999'999'999'994, .sharesTotal = 9'999'999'999'999'997}, .amount = 5, .expected = tesSUCCESS},
        {.vault = {.available = 4, .deployed = 9'999'999'999'999'994, .sharesTotal = 9'999'999'999'999'998}, .amount = 5, .expected = tesSUCCESS},
        {.vault = {.available = 5, .deployed = 9'999'999'999'999'994, .sharesTotal = 9'999'999'999'999'999}, .amount = 5, .expected = tesSUCCESS},
        // available 9'999'999'999'999'996, deployed 1, amount 9'999'999'999'999'996
        {.vault = {.available = 9'999'999'999'999'994, .deployed = 1, .sharesTotal = 9'999'999'999'999'995}, .amount = 9'999'999'999'999'994, .expected = tesSUCCESS},
        {.vault = {.available = 9'999'999'999'999'995, .deployed = 1, .sharesTotal = 9'999'999'999'999'996}, .amount = 9'999'999'999'999'994, .expected = tesSUCCESS},
        {.vault = {.available = 9'999'999'999'999'996, .deployed = 1, .sharesTotal = 9'999'999'999'999'997}, .amount = 9'999'999'999'999'994, .expected = tesSUCCESS},
        {.vault = {.available = 9'999'999'999'999'997, .deployed = 1, .sharesTotal = 9'999'999'999'999'998}, .amount = 9'999'999'999'999'994, .expected = tesSUCCESS},
        {.vault = {.available = 9'999'999'999'999'998, .deployed = 1, .sharesTotal = 9'999'999'999'999'999}, .amount = 9'999'999'999'999'994, .expected = tesSUCCESS},
        {.vault = {.available = 9'999'999'999'999'994, .deployed = 1, .sharesTotal = 9'999'999'999'999'995}, .amount = 9'999'999'999'999'995, .expected = tesSUCCESS},
        {.vault = {.available = 9'999'999'999'999'995, .deployed = 1, .sharesTotal = 9'999'999'999'999'996}, .amount = 9'999'999'999'999'995, .expected = tesSUCCESS},
        {.vault = {.available = 9'999'999'999'999'996, .deployed = 1, .sharesTotal = 9'999'999'999'999'997}, .amount = 9'999'999'999'999'995, .expected = tesSUCCESS},
        {.vault = {.available = 9'999'999'999'999'997, .deployed = 1, .sharesTotal = 9'999'999'999'999'998}, .amount = 9'999'999'999'999'995, .expected = tesSUCCESS},
        {.vault = {.available = 9'999'999'999'999'998, .deployed = 1, .sharesTotal = 9'999'999'999'999'999}, .amount = 9'999'999'999'999'995, .expected = tesSUCCESS},
        {.vault = {.available = 9'999'999'999'999'994, .deployed = 1, .sharesTotal = 9'999'999'999'999'995}, .amount = 9'999'999'999'999'996, .expected = tesSUCCESS},
        {.vault = {.available = 9'999'999'999'999'995, .deployed = 1, .sharesTotal = 9'999'999'999'999'996}, .amount = 9'999'999'999'999'996, .expected = tesSUCCESS},
        {.vault = {.available = 9'999'999'999'999'996, .deployed = 1, .sharesTotal = 9'999'999'999'999'997}, .amount = 9'999'999'999'999'996, .expected = tesSUCCESS},
        {.vault = {.available = 9'999'999'999'999'997, .deployed = 1, .sharesTotal = 9'999'999'999'999'998}, .amount = 9'999'999'999'999'996, .expected = tesSUCCESS},
        {.vault = {.available = 9'999'999'999'999'998, .deployed = 1, .sharesTotal = 9'999'999'999'999'999}, .amount = 9'999'999'999'999'996, .expected = tesSUCCESS},
        {.vault = {.available = 9'999'999'999'999'994, .deployed = 1, .sharesTotal = 9'999'999'999'999'995}, .amount = 9'999'999'999'999'997, .expected = tesSUCCESS},
        {.vault = {.available = 9'999'999'999'999'995, .deployed = 1, .sharesTotal = 9'999'999'999'999'996}, .amount = 9'999'999'999'999'997, .expected = tesSUCCESS},
        {.vault = {.available = 9'999'999'999'999'996, .deployed = 1, .sharesTotal = 9'999'999'999'999'997}, .amount = 9'999'999'999'999'997, .expected = tesSUCCESS},
        {.vault = {.available = 9'999'999'999'999'997, .deployed = 1, .sharesTotal = 9'999'999'999'999'998}, .amount = 9'999'999'999'999'997, .expected = tesSUCCESS},
        {.vault = {.available = 9'999'999'999'999'998, .deployed = 1, .sharesTotal = 9'999'999'999'999'999}, .amount = 9'999'999'999'999'997, .expected = tesSUCCESS},
        {.vault = {.available = 9'999'999'999'999'994, .deployed = 1, .sharesTotal = 9'999'999'999'999'995}, .amount = 9'999'999'999'999'998, .expected = tesSUCCESS},
        {.vault = {.available = 9'999'999'999'999'995, .deployed = 1, .sharesTotal = 9'999'999'999'999'996}, .amount = 9'999'999'999'999'998, .expected = tesSUCCESS},
        {.vault = {.available = 9'999'999'999'999'996, .deployed = 1, .sharesTotal = 9'999'999'999'999'997}, .amount = 9'999'999'999'999'998, .expected = tesSUCCESS},
        {.vault = {.available = 9'999'999'999'999'997, .deployed = 1, .sharesTotal = 9'999'999'999'999'998}, .amount = 9'999'999'999'999'998, .expected = tesSUCCESS},
        {.vault = {.available = 9'999'999'999'999'998, .deployed = 1, .sharesTotal = 9'999'999'999'999'999}, .amount = 9'999'999'999'999'998, .expected = tesSUCCESS},
        // available 4'999'999'999'999'998, deployed 4'999'999'999'999'999, amount 4'999'999'999'999'998
        {.vault = {.available = 4'999'999'999'999'996, .deployed = 4'999'999'999'999'999, .sharesTotal = 9'999'999'999'999'995}, .amount = 4'999'999'999'999'996, .expected = tesSUCCESS},
        {.vault = {.available = 4'999'999'999'999'997, .deployed = 4'999'999'999'999'999, .sharesTotal = 9'999'999'999'999'996}, .amount = 4'999'999'999'999'996, .expected = tesSUCCESS},
        {.vault = {.available = 4'999'999'999'999'998, .deployed = 4'999'999'999'999'999, .sharesTotal = 9'999'999'999'999'997}, .amount = 4'999'999'999'999'996, .expected = tesSUCCESS},
        {.vault = {.available = 4'999'999'999'999'999, .deployed = 4'999'999'999'999'999, .sharesTotal = 9'999'999'999'999'998}, .amount = 4'999'999'999'999'996, .expected = tesSUCCESS},
        {.vault = {.available = 5'000'000'000'000'000, .deployed = 4'999'999'999'999'999, .sharesTotal = 9'999'999'999'999'999}, .amount = 4'999'999'999'999'996, .expected = tesSUCCESS},
        {.vault = {.available = 4'999'999'999'999'996, .deployed = 4'999'999'999'999'999, .sharesTotal = 9'999'999'999'999'995}, .amount = 4'999'999'999'999'997, .expected = tesSUCCESS},
        {.vault = {.available = 4'999'999'999'999'997, .deployed = 4'999'999'999'999'999, .sharesTotal = 9'999'999'999'999'996}, .amount = 4'999'999'999'999'997, .expected = tesSUCCESS},
        {.vault = {.available = 4'999'999'999'999'998, .deployed = 4'999'999'999'999'999, .sharesTotal = 9'999'999'999'999'997}, .amount = 4'999'999'999'999'997, .expected = tesSUCCESS},
        {.vault = {.available = 4'999'999'999'999'999, .deployed = 4'999'999'999'999'999, .sharesTotal = 9'999'999'999'999'998}, .amount = 4'999'999'999'999'997, .expected = tesSUCCESS},
        {.vault = {.available = 5'000'000'000'000'000, .deployed = 4'999'999'999'999'999, .sharesTotal = 9'999'999'999'999'999}, .amount = 4'999'999'999'999'997, .expected = tesSUCCESS},
        {.vault = {.available = 4'999'999'999'999'996, .deployed = 4'999'999'999'999'999, .sharesTotal = 9'999'999'999'999'995}, .amount = 4'999'999'999'999'998, .expected = tesSUCCESS},
        {.vault = {.available = 4'999'999'999'999'997, .deployed = 4'999'999'999'999'999, .sharesTotal = 9'999'999'999'999'996}, .amount = 4'999'999'999'999'998, .expected = tesSUCCESS},
        {.vault = {.available = 4'999'999'999'999'998, .deployed = 4'999'999'999'999'999, .sharesTotal = 9'999'999'999'999'997}, .amount = 4'999'999'999'999'998, .expected = tesSUCCESS},
        {.vault = {.available = 4'999'999'999'999'999, .deployed = 4'999'999'999'999'999, .sharesTotal = 9'999'999'999'999'998}, .amount = 4'999'999'999'999'998, .expected = tesSUCCESS},
        {.vault = {.available = 5'000'000'000'000'000, .deployed = 4'999'999'999'999'999, .sharesTotal = 9'999'999'999'999'999}, .amount = 4'999'999'999'999'998, .expected = tesSUCCESS},
        {.vault = {.available = 4'999'999'999'999'996, .deployed = 4'999'999'999'999'999, .sharesTotal = 9'999'999'999'999'995}, .amount = 4'999'999'999'999'999, .expected = tesSUCCESS},
        {.vault = {.available = 4'999'999'999'999'997, .deployed = 4'999'999'999'999'999, .sharesTotal = 9'999'999'999'999'996}, .amount = 4'999'999'999'999'999, .expected = tesSUCCESS},
        {.vault = {.available = 4'999'999'999'999'998, .deployed = 4'999'999'999'999'999, .sharesTotal = 9'999'999'999'999'997}, .amount = 4'999'999'999'999'999, .expected = tesSUCCESS},
        {.vault = {.available = 4'999'999'999'999'999, .deployed = 4'999'999'999'999'999, .sharesTotal = 9'999'999'999'999'998}, .amount = 4'999'999'999'999'999, .expected = tesSUCCESS},
        {.vault = {.available = 5'000'000'000'000'000, .deployed = 4'999'999'999'999'999, .sharesTotal = 9'999'999'999'999'999}, .amount = 4'999'999'999'999'999, .expected = tesSUCCESS},
        {.vault = {.available = 4'999'999'999'999'996, .deployed = 4'999'999'999'999'999, .sharesTotal = 9'999'999'999'999'995}, .amount = 5'000'000'000'000'000, .expected = tesSUCCESS},
        {.vault = {.available = 4'999'999'999'999'997, .deployed = 4'999'999'999'999'999, .sharesTotal = 9'999'999'999'999'996}, .amount = 5'000'000'000'000'000, .expected = tesSUCCESS},
        {.vault = {.available = 4'999'999'999'999'998, .deployed = 4'999'999'999'999'999, .sharesTotal = 9'999'999'999'999'997}, .amount = 5'000'000'000'000'000, .expected = tesSUCCESS},
        {.vault = {.available = 4'999'999'999'999'999, .deployed = 4'999'999'999'999'999, .sharesTotal = 9'999'999'999'999'998}, .amount = 5'000'000'000'000'000, .expected = tesSUCCESS},
        {.vault = {.available = 5'000'000'000'000'000, .deployed = 4'999'999'999'999'999, .sharesTotal = 9'999'999'999'999'999}, .amount = 5'000'000'000'000'000, .expected = tesSUCCESS},
    };
    static constexpr ClawbackCase kCoarseClawAll[] = {
        // mantissa 2'000'000'000'000'000, exponent 1, deployed 5
        {.vault = {.available = 1'999'999'999'999'998, .deployed = 3, .sharesTotal = 1'000'000'000}, .amount = 0, .expected = tecHAS_OBLIGATIONS, .availableExponent = 1},
        {.vault = {.available = 1'999'999'999'999'998, .deployed = 4, .sharesTotal = 1'000'000'000}, .amount = 0, .expected = tecHAS_OBLIGATIONS, .availableExponent = 1},
        {.vault = {.available = 1'999'999'999'999'998, .deployed = 5, .sharesTotal = 1'000'000'000}, .amount = 0, .expected = tecHAS_OBLIGATIONS, .availableExponent = 1},
        {.vault = {.available = 1'999'999'999'999'998, .deployed = 6, .sharesTotal = 1'000'000'000}, .amount = 0, .expected = tesSUCCESS, .availableExponent = 1},
        {.vault = {.available = 1'999'999'999'999'998, .deployed = 7, .sharesTotal = 1'000'000'000}, .amount = 0, .expected = tesSUCCESS, .availableExponent = 1},
        {.vault = {.available = 1'999'999'999'999'999, .deployed = 3, .sharesTotal = 1'000'000'000}, .amount = 0, .expected = tecHAS_OBLIGATIONS, .availableExponent = 1},
        {.vault = {.available = 1'999'999'999'999'999, .deployed = 4, .sharesTotal = 1'000'000'000}, .amount = 0, .expected = tecHAS_OBLIGATIONS, .availableExponent = 1},
        {.vault = {.available = 1'999'999'999'999'999, .deployed = 5, .sharesTotal = 1'000'000'000}, .amount = 0, .expected = tesSUCCESS, .availableExponent = 1},
        {.vault = {.available = 1'999'999'999'999'999, .deployed = 6, .sharesTotal = 1'000'000'000}, .amount = 0, .expected = tesSUCCESS, .availableExponent = 1},
        {.vault = {.available = 1'999'999'999'999'999, .deployed = 7, .sharesTotal = 1'000'000'000}, .amount = 0, .expected = tesSUCCESS, .availableExponent = 1},
        {.vault = {.available = 2'000'000'000'000'000, .deployed = 3, .sharesTotal = 1'000'000'000}, .amount = 0, .expected = tecHAS_OBLIGATIONS, .availableExponent = 1},
        {.vault = {.available = 2'000'000'000'000'000, .deployed = 4, .sharesTotal = 1'000'000'000}, .amount = 0, .expected = tecHAS_OBLIGATIONS, .availableExponent = 1},
        {.vault = {.available = 2'000'000'000'000'000, .deployed = 5, .sharesTotal = 1'000'000'000}, .amount = 0, .expected = tecHAS_OBLIGATIONS, .availableExponent = 1},
        {.vault = {.available = 2'000'000'000'000'000, .deployed = 6, .sharesTotal = 1'000'000'000}, .amount = 0, .expected = tesSUCCESS, .availableExponent = 1},
        {.vault = {.available = 2'000'000'000'000'000, .deployed = 7, .sharesTotal = 1'000'000'000}, .amount = 0, .expected = tesSUCCESS, .availableExponent = 1},
        {.vault = {.available = 2'000'000'000'000'001, .deployed = 3, .sharesTotal = 1'000'000'000}, .amount = 0, .expected = tecHAS_OBLIGATIONS, .availableExponent = 1},
        {.vault = {.available = 2'000'000'000'000'001, .deployed = 4, .sharesTotal = 1'000'000'000}, .amount = 0, .expected = tecHAS_OBLIGATIONS, .availableExponent = 1},
        {.vault = {.available = 2'000'000'000'000'001, .deployed = 5, .sharesTotal = 1'000'000'000}, .amount = 0, .expected = tesSUCCESS, .availableExponent = 1},
        {.vault = {.available = 2'000'000'000'000'001, .deployed = 6, .sharesTotal = 1'000'000'000}, .amount = 0, .expected = tesSUCCESS, .availableExponent = 1},
        {.vault = {.available = 2'000'000'000'000'001, .deployed = 7, .sharesTotal = 1'000'000'000}, .amount = 0, .expected = tesSUCCESS, .availableExponent = 1},
        {.vault = {.available = 2'000'000'000'000'002, .deployed = 3, .sharesTotal = 1'000'000'000}, .amount = 0, .expected = tecHAS_OBLIGATIONS, .availableExponent = 1},
        {.vault = {.available = 2'000'000'000'000'002, .deployed = 4, .sharesTotal = 1'000'000'000}, .amount = 0, .expected = tecHAS_OBLIGATIONS, .availableExponent = 1},
        {.vault = {.available = 2'000'000'000'000'002, .deployed = 5, .sharesTotal = 1'000'000'000}, .amount = 0, .expected = tecHAS_OBLIGATIONS, .availableExponent = 1},
        {.vault = {.available = 2'000'000'000'000'002, .deployed = 6, .sharesTotal = 1'000'000'000}, .amount = 0, .expected = tesSUCCESS, .availableExponent = 1},
        {.vault = {.available = 2'000'000'000'000'002, .deployed = 7, .sharesTotal = 1'000'000'000}, .amount = 0, .expected = tesSUCCESS, .availableExponent = 1},
        // mantissa 2'000'000'000'000'001, exponent 1, deployed 5
        {.vault = {.available = 1'999'999'999'999'999, .deployed = 3, .sharesTotal = 1'000'000'000}, .amount = 0, .expected = tecHAS_OBLIGATIONS, .availableExponent = 1},
        {.vault = {.available = 1'999'999'999'999'999, .deployed = 4, .sharesTotal = 1'000'000'000}, .amount = 0, .expected = tecHAS_OBLIGATIONS, .availableExponent = 1},
        {.vault = {.available = 1'999'999'999'999'999, .deployed = 5, .sharesTotal = 1'000'000'000}, .amount = 0, .expected = tesSUCCESS, .availableExponent = 1},
        {.vault = {.available = 1'999'999'999'999'999, .deployed = 6, .sharesTotal = 1'000'000'000}, .amount = 0, .expected = tesSUCCESS, .availableExponent = 1},
        {.vault = {.available = 1'999'999'999'999'999, .deployed = 7, .sharesTotal = 1'000'000'000}, .amount = 0, .expected = tesSUCCESS, .availableExponent = 1},
        {.vault = {.available = 2'000'000'000'000'000, .deployed = 3, .sharesTotal = 1'000'000'000}, .amount = 0, .expected = tecHAS_OBLIGATIONS, .availableExponent = 1},
        {.vault = {.available = 2'000'000'000'000'000, .deployed = 4, .sharesTotal = 1'000'000'000}, .amount = 0, .expected = tecHAS_OBLIGATIONS, .availableExponent = 1},
        {.vault = {.available = 2'000'000'000'000'000, .deployed = 5, .sharesTotal = 1'000'000'000}, .amount = 0, .expected = tecHAS_OBLIGATIONS, .availableExponent = 1},
        {.vault = {.available = 2'000'000'000'000'000, .deployed = 6, .sharesTotal = 1'000'000'000}, .amount = 0, .expected = tesSUCCESS, .availableExponent = 1},
        {.vault = {.available = 2'000'000'000'000'000, .deployed = 7, .sharesTotal = 1'000'000'000}, .amount = 0, .expected = tesSUCCESS, .availableExponent = 1},
        {.vault = {.available = 2'000'000'000'000'001, .deployed = 3, .sharesTotal = 1'000'000'000}, .amount = 0, .expected = tecHAS_OBLIGATIONS, .availableExponent = 1},
        {.vault = {.available = 2'000'000'000'000'001, .deployed = 4, .sharesTotal = 1'000'000'000}, .amount = 0, .expected = tecHAS_OBLIGATIONS, .availableExponent = 1},
        {.vault = {.available = 2'000'000'000'000'001, .deployed = 5, .sharesTotal = 1'000'000'000}, .amount = 0, .expected = tesSUCCESS, .availableExponent = 1},
        {.vault = {.available = 2'000'000'000'000'001, .deployed = 6, .sharesTotal = 1'000'000'000}, .amount = 0, .expected = tesSUCCESS, .availableExponent = 1},
        {.vault = {.available = 2'000'000'000'000'001, .deployed = 7, .sharesTotal = 1'000'000'000}, .amount = 0, .expected = tesSUCCESS, .availableExponent = 1},
        {.vault = {.available = 2'000'000'000'000'002, .deployed = 3, .sharesTotal = 1'000'000'000}, .amount = 0, .expected = tecHAS_OBLIGATIONS, .availableExponent = 1},
        {.vault = {.available = 2'000'000'000'000'002, .deployed = 4, .sharesTotal = 1'000'000'000}, .amount = 0, .expected = tecHAS_OBLIGATIONS, .availableExponent = 1},
        {.vault = {.available = 2'000'000'000'000'002, .deployed = 5, .sharesTotal = 1'000'000'000}, .amount = 0, .expected = tecHAS_OBLIGATIONS, .availableExponent = 1},
        {.vault = {.available = 2'000'000'000'000'002, .deployed = 6, .sharesTotal = 1'000'000'000}, .amount = 0, .expected = tesSUCCESS, .availableExponent = 1},
        {.vault = {.available = 2'000'000'000'000'002, .deployed = 7, .sharesTotal = 1'000'000'000}, .amount = 0, .expected = tesSUCCESS, .availableExponent = 1},
        {.vault = {.available = 2'000'000'000'000'003, .deployed = 3, .sharesTotal = 1'000'000'000}, .amount = 0, .expected = tecHAS_OBLIGATIONS, .availableExponent = 1},
        {.vault = {.available = 2'000'000'000'000'003, .deployed = 4, .sharesTotal = 1'000'000'000}, .amount = 0, .expected = tecHAS_OBLIGATIONS, .availableExponent = 1},
        {.vault = {.available = 2'000'000'000'000'003, .deployed = 5, .sharesTotal = 1'000'000'000}, .amount = 0, .expected = tesSUCCESS, .availableExponent = 1},
        {.vault = {.available = 2'000'000'000'000'003, .deployed = 6, .sharesTotal = 1'000'000'000}, .amount = 0, .expected = tesSUCCESS, .availableExponent = 1},
        {.vault = {.available = 2'000'000'000'000'003, .deployed = 7, .sharesTotal = 1'000'000'000}, .amount = 0, .expected = tesSUCCESS, .availableExponent = 1},
        // mantissa 9'999'999'999'999'998, exponent 1, deployed 5
        {.vault = {.available = 9'999'999'999'999'996, .deployed = 3, .sharesTotal = 1'000'000'000}, .amount = 0, .expected = tecHAS_OBLIGATIONS, .availableExponent = 1},
        {.vault = {.available = 9'999'999'999'999'996, .deployed = 4, .sharesTotal = 1'000'000'000}, .amount = 0, .expected = tecHAS_OBLIGATIONS, .availableExponent = 1},
        {.vault = {.available = 9'999'999'999'999'996, .deployed = 5, .sharesTotal = 1'000'000'000}, .amount = 0, .expected = tecHAS_OBLIGATIONS, .availableExponent = 1},
        {.vault = {.available = 9'999'999'999'999'996, .deployed = 6, .sharesTotal = 1'000'000'000}, .amount = 0, .expected = tesSUCCESS, .availableExponent = 1},
        {.vault = {.available = 9'999'999'999'999'996, .deployed = 7, .sharesTotal = 1'000'000'000}, .amount = 0, .expected = tesSUCCESS, .availableExponent = 1},
        {.vault = {.available = 9'999'999'999'999'997, .deployed = 3, .sharesTotal = 1'000'000'000}, .amount = 0, .expected = tecHAS_OBLIGATIONS, .availableExponent = 1},
        {.vault = {.available = 9'999'999'999'999'997, .deployed = 4, .sharesTotal = 1'000'000'000}, .amount = 0, .expected = tecHAS_OBLIGATIONS, .availableExponent = 1},
        {.vault = {.available = 9'999'999'999'999'997, .deployed = 5, .sharesTotal = 1'000'000'000}, .amount = 0, .expected = tesSUCCESS, .availableExponent = 1},
        {.vault = {.available = 9'999'999'999'999'997, .deployed = 6, .sharesTotal = 1'000'000'000}, .amount = 0, .expected = tesSUCCESS, .availableExponent = 1},
        {.vault = {.available = 9'999'999'999'999'997, .deployed = 7, .sharesTotal = 1'000'000'000}, .amount = 0, .expected = tesSUCCESS, .availableExponent = 1},
        {.vault = {.available = 9'999'999'999'999'998, .deployed = 3, .sharesTotal = 1'000'000'000}, .amount = 0, .expected = tecHAS_OBLIGATIONS, .availableExponent = 1},
        {.vault = {.available = 9'999'999'999'999'998, .deployed = 4, .sharesTotal = 1'000'000'000}, .amount = 0, .expected = tecHAS_OBLIGATIONS, .availableExponent = 1},
        {.vault = {.available = 9'999'999'999'999'998, .deployed = 5, .sharesTotal = 1'000'000'000}, .amount = 0, .expected = tecHAS_OBLIGATIONS, .availableExponent = 1},
        {.vault = {.available = 9'999'999'999'999'998, .deployed = 6, .sharesTotal = 1'000'000'000}, .amount = 0, .expected = tesSUCCESS, .availableExponent = 1},
        {.vault = {.available = 9'999'999'999'999'998, .deployed = 7, .sharesTotal = 1'000'000'000}, .amount = 0, .expected = tesSUCCESS, .availableExponent = 1},
        {.vault = {.available = 9'999'999'999'999'999, .deployed = 3, .sharesTotal = 1'000'000'000}, .amount = 0, .expected = tecHAS_OBLIGATIONS, .availableExponent = 1},
        {.vault = {.available = 9'999'999'999'999'999, .deployed = 4, .sharesTotal = 1'000'000'000}, .amount = 0, .expected = tecHAS_OBLIGATIONS, .availableExponent = 1},
        {.vault = {.available = 9'999'999'999'999'999, .deployed = 5, .sharesTotal = 1'000'000'000}, .amount = 0, .expected = tesSUCCESS, .availableExponent = 1},
        {.vault = {.available = 9'999'999'999'999'999, .deployed = 6, .sharesTotal = 1'000'000'000}, .amount = 0, .expected = tesSUCCESS, .availableExponent = 1},
        {.vault = {.available = 9'999'999'999'999'999, .deployed = 7, .sharesTotal = 1'000'000'000}, .amount = 0, .expected = tesSUCCESS, .availableExponent = 1},
        {.vault = {.available = 10'000'000'000'000'000, .deployed = 3, .sharesTotal = 1'000'000'000}, .amount = 0, .expected = tecHAS_OBLIGATIONS, .availableExponent = 1},
        {.vault = {.available = 10'000'000'000'000'000, .deployed = 4, .sharesTotal = 1'000'000'000}, .amount = 0, .expected = tecHAS_OBLIGATIONS, .availableExponent = 1},
        {.vault = {.available = 10'000'000'000'000'000, .deployed = 5, .sharesTotal = 1'000'000'000}, .amount = 0, .expected = tecHAS_OBLIGATIONS, .availableExponent = 1},
        {.vault = {.available = 10'000'000'000'000'000, .deployed = 6, .sharesTotal = 1'000'000'000}, .amount = 0, .expected = tecHAS_OBLIGATIONS, .availableExponent = 1},
        {.vault = {.available = 10'000'000'000'000'000, .deployed = 7, .sharesTotal = 1'000'000'000}, .amount = 0, .expected = tecHAS_OBLIGATIONS, .availableExponent = 1},
        // mantissa 2'000'000'000'000'000, exponent 2, deployed 50
        {.vault = {.available = 1'999'999'999'999'998, .deployed = 48, .sharesTotal = 1'000'000'000}, .amount = 0, .expected = tecHAS_OBLIGATIONS, .availableExponent = 2},
        {.vault = {.available = 1'999'999'999'999'998, .deployed = 49, .sharesTotal = 1'000'000'000}, .amount = 0, .expected = tecHAS_OBLIGATIONS, .availableExponent = 2},
        {.vault = {.available = 1'999'999'999'999'998, .deployed = 50, .sharesTotal = 1'000'000'000}, .amount = 0, .expected = tecHAS_OBLIGATIONS, .availableExponent = 2},
        {.vault = {.available = 1'999'999'999'999'998, .deployed = 51, .sharesTotal = 1'000'000'000}, .amount = 0, .expected = tesSUCCESS, .availableExponent = 2},
        {.vault = {.available = 1'999'999'999'999'998, .deployed = 52, .sharesTotal = 1'000'000'000}, .amount = 0, .expected = tesSUCCESS, .availableExponent = 2},
        {.vault = {.available = 1'999'999'999'999'999, .deployed = 48, .sharesTotal = 1'000'000'000}, .amount = 0, .expected = tecHAS_OBLIGATIONS, .availableExponent = 2},
        {.vault = {.available = 1'999'999'999'999'999, .deployed = 49, .sharesTotal = 1'000'000'000}, .amount = 0, .expected = tecHAS_OBLIGATIONS, .availableExponent = 2},
        {.vault = {.available = 1'999'999'999'999'999, .deployed = 50, .sharesTotal = 1'000'000'000}, .amount = 0, .expected = tesSUCCESS, .availableExponent = 2},
        {.vault = {.available = 1'999'999'999'999'999, .deployed = 51, .sharesTotal = 1'000'000'000}, .amount = 0, .expected = tesSUCCESS, .availableExponent = 2},
        {.vault = {.available = 1'999'999'999'999'999, .deployed = 52, .sharesTotal = 1'000'000'000}, .amount = 0, .expected = tesSUCCESS, .availableExponent = 2},
        {.vault = {.available = 2'000'000'000'000'000, .deployed = 48, .sharesTotal = 1'000'000'000}, .amount = 0, .expected = tecHAS_OBLIGATIONS, .availableExponent = 2},
        {.vault = {.available = 2'000'000'000'000'000, .deployed = 49, .sharesTotal = 1'000'000'000}, .amount = 0, .expected = tecHAS_OBLIGATIONS, .availableExponent = 2},
        {.vault = {.available = 2'000'000'000'000'000, .deployed = 50, .sharesTotal = 1'000'000'000}, .amount = 0, .expected = tecHAS_OBLIGATIONS, .availableExponent = 2},
        {.vault = {.available = 2'000'000'000'000'000, .deployed = 51, .sharesTotal = 1'000'000'000}, .amount = 0, .expected = tesSUCCESS, .availableExponent = 2},
        {.vault = {.available = 2'000'000'000'000'000, .deployed = 52, .sharesTotal = 1'000'000'000}, .amount = 0, .expected = tesSUCCESS, .availableExponent = 2},
        {.vault = {.available = 2'000'000'000'000'001, .deployed = 48, .sharesTotal = 1'000'000'000}, .amount = 0, .expected = tecHAS_OBLIGATIONS, .availableExponent = 2},
        {.vault = {.available = 2'000'000'000'000'001, .deployed = 49, .sharesTotal = 1'000'000'000}, .amount = 0, .expected = tecHAS_OBLIGATIONS, .availableExponent = 2},
        {.vault = {.available = 2'000'000'000'000'001, .deployed = 50, .sharesTotal = 1'000'000'000}, .amount = 0, .expected = tesSUCCESS, .availableExponent = 2},
        {.vault = {.available = 2'000'000'000'000'001, .deployed = 51, .sharesTotal = 1'000'000'000}, .amount = 0, .expected = tesSUCCESS, .availableExponent = 2},
        {.vault = {.available = 2'000'000'000'000'001, .deployed = 52, .sharesTotal = 1'000'000'000}, .amount = 0, .expected = tesSUCCESS, .availableExponent = 2},
        {.vault = {.available = 2'000'000'000'000'002, .deployed = 48, .sharesTotal = 1'000'000'000}, .amount = 0, .expected = tecHAS_OBLIGATIONS, .availableExponent = 2},
        {.vault = {.available = 2'000'000'000'000'002, .deployed = 49, .sharesTotal = 1'000'000'000}, .amount = 0, .expected = tecHAS_OBLIGATIONS, .availableExponent = 2},
        {.vault = {.available = 2'000'000'000'000'002, .deployed = 50, .sharesTotal = 1'000'000'000}, .amount = 0, .expected = tecHAS_OBLIGATIONS, .availableExponent = 2},
        {.vault = {.available = 2'000'000'000'000'002, .deployed = 51, .sharesTotal = 1'000'000'000}, .amount = 0, .expected = tesSUCCESS, .availableExponent = 2},
        {.vault = {.available = 2'000'000'000'000'002, .deployed = 52, .sharesTotal = 1'000'000'000}, .amount = 0, .expected = tesSUCCESS, .availableExponent = 2},
    };
    static constexpr ClawbackCase kDecade[] = {
        // availableMantissa 1'000'000'000'000'000, amount 1
        {.vault = {.available = 999'999'999'999'998, .sharesTotal = 9'999'999'999'999'980, .holderShares = 9'999'999'999'999'979}, .amount = 1, .expected = tesSUCCESS, .availableExponent = 1},
        {.vault = {.available = 999'999'999'999'998, .sharesTotal = 9'999'999'999'999'980, .holderShares = 9'999'999'999'999'979}, .amount = 2, .expected = tesSUCCESS, .availableExponent = 1},
        {.vault = {.available = 999'999'999'999'998, .sharesTotal = 9'999'999'999'999'980, .holderShares = 9'999'999'999'999'979}, .amount = 3, .expected = tesSUCCESS, .availableExponent = 1},
        {.vault = {.available = 999'999'999'999'999, .sharesTotal = 9'999'999'999'999'990, .holderShares = 9'999'999'999'999'989}, .amount = 1, .expected = tesSUCCESS, .availableExponent = 1},
        {.vault = {.available = 999'999'999'999'999, .sharesTotal = 9'999'999'999'999'990, .holderShares = 9'999'999'999'999'989}, .amount = 2, .expected = tesSUCCESS, .availableExponent = 1},
        {.vault = {.available = 999'999'999'999'999, .sharesTotal = 9'999'999'999'999'990, .holderShares = 9'999'999'999'999'989}, .amount = 3, .expected = tesSUCCESS, .availableExponent = 1},
        {.vault = {.available = 1'000'000'000'000'000, .sharesTotal = 10'000'000'000'000'000, .holderShares = 9'999'999'999'999'999}, .amount = 1, .expected = tesSUCCESS, .availableExponent = 1},
        {.vault = {.available = 1'000'000'000'000'000, .sharesTotal = 10'000'000'000'000'000, .holderShares = 9'999'999'999'999'999}, .amount = 2, .expected = tesSUCCESS, .availableExponent = 1},
        {.vault = {.available = 1'000'000'000'000'000, .sharesTotal = 10'000'000'000'000'000, .holderShares = 9'999'999'999'999'999}, .amount = 3, .expected = tesSUCCESS, .availableExponent = 1},
        {.vault = {.available = 1'000'000'000'000'001, .sharesTotal = 10'000'000'000'000'010, .holderShares = 10'000'000'000'000'009}, .amount = 1, .expected = tecPRECISION_LOSS, .availableExponent = 1},
        {.vault = {.available = 1'000'000'000'000'001, .sharesTotal = 10'000'000'000'000'010, .holderShares = 10'000'000'000'000'009}, .amount = 2, .expected = tecPRECISION_LOSS, .availableExponent = 1},
        {.vault = {.available = 1'000'000'000'000'001, .sharesTotal = 10'000'000'000'000'010, .holderShares = 10'000'000'000'000'009}, .amount = 3, .expected = tecPRECISION_LOSS, .availableExponent = 1},
        {.vault = {.available = 1'000'000'000'000'002, .sharesTotal = 10'000'000'000'000'020, .holderShares = 10'000'000'000'000'019}, .amount = 1, .expected = tecPRECISION_LOSS, .availableExponent = 1},
        {.vault = {.available = 1'000'000'000'000'002, .sharesTotal = 10'000'000'000'000'020, .holderShares = 10'000'000'000'000'019}, .amount = 2, .expected = tecPRECISION_LOSS, .availableExponent = 1},
        {.vault = {.available = 1'000'000'000'000'002, .sharesTotal = 10'000'000'000'000'020, .holderShares = 10'000'000'000'000'019}, .amount = 3, .expected = tecPRECISION_LOSS, .availableExponent = 1},
        // availableMantissa 1'000'000'000'000'001, amount 10
        {.vault = {.available = 999'999'999'999'999, .sharesTotal = 9'999'999'999'999'990, .holderShares = 9'999'999'999'999'989}, .amount = 8, .expected = tesSUCCESS, .availableExponent = 1},
        {.vault = {.available = 999'999'999'999'999, .sharesTotal = 9'999'999'999'999'990, .holderShares = 9'999'999'999'999'989}, .amount = 9, .expected = tesSUCCESS, .availableExponent = 1},
        {.vault = {.available = 999'999'999'999'999, .sharesTotal = 9'999'999'999'999'990, .holderShares = 9'999'999'999'999'989}, .amount = 10, .expected = tesSUCCESS, .availableExponent = 1},
        {.vault = {.available = 999'999'999'999'999, .sharesTotal = 9'999'999'999'999'990, .holderShares = 9'999'999'999'999'989}, .amount = 11, .expected = tesSUCCESS, .availableExponent = 1},
        {.vault = {.available = 999'999'999'999'999, .sharesTotal = 9'999'999'999'999'990, .holderShares = 9'999'999'999'999'989}, .amount = 12, .expected = tesSUCCESS, .availableExponent = 1},
        {.vault = {.available = 1'000'000'000'000'000, .sharesTotal = 10'000'000'000'000'000, .holderShares = 9'999'999'999'999'999}, .amount = 8, .expected = tesSUCCESS, .availableExponent = 1},
        {.vault = {.available = 1'000'000'000'000'000, .sharesTotal = 10'000'000'000'000'000, .holderShares = 9'999'999'999'999'999}, .amount = 9, .expected = tesSUCCESS, .availableExponent = 1},
        {.vault = {.available = 1'000'000'000'000'000, .sharesTotal = 10'000'000'000'000'000, .holderShares = 9'999'999'999'999'999}, .amount = 10, .expected = tesSUCCESS, .availableExponent = 1},
        {.vault = {.available = 1'000'000'000'000'000, .sharesTotal = 10'000'000'000'000'000, .holderShares = 9'999'999'999'999'999}, .amount = 11, .expected = tesSUCCESS, .availableExponent = 1},
        {.vault = {.available = 1'000'000'000'000'000, .sharesTotal = 10'000'000'000'000'000, .holderShares = 9'999'999'999'999'999}, .amount = 12, .expected = tesSUCCESS, .availableExponent = 1},
        {.vault = {.available = 1'000'000'000'000'001, .sharesTotal = 10'000'000'000'000'010, .holderShares = 10'000'000'000'000'009}, .amount = 8, .expected = tecPRECISION_LOSS, .availableExponent = 1},
        {.vault = {.available = 1'000'000'000'000'001, .sharesTotal = 10'000'000'000'000'010, .holderShares = 10'000'000'000'000'009}, .amount = 9, .expected = tecPRECISION_LOSS, .availableExponent = 1},
        {.vault = {.available = 1'000'000'000'000'001, .sharesTotal = 10'000'000'000'000'010, .holderShares = 10'000'000'000'000'009}, .amount = 10, .expected = tesSUCCESS, .availableExponent = 1},
        {.vault = {.available = 1'000'000'000'000'001, .sharesTotal = 10'000'000'000'000'010, .holderShares = 10'000'000'000'000'009}, .amount = 11, .expected = tesSUCCESS, .availableExponent = 1},
        {.vault = {.available = 1'000'000'000'000'001, .sharesTotal = 10'000'000'000'000'010, .holderShares = 10'000'000'000'000'009}, .amount = 12, .expected = tesSUCCESS, .availableExponent = 1},
        {.vault = {.available = 1'000'000'000'000'002, .sharesTotal = 10'000'000'000'000'020, .holderShares = 10'000'000'000'000'019}, .amount = 8, .expected = tecPRECISION_LOSS, .availableExponent = 1},
        {.vault = {.available = 1'000'000'000'000'002, .sharesTotal = 10'000'000'000'000'020, .holderShares = 10'000'000'000'000'019}, .amount = 9, .expected = tecPRECISION_LOSS, .availableExponent = 1},
        {.vault = {.available = 1'000'000'000'000'002, .sharesTotal = 10'000'000'000'000'020, .holderShares = 10'000'000'000'000'019}, .amount = 10, .expected = tesSUCCESS, .availableExponent = 1},
        {.vault = {.available = 1'000'000'000'000'002, .sharesTotal = 10'000'000'000'000'020, .holderShares = 10'000'000'000'000'019}, .amount = 11, .expected = tesSUCCESS, .availableExponent = 1},
        {.vault = {.available = 1'000'000'000'000'002, .sharesTotal = 10'000'000'000'000'020, .holderShares = 10'000'000'000'000'019}, .amount = 12, .expected = tesSUCCESS, .availableExponent = 1},
        {.vault = {.available = 1'000'000'000'000'003, .sharesTotal = 10'000'000'000'000'030, .holderShares = 10'000'000'000'000'029}, .amount = 8, .expected = tecPRECISION_LOSS, .availableExponent = 1},
        {.vault = {.available = 1'000'000'000'000'003, .sharesTotal = 10'000'000'000'000'030, .holderShares = 10'000'000'000'000'029}, .amount = 9, .expected = tecPRECISION_LOSS, .availableExponent = 1},
        {.vault = {.available = 1'000'000'000'000'003, .sharesTotal = 10'000'000'000'000'030, .holderShares = 10'000'000'000'000'029}, .amount = 10, .expected = tesSUCCESS, .availableExponent = 1},
        {.vault = {.available = 1'000'000'000'000'003, .sharesTotal = 10'000'000'000'000'030, .holderShares = 10'000'000'000'000'029}, .amount = 11, .expected = tesSUCCESS, .availableExponent = 1},
        {.vault = {.available = 1'000'000'000'000'003, .sharesTotal = 10'000'000'000'000'030, .holderShares = 10'000'000'000'000'029}, .amount = 12, .expected = tesSUCCESS, .availableExponent = 1},
    };
    static constexpr ClawbackCase kWaiver[] = {
        // total 12, deployed 6, loss 4, holderShares 12, amount 4
        {.vault = {.available = 6, .deployed = 6, .loss = 2, .sharesTotal = 12, .holderShares = 10}, .amount = 4, .expected = tesSUCCESS},
        {.vault = {.available = 6, .deployed = 6, .loss = 3, .sharesTotal = 12, .holderShares = 10}, .amount = 4, .expected = tesSUCCESS},
        {.vault = {.available = 6, .deployed = 6, .loss = 4, .sharesTotal = 12, .holderShares = 10}, .amount = 4, .expected = tesSUCCESS},
        {.vault = {.available = 6, .deployed = 6, .loss = 5, .sharesTotal = 12, .holderShares = 10}, .amount = 4, .expected = tesSUCCESS},
        {.vault = {.available = 6, .deployed = 6, .loss = 6, .sharesTotal = 12, .holderShares = 10}, .amount = 4, .expected = tesSUCCESS},
        {.vault = {.available = 6, .deployed = 6, .loss = 2, .sharesTotal = 12, .holderShares = 11}, .amount = 4, .expected = tesSUCCESS},
        {.vault = {.available = 6, .deployed = 6, .loss = 3, .sharesTotal = 12, .holderShares = 11}, .amount = 4, .expected = tesSUCCESS},
        {.vault = {.available = 6, .deployed = 6, .loss = 4, .sharesTotal = 12, .holderShares = 11}, .amount = 4, .expected = tesSUCCESS},
        {.vault = {.available = 6, .deployed = 6, .loss = 5, .sharesTotal = 12, .holderShares = 11}, .amount = 4, .expected = tesSUCCESS},
        {.vault = {.available = 6, .deployed = 6, .loss = 6, .sharesTotal = 12, .holderShares = 11}, .amount = 4, .expected = tesSUCCESS},
        {.vault = {.available = 6, .deployed = 6, .loss = 2, .sharesTotal = 12, .holderShares = 12}, .amount = 4, .expected = tesSUCCESS},
        {.vault = {.available = 6, .deployed = 6, .loss = 3, .sharesTotal = 12, .holderShares = 12}, .amount = 4, .expected = tesSUCCESS},
        {.vault = {.available = 6, .deployed = 6, .loss = 4, .sharesTotal = 12, .holderShares = 12}, .amount = 4, .expected = tesSUCCESS},
        {.vault = {.available = 6, .deployed = 6, .loss = 5, .sharesTotal = 12, .holderShares = 12}, .amount = 4, .expected = tesSUCCESS},
        {.vault = {.available = 6, .deployed = 6, .loss = 6, .sharesTotal = 12, .holderShares = 12}, .amount = 4, .expected = tesSUCCESS},
        // total 1'000'000'000, deployed 500'000'000, loss 250'000'000, holderShares 1'000'000'000, amount 100'000'000
        {.vault = {.available = 500'000'000, .deployed = 500'000'000, .loss = 249'999'998, .sharesTotal = 1'000'000'000, .holderShares = 999'999'998}, .amount = 100'000'000, .expected = tesSUCCESS},
        {.vault = {.available = 500'000'000, .deployed = 500'000'000, .loss = 249'999'999, .sharesTotal = 1'000'000'000, .holderShares = 999'999'998}, .amount = 100'000'000, .expected = tesSUCCESS},
        {.vault = {.available = 500'000'000, .deployed = 500'000'000, .loss = 250'000'000, .sharesTotal = 1'000'000'000, .holderShares = 999'999'998}, .amount = 100'000'000, .expected = tesSUCCESS},
        {.vault = {.available = 500'000'000, .deployed = 500'000'000, .loss = 250'000'001, .sharesTotal = 1'000'000'000, .holderShares = 999'999'998}, .amount = 100'000'000, .expected = tesSUCCESS},
        {.vault = {.available = 500'000'000, .deployed = 500'000'000, .loss = 250'000'002, .sharesTotal = 1'000'000'000, .holderShares = 999'999'998}, .amount = 100'000'000, .expected = tesSUCCESS},
        {.vault = {.available = 500'000'000, .deployed = 500'000'000, .loss = 249'999'998, .sharesTotal = 1'000'000'000, .holderShares = 999'999'999}, .amount = 100'000'000, .expected = tesSUCCESS},
        {.vault = {.available = 500'000'000, .deployed = 500'000'000, .loss = 249'999'999, .sharesTotal = 1'000'000'000, .holderShares = 999'999'999}, .amount = 100'000'000, .expected = tesSUCCESS},
        {.vault = {.available = 500'000'000, .deployed = 500'000'000, .loss = 250'000'000, .sharesTotal = 1'000'000'000, .holderShares = 999'999'999}, .amount = 100'000'000, .expected = tesSUCCESS},
        {.vault = {.available = 500'000'000, .deployed = 500'000'000, .loss = 250'000'001, .sharesTotal = 1'000'000'000, .holderShares = 999'999'999}, .amount = 100'000'000, .expected = tesSUCCESS},
        {.vault = {.available = 500'000'000, .deployed = 500'000'000, .loss = 250'000'002, .sharesTotal = 1'000'000'000, .holderShares = 999'999'999}, .amount = 100'000'000, .expected = tesSUCCESS},
        {.vault = {.available = 500'000'000, .deployed = 500'000'000, .loss = 249'999'998, .sharesTotal = 1'000'000'000, .holderShares = 1'000'000'000}, .amount = 100'000'000, .expected = tesSUCCESS},
        {.vault = {.available = 500'000'000, .deployed = 500'000'000, .loss = 249'999'999, .sharesTotal = 1'000'000'000, .holderShares = 1'000'000'000}, .amount = 100'000'000, .expected = tesSUCCESS},
        {.vault = {.available = 500'000'000, .deployed = 500'000'000, .loss = 250'000'000, .sharesTotal = 1'000'000'000, .holderShares = 1'000'000'000}, .amount = 100'000'000, .expected = tesSUCCESS},
        {.vault = {.available = 500'000'000, .deployed = 500'000'000, .loss = 250'000'001, .sharesTotal = 1'000'000'000, .holderShares = 1'000'000'000}, .amount = 100'000'000, .expected = tesSUCCESS},
        {.vault = {.available = 500'000'000, .deployed = 500'000'000, .loss = 250'000'002, .sharesTotal = 1'000'000'000, .holderShares = 1'000'000'000}, .amount = 100'000'000, .expected = tesSUCCESS},
        // total 9'999'999'999'999'996, deployed 4'999'999'999'999'998, loss 2'499'999'999'999'999, holderShares 9'999'999'999'999'996, amount 1'000'000'000
        {.vault = {.available = 4'999'999'999'999'998, .deployed = 4'999'999'999'999'998, .loss = 2'499'999'999'999'997, .sharesTotal = 9'999'999'999'999'996, .holderShares = 9'999'999'999'999'994}, .amount = 1'000'000'000, .expected = tesSUCCESS},
        {.vault = {.available = 4'999'999'999'999'998, .deployed = 4'999'999'999'999'998, .loss = 2'499'999'999'999'998, .sharesTotal = 9'999'999'999'999'996, .holderShares = 9'999'999'999'999'994}, .amount = 1'000'000'000, .expected = tesSUCCESS},
        {.vault = {.available = 4'999'999'999'999'998, .deployed = 4'999'999'999'999'998, .loss = 2'499'999'999'999'999, .sharesTotal = 9'999'999'999'999'996, .holderShares = 9'999'999'999'999'994}, .amount = 1'000'000'000, .expected = tesSUCCESS},
        {.vault = {.available = 4'999'999'999'999'998, .deployed = 4'999'999'999'999'998, .loss = 2'500'000'000'000'000, .sharesTotal = 9'999'999'999'999'996, .holderShares = 9'999'999'999'999'994}, .amount = 1'000'000'000, .expected = tesSUCCESS},
        {.vault = {.available = 4'999'999'999'999'998, .deployed = 4'999'999'999'999'998, .loss = 2'500'000'000'000'001, .sharesTotal = 9'999'999'999'999'996, .holderShares = 9'999'999'999'999'994}, .amount = 1'000'000'000, .expected = tesSUCCESS},
        {.vault = {.available = 4'999'999'999'999'998, .deployed = 4'999'999'999'999'998, .loss = 2'499'999'999'999'997, .sharesTotal = 9'999'999'999'999'996, .holderShares = 9'999'999'999'999'995}, .amount = 1'000'000'000, .expected = tesSUCCESS},
        {.vault = {.available = 4'999'999'999'999'998, .deployed = 4'999'999'999'999'998, .loss = 2'499'999'999'999'998, .sharesTotal = 9'999'999'999'999'996, .holderShares = 9'999'999'999'999'995}, .amount = 1'000'000'000, .expected = tesSUCCESS},
        {.vault = {.available = 4'999'999'999'999'998, .deployed = 4'999'999'999'999'998, .loss = 2'499'999'999'999'999, .sharesTotal = 9'999'999'999'999'996, .holderShares = 9'999'999'999'999'995}, .amount = 1'000'000'000, .expected = tesSUCCESS},
        {.vault = {.available = 4'999'999'999'999'998, .deployed = 4'999'999'999'999'998, .loss = 2'500'000'000'000'000, .sharesTotal = 9'999'999'999'999'996, .holderShares = 9'999'999'999'999'995}, .amount = 1'000'000'000, .expected = tesSUCCESS},
        {.vault = {.available = 4'999'999'999'999'998, .deployed = 4'999'999'999'999'998, .loss = 2'500'000'000'000'001, .sharesTotal = 9'999'999'999'999'996, .holderShares = 9'999'999'999'999'995}, .amount = 1'000'000'000, .expected = tesSUCCESS},
        {.vault = {.available = 4'999'999'999'999'998, .deployed = 4'999'999'999'999'998, .loss = 2'499'999'999'999'997, .sharesTotal = 9'999'999'999'999'996, .holderShares = 9'999'999'999'999'996}, .amount = 1'000'000'000, .expected = tesSUCCESS},
        {.vault = {.available = 4'999'999'999'999'998, .deployed = 4'999'999'999'999'998, .loss = 2'499'999'999'999'998, .sharesTotal = 9'999'999'999'999'996, .holderShares = 9'999'999'999'999'996}, .amount = 1'000'000'000, .expected = tesSUCCESS},
        {.vault = {.available = 4'999'999'999'999'998, .deployed = 4'999'999'999'999'998, .loss = 2'499'999'999'999'999, .sharesTotal = 9'999'999'999'999'996, .holderShares = 9'999'999'999'999'996}, .amount = 1'000'000'000, .expected = tesSUCCESS},
        {.vault = {.available = 4'999'999'999'999'998, .deployed = 4'999'999'999'999'998, .loss = 2'500'000'000'000'000, .sharesTotal = 9'999'999'999'999'996, .holderShares = 9'999'999'999'999'996}, .amount = 1'000'000'000, .expected = tesSUCCESS},
        {.vault = {.available = 4'999'999'999'999'998, .deployed = 4'999'999'999'999'998, .loss = 2'500'000'000'000'001, .sharesTotal = 9'999'999'999'999'996, .holderShares = 9'999'999'999'999'996}, .amount = 1'000'000'000, .expected = tesSUCCESS},
    };
    static constexpr ClawbackCase kShareOverflow[] = {
        // total 1, sharesTotal 1'317'624'576'693'539'401, amount 7
        {.vault = {.available = 1, .sharesTotal = 1'317'624'576'693'539'399}, .amount = 5, .expected = tesSUCCESS},
        {.vault = {.available = 1, .sharesTotal = 1'317'624'576'693'539'399}, .amount = 6, .expected = tesSUCCESS},
        {.vault = {.available = 1, .sharesTotal = 1'317'624'576'693'539'399}, .amount = 7, .expected = tesSUCCESS},
        {.vault = {.available = 1, .sharesTotal = 1'317'624'576'693'539'399}, .amount = 8, .expected = tecPATH_DRY},
        {.vault = {.available = 1, .sharesTotal = 1'317'624'576'693'539'399}, .amount = 9, .expected = tecPATH_DRY},
        {.vault = {.available = 1, .sharesTotal = 1'317'624'576'693'539'400}, .amount = 5, .expected = tesSUCCESS},
        {.vault = {.available = 1, .sharesTotal = 1'317'624'576'693'539'400}, .amount = 6, .expected = tesSUCCESS},
        {.vault = {.available = 1, .sharesTotal = 1'317'624'576'693'539'400}, .amount = 7, .expected = tesSUCCESS},
        {.vault = {.available = 1, .sharesTotal = 1'317'624'576'693'539'400}, .amount = 8, .expected = tecPATH_DRY},
        {.vault = {.available = 1, .sharesTotal = 1'317'624'576'693'539'400}, .amount = 9, .expected = tecPATH_DRY},
        {.vault = {.available = 1, .sharesTotal = 1'317'624'576'693'539'401}, .amount = 5, .expected = tesSUCCESS},
        {.vault = {.available = 1, .sharesTotal = 1'317'624'576'693'539'401}, .amount = 6, .expected = tesSUCCESS},
        {.vault = {.available = 1, .sharesTotal = 1'317'624'576'693'539'401}, .amount = 7, .expected = tesSUCCESS},
        {.vault = {.available = 1, .sharesTotal = 1'317'624'576'693'539'401}, .amount = 8, .expected = tecPATH_DRY},
        {.vault = {.available = 1, .sharesTotal = 1'317'624'576'693'539'401}, .amount = 9, .expected = tecPATH_DRY},
        {.vault = {.available = 1, .sharesTotal = 1'317'624'576'693'539'402}, .amount = 5, .expected = tesSUCCESS},
        {.vault = {.available = 1, .sharesTotal = 1'317'624'576'693'539'402}, .amount = 6, .expected = tesSUCCESS},
        {.vault = {.available = 1, .sharesTotal = 1'317'624'576'693'539'402}, .amount = 7, .expected = tecPATH_DRY},
        {.vault = {.available = 1, .sharesTotal = 1'317'624'576'693'539'402}, .amount = 8, .expected = tecPATH_DRY},
        {.vault = {.available = 1, .sharesTotal = 1'317'624'576'693'539'402}, .amount = 9, .expected = tecPATH_DRY},
        {.vault = {.available = 1, .sharesTotal = 1'317'624'576'693'539'403}, .amount = 5, .expected = tesSUCCESS},
        {.vault = {.available = 1, .sharesTotal = 1'317'624'576'693'539'403}, .amount = 6, .expected = tesSUCCESS},
        {.vault = {.available = 1, .sharesTotal = 1'317'624'576'693'539'403}, .amount = 7, .expected = tecPATH_DRY},
        {.vault = {.available = 1, .sharesTotal = 1'317'624'576'693'539'403}, .amount = 8, .expected = tecPATH_DRY},
        {.vault = {.available = 1, .sharesTotal = 1'317'624'576'693'539'403}, .amount = 9, .expected = tecPATH_DRY},
        // total 1, sharesTotal 3'074'457'345'618'258'602, amount 3
        {.vault = {.available = 1, .sharesTotal = 3'074'457'345'618'258'600}, .amount = 1, .expected = tesSUCCESS},
        {.vault = {.available = 1, .sharesTotal = 3'074'457'345'618'258'600}, .amount = 2, .expected = tesSUCCESS},
        {.vault = {.available = 1, .sharesTotal = 3'074'457'345'618'258'600}, .amount = 3, .expected = tesSUCCESS},
        {.vault = {.available = 1, .sharesTotal = 3'074'457'345'618'258'600}, .amount = 4, .expected = tecPATH_DRY},
        {.vault = {.available = 1, .sharesTotal = 3'074'457'345'618'258'600}, .amount = 5, .expected = tecPATH_DRY},
        {.vault = {.available = 1, .sharesTotal = 3'074'457'345'618'258'601}, .amount = 1, .expected = tesSUCCESS},
        {.vault = {.available = 1, .sharesTotal = 3'074'457'345'618'258'601}, .amount = 2, .expected = tesSUCCESS},
        {.vault = {.available = 1, .sharesTotal = 3'074'457'345'618'258'601}, .amount = 3, .expected = tesSUCCESS},
        {.vault = {.available = 1, .sharesTotal = 3'074'457'345'618'258'601}, .amount = 4, .expected = tecPATH_DRY},
        {.vault = {.available = 1, .sharesTotal = 3'074'457'345'618'258'601}, .amount = 5, .expected = tecPATH_DRY},
        {.vault = {.available = 1, .sharesTotal = 3'074'457'345'618'258'602}, .amount = 1, .expected = tesSUCCESS},
        {.vault = {.available = 1, .sharesTotal = 3'074'457'345'618'258'602}, .amount = 2, .expected = tesSUCCESS},
        {.vault = {.available = 1, .sharesTotal = 3'074'457'345'618'258'602}, .amount = 3, .expected = tesSUCCESS},
        {.vault = {.available = 1, .sharesTotal = 3'074'457'345'618'258'602}, .amount = 4, .expected = tecPATH_DRY},
        {.vault = {.available = 1, .sharesTotal = 3'074'457'345'618'258'602}, .amount = 5, .expected = tecPATH_DRY},
        {.vault = {.available = 1, .sharesTotal = 3'074'457'345'618'258'603}, .amount = 1, .expected = tesSUCCESS},
        {.vault = {.available = 1, .sharesTotal = 3'074'457'345'618'258'603}, .amount = 2, .expected = tesSUCCESS},
        {.vault = {.available = 1, .sharesTotal = 3'074'457'345'618'258'603}, .amount = 3, .expected = tecPATH_DRY},
        {.vault = {.available = 1, .sharesTotal = 3'074'457'345'618'258'603}, .amount = 4, .expected = tecPATH_DRY},
        {.vault = {.available = 1, .sharesTotal = 3'074'457'345'618'258'603}, .amount = 5, .expected = tecPATH_DRY},
        {.vault = {.available = 1, .sharesTotal = 3'074'457'345'618'258'604}, .amount = 1, .expected = tesSUCCESS},
        {.vault = {.available = 1, .sharesTotal = 3'074'457'345'618'258'604}, .amount = 2, .expected = tesSUCCESS},
        {.vault = {.available = 1, .sharesTotal = 3'074'457'345'618'258'604}, .amount = 3, .expected = tecPATH_DRY},
        {.vault = {.available = 1, .sharesTotal = 3'074'457'345'618'258'604}, .amount = 4, .expected = tecPATH_DRY},
        {.vault = {.available = 1, .sharesTotal = 3'074'457'345'618'258'604}, .amount = 5, .expected = tecPATH_DRY},
    };
    static constexpr ClawbackCase kHolderValue[] = {
        // holderShares 1, sharesTotal 2, amount 1
        {.vault = {.available = 2, .sharesTotal = 2, .holderShares = 1}, .amount = 1, .expected = tesSUCCESS},
        {.vault = {.available = 2, .sharesTotal = 2, .holderShares = 1}, .amount = 2, .expected = tecINSUFFICIENT_FUNDS},
        {.vault = {.available = 2, .sharesTotal = 2, .holderShares = 1}, .amount = 3, .expected = tecINSUFFICIENT_FUNDS},
        // holderShares 1'000'000'000, sharesTotal 1'000'000'001, amount 1'000'000'000
        {.vault = {.available = 1'000'000'001, .sharesTotal = 1'000'000'001, .holderShares = 999'999'998}, .amount = 999'999'998, .expected = tesSUCCESS},
        {.vault = {.available = 1'000'000'001, .sharesTotal = 1'000'000'001, .holderShares = 999'999'999}, .amount = 999'999'998, .expected = tesSUCCESS},
        {.vault = {.available = 1'000'000'001, .sharesTotal = 1'000'000'001, .holderShares = 1'000'000'000}, .amount = 999'999'998, .expected = tesSUCCESS},
        {.vault = {.available = 1'000'000'001, .sharesTotal = 1'000'000'001, .holderShares = 999'999'998}, .amount = 999'999'999, .expected = tecINSUFFICIENT_FUNDS},
        {.vault = {.available = 1'000'000'001, .sharesTotal = 1'000'000'001, .holderShares = 999'999'999}, .amount = 999'999'999, .expected = tesSUCCESS},
        {.vault = {.available = 1'000'000'001, .sharesTotal = 1'000'000'001, .holderShares = 1'000'000'000}, .amount = 999'999'999, .expected = tesSUCCESS},
        {.vault = {.available = 1'000'000'001, .sharesTotal = 1'000'000'001, .holderShares = 999'999'998}, .amount = 1'000'000'000, .expected = tecINSUFFICIENT_FUNDS},
        {.vault = {.available = 1'000'000'001, .sharesTotal = 1'000'000'001, .holderShares = 999'999'999}, .amount = 1'000'000'000, .expected = tecINSUFFICIENT_FUNDS},
        {.vault = {.available = 1'000'000'001, .sharesTotal = 1'000'000'001, .holderShares = 1'000'000'000}, .amount = 1'000'000'000, .expected = tesSUCCESS},
        {.vault = {.available = 1'000'000'001, .sharesTotal = 1'000'000'001, .holderShares = 999'999'998}, .amount = 1'000'000'001, .expected = tecINSUFFICIENT_FUNDS},
        {.vault = {.available = 1'000'000'001, .sharesTotal = 1'000'000'001, .holderShares = 999'999'999}, .amount = 1'000'000'001, .expected = tecINSUFFICIENT_FUNDS},
        {.vault = {.available = 1'000'000'001, .sharesTotal = 1'000'000'001, .holderShares = 1'000'000'000}, .amount = 1'000'000'001, .expected = tecINSUFFICIENT_FUNDS},
        {.vault = {.available = 1'000'000'001, .sharesTotal = 1'000'000'001, .holderShares = 999'999'998}, .amount = 1'000'000'002, .expected = tecINSUFFICIENT_FUNDS},
        {.vault = {.available = 1'000'000'001, .sharesTotal = 1'000'000'001, .holderShares = 999'999'999}, .amount = 1'000'000'002, .expected = tecINSUFFICIENT_FUNDS},
        {.vault = {.available = 1'000'000'001, .sharesTotal = 1'000'000'001, .holderShares = 1'000'000'000}, .amount = 1'000'000'002, .expected = tecINSUFFICIENT_FUNDS},
        // holderShares 1'000'000'000, sharesTotal 2'000'000'000, amount 1'000'000'000
        {.vault = {.available = 2'000'000'000, .sharesTotal = 2'000'000'000, .holderShares = 999'999'998}, .amount = 999'999'998, .expected = tesSUCCESS},
        {.vault = {.available = 2'000'000'000, .sharesTotal = 2'000'000'000, .holderShares = 999'999'999}, .amount = 999'999'998, .expected = tesSUCCESS},
        {.vault = {.available = 2'000'000'000, .sharesTotal = 2'000'000'000, .holderShares = 1'000'000'000}, .amount = 999'999'998, .expected = tesSUCCESS},
        {.vault = {.available = 2'000'000'000, .sharesTotal = 2'000'000'000, .holderShares = 1'000'000'001}, .amount = 999'999'998, .expected = tesSUCCESS},
        {.vault = {.available = 2'000'000'000, .sharesTotal = 2'000'000'000, .holderShares = 1'000'000'002}, .amount = 999'999'998, .expected = tesSUCCESS},
        {.vault = {.available = 2'000'000'000, .sharesTotal = 2'000'000'000, .holderShares = 999'999'998}, .amount = 999'999'999, .expected = tecINSUFFICIENT_FUNDS},
        {.vault = {.available = 2'000'000'000, .sharesTotal = 2'000'000'000, .holderShares = 999'999'999}, .amount = 999'999'999, .expected = tesSUCCESS},
        {.vault = {.available = 2'000'000'000, .sharesTotal = 2'000'000'000, .holderShares = 1'000'000'000}, .amount = 999'999'999, .expected = tesSUCCESS},
        {.vault = {.available = 2'000'000'000, .sharesTotal = 2'000'000'000, .holderShares = 1'000'000'001}, .amount = 999'999'999, .expected = tesSUCCESS},
        {.vault = {.available = 2'000'000'000, .sharesTotal = 2'000'000'000, .holderShares = 1'000'000'002}, .amount = 999'999'999, .expected = tesSUCCESS},
        {.vault = {.available = 2'000'000'000, .sharesTotal = 2'000'000'000, .holderShares = 999'999'998}, .amount = 1'000'000'000, .expected = tecINSUFFICIENT_FUNDS},
        {.vault = {.available = 2'000'000'000, .sharesTotal = 2'000'000'000, .holderShares = 999'999'999}, .amount = 1'000'000'000, .expected = tecINSUFFICIENT_FUNDS},
        {.vault = {.available = 2'000'000'000, .sharesTotal = 2'000'000'000, .holderShares = 1'000'000'000}, .amount = 1'000'000'000, .expected = tesSUCCESS},
        {.vault = {.available = 2'000'000'000, .sharesTotal = 2'000'000'000, .holderShares = 1'000'000'001}, .amount = 1'000'000'000, .expected = tesSUCCESS},
        {.vault = {.available = 2'000'000'000, .sharesTotal = 2'000'000'000, .holderShares = 1'000'000'002}, .amount = 1'000'000'000, .expected = tesSUCCESS},
        {.vault = {.available = 2'000'000'000, .sharesTotal = 2'000'000'000, .holderShares = 999'999'998}, .amount = 1'000'000'001, .expected = tecINSUFFICIENT_FUNDS},
        {.vault = {.available = 2'000'000'000, .sharesTotal = 2'000'000'000, .holderShares = 999'999'999}, .amount = 1'000'000'001, .expected = tecINSUFFICIENT_FUNDS},
        {.vault = {.available = 2'000'000'000, .sharesTotal = 2'000'000'000, .holderShares = 1'000'000'000}, .amount = 1'000'000'001, .expected = tecINSUFFICIENT_FUNDS},
        {.vault = {.available = 2'000'000'000, .sharesTotal = 2'000'000'000, .holderShares = 1'000'000'001}, .amount = 1'000'000'001, .expected = tesSUCCESS},
        {.vault = {.available = 2'000'000'000, .sharesTotal = 2'000'000'000, .holderShares = 1'000'000'002}, .amount = 1'000'000'001, .expected = tesSUCCESS},
        {.vault = {.available = 2'000'000'000, .sharesTotal = 2'000'000'000, .holderShares = 999'999'998}, .amount = 1'000'000'002, .expected = tecINSUFFICIENT_FUNDS},
        {.vault = {.available = 2'000'000'000, .sharesTotal = 2'000'000'000, .holderShares = 999'999'999}, .amount = 1'000'000'002, .expected = tecINSUFFICIENT_FUNDS},
        {.vault = {.available = 2'000'000'000, .sharesTotal = 2'000'000'000, .holderShares = 1'000'000'000}, .amount = 1'000'000'002, .expected = tecINSUFFICIENT_FUNDS},
        {.vault = {.available = 2'000'000'000, .sharesTotal = 2'000'000'000, .holderShares = 1'000'000'001}, .amount = 1'000'000'002, .expected = tecINSUFFICIENT_FUNDS},
        {.vault = {.available = 2'000'000'000, .sharesTotal = 2'000'000'000, .holderShares = 1'000'000'002}, .amount = 1'000'000'002, .expected = tesSUCCESS},
        // holderShares 9'999'999'999'999'998, sharesTotal 9'999'999'999'999'999, amount 9'999'999'999'999'998
        {.vault = {.available = 9'999'999'999'999'999, .sharesTotal = 9'999'999'999'999'999, .holderShares = 9'999'999'999'999'996}, .amount = 9'999'999'999'999'996, .expected = tesSUCCESS},
        {.vault = {.available = 9'999'999'999'999'999, .sharesTotal = 9'999'999'999'999'999, .holderShares = 9'999'999'999'999'997}, .amount = 9'999'999'999'999'996, .expected = tesSUCCESS},
        {.vault = {.available = 9'999'999'999'999'999, .sharesTotal = 9'999'999'999'999'999, .holderShares = 9'999'999'999'999'998}, .amount = 9'999'999'999'999'996, .expected = tesSUCCESS},
        {.vault = {.available = 9'999'999'999'999'999, .sharesTotal = 9'999'999'999'999'999, .holderShares = 9'999'999'999'999'996}, .amount = 9'999'999'999'999'997, .expected = tecINSUFFICIENT_FUNDS},
        {.vault = {.available = 9'999'999'999'999'999, .sharesTotal = 9'999'999'999'999'999, .holderShares = 9'999'999'999'999'997}, .amount = 9'999'999'999'999'997, .expected = tesSUCCESS},
        {.vault = {.available = 9'999'999'999'999'999, .sharesTotal = 9'999'999'999'999'999, .holderShares = 9'999'999'999'999'998}, .amount = 9'999'999'999'999'997, .expected = tesSUCCESS},
        {.vault = {.available = 9'999'999'999'999'999, .sharesTotal = 9'999'999'999'999'999, .holderShares = 9'999'999'999'999'996}, .amount = 9'999'999'999'999'998, .expected = tecINSUFFICIENT_FUNDS},
        {.vault = {.available = 9'999'999'999'999'999, .sharesTotal = 9'999'999'999'999'999, .holderShares = 9'999'999'999'999'997}, .amount = 9'999'999'999'999'998, .expected = tecINSUFFICIENT_FUNDS},
        {.vault = {.available = 9'999'999'999'999'999, .sharesTotal = 9'999'999'999'999'999, .holderShares = 9'999'999'999'999'998}, .amount = 9'999'999'999'999'998, .expected = tesSUCCESS},
        {.vault = {.available = 9'999'999'999'999'999, .sharesTotal = 9'999'999'999'999'999, .holderShares = 9'999'999'999'999'996}, .amount = 9'999'999'999'999'999, .expected = tecINSUFFICIENT_FUNDS},
        {.vault = {.available = 9'999'999'999'999'999, .sharesTotal = 9'999'999'999'999'999, .holderShares = 9'999'999'999'999'997}, .amount = 9'999'999'999'999'999, .expected = tecINSUFFICIENT_FUNDS},
        {.vault = {.available = 9'999'999'999'999'999, .sharesTotal = 9'999'999'999'999'999, .holderShares = 9'999'999'999'999'998}, .amount = 9'999'999'999'999'999, .expected = tecINSUFFICIENT_FUNDS},
        {.vault = {.available = 9'999'999'999'999'999, .sharesTotal = 9'999'999'999'999'999, .holderShares = 9'999'999'999'999'996}, .amount = 10'000'000'000'000'000, .expected = tecINSUFFICIENT_FUNDS},
        {.vault = {.available = 9'999'999'999'999'999, .sharesTotal = 9'999'999'999'999'999, .holderShares = 9'999'999'999'999'997}, .amount = 10'000'000'000'000'000, .expected = tecINSUFFICIENT_FUNDS},
        {.vault = {.available = 9'999'999'999'999'999, .sharesTotal = 9'999'999'999'999'999, .holderShares = 9'999'999'999'999'998}, .amount = 10'000'000'000'000'000, .expected = tecINSUFFICIENT_FUNDS},
        // holderShares 4'999'999'999'999'999, sharesTotal 9'999'999'999'999'998, amount 4'999'999'999'999'999
        {.vault = {.available = 9'999'999'999'999'998, .sharesTotal = 9'999'999'999'999'998, .holderShares = 4'999'999'999'999'997}, .amount = 4'999'999'999'999'997, .expected = tesSUCCESS},
        {.vault = {.available = 9'999'999'999'999'998, .sharesTotal = 9'999'999'999'999'998, .holderShares = 4'999'999'999'999'998}, .amount = 4'999'999'999'999'997, .expected = tesSUCCESS},
        {.vault = {.available = 9'999'999'999'999'998, .sharesTotal = 9'999'999'999'999'998, .holderShares = 4'999'999'999'999'999}, .amount = 4'999'999'999'999'997, .expected = tesSUCCESS},
        {.vault = {.available = 9'999'999'999'999'998, .sharesTotal = 9'999'999'999'999'998, .holderShares = 5'000'000'000'000'000}, .amount = 4'999'999'999'999'997, .expected = tesSUCCESS},
        {.vault = {.available = 9'999'999'999'999'998, .sharesTotal = 9'999'999'999'999'998, .holderShares = 5'000'000'000'000'001}, .amount = 4'999'999'999'999'997, .expected = tesSUCCESS},
        {.vault = {.available = 9'999'999'999'999'998, .sharesTotal = 9'999'999'999'999'998, .holderShares = 4'999'999'999'999'997}, .amount = 4'999'999'999'999'998, .expected = tecINSUFFICIENT_FUNDS},
        {.vault = {.available = 9'999'999'999'999'998, .sharesTotal = 9'999'999'999'999'998, .holderShares = 4'999'999'999'999'998}, .amount = 4'999'999'999'999'998, .expected = tesSUCCESS},
        {.vault = {.available = 9'999'999'999'999'998, .sharesTotal = 9'999'999'999'999'998, .holderShares = 4'999'999'999'999'999}, .amount = 4'999'999'999'999'998, .expected = tesSUCCESS},
        {.vault = {.available = 9'999'999'999'999'998, .sharesTotal = 9'999'999'999'999'998, .holderShares = 5'000'000'000'000'000}, .amount = 4'999'999'999'999'998, .expected = tesSUCCESS},
        {.vault = {.available = 9'999'999'999'999'998, .sharesTotal = 9'999'999'999'999'998, .holderShares = 5'000'000'000'000'001}, .amount = 4'999'999'999'999'998, .expected = tesSUCCESS},
        {.vault = {.available = 9'999'999'999'999'998, .sharesTotal = 9'999'999'999'999'998, .holderShares = 4'999'999'999'999'997}, .amount = 4'999'999'999'999'999, .expected = tecINSUFFICIENT_FUNDS},
        {.vault = {.available = 9'999'999'999'999'998, .sharesTotal = 9'999'999'999'999'998, .holderShares = 4'999'999'999'999'998}, .amount = 4'999'999'999'999'999, .expected = tecINSUFFICIENT_FUNDS},
        {.vault = {.available = 9'999'999'999'999'998, .sharesTotal = 9'999'999'999'999'998, .holderShares = 4'999'999'999'999'999}, .amount = 4'999'999'999'999'999, .expected = tesSUCCESS},
        {.vault = {.available = 9'999'999'999'999'998, .sharesTotal = 9'999'999'999'999'998, .holderShares = 5'000'000'000'000'000}, .amount = 4'999'999'999'999'999, .expected = tesSUCCESS},
        {.vault = {.available = 9'999'999'999'999'998, .sharesTotal = 9'999'999'999'999'998, .holderShares = 5'000'000'000'000'001}, .amount = 4'999'999'999'999'999, .expected = tesSUCCESS},
        {.vault = {.available = 9'999'999'999'999'998, .sharesTotal = 9'999'999'999'999'998, .holderShares = 4'999'999'999'999'997}, .amount = 5'000'000'000'000'000, .expected = tecINSUFFICIENT_FUNDS},
        {.vault = {.available = 9'999'999'999'999'998, .sharesTotal = 9'999'999'999'999'998, .holderShares = 4'999'999'999'999'998}, .amount = 5'000'000'000'000'000, .expected = tecINSUFFICIENT_FUNDS},
        {.vault = {.available = 9'999'999'999'999'998, .sharesTotal = 9'999'999'999'999'998, .holderShares = 4'999'999'999'999'999}, .amount = 5'000'000'000'000'000, .expected = tecINSUFFICIENT_FUNDS},
        {.vault = {.available = 9'999'999'999'999'998, .sharesTotal = 9'999'999'999'999'998, .holderShares = 5'000'000'000'000'000}, .amount = 5'000'000'000'000'000, .expected = tesSUCCESS},
        {.vault = {.available = 9'999'999'999'999'998, .sharesTotal = 9'999'999'999'999'998, .holderShares = 5'000'000'000'000'001}, .amount = 5'000'000'000'000'000, .expected = tesSUCCESS},
        {.vault = {.available = 9'999'999'999'999'998, .sharesTotal = 9'999'999'999'999'998, .holderShares = 4'999'999'999'999'997}, .amount = 5'000'000'000'000'001, .expected = tecINSUFFICIENT_FUNDS},
        {.vault = {.available = 9'999'999'999'999'998, .sharesTotal = 9'999'999'999'999'998, .holderShares = 4'999'999'999'999'998}, .amount = 5'000'000'000'000'001, .expected = tecINSUFFICIENT_FUNDS},
        {.vault = {.available = 9'999'999'999'999'998, .sharesTotal = 9'999'999'999'999'998, .holderShares = 4'999'999'999'999'999}, .amount = 5'000'000'000'000'001, .expected = tecINSUFFICIENT_FUNDS},
        {.vault = {.available = 9'999'999'999'999'998, .sharesTotal = 9'999'999'999'999'998, .holderShares = 5'000'000'000'000'000}, .amount = 5'000'000'000'000'001, .expected = tecINSUFFICIENT_FUNDS},
        {.vault = {.available = 9'999'999'999'999'998, .sharesTotal = 9'999'999'999'999'998, .holderShares = 5'000'000'000'000'001}, .amount = 5'000'000'000'000'001, .expected = tesSUCCESS},
    };
    static constexpr ClawbackCase kNative[] = {
        {.vault = {.available = 1'000'000'000, .sharesTotal = 1'000'000'000}, .amount = 0, .expected = tecNO_PERMISSION, .omitAmount = true},
        {.vault = {.available = 1, .sharesTotal = 1}, .amount = 0, .expected = tecNO_PERMISSION, .omitAmount = true},
    };
    // clang-format on

    // Runs every list on the vaults staged open-ended or, when `closed`, closed-ended in Investment
    // with a 5% early-exit fee: clawback has no phase or fee logic, so it behaves as on an
    // open-ended vault even where withdraw would charge the fee.
    void
    runClawbackBoundaries(jtx::Env& env, Setup const& s, bool closed)
    {
        std::uint32_t const p = parentCloseTime(env);
        auto const run = [&](std::string const& name,
                             TestVaults const& vaults,
                             std::span<ClawbackCase const> cases) {
            testcase("clawback " + name + (closed ? ", closed-ended" : ""));
            for (Keylet const& vault : vaults)
            {
                for (std::size_t i = 0;
                     auto const& [row, amount, expected, burn, availableExponent, omitAmount] :
                     cases)
                {
                    StagedVault staged = row;
                    if (closed)
                        inInvestment(staged, p, kFee5Pct);
                    STAmount const claw = burn ? STAmount{shareIssue(env, vault), amount}
                                               : vaultUnits(env, vault, amount);
                    StagedAmounts amounts = stagedAmounts(env, vault, staged);
                    std::string at = rowText(i++, vaultName(env, vault)) + sampleText(staged, claw);
                    if (availableExponent)
                    {
                        amounts.available =
                            vaultUnits(env, vault, row.available, *availableExponent);
                        at += "available at grid exponent " + std::to_string(*availableExponent) +
                            ": ";
                    }
                    AppliedVaultTx const cpp = applyClawback(
                        env,
                        vault,
                        burn ? owner_ : issuer_,
                        holder_,
                        amounts,
                        omitAmount ? std::nullopt : std::optional<STAmount>{claw});
                    LeanVaultResult const lean = burn
                        ? leanOwnerBurn(cpp, amounts, claw)
                        : leanClawback(cpp, amounts, claw, shareIssue(env, vault));
                    expectSame(*this, at, cpp, lean, expected);
                }
            }
        };

        run("owner burn", s.all, kBurn);
        run("owner burn, no shares", s.all, kBurnNoShares);
        run("zero shares", s.clawable, kZeroShares);
        run("zero shares, recovery rounds up", s.mpt, kZeroSharesMpt);
        run("zero shares, recovery floors", s.ious, kZeroSharesIou);
        run("clamp to zero", s.ious, kClampToZero);
        run("clamp to available", s.clawable, kAvailable);
        run("coarse claw-all", s.ious, kCoarseClawAll);
        run("decade crossing", s.ious, kDecade);
        run("loss waiver", s.clawable, kWaiver);
        run("share overflow", s.clawable, kShareOverflow);
        run("holder value", s.clawable, kHolderValue);
        run("native", s.xrp, kNative);
    }

    void
    testClawbackBoundaries(jtx::Env& env, Setup const& s)
    {
        runClawbackBoundaries(env, s, false);
    }

    // The same lists on a closed-ended vault. Clawback reads neither the phase nor the early-exit
    // fee, so there are no lists only a closed-ended vault has.
    void
    testClosedEndedClawbackBoundaries(jtx::Env& env, Setup const& s)
    {
        runClawbackBoundaries(env, s, true);
    }

    void
    runTests() override
    {
        jtx::Env env{*this, vaultTestAmendments()};
        Setup const s = setup(env);
        Keylet const& mptVault = s.mptVault;
        Keylet const& iouVault = s.iouDefaultScaleVault;

        Number const iouMax{9'999'999'999'999'999LL, 80};

        // Asset clawback by the issuer: partial, full, and over-seed (clamped to available).
        testClawbackAsset(env, mptVault, 1'000, 400, tesSUCCESS);
        testClawbackAsset(env, mptVault, 1'000, 1'000, tesSUCCESS);
        // covered by testClawbackBoundaries
        testClawbackAsset(env, mptVault, 1'000, 1'001, tesSUCCESS);

        // canBurnShares over VALID (assetsTotal, assetsAvailable, sharesTotal) states
        struct CanBurnRow
        {
            Number assetsTotal;
            Number available;
            std::uint64_t sharesTotal{};
            TER expected;
        };
        // clang-format off
        CanBurnRow const canBurnRows[] = {
            // covered by testClawbackBoundaries
            {.assetsTotal = Number{0}, .available = Number{0}, .sharesTotal = 0, .expected = tecNO_PERMISSION},
            {.assetsTotal = Number{0}, .available = Number{0}, .sharesTotal = 1'000, .expected = tesSUCCESS},
            {.assetsTotal = Number{1'000}, .available = Number{0}, .sharesTotal = 1'000, .expected = tecNO_PERMISSION},
            {.assetsTotal = Number{1'000}, .available = Number{1'000}, .sharesTotal = 1'000, .expected = tecNO_PERMISSION},
            {.assetsTotal = Number{0}, .available = Number{0}, .sharesTotal = kMaxMpTokenAmount, .expected = tesSUCCESS},
            // Per-field extremes: huge assets deny
            {.assetsTotal = iouMax, .available = iouMax, .sharesTotal = 1'000, .expected = tecNO_PERMISSION},
            {.assetsTotal = iouMax, .available = Number{0}, .sharesTotal = 1'000, .expected = tecNO_PERMISSION},
        };
        // clang-format on
        for (CanBurnRow const& r : canBurnRows)
            testCanBurnShares(env, iouVault, r.assetsTotal, r.available, r.sharesTotal, r.expected);
        testBurnSharesPartialAmount(env, iouVault);

        // The holder's deposit, all of it burnt, against the staged outstanding shares.
        struct BurnRow
        {
            std::int64_t held{};
            std::uint64_t outstanding{};
        };
        // clang-format off
        static constexpr BurnRow kBurnRows[] = {
            // covered by testClawbackBoundaries
            {.held = 1'000'000'000, .outstanding = 1'000'000'000},
            {.held = 1'000'000'000, .outstanding = 2'000'000'000},
            {.held = kOpenLimitUnits, .outstanding = kOpenLimitUnits},
            {.held = 1, .outstanding = kMaxMpTokenAmount},
            {.held = 1, .outstanding = 1},
        };
        // clang-format on
        for (BurnRow const& r : kBurnRows)
            testBurnShares(env, mptVault, r.held, r.outstanding);

        struct ClawbackRow
        {
            std::int64_t seed{};
            std::int64_t amount{};
            TER expected;
        };
        // clang-format off
        static ClawbackRow const kClawbackRows[] = {
            {.seed = kOpenLimitUnits, .amount = kOpenLimitUnits, .expected = tesSUCCESS},
            {.seed = kOpenLimitUnits, .amount = kOpenLimitUnits / 2, .expected = tesSUCCESS},
            {.seed = kOpenLimitUnits, .amount = 1, .expected = tesSUCCESS},
            {.seed = 1, .amount = 1, .expected = tesSUCCESS},
            {.seed = 1'000, .amount = 0, .expected = tesSUCCESS},
        };
        // clang-format on
        for (ClawbackRow const& r : kClawbackRows)
            testClawbackAsset(env, mptVault, r.seed, r.amount, r.expected);
        testClawbackAllNotSole(env, mptVault, false);
        testClawbackAllNotSole(env, mptVault, true);
        testClawbackAllWhileDeployed(env, iouVault);

        // NAV-drifted vault (owner donation)
        testClawbackDrifted(env, mptVault, 3, 2, 3, tesSUCCESS);
        testClawbackDrifted(env, mptVault, 7, 5, 4, tesSUCCESS);

        testUpdatedStateClawback(Number{1'000}, Number{0}, 1'000, 400, tecPRECISION_LOSS);

        testClawbackBoundaries(env, s);

        testClawbackInInvestment(env, s);
        testClosedEndedClawbackBoundaries(env, s);
    }
};

BEAST_DEFINE_TESTSUITE(LeanVaultClawback, formal_verification, xrpl);

}  // namespace xrpl::test::formal_verification
