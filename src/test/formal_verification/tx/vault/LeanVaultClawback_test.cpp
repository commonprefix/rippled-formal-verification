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
#include <xrpl/protocol/MPTIssue.h>
#include <xrpl/protocol/Protocol.h>
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
        StagedAmounts staged,
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
        StagedAmounts const& staged,
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
    checkBurn(jtx::Env& env, Keylet const& vault, StagedAmounts const& staged, std::int64_t amount)
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
        env(jtx::Vault::clawback({
                .issuer = issuer,
                .id = vaultKeylet.key,
                .holder = holder,
                .amount = omitAmount ? std::nullopt : std::optional<STAmount>{amount},
            }),
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
        StagedAmounts const staged{
            .available = vaultUnits(env, vault, 1'500),
            .sharesTotal = 1'500,
            .holderShares = 1'000,
            .pseudoHolding = true,
        };
        expectStagedClawback(env, vault, staged, vaultUnits(env, vault, 0), tesSUCCESS, omitAmount);
    }

    // A coarsened IOU vault whose deployed assets round away against the total: clawing every
    // share would leave the deployed assets without shares. Covered by testCoarseClawAllSweep.
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
    // testBurnSweep.
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
        StagedAmounts const staged{
            .available = vaultUnits(env, vault, 0),
            .sharesTotal = stagedOutstanding,
            .holderShares = static_cast<std::uint64_t>(deposit),
        };
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

    // ---- Sweeps -------------------------------------------------------------------------------

    // The vaults a sweep runs on; holder_ holds their shares.
    using SweepVaults = std::vector<Keylet>;

    // A sole holder of price row `c` (assets total, shares total) claws back its amount.
    TER
    checkPriceCase(jtx::Env& env, Keylet const& vault, PriceCusp const& c)
    {
        StagedAmounts const staged{
            .available = vaultUnits(env, vault, c.total),
            .sharesTotal = static_cast<std::uint64_t>(c.sharesTotal),
            .pseudoHolding = true,
        };
        return checkClawback(env, vault, staged, vaultUnits(env, vault, c.amount)).cpp.ter;
    }

    // Holder value: a clawback from one of several holders burns trunc(shares total * amount /
    // assets total) shares; C++ refuses (tecINSUFFICIENT_FUNDS) once that exceeds the holder's
    // shares. At price 1 the cusp is amount == the holder's shares.
    void
    testHolderValueSweep(jtx::Env& env, SweepVaults const& vaults)
    {
        for (Keylet const& vault : vaults)
        {
            auto const units = [&](std::int64_t n) { return vaultUnits(env, vault, n); };
            auto const shares = [](std::int64_t n) { return static_cast<std::uint64_t>(n); };
            beginCase(("clawback " + vaultName(env, vault) + " holder value-Sweep").c_str());
            for (auto const& [cusp, cases] : kHolderValueCases)
            {
                std::set<TER> seen;
                for (HolderValueCusp const& c : cases)
                {
                    StagedAmounts const staged{
                        .available = units(c.sharesTotal),
                        .sharesTotal = shares(c.sharesTotal),
                        .holderShares = shares(c.holderShares),
                        .pseudoHolding = true,
                    };
                    seen.insert(checkClawback(env, vault, staged, units(c.amount)).cpp.ter);
                }
                expectCrossed(cusp, seen, {tecINSUFFICIENT_FUNDS});
            }
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
            auto const shares = [](std::int64_t n) { return static_cast<std::uint64_t>(n); };
            beginCase(("clawback " + vaultName(env, vault) + " owner burn-Sweep").c_str());
            auto const check = [&](BurnCusp const& c) {
                StagedAmounts const staged{
                    .available = vaultUnits(env, vault, c.available),
                    .sharesTotal = shares(c.sharesTotal),
                    .holderShares = shares(c.holderShares),
                    .pseudoHolding = true,
                };
                return checkBurn(env, vault, staged, c.amount);
            };
            for (auto const& [cusp, cases] : kBurnCases)
            {
                std::set<TER> seen;
                for (BurnCusp const& c : cases)
                {
                    seen.insert(check(c));
                }
                expectCrossed(cusp, seen, {tecLIMIT_EXCEEDED});
            }
            for (auto const& [cusp, cases] : kBurnNoSharesCases)
            {
                std::set<TER> seen;
                for (BurnCusp const& c : cases)
                {
                    seen.insert(check(c));
                }
                expectCrossed(cusp, seen, {tecPRECISION_LOSS});
            }
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
            for (auto const& [cusp, cases] : kZeroSharesCases)
            {
                std::set<TER> seen;
                for (PriceCusp const& c : cases)
                {
                    seen.insert(checkPriceCase(env, vault, c));
                }
                expectCrossed(cusp, seen, {tecPRECISION_LOSS});
            }
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
            for (auto const& [cusp, cases] : kClampToZeroCases)
            {
                std::set<TER> seen;
                for (PriceCusp const& c : cases)
                {
                    seen.insert(checkPriceCase(env, vault, c));
                }
                expectCrossed(cusp, seen, {tecPRECISION_LOSS});
            }
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
            auto const units = [&](std::int64_t n) { return vaultUnits(env, vault, n); };
            auto const shares = [](std::int64_t n) { return static_cast<std::uint64_t>(n); };
            beginCase(("clawback " + vaultName(env, vault) + " clamp to available-Sweep").c_str());
            for (auto const& [cusp, cases] : kAvailableCases)
            {
                for (AvailableCusp const& c : cases)
                {
                    StagedAmounts const staged{
                        .available = units(c.available),
                        .deployed = units(c.deployed),
                        .sharesTotal = shares(c.available + c.deployed),
                        .pseudoHolding = true,
                    };
                    checkClawback(env, vault, staged, units(c.amount));
                }
            }
        }
    }

    // Decade-crossing outflow: the recovery is truncated to the grid of available - amount, ten
    // units from 10^16 units up, so there a one-unit clawback truncates to zero
    // (tecPRECISION_LOSS). Each row leaves exactly 10^16 - 1 or 10^16 units, at price 1, from a
    // holder of all shares but one.
    void
    testDecadeSweep(jtx::Env& env, SweepVaults const& vaults)
    {
        for (Keylet const& vault : vaults)
        {
            beginCase(("clawback " + vaultName(env, vault) + " decade crossing-Sweep").c_str());
            auto const sle = env.le(vault);
            Asset const asset = sle->at(sfAsset);
            int const scale = sle->at(sfScale);
            for (auto const& [cusp, cases] : kDecadeCases)
            {
                std::set<TER> seen;
                for (DecadeCusp const& c : cases)
                {
                    auto const sharesTotal = static_cast<std::uint64_t>(c.availableMantissa * 10);
                    StagedAmounts const staged{
                        .available =
                            STAmount{
                                asset, static_cast<std::uint64_t>(c.availableMantissa), 1 - scale},
                        .sharesTotal = sharesTotal,
                        .holderShares = sharesTotal - 1,
                        .pseudoHolding = true,
                    };
                    seen.insert(checkClawback(env, vault, staged, vaultUnits(env, vault, c.amount))
                                    .cpp.ter);
                }
                expectCrossed(cusp, seen, {tecPRECISION_LOSS});
            }
        }
    }

    // Sole-holder loss waiver: a holder of every share is priced at the assets total, any other at
    // assets total - loss unrealized, so the same amount burns more shares. Both sides succeed;
    // the post-states and recoveries are compared.
    void
    testWaiverSweep(jtx::Env& env, SweepVaults const& vaults)
    {
        for (Keylet const& vault : vaults)
        {
            auto const units = [&](std::int64_t n) { return vaultUnits(env, vault, n); };
            auto const shares = [](std::int64_t n) { return static_cast<std::uint64_t>(n); };
            beginCase(("clawback " + vaultName(env, vault) + " loss waiver-Sweep").c_str());
            for (auto const& [cusp, cases] : kWaiverCases)
            {
                for (WaiverCusp const& c : cases)
                {
                    StagedAmounts const staged{
                        .available = units(c.total - c.deployed),
                        .deployed = units(c.deployed),
                        .loss = units(c.loss),
                        .sharesTotal = shares(c.total),
                        .holderShares = shares(c.holderShares),
                        .pseudoHolding = true,
                    };
                    checkClawback(env, vault, staged, units(c.amount));
                }
            }
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
            auto const units = [&](std::int64_t n) { return vaultUnits(env, vault, n); };
            beginCase(("clawback " + vaultName(env, vault) + " coarse claw-all-Sweep").c_str());
            Asset const asset = env.le(vault)->at(sfAsset);
            int const base = -static_cast<int>(env.le(vault)->at(sfScale));
            for (auto const& [cusp, cases] : kCoarseClawAllCases)
            {
                std::set<TER> seen;
                for (CoarseClawAllCusp const& c : cases)
                {
                    StagedAmounts const staged{
                        .available =
                            STAmount{
                                asset, static_cast<std::uint64_t>(c.mantissa), base + c.exponent},
                        .deployed = units(c.deployed),
                        .sharesTotal = kCoarseShares,
                        .pseudoHolding = true,
                    };
                    seen.insert(checkClawback(env, vault, staged, units(0)).cpp.ter);
                }
                expectCrossed(cusp, seen, {tecHAS_OBLIGATIONS});
            }
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
            for (auto const& [cusp, cases] : clawback_sweep::kShareOverflowCases)
            {
                std::set<TER> seen;
                for (PriceCusp const& c : cases)
                {
                    seen.insert(checkPriceCase(env, vault, c));
                }
                expectCrossed(cusp, seen, {tecPATH_DRY});
            }
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
        // Outstanding MPT (the cap) covers any staged holding the issuer claws back.
        env(pay(issuer_, holder_, mpt(kShareCap)));
        env.close();

        Keylet const mptVault = createVault(env, owner_, mpt);
        // IOU at the smallest, the default and the largest vault scale.
        Keylet const iouMinScaleVault = createVault(env, owner_, iou, kVaultMinimumIouScale);
        Keylet const iouDefaultScaleVault = createVault(env, owner_, iou, kVaultDefaultIouScale);
        Keylet const iouMaxScaleVault =
            createVault(env, owner_, iou, kFixedPrecisionVaultMaximumIouScale);
        SweepVaults const all{mptVault, iouMinScaleVault, iouDefaultScaleVault, iouMaxScaleVault};
        SweepVaults const ious{iouMinScaleVault, iouDefaultScaleVault, iouMaxScaleVault};
        // One unit each: the holder gets its share MPToken and an IOU vault its pseudo-account
        // trust line, which staging state on the vault needs.
        for (Keylet const& vault : all)
        {
            env(jtx::Vault::deposit(
                {.depositor = holder_, .id = vault.key, .amount = vaultUnits(env, vault, 1)}));
        }
        env.close();

        Number const iouMax{9'999'999'999'999'999LL, 80};

        // Asset clawback by the issuer: partial, full, and over-seed (clamped to available).
        testClawbackAsset(env, mptVault, 1'000, 400, tesSUCCESS);
        testClawbackAsset(env, mptVault, 1'000, 1'000, tesSUCCESS);
        testClawbackAsset(
            env, mptVault, 1'000, 1'001, tesSUCCESS);  // covered by testClampToAvailableSweep

        // canBurnShares over VALID (assetsTotal, assetsAvailable, sharesTotal) states
        // Covered by testBurnSweep.
        testCanBurnShares(env, iouDefaultScaleVault, Number{0}, Number{0}, 0, tecNO_PERMISSION);
        testCanBurnShares(env, iouDefaultScaleVault, Number{0}, Number{0}, 1'000, tesSUCCESS);
        testCanBurnShares(
            env, iouDefaultScaleVault, Number{1'000}, Number{0}, 1'000, tecNO_PERMISSION);
        testCanBurnShares(
            env, iouDefaultScaleVault, Number{1'000}, Number{1'000}, 1'000, tecNO_PERMISSION);
        testCanBurnShares(
            env, iouDefaultScaleVault, Number{0}, Number{0}, kMaxMpTokenAmount, tesSUCCESS);
        // Per-field extremes: huge assets deny
        testCanBurnShares(env, iouDefaultScaleVault, iouMax, iouMax, 1'000, tecNO_PERMISSION);
        testCanBurnShares(env, iouDefaultScaleVault, iouMax, Number{0}, 1'000, tecNO_PERMISSION);
        testBurnSharesPartialAmount(env, iouDefaultScaleVault);

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
        testClawbackAllWhileDeployed(env, iouDefaultScaleVault);

        // NAV-drifted vault (owner donation)
        testClawbackDrifted(env, mptVault, 3, 2, 3, tesSUCCESS);
        testClawbackDrifted(env, mptVault, 7, 5, 4, tesSUCCESS);

        // Own ledgers: these stage values an MPT amount cannot hold.
        testUpdatedStateClawback(iouMax, iouMax, 1'000, 1, tecPRECISION_LOSS);
        testUpdatedStateClawback(iouMax, iouMax, kMaxMpTokenAmount, 1, tecPRECISION_LOSS);
        testUpdatedStateClawback(Number{1'000}, Number{0}, 1'000, 400, tecPRECISION_LOSS);

        testBurnSweep(env, all);
        testZeroSharesSweep(env, all);
        testClampToZeroSweep(env, ious);
        testClampToAvailableSweep(env, all);
        testCoarseClawAllSweep(env, ious);
        testDecadeSweep(env, ious);
        testWaiverSweep(env, all);
        testShareOverflowSweep(env, all);

        // Clawing back more than a non-sole holder's shares are worth is tecINSUFFICIENT_FUNDS
        // on both sides (C++ at the share transfer).
        testHolderValueSweep(env, all);
    }
};

BEAST_DEFINE_TESTSUITE(LeanVaultClawback, formal_verification, xrpl);

}  // namespace xrpl::test::formal_verification
