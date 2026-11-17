#include <test/formal_verification/common/LeanSuite.h>
#include <test/formal_verification/ffi/vault/VaultFFI.h>
#include <test/formal_verification/ffi/vault/VaultWithdrawFFI.h>
#include <test/formal_verification/tx/vault/VaultTestHelpers.h>
#include <test/formal_verification/tx/vault/WithdrawSweepCases.h>
#include <test/jtx/Account.h>
#include <test/jtx/Env.h>
#include <test/jtx/amount.h>
#include <test/jtx/mpt.h>
#include <test/jtx/pay.h>

#include <xrpl/basics/Number.h>
#include <xrpl/protocol/Protocol.h>
#include <xrpl/protocol/SField.h>
#include <xrpl/protocol/STNumber.h>
#include <xrpl/protocol/TER.h>

#include <chrono>
#include <cstdint>
#include <optional>
#include <string>
#include <utility>
#include <vector>

namespace xrpl::test::formal_verification {

using namespace withdraw_sweep;

class LeanVaultWithdraw_test : public LeanSuite
{
    void
    expectStagedWithdraw(
        jtx::Env& env,
        Keylet const& vault,
        jtx::Account const& holder,
        StagedAmounts const& staged,
        STAmount const& amount,
        TER expected)
    {
        TER const ter = checkWithdraw(*this, env, vault, holder, staged, amount).ter;
        BEAST_EXPECTS(
            ter == expected, "cpp=" + transToken(ter) + " expected " + transToken(expected));
    }

    // A vault after a first deposit of `seed` by the holder, who owns the seed * 10^scale shares.
    static StagedAmounts
    seededVault(jtx::Env& env, Keylet const& vault, STAmount const& seed)
    {
        int const scale = env.le(vault)->at(sfScale);
        auto const shares =
            static_cast<std::uint64_t>(static_cast<std::int64_t>(Number{seed} * Number{1, scale}));
        return StagedAmounts{.available = seed, .sharesTotal = shares, .holderShares = shares};
    }

    // A state staged over a vault the holder seeded with 1000 units (the holder keeps the seed's
    // shares); the total splits into `available` and the deployed rest.
    static StagedAmounts
    overSeed(
        jtx::Env& env,
        Keylet const& vault,
        Number const& assetsTotal,
        Number const& assetsAvailable,
        std::uint64_t sharesTotal)
    {
        Asset const asset = env.le(vault)->at(sfAsset);
        StagedAmounts staged = seededVault(env, vault, STAmount{asset, Number{1'000}});
        staged.available = STAmount{asset, assetsAvailable};
        staged.deployed = STAmount{asset, assetsTotal - assetsAvailable};
        staged.sharesTotal = sharesTotal;
        return staged;
    }

    void
    testWithdrawXRP(
        jtx::Env& env,
        Keylet const& vault,
        jtx::Account const& holder,
        STAmount seed,
        STAmount amount,
        TER expected)
    {
        testcase("withdraw XRP " + amount.getText() + " from " + seed.getText());
        expectStagedWithdraw(env, vault, holder, seededVault(env, vault, seed), amount, expected);
    }

    void
    testWithdrawIOU(
        jtx::Env& env,
        Keylet const& vault,
        jtx::Account const& holder,
        Number seed,
        Number amount,
        TER expected)
    {
        testcase("withdraw IOU " + to_string(amount) + " from " + to_string(seed));
        Asset const asset = env.le(vault)->at(sfAsset);
        expectStagedWithdraw(
            env,
            vault,
            holder,
            seededVault(env, vault, STAmount{asset, seed}),
            STAmount{asset, amount},
            expected);
    }

    void
    testWithdrawMPT(
        jtx::Env& env,
        Keylet const& vault,
        jtx::Account const& holder,
        std::int64_t seed,
        std::int64_t amount,
        TER expected)
    {
        testcase("withdraw MPT " + std::to_string(amount) + " from " + std::to_string(seed));
        expectStagedWithdraw(
            env,
            vault,
            holder,
            seededVault(env, vault, vaultUnits(env, vault, seed)),
            vaultUnits(env, vault, amount),
            expected);
    }

    void
    testWithdrawAllShares(jtx::Env& env, Keylet const& vault, jtx::Account const& holder)
    {
        testcase("withdraw all shares (full redemption)");
        Asset const asset = env.le(vault)->at(sfAsset);
        StagedAmounts const staged = seededVault(env, vault, STAmount{asset, Number{1'000}});
        STAmount const allShares{shareIssue(env, vault), staged.sharesTotal};
        expectStagedWithdraw(env, vault, holder, staged, allShares, tesSUCCESS);
    }

    // Validate sharesToAssetsWithdraw through the withdraw tx
    void
    testSharesToAssets(
        jtx::Env& env,
        Keylet const& vault,
        jtx::Account const& holder,
        Number seed,
        Number donation,
        std::int64_t shareCount)
    {
        testcase(
            "sharesToAssetsWithdraw " + std::to_string(shareCount) +
            " shares (seed=" + to_string(seed) + ", donation=" + to_string(donation) + ")");

        // A donation adds assets but no shares.
        Asset const asset = env.le(vault)->at(sfAsset);
        StagedAmounts staged = seededVault(env, vault, STAmount{asset, seed});
        staged.available = STAmount{asset, seed + donation};
        STAmount const shares{shareIssue(env, vault), shareCount};
        AppliedVaultTx const cpp = checkWithdraw(*this, env, vault, holder, staged, shares);
        BEAST_EXPECTS(cpp.ter == tesSUCCESS, "cpp=" + transToken(cpp.ter));
        Number const paid = cpp.pre.assetsAvailable - cpp.post.assetsAvailable;

        LeanSharesToAssetsResult const lean = leanSharesToAssetsWithdraw(cpp.pre, shares, false);
        expectLawful(lean);
        BEAST_EXPECTS(!lean.leanError.has_value(), "lean sharesToAssetsWithdraw error");
        // The payout is the conversion clamped toward zero to the vault grid.
        Number const conversion{lean.assets};
        BEAST_EXPECTS(
            (conversion >= paid && conversion - paid < Number{1, -static_cast<int>(cpp.pre.scale)}),
            "conversion " + to_string(conversion) + " is not the payout " + to_string(paid) +
                " before the clamp");
    }

    // Force an extreme vault state a real deposit cannot reach, then withdraw and compare.
    void
    testWithdrawUpdatedState(
        jtx::Env& env,
        Keylet const& vault,
        jtx::Account const& holder,
        Number const& assetsTotal,
        Number const& assetsAvailable,
        std::uint64_t sharesTotal,
        std::int64_t shareAmount,
        TER expected)
    {
        testcase(
            "withdraw updated-state shares=" + std::to_string(shareAmount) + " (assetsTotal=" +
            to_string(assetsTotal) + ", assetsAvailable=" + to_string(assetsAvailable) +
            ", sharesTotal=" + std::to_string(sharesTotal) + ")");
        expectStagedWithdraw(
            env,
            vault,
            holder,
            overSeed(env, vault, assetsTotal, assetsAvailable, sharesTotal),
            STAmount{shareIssue(env, vault), shareAmount},
            expected);
    }

    // Withdraw by assets from a vault whose sharesTotal is INT64_MAX, so the share computation
    // (sharesTotal * assets / NAV) overflows the MPT domain.
    void
    testWithdrawAssetsShareOverflow(
        jtx::Env& env,
        Keylet const& vault,
        jtx::Account const& holder,
        TER expected)
    {
        testcase("withdraw assets with INT64_MAX shares");
        Asset const asset = env.le(vault)->at(sfAsset);
        expectStagedWithdraw(
            env,
            vault,
            holder,
            overSeed(env, vault, Number{1}, Number{1}, kMaxMpTokenAmount),
            STAmount{asset, Number{1'000}},
            expected);
    }

    // ---- Sweeps --------------------------------------------------------------------------------

    // The vaults a sweep runs on, each with the account that withdraws from it.
    using SweepVaults = std::vector<std::pair<Keylet, jtx::Account>>;

    // A staged vault in its Investment phase (closed-ended, between its two dates) with an
    // early-exit fee rate.
    static StagedAmounts
    inInvestment(jtx::Env& env, StagedAmounts staged, std::int64_t rate)
    {
        std::uint32_t const now = parentCloseTime(env);
        staged.subscriptionDate = now - 1'000;
        staged.redemptionDate = now + 1'000'000;
        staged.earlyExitFeeRate = static_cast<std::uint32_t>(rate);
        return staged;
    }

    // A by-shares redemption row: `nav` available, nothing deployed, all shares held.
    TER
    checkRedeemCase(
        jtx::Env& env,
        Keylet const& vault,
        jtx::Account const& holder,
        RedeemCusp const& c,
        std::optional<std::int64_t> feeRate = std::nullopt)
    {
        StagedAmounts staged{
            .available = vaultUnits(env, vault, c.nav),
            .sharesTotal = static_cast<std::uint64_t>(c.sharesTotal),
        };
        if (feeRate)
            staged = inInvestment(env, staged, *feeRate);
        return checkWithdraw(
                   *this, env, vault, holder, staged, STAmount{shareIssue(env, vault), c.shares})
            .ter;
    }

    // Zero shares by assets: an amount worth trunc(shares total * amount / assets total) = 0
    // shares is rejected (tecPRECISION_LOSS). Each row (the deposit zero-shares rows) burns
    // exactly one share.
    void
    testZeroSharesByAssetsSweep(jtx::Env& env, SweepVaults const& vaults)
    {
        for (auto const& [vault, holder] : vaults)
        {
            auto const units = [&](std::int64_t n) { return vaultUnits(env, vault, n); };
            auto const shares = [](std::int64_t n) { return static_cast<std::uint64_t>(n); };
            beginCase(
                ("withdraw " + vaultName(env, vault) + " zero shares by assets-Sweep").c_str());
            for (auto const& [cusp, cases] : kZeroSharesByAssetsCases)
            {
                std::set<TER> seen;
                for (PriceCusp const& c : cases)
                {
                    StagedAmounts const staged{
                        .available = units(c.total),
                        .sharesTotal = shares(c.sharesTotal),
                    };
                    seen.insert(
                        checkWithdraw(*this, env, vault, holder, staged, units(c.amount)).ter);
                }
                expectCrossed(cusp, seen, {tecPRECISION_LOSS});
            }
        }
    }

    // Zero payout: a by-shares redemption paying round(nav * shares / shares total) = 0 units is
    // rejected (tecPRECISION_LOSS). Each row pays exactly half a unit, which rounds to even (0).
    void
    testZeroPayoutSweep(jtx::Env& env, SweepVaults const& vaults)
    {
        for (auto const& [vault, holder] : vaults)
        {
            beginCase(("withdraw " + vaultName(env, vault) + " zero payout-Sweep").c_str());
            for (auto const& [cusp, cases] : kZeroPayoutCases)
            {
                std::set<TER> seen;
                for (RedeemCusp const& c : cases)
                {
                    seen.insert(checkRedeemCase(env, vault, holder, c));
                }
                expectCrossed(cusp, seen, {tecPRECISION_LOSS});
            }
        }
    }

    // Clamp to zero: a by-shares payout below one grid step floors to zero and is rejected
    // (tecPRECISION_LOSS). Each row pays exactly one grid step.
    void
    testClampToZeroSweep(jtx::Env& env, SweepVaults const& vaults)
    {
        for (auto const& [vault, holder] : vaults)
        {
            beginCase(("withdraw " + vaultName(env, vault) + " clamp to zero-Sweep").c_str());
            for (auto const& [cusp, cases] : kClampToZeroBySharesCases)
            {
                std::set<TER> seen;
                for (RedeemCusp const& c : cases)
                {
                    seen.insert(checkRedeemCase(env, vault, holder, c));
                }
                expectCrossed(cusp, seen, {tecPRECISION_LOSS});
            }
        }
    }

    // Payout out of range: a by-shares request for far more shares than exist converts to more
    // than the asset can represent and is rejected before the holder's shares are checked. Each
    // row pays exactly the largest amount (then fails on the holder's shares). XRP: C++
    // tefEXCEPTION (an uncaught runtime_error), the model outOfRange; both reject.
    void
    testPayoutRangeSweep(jtx::Env& env, SweepVaults const& vaults)
    {
        for (auto const& [vault, holder] : vaults)
        {
            beginCase(("withdraw " + vaultName(env, vault) + " payout range-Sweep").c_str());
            bool const native = Asset{env.le(vault)->at(sfAsset)}.native();
            for (auto const& [cusp, cases] : native ? kXrpPayoutRangeCases : kMptPayoutRangeCases)
            {
                std::set<TER> seen;
                for (RedeemCusp const& c : cases)
                {
                    seen.insert(checkRedeemCase(env, vault, holder, c));
                }
                expectCrossed(cusp, seen, {native ? TER{tefEXCEPTION} : TER{tecPATH_DRY}});
            }
        }
    }

    // IOU payout out of range: a by-shares payout past the largest IOU amount fails (tecPATH_DRY).
    // Each row redeems every share of a vault holding exactly that amount (a final withdrawal).
    void
    testIouPayoutRangeSweep(jtx::Env& env, SweepVaults const& vaults)
    {
        for (auto const& [vault, holder] : vaults)
        {
            beginCase(("withdraw " + vaultName(env, vault) + " payout range-Sweep").c_str());
            Asset const asset = env.le(vault)->at(sfAsset);
            for (auto const& [cusp, cases] : kIouPayoutRangeCases)
            {
                std::set<TER> seen;
                for (RedeemCusp const& c : cases)
                {
                    StagedAmounts const staged{
                        .available =
                            STAmount{
                                asset, static_cast<std::uint64_t>(c.nav), STAmount::kMaxOffset},
                        .sharesTotal = static_cast<std::uint64_t>(c.sharesTotal),
                    };
                    seen.insert(checkWithdraw(
                                    *this,
                                    env,
                                    vault,
                                    holder,
                                    staged,
                                    STAmount{shareIssue(env, vault), c.shares})
                                    .ter);
                }
                expectCrossed(cusp, seen, {tecPATH_DRY});
            }
        }
    }

    // To-nearest switch: a payout of X + 1/2 units truncates below X = 10^15 and rounds to even
    // from there, where the payout amount itself rounds to the grid. Both sides succeed at every
    // row; the post-state and payout are compared.
    void
    testToNearestSweep(jtx::Env& env, SweepVaults const& vaults)
    {
        for (auto const& [vault, holder] : vaults)
        {
            beginCase(("withdraw " + vaultName(env, vault) + " to nearest-Sweep").c_str());
            for (auto const& [cusp, cases] : kToNearestCases)
            {
                for (RedeemCusp const& c : cases)
                {
                    checkRedeemCase(env, vault, holder, c);
                }
            }
        }
    }

    // Dust with a 100% early-exit fee: a debit too small to change the stored available assets is
    // rejected (tecPRECISION_LOSS); with a 100% fee no clamp runs, so this check alone decides.
    // Each row debits exactly half the last stored digit.
    void
    testFullFeeDustSweep(jtx::Env& env, SweepVaults const& vaults)
    {
        for (auto const& [vault, holder] : vaults)
        {
            beginCase(("withdraw " + vaultName(env, vault) + " full fee dust-Sweep").c_str());
            for (auto const& [cusp, cases] : kFullFeeDustCases)
            {
                std::set<TER> seen;
                for (RedeemCusp const& c : cases)
                {
                    seen.insert(
                        checkRedeemCase(env, vault, holder, c, kMaxEarlyExitFeeRate.value()));
                }
                expectCrossed(cusp, seen, {tecPRECISION_LOSS});
            }
        }
    }

    // Available assets: with assets deployed, a withdrawal above the available assets is rejected
    // (tecINSUFFICIENT_FUNDS). Each row withdraws exactly the available assets, at price 1.
    void
    testAvailableSweep(jtx::Env& env, SweepVaults const& vaults)
    {
        for (auto const& [vault, holder] : vaults)
        {
            auto const units = [&](std::int64_t n) { return vaultUnits(env, vault, n); };
            auto const shares = [](std::int64_t n) { return static_cast<std::uint64_t>(n); };
            beginCase(("withdraw " + vaultName(env, vault) + " available-Sweep").c_str());
            for (auto const& [cusp, cases] : kAvailableCases)
            {
                std::set<TER> seen;
                for (AvailableCusp const& c : cases)
                {
                    auto const sharesTotal = shares(c.available + c.deployed);
                    StagedAmounts const staged{
                        .available = units(c.available),
                        .deployed = units(c.deployed),
                        .sharesTotal = sharesTotal,
                        .holderShares = sharesTotal - 1,
                    };
                    seen.insert(
                        checkWithdraw(*this, env, vault, holder, staged, units(c.amount)).ter);
                }
                expectCrossed(cusp, seen, {tecINSUFFICIENT_FUNDS});
            }
        }
    }

    // Fee consumes the payout: in Investment the payout gross - fee (fee rounded up, payout down)
    // must be at least one unit (tecPRECISION_LOSS below); a 100% rate pays nothing and succeeds.
    // Each row pays exactly one unit.
    void
    testFeeConsumesPayoutSweep(jtx::Env& env, SweepVaults const& vaults)
    {
        for (auto const& [vault, holder] : vaults)
        {
            auto const units = [&](std::int64_t n) { return vaultUnits(env, vault, n); };
            beginCase(("withdraw " + vaultName(env, vault) + " fee consumes payout-Sweep").c_str());
            for (auto const& [cusp, cases] : kFeeConsumesPayoutCases)
            {
                std::set<TER> seen;
                for (FeeCusp const& c : cases)
                {
                    StagedAmounts const staged{
                        .available = units(1'000'000),
                        .sharesTotal = 1'000'000,
                        .holderShares = 999'999,
                    };
                    seen.insert(checkWithdraw(
                                    *this,
                                    env,
                                    vault,
                                    holder,
                                    inInvestment(env, staged, c.rate),
                                    units(c.gross))
                                    .ter);
                }
                expectCrossed(cusp, seen, {tecPRECISION_LOSS});
            }
        }
    }

    // Net payout over available: with a fee only the net payout must be available
    // (tecINSUFFICIENT_FUNDS above). Each row nets exactly the available assets, at price 1.
    void
    testNetOverAvailableSweep(jtx::Env& env, SweepVaults const& vaults)
    {
        for (auto const& [vault, holder] : vaults)
        {
            auto const units = [&](std::int64_t n) { return vaultUnits(env, vault, n); };
            auto const shares = [](std::int64_t n) { return static_cast<std::uint64_t>(n); };
            beginCase(("withdraw " + vaultName(env, vault) + " net over available-Sweep").c_str());
            for (auto const& [cusp, cases] : kNetOverAvailableCases)
            {
                std::set<TER> seen;
                for (NetOverAvailableCusp const& c : cases)
                {
                    auto const sharesTotal = shares(c.available + c.deployed);
                    StagedAmounts const staged{
                        .available = units(c.available),
                        .deployed = units(c.deployed),
                        .sharesTotal = sharesTotal,
                        .holderShares = sharesTotal - 1,
                    };
                    seen.insert(checkWithdraw(
                                    *this,
                                    env,
                                    vault,
                                    holder,
                                    inInvestment(env, staged, c.rate),
                                    units(c.gross))
                                    .ter);
                }
                expectCrossed(cusp, seen, {tecINSUFFICIENT_FUNDS});
            }
        }
    }

    // Final withdrawal: redeeming every share pays all available assets, and is rejected while
    // assets are deployed (tecHAS_OBLIGATIONS). Each row redeems every share of a vault with
    // nothing deployed, at price 1.
    void
    testFinalSweep(jtx::Env& env, SweepVaults const& vaults)
    {
        for (auto const& [vault, holder] : vaults)
        {
            auto const units = [&](std::int64_t n) { return vaultUnits(env, vault, n); };
            auto const shares = [](std::int64_t n) { return static_cast<std::uint64_t>(n); };
            beginCase(("withdraw " + vaultName(env, vault) + " final-Sweep").c_str());
            for (auto const& [cusp, cases] : kFinalCases)
            {
                std::set<TER> seen;
                for (FinalCusp const& c : cases)
                {
                    StagedAmounts const staged{
                        .available = units(c.available),
                        .deployed = units(c.deployed),
                        .sharesTotal = shares(c.available + c.deployed),
                    };
                    seen.insert(checkWithdraw(
                                    *this,
                                    env,
                                    vault,
                                    holder,
                                    staged,
                                    STAmount{shareIssue(env, vault), c.shares})
                                    .ter);
                }
                expectCrossed(cusp, seen, {tecHAS_OBLIGATIONS});
            }
        }
    }

    // Fully impaired vault: with a zero net asset value a by-shares redemption burns the shares
    // for nothing (tesSUCCESS); one unit of net asset value makes the payout non-zero, which fails
    // (tecPRECISION_LOSS or tecINSUFFICIENT_FUNDS). Each row has the whole deployed total lost.
    void
    testImpairedSweep(jtx::Env& env, SweepVaults const& vaults)
    {
        for (auto const& [vault, holder] : vaults)
        {
            auto const units = [&](std::int64_t n) { return vaultUnits(env, vault, n); };
            auto const shares = [](std::int64_t n) { return static_cast<std::uint64_t>(n); };
            beginCase(("withdraw " + vaultName(env, vault) + " fully impaired-Sweep").c_str());
            for (auto const& [cusp, cases] : kImpairedCases)
            {
                std::set<TER> seen;
                for (ImpairedCusp const& c : cases)
                {
                    StagedAmounts const staged{
                        .available = units(0),
                        .deployed = units(c.deployed),
                        .loss = units(c.loss),
                        .sharesTotal = shares(c.sharesTotal),
                        .holderShares = shares(c.sharesTotal - 1),
                    };
                    seen.insert(checkWithdraw(
                                    *this,
                                    env,
                                    vault,
                                    holder,
                                    staged,
                                    STAmount{shareIssue(env, vault), c.shares})
                                    .ter);
                }
                expectCrossed(cusp, seen, {tecPRECISION_LOSS, tecINSUFFICIENT_FUNDS});
            }
        }
    }

    // Sub-grid payout over available: a payout a tenth of a unit above the available assets is
    // rejected (tecINSUFFICIENT_FUNDS) by the check on the unclamped payout, which the clamp would
    // otherwise floor back to the available assets. Each row pays exactly the available assets.
    void
    testSubGridOverAvailableSweep(jtx::Env& env, SweepVaults const& vaults)
    {
        for (auto const& [vault, holder] : vaults)
        {
            auto const units = [&](std::int64_t n) { return vaultUnits(env, vault, n); };
            auto const shares = [](std::int64_t n) { return static_cast<std::uint64_t>(n); };
            beginCase(
                ("withdraw " + vaultName(env, vault) + " sub-grid over available-Sweep").c_str());
            for (auto const& [cusp, cases] : kSubGridOverAvailableCases)
            {
                std::set<TER> seen;
                for (SubGridCusp const& c : cases)
                {
                    StagedAmounts const staged{
                        .available = units(c.available),
                        .deployed = units(c.deployed),
                        .sharesTotal = shares(c.sharesTotal),
                        .holderShares = shares(c.sharesTotal - 1),
                    };
                    seen.insert(checkWithdraw(
                                    *this,
                                    env,
                                    vault,
                                    holder,
                                    staged,
                                    STAmount{shareIssue(env, vault), c.shares})
                                    .ter);
                }
                expectCrossed(cusp, seen, {tecINSUFFICIENT_FUNDS});
            }
        }
    }

    // Decade-crossing outflow: the payout is truncated to the grid of available - amount, ten
    // units from 10^16 units up, so there a one-unit withdrawal truncates to zero
    // (tecPRECISION_LOSS). Each row leaves exactly 10^16 - 1 or 10^16 units, at price 1.
    void
    testDecadeSweep(jtx::Env& env, SweepVaults const& vaults)
    {
        for (auto const& [vault, holder] : vaults)
        {
            beginCase(("withdraw " + vaultName(env, vault) + " decade crossing-Sweep").c_str());
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
                    };
                    seen.insert(
                        checkWithdraw(
                            *this, env, vault, holder, staged, vaultUnits(env, vault, c.amount))
                            .ter);
                }
                expectCrossed(cusp, seen, {tecPRECISION_LOSS});
            }
        }
    }

    // Holder's shares: redeeming more shares than the holder owns is rejected
    // (tecINSUFFICIENT_FUNDS). Each row redeems exactly the shares held; one more share is held by
    // someone else.
    void
    testHolderSharesSweep(jtx::Env& env, SweepVaults const& vaults)
    {
        for (auto const& [vault, holder] : vaults)
        {
            auto const shares = [](std::int64_t n) { return static_cast<std::uint64_t>(n); };
            beginCase(("withdraw " + vaultName(env, vault) + " holder shares-Sweep").c_str());
            for (auto const& [cusp, cases] : kHolderSharesCases)
            {
                std::set<TER> seen;
                for (HolderCusp const& c : cases)
                {
                    StagedAmounts const staged{
                        .available = vaultUnits(env, vault, c.holderShares + 1),
                        .sharesTotal = shares(c.holderShares + 1),
                        .holderShares = shares(c.holderShares),
                    };
                    seen.insert(checkWithdraw(
                                    *this,
                                    env,
                                    vault,
                                    holder,
                                    staged,
                                    STAmount{shareIssue(env, vault), c.shares})
                                    .ter);
                }
                expectCrossed(cusp, seen, {tecINSUFFICIENT_FUNDS});
            }
        }
    }

    // Sole-holder loss waiver: a holder of every share redeems at the assets total, any other at
    // assets total - loss unrealized. Both sides succeed; the post-state and payout are compared.
    void
    testWaiverSweep(jtx::Env& env, SweepVaults const& vaults)
    {
        for (auto const& [vault, holder] : vaults)
        {
            auto const units = [&](std::int64_t n) { return vaultUnits(env, vault, n); };
            auto const shares = [](std::int64_t n) { return static_cast<std::uint64_t>(n); };
            beginCase(("withdraw " + vaultName(env, vault) + " loss waiver-Sweep").c_str());
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
                    };
                    checkWithdraw(
                        *this,
                        env,
                        vault,
                        holder,
                        staged,
                        STAmount{shareIssue(env, vault), c.shares});
                }
            }
        }
    }

    // By-assets share overflow: an amount worth more than 2^63 - 1 shares fails the share
    // computation (tecPATH_DRY). Each row converts to exactly 2^63 - 1 shares.
    void
    testShareOverflowSweep(jtx::Env& env, SweepVaults const& vaults)
    {
        for (auto const& [vault, holder] : vaults)
        {
            auto const units = [&](std::int64_t n) { return vaultUnits(env, vault, n); };
            auto const shares = [](std::int64_t n) { return static_cast<std::uint64_t>(n); };
            beginCase(("withdraw " + vaultName(env, vault) + " share overflow-Sweep").c_str());
            for (auto const& [cusp, cases] : kAssetsShareOverflowCases)
            {
                std::set<TER> seen;
                for (ShareOverflowCusp const& c : cases)
                {
                    StagedAmounts const staged{
                        .available = units(c.nav),
                        .sharesTotal = shares(c.sharesTotal),
                    };
                    seen.insert(
                        checkWithdraw(*this, env, vault, holder, staged, units(c.amount)).ter);
                }
                expectCrossed(cusp, seen, {tecPATH_DRY});
            }
        }
    }

    void
    runTests() override
    {
        using namespace jtx;

        // One ledger holding a vault per asset; every staged withdrawal (old tests and sweeps)
        // runs on a throwaway view of it.
        Env env{*this};
        Account const owner{"owner"};
        Account const issuer{"issuer"};
        Account const depositor{"depositor"};
        env.fund(XRP(1'000'000), owner, issuer);
        env.fund(XRP(9'500'000'000), depositor);
        env.close();

        PrettyAsset const xrp = xrpIssue();
        PrettyAsset const iou = issuer["USD"];
        MPTTester mptt{env, issuer, kMptInitNoFund};
        mptt.create({.flags = tfMPTCanTransfer});
        mptt.authorize({.account = depositor});
        PrettyAsset const mpt = mptt.issuanceID();
        env(pay(issuer, depositor, mpt(9'200'000'000'000'000)));
        env.close();

        // The IOU withdrawer is the issuer, which skips the C++-only trust-line checks.
        Keylet const xrpVault = createVault(env, owner, xrp);
        Keylet const mptVault = createVault(env, owner, mpt);
        // IOU at the smallest, the default and the largest vault scale.
        Keylet const iouMinScaleVault = createVault(env, owner, iou, kVaultMinimumIouScale);
        Keylet const iouDefaultScaleVault = createVault(env, owner, iou, kVaultDefaultIouScale);
        Keylet const iouMaxScaleVault =
            createVault(env, owner, iou, kFixedPrecisionVaultMaximumIouScale);
        SweepVaults const ious{
            {iouMinScaleVault, issuer},
            {iouDefaultScaleVault, issuer},
            {iouMaxScaleVault, issuer},
        };
        SweepVaults const integral{{xrpVault, depositor}, {mptVault, depositor}};
        SweepVaults all = integral;
        all.insert(all.end(), ious.begin(), ious.end());
        // One unit each: the holder gets its share MPToken and an IOU vault its pseudo-account
        // trust line, which staging state on the vault needs.
        for (auto const& [vault, account] : all)
        {
            env(jtx::Vault::deposit(
                {.depositor = account, .id = vault.key, .amount = vaultUnits(env, vault, 1)}));
        }
        env.close();
        // Staged Investment dates sit 1000 s before the parent close time, which starts near 0.
        env.close(env.now() + std::chrono::seconds{100'000'000});

        // Partial and final withdrawal by assets. IOU is scale 6, MPT is scale 0 (like XRP), so the
        // two cover the distinct share arithmetic
        testWithdrawIOU(env, iouDefaultScaleVault, issuer, Number{1'000}, Number{400}, tesSUCCESS);
        testWithdrawIOU(
            env, iouDefaultScaleVault, issuer, Number{1'000}, Number{1'000}, tesSUCCESS);
        testWithdrawMPT(env, mptVault, depositor, 1'000, 400, tesSUCCESS);
        testWithdrawMPT(env, mptVault, depositor, 1'000, 1'000, tesSUCCESS);
        testWithdrawXRP(env, xrpVault, depositor, XRP(1'000), drops(1), tesSUCCESS);

        // Insufficient vault assets (the check is asset-agnostic, so one case suffices).
        // covered by testAvailableSweep
        testWithdrawIOU(
            env, iouDefaultScaleVault, issuer, Number{1'000}, Number{1'001}, tecINSUFFICIENT_FUNDS);
        // Sub-share withdrawal: the amount converts to zero shares.
        // covered by testZeroSharesByAssetsSweep
        testWithdrawIOU(
            env, iouDefaultScaleVault, issuer, Number{1, 9}, Number{1, -7}, tecPRECISION_LOSS);
        // MPT at the open limit.
        testWithdrawMPT(env, mptVault, depositor, kOpenLimitUnits, kOpenLimitUnits, tesSUCCESS);

        // covered by testFinalSweep
        testWithdrawAllShares(env, iouDefaultScaleVault, issuer);

        // Direct sharesToAssetsWithdraw checks
        testSharesToAssets(env, iouDefaultScaleVault, issuer, Number{1'000}, Number{0}, 1);
        testSharesToAssets(
            env, iouDefaultScaleVault, issuer, Number{1'000}, Number{0}, 500'000'000);
        testSharesToAssets(
            env, iouDefaultScaleVault, issuer, Number{1'000}, Number{0}, 999'999'999);
        testSharesToAssets(
            env, iouDefaultScaleVault, issuer, Number{1'000}, Number{2'000}, 333'333'333);
        testSharesToAssets(
            env, iouDefaultScaleVault, issuer, Number{1'000}, Number{500}, 123'456'789);
        testSharesToAssets(
            env, iouDefaultScaleVault, issuer, Number{1'000'000}, Number{0}, 123'456'789);
        testSharesToAssets(
            env, iouDefaultScaleVault, issuer, Number{1}, Number{1'000'000}, 500'000);

        // Staged extreme states (a 1000-asset seed mints 1e9 shares at scale 6). Each mixes an
        // extreme across a different field: AssetsTotal, AssetsAvailable, sharesTotal, shareAmount.
        Number const iouMax{9'999'999'999'999'999LL, 80};
        // Extreme AssetsTotal, tiny available, full shareholder
        testWithdrawUpdatedState(
            env,
            iouDefaultScaleVault,
            issuer,
            iouMax,
            Number{1},
            1'000'000'000,
            500'000'000,
            tecINSUFFICIENT_FUNDS);
        // Extreme AssetsTotal, mid available, minimal sharesTotal/shareAmount: a full exit while
        // assets are deployed
        // covered by testFinalSweep
        testWithdrawUpdatedState(
            env, iouDefaultScaleVault, issuer, iouMax, Number{1, 50}, 1, 1, tecHAS_OBLIGATIONS);
        // Most assets lent out: half the shares are worth more than is available
        // covered by testAvailableSweep
        testWithdrawUpdatedState(
            env,
            iouDefaultScaleVault,
            issuer,
            Number{1'000},
            Number{100},
            1'000'000'000,
            500'000'000,
            tecINSUFFICIENT_FUNDS);
        // Extreme AssetsTotal, tiny available, extreme sharesTotal, minimal shareAmount
        testWithdrawUpdatedState(
            env,
            iouDefaultScaleVault,
            issuer,
            iouMax,
            Number{1},
            1'000'000'000,
            1,
            tecINSUFFICIENT_FUNDS);
        // Overflow: NAV * shares / sharesTotal exceeds the IOU domain
        // covered by testIouPayoutRangeSweep
        testWithdrawUpdatedState(
            env, iouDefaultScaleVault, issuer, iouMax, iouMax, 1'000, 1'000'000'000, tecPATH_DRY);
        // Overflow: minimal sharesTotal with a maximal shareAmount,
        // covered by testIouPayoutRangeSweep
        testWithdrawUpdatedState(
            env, iouDefaultScaleVault, issuer, iouMax, Number{1}, 1, 1'000'000'000, tecPATH_DRY);
        // Overflow: sharesTotal * assets / NAV exceeds the MPT domain (by assets).
        // covered by testShareOverflowSweep
        testWithdrawAssetsShareOverflow(env, iouDefaultScaleVault, issuer, tecPATH_DRY);

        // Sweeps.

        testZeroSharesByAssetsSweep(env, all);
        testZeroPayoutSweep(env, integral);
        testClampToZeroSweep(env, ious);
        testPayoutRangeSweep(env, integral);
        testIouPayoutRangeSweep(env, ious);
        testToNearestSweep(env, ious);
        testFullFeeDustSweep(env, ious);
        testAvailableSweep(env, all);
        testFeeConsumesPayoutSweep(env, all);
        testNetOverAvailableSweep(env, all);
        testFinalSweep(env, all);
        testImpairedSweep(env, all);
        testSubGridOverAvailableSweep(env, ious);
        testDecadeSweep(env, ious);
        testHolderSharesSweep(env, all);
        testWaiverSweep(env, all);
        testShareOverflowSweep(env, integral);
    }
};

BEAST_DEFINE_TESTSUITE(LeanVaultWithdraw, formal_verification, xrpl);

}  // namespace xrpl::test::formal_verification
