#pragma once

#include <test/formal_verification/common/LeanSuite.h>
#include <test/formal_verification/ffi/vault/VaultClawbackFFI.h>
#include <test/formal_verification/ffi/vault/VaultDepositFFI.h>
#include <test/formal_verification/ffi/vault/VaultFFI.h>
#include <test/formal_verification/ffi/vault/VaultWithdrawFFI.h>
#include <test/jtx/Account.h>
#include <test/jtx/Env.h>
#include <test/jtx/amount.h>
#include <test/jtx/flags.h>
#include <test/jtx/mpt.h>
#include <test/jtx/pay.h>
#include <test/jtx/trust.h>
#include <test/jtx/vault.h>

#include <xrpl/basics/Number.h>
#include <xrpl/basics/chrono.h>
#include <xrpl/beast/unit_test/suite.h>
#include <xrpl/ledger/OpenView.h>
#include <xrpl/ledger/Sandbox.h>
#include <xrpl/ledger/helpers/VaultHelpers.h>
#include <xrpl/protocol/Asset.h>
#include <xrpl/protocol/Indexes.h>
#include <xrpl/protocol/LedgerFormats.h>
#include <xrpl/protocol/MPTIssue.h>
#include <xrpl/protocol/Protocol.h>
#include <xrpl/protocol/SField.h>
#include <xrpl/protocol/STAmount.h>
#include <xrpl/protocol/STLedgerEntry.h>
#include <xrpl/protocol/STNumber.h>
#include <xrpl/protocol/TER.h>
#include <xrpl/tx/apply.h>

#include <algorithm>
#include <chrono>
#include <cstddef>
#include <cstdint>
#include <optional>
#include <stdexcept>
#include <string>
#include <type_traits>
#include <utility>

namespace xrpl::test::formal_verification {

// The amendments every vault suite enables; the expected verdicts are for this set.
[[nodiscard]] inline FeatureBitset
vaultTestAmendments()
{
    return jtx::testableAmendments();
}

// A FixedPrecision vault rejects inflows past 9e15 units of its base grid (10^-scale): 9e15 drops
// or MPT units, 9e9 for an IOU at the default scale 6.
constexpr std::int64_t kOpenLimitUnits = 9'000'000'000'000'000LL;

// The smallest IOU vault scale; the protocol names only the default and the maximum.
constexpr std::uint8_t kVaultMinimumIouScale = 0;

// A vault on grid scale `scale` (IOU only; none keeps the default), with no deposit.
inline Keylet
createVault(
    jtx::Env& env,
    jtx::Account const& owner,
    Asset const& asset,
    std::optional<std::uint8_t> scale = std::nullopt)
{
    jtx::Vault vault{env};
    auto [jv, keylet] = vault.create({.owner = owner, .asset = asset});
    if (scale)
        jv[sfScale] = *scale;
    env(jv);
    env.close();
    return keylet;
}

// Snapshot the vault in `view` into the model's Vault DTO
inline Vault
readVaultState(ReadView const& view, Keylet const& vaultKeylet, Asset const& asset)
{
    auto const vaultSle = view.read(vaultKeylet);
    if (!vaultSle)
        throw std::runtime_error("readVaultState: no vault on the ledger");
    auto const shareMptId = vaultSle->at(sfShareMPTID);
    return Vault{
        .assetsTotal = getAssetsTotal(vaultSle),
        .assetsAvailable = vaultSle->at(sfAssetsAvailable),
        .assetsDeployed = vaultSle->at(sfAssetsDeployed),
        .assetsReserved = vaultSle->at(sfAssetsReserved),
        .assetsMaximum = vaultSle->isFieldPresent(sfAssetsMaximum)
            ? std::optional<Number>(vaultSle->at(sfAssetsMaximum))
            : std::nullopt,
        .numericType = NumericTypeFFI::tagOf(asset),
        .scale = vaultSle->at(sfScale),
        .sharesTotal = Number{static_cast<std::int64_t>(
            view.read(keylet::mptokenIssuance(shareMptId))->at(sfOutstandingAmount))},
        .lossUnrealized = vaultSle->at(sfLossUnrealized),
        .yieldUnrealized = vaultSle->at(sfYieldUnrealized),
        .subscriptionDate = vaultSle->at(~sfSubscriptionDate),
        .redemptionDate = vaultSle->at(~sfRedemptionDate),
        .earlyExitFeeRate = vaultSle->at(~sfEarlyExitFeeRate),
        .ownerCanBlockDeposit = vaultSle->isFlag(lsfVaultOwnerCanBlockDeposit),
        .depositBlocked = vaultSle->isFlag(lsfVaultDepositBlocked)};
}

inline Vault
readVaultState(jtx::Env const& env, Keylet const& vaultKeylet, Asset const& asset)
{
    return readVaultState(*env.current(), vaultKeylet, asset);
}

// The holder's balance of the vault's share MPT (zero without an MPToken).
[[nodiscard]] inline STAmount
fetchHolderShares(jtx::Env& env, Keylet const& vaultKeylet, jtx::Account const& holder)
{
    auto const vaultSle = env.le(vaultKeylet);
    if (!vaultSle)
        throw std::runtime_error("fetchHolderShares: no vault on the ledger");
    MPTIssue const share{vaultSle->at(sfShareMPTID)};
    auto const sleToken = env.le(keylet::mptoken(share.getMptID(), holder.id()));
    return STAmount{share, sleToken ? sleToken->at(sfMPTAmount) : 0};
}

// True iff `holder` owns every outstanding share: C++ then waives the unrealized loss on a
// withdrawal or clawback, and the model must be told so.
[[nodiscard]] inline bool
holderOwnsAllShares(jtx::Env& env, Keylet const& vaultKeylet, jtx::Account const& holder)
{
    auto const vaultSle = env.le(vaultKeylet);
    if (!vaultSle)
        throw std::runtime_error("holderOwnsAllShares: no vault on the ledger");
    auto const shareMptId = vaultSle->at(sfShareMPTID);
    std::uint64_t const outstanding =
        env.le(keylet::mptokenIssuance(shareMptId))->at(sfOutstandingAmount);
    if (outstanding == 0)
        return false;
    auto const token = env.le(keylet::mptoken(shareMptId, holder.id()));
    return token && token->at(sfMPTAmount) == outstanding;
}

// The close time of the parent ledger, the "now" of the transaction phase checks.
[[nodiscard]] inline std::uint32_t
parentCloseTime(jtx::Env& env)
{
    return env.current()->parentCloseTime().time_since_epoch().count();
}

[[nodiscard]] inline std::uint32_t
timeCount(NetClock::time_point t)
{
    return static_cast<std::uint32_t>(t.time_since_epoch().count());
}

// `t` rounded up to a multiple of the ledger's close-time resolution.
[[nodiscard]] inline NetClock::time_point
alignedTime(jtx::Env& env, NetClock::time_point t)
{
    using namespace std::chrono_literals;
    auto const resolution = env.closed()->header().closeTimeResolution;
    auto const rem = t.time_since_epoch() % resolution;
    return rem == 0s ? t : t + (resolution - rem);
}

// Close the ledger so that the next transaction's parent close time is exactly `at`, which must
// be aligned (`alignedTime`). Returns whether it landed.
[[nodiscard]] inline bool
closeExactlyAt(jtx::Env& env, NetClock::time_point at)
{
    using namespace std::chrono_literals;
    auto const resolution = env.closed()->header().closeTimeResolution;
    env.close(at - resolution + 1s);
    return parentCloseTime(env) == timeCount(at);
}

// Overwrite the vault totals and share issuance outstanding on the open ledger to reach states a
// real transaction cannot. The total is split into assetsAvailable and the deployed remainder.
// Returns false if the vault or issuance is missing.
[[nodiscard]] inline bool
updateVaultState(
    jtx::Env& env,
    Keylet const& vaultKeylet,
    Number const& assetsTotal,
    Number const& assetsAvailable,
    std::uint64_t sharesTotal,
    Number const& assetsMaximum = Number{0},
    Number const& lossUnrealized = Number{0},
    Number const& yieldUnrealized = Number{0})
{
    return env.app().getOpenLedger().modify(  //
        [&](OpenView& view, beast::Journal) -> bool {
            Sandbox sb(&view, TapNone);
            auto v = sb.peek(vaultKeylet);
            if (!v)
                return false;
            auto iss = sb.peek(keylet::mptokenIssuance(v->at(sfShareMPTID)));
            if (!iss)
                return false;
            v->at(sfAssetsTotal) = assetsTotal;
            v->at(sfAssetsAvailable) = assetsAvailable;
            v->at(sfAssetsDeployed) = assetsTotal - assetsAvailable;
            v->at(sfAssetsMaximum) = assetsMaximum;
            v->at(sfLossUnrealized) = lossUnrealized;
            v->at(sfYieldUnrealized) = yieldUnrealized;
            iss->setFieldU64(sfOutstandingAmount, sharesTotal);
            sb.update(v);
            sb.update(iss);
            sb.apply(view);
            return true;
        });
}

// True iff totalA / sharesA >= totalB / sharesB, compared exactly via an int128 cross-multiply
// (a Number multiply would re-round and hide a sub-ULP dilution).
[[nodiscard]] inline bool
priceNotBelow(
    Number const& totalA,
    Number const& sharesA,
    Number const& totalB,
    Number const& sharesB)
{
    __int128 lhs = static_cast<__int128>(totalA.mantissa()) * sharesB.mantissa();
    __int128 rhs = static_cast<__int128>(totalB.mantissa()) * sharesA.mantissa();
    int const eL = totalA.exponent() + sharesB.exponent();
    int const eR = totalB.exponent() + sharesA.exponent();
    int const e = eL < eR ? eL : eR;
    for (int i = e; i < eL; ++i)
        lhs *= 10;
    for (int i = e; i < eR; ++i)
        rhs *= 10;
    return lhs >= rhs;
}

// Build a NAV-drifted IOU vault by real deposits: the holder deposits 899999999.876543 (minting
// 899999999876543 shares at the default scale 6) and the owner donates 123.4567891 (no shares), so
// assetsTotal = 900000123.3333321 and the share price is a non-terminating decimal.
[[nodiscard]] inline Keylet
createDilutionVault(
    jtx::Env& env,
    jtx::Account const& owner,
    jtx::Account const& issuer,
    jtx::Account const& holder,
    jtx::PrettyAsset const& asset,
    Number const& holderExtra = Number{0})
{
    using namespace jtx;
    env.fund(XRP(1'000'000), owner, issuer, holder);
    env.close();
    env(fset(issuer, asfAllowTrustLineClawback));  // for the clawback variant
    env.close();
    env(trust(owner, asset(1'000'000)));
    env(trust(holder, asset(2'000'000'000)));
    env.close();

    Number const seed{899'999'999'876'543LL, -6};
    Number const donation{1'234'567'891LL, -7};
    env(pay(issuer, holder, asset(seed + holderExtra)));
    env(pay(issuer, owner, asset(donation)));
    env.close();

    auto const keylet = createVault(env, owner, asset.raw());
    env(jtx::Vault::deposit({.depositor = holder, .id = keylet.key, .amount = asset(seed)}));
    env.close();
    env(jtx::Vault::deposit(
        {.depositor = owner, .id = keylet.key, .amount = asset(donation), .flags = tfVaultDonate}));
    env.close();
    return keylet;
}

// A scale-10 vault mints 7e7 shares for a 0.007 deposit, then a 2.993 owner donation lifts
// the total to 3. The share price 3/7e7 puts every round-trip amount off the vault grid.
[[nodiscard]] inline Keylet
createAppliedDeltaVault(
    jtx::Env& env,
    jtx::Account const& owner,
    jtx::Account const& issuer,
    jtx::Account const& holder,
    jtx::PrettyAsset const& asset)
{
    using namespace jtx;
    env.fund(XRP(1'000'000), owner, issuer, holder);
    env.close();
    // Clawback must be enabled while the issuer has no trust line yet.
    env(fset(issuer, asfAllowTrustLineClawback));
    env.close();
    env(trust(owner, asset(10)));
    env(trust(holder, asset(10)));
    env.close();
    env(pay(issuer, owner, asset(Number{2'993, -3})));
    env(pay(issuer, holder, asset(Number{1})));
    env.close();

    jtx::Vault vault{env};
    auto [tx, keylet] = vault.create({.owner = owner, .asset = asset.raw()});
    tx[sfScale] = 10;
    env(tx);
    env.close();

    env(jtx::Vault::deposit(
        {.depositor = holder, .id = keylet.key, .amount = asset(Number{7, -3})}));
    env.close();
    env(jtx::Vault::deposit(
        {.depositor = owner,
         .id = keylet.key,
         .amount = asset(Number{2'993, -3}),
         .flags = tfVaultDonate}));
    env.close();
    return keylet;
}

// The account's IOU balance as a Number.
[[nodiscard]] inline Number
iouBalance(jtx::Env& env, jtx::Account const& account, jtx::PrettyAsset const& asset)
{
    return env.balance(account, asset.raw().get<Issue>()).value();
}

// Round the magnitude of `delta` toward zero to the grid `reference` has after adding it: the vault
// base grid 10^-scale, or the coarser grid of a sum past 16 digits.
[[nodiscard]] inline STAmount
roundToVaultGrid(
    jtx::PrettyAsset const& asset,
    std::uint8_t vaultScale,
    Number const& reference,
    Number const& delta)
{
    int const postScale = [&] {
        NumberRoundModeGuard const rg(Number::RoundingMode::ToNearest);
        return std::max(-static_cast<int>(vaultScale), scale(reference + delta, asset.raw()));
    }();
    Number const magnitude = delta < Number{0} ? -delta : delta;
    return roundToScale(
        STAmount{asset.raw(), magnitude}, postScale, Number::RoundingMode::TowardsZero);
}

// Stage a vault whose whole share supply is held by `holder`. The loss is backed by an equal
// deployed amount, the rest is available.
[[nodiscard]] inline bool
stageSoleHolderVault(
    jtx::Env& env,
    Keylet const& vaultKeylet,
    jtx::Account const& holder,
    Number const& assetsTotal,
    Number const& lossUnrealized,
    std::uint64_t sharesTotal)
{
    return env.app().getOpenLedger().modify(  //
        [&](OpenView& view, beast::Journal) -> bool {
            Sandbox sb(&view, TapNone);
            auto vaultSle = sb.peek(vaultKeylet);
            if (!vaultSle)
                return false;
            auto const shareId = vaultSle->at(sfShareMPTID);
            auto issuance = sb.peek(keylet::mptokenIssuance(shareId));
            auto holderShares = sb.peek(keylet::mptoken(shareId, holder.id()));
            if (!issuance || !holderShares)
                return false;
            vaultSle->at(sfAssetsTotal) = assetsTotal;
            vaultSle->at(sfAssetsAvailable) = assetsTotal - lossUnrealized;
            vaultSle->at(sfAssetsDeployed) = lossUnrealized;
            vaultSle->at(sfLossUnrealized) = lossUnrealized;
            issuance->setFieldU64(sfOutstandingAmount, sharesTotal);
            holderShares->setFieldU64(sfMPTAmount, sharesTotal);
            sb.update(vaultSle);
            sb.update(issuance);
            sb.update(holderShares);
            sb.apply(view);
            return true;
        });
}

// The vault's share MPT.
[[nodiscard]] inline MPTIssue
shareIssue(jtx::Env const& env, Keylet const& vault)
{
    return MPTIssue{env.le(vault)->at(sfShareMPTID)};
}

// n * 10^exponent of the vault's smallest unit: drops, MPT units, or 10^-scale of an IOU. Built
// from (mantissa, exponent), not through Number, so large values are not rounded.
[[nodiscard]] inline STAmount
vaultUnits(jtx::Env const& env, Keylet const& vault, std::int64_t n, int exponent = 0)
{
    auto const sle = env.le(vault);
    if (!sle)
        throw std::runtime_error("vaultUnits: no vault on the ledger");
    return STAmount{
        Asset{sle->at(sfAsset)},
        static_cast<std::uint64_t>(n),
        exponent - static_cast<int>(sle->at(sfScale))};
}

// The vault's asset and scale as a testcase label: "XRP", "MPT" or "IOU scale 6".
[[nodiscard]] inline std::string
vaultName(jtx::Env const& env, Keylet const& vault)
{
    auto const sle = env.le(vault);
    if (!sle)
        throw std::runtime_error("vaultName: no vault on the ledger");
    Asset const asset = sle->at(sfAsset);
    if (asset.native())
        return "XRP";
    if (asset.holds<MPTIssue>())
        return "MPT";
    return "IOU scale " + std::to_string(sle->at(sfScale));
}

// Vault fields to stage, as canonical amounts. AssetsTotal is derived (Downward, as C++ stores it).
struct StagedAmounts
{
    STAmount available;
    STAmount deployed{};
    STAmount yield{};
    STAmount loss{};
    std::optional<STAmount> maximum;
    std::uint64_t sharesTotal{};
    // The owner blocked deposits (VaultSet with tfVaultDepositBlock).
    bool depositBlocked = false;
    // The depositor's IOU trust-line balance, staged when set; a holder that is not the issuer
    // then holds exactly this much, as a funded real holder would.
    std::optional<STAmount> depositorBalance;
    // The holder's share MPToken; staged only when set (withdraw, clawback).
    std::optional<std::uint64_t> holderShares;
    // Both set: the vault is closed-ended with these dates.
    std::optional<std::uint32_t> subscriptionDate;
    std::optional<std::uint32_t> redemptionDate;
    std::optional<std::uint32_t> earlyExitFeeRate;
    // The pseudo-account really holds the available assets (needed by any payout).
    bool pseudoHolding = false;
};

// StagedAmounts with every amount in the vault's smallest unit (see vaultUnits).
struct StagedVault
{
    std::int64_t available{};
    std::int64_t deployed{};
    std::int64_t yield{};
    std::int64_t loss{};
    std::optional<std::int64_t> maximum{};
    std::uint64_t sharesTotal{};
    bool depositBlocked = false;
    std::optional<std::int64_t> depositorBalance{};
    std::optional<std::uint64_t> holderShares{};
    std::optional<std::uint32_t> subscriptionDate{};
    std::optional<std::uint32_t> redemptionDate{};
    std::optional<std::uint32_t> earlyExitFeeRate{};
    bool pseudoHolding = false;
};

[[nodiscard]] inline StagedAmounts
stagedAmounts(jtx::Env const& env, Keylet const& vault, StagedVault const& s)
{
    auto const units = [&](std::optional<std::int64_t> n) {
        return n ? std::optional<STAmount>{vaultUnits(env, vault, *n)} : std::nullopt;
    };
    return {
        .available = vaultUnits(env, vault, s.available),
        .deployed = vaultUnits(env, vault, s.deployed),
        .yield = vaultUnits(env, vault, s.yield),
        .loss = vaultUnits(env, vault, s.loss),
        .maximum = units(s.maximum),
        .sharesTotal = s.sharesTotal,
        .depositBlocked = s.depositBlocked,
        .depositorBalance = units(s.depositorBalance),
        .holderShares = s.holderShares,
        .subscriptionDate = s.subscriptionDate,
        .redemptionDate = s.redemptionDate,
        .earlyExitFeeRate = s.earlyExitFeeRate,
        .pseudoHolding = s.pseudoHolding,
    };
}

// A closed-ended vault in Subscription: subscription date 1'000 s after the parent close time,
// redemption date 1'000'000 s after that.
inline void
inSubscription(StagedVault& s, std::uint32_t parentClose)
{
    s.subscriptionDate = parentClose + 1'000;
    s.redemptionDate = parentClose + 1'001'000;
}

// A closed-ended vault in Investment: subscription date 1'000 s before the parent close time,
// redemption date 1'000'000 s after it.
inline void
inInvestment(StagedVault& s, std::uint32_t parentClose, std::uint32_t feeRate)
{
    s.subscriptionDate = parentClose - 1'000;
    s.redemptionDate = parentClose + 1'000'000;
    s.earlyExitFeeRate = feeRate;
}

// `onDate` puts the parent close time exactly on the date bounding the phase: the subscription
// date is the last instant of Subscription, the redemption date the first of Redemption.
constexpr bool kOnDate = true;

[[nodiscard]] inline std::string
phaseName(VaultPhase phase, bool onDate)
{
    switch (phase)
    {
        case VaultPhase::NoPhase:
            return "open-ended";
        case VaultPhase::Subscription:
            return onDate ? "at the subscription date" : "subscription";
        case VaultPhase::Investment:
            return "investment";
        case VaultPhase::Redemption:
            return onDate ? "at the redemption date" : "redemption";
    }
    return "?";
}

// Long enough for the creation and initial-deposit ledgers (5 s each) to stay in Subscription.
constexpr auto kSubscriptionOffset = std::chrono::seconds{600};
constexpr auto kInvestmentWindow = std::chrono::seconds{1'000'000};

// 1000 IOU at scale 6, or 1000 XRP in drops: the old tests' initial deposit, in grid units and
// in shares (price 1).
constexpr std::int64_t kInitialDepositUnits = 1'000'000'000;

// The schedule dates that put the parent close time P in `phase` (on the bounding date when
// `onDate`).
inline void
stagePhase(
    StagedAmounts& s,
    std::uint32_t p,
    VaultPhase phase,
    std::optional<std::uint32_t> earlyExitFeeRate,
    bool onDate = false)
{
    auto const offset = static_cast<std::uint32_t>(kSubscriptionOffset.count());
    auto const window = static_cast<std::uint32_t>(kInvestmentWindow.count());
    switch (phase)
    {
        case VaultPhase::NoPhase:
            return;
        case VaultPhase::Subscription:
            s.subscriptionDate = onDate ? p : p + offset;
            break;
        case VaultPhase::Investment:
            s.subscriptionDate = p - 1;
            break;
        case VaultPhase::Redemption:
            s.subscriptionDate = (onDate ? p : p - 1) - window;
            break;
    }
    s.redemptionDate = *s.subscriptionDate + window;
    s.earlyExitFeeRate = earlyExitFeeRate;
}

// A vault at price 1 holding `units` grid units, every share owned by the holder.
[[nodiscard]] inline StagedAmounts
depositedVault(jtx::Env const& env, Keylet const& vault, std::int64_t units)
{
    return {
        .available = vaultUnits(env, vault, units),
        .sharesTotal = static_cast<std::uint64_t>(units),
        .holderShares = static_cast<std::uint64_t>(units),
        .pseudoHolding = true,
    };
}

struct AppliedVaultTx
{
    Vault pre;
    TER ter;
    Vault post;
    // What C++ moved, when the transaction reports it: compared with the model's assets / shares.
    std::optional<Number> assets{};
    std::optional<Number> shares{};
    // The vault's asset and its stored sfAssetsTotal after the transaction, when read.
    Asset asset{};
    std::optional<Number> storedTotal{};
    // What really moved, signed like `assets` / `shares`: the pseudo-account's holding of the
    // asset and the holder's share balance.
    std::optional<Number> held{};
    std::optional<Number> heldShares{};
};

// The pseudo-account's raw holding of the vault asset (XRP balance, MPT amount or trust-line
// balance), zero without an MPToken or trust line.
[[nodiscard]] inline Number
pseudoHolding(ReadView const& view, Keylet const& vault)
{
    auto const v = view.read(vault);
    Asset const asset = v->at(sfAsset);
    AccountID const pseudo = v->at(sfAccount);
    if (asset.native())
        return view.read(keylet::account(pseudo))->getFieldAmount(sfBalance);
    if (asset.holds<MPTIssue>())
    {
        auto const token = view.read(keylet::mptoken(asset.get<MPTIssue>().getMptID(), pseudo));
        return token ? Number{static_cast<std::int64_t>(token->at(sfMPTAmount))} : Number{0};
    }
    Issue const& issue = asset.get<Issue>();
    auto const line = view.read(keylet::trustLine(pseudo, issue));
    if (!line)
        return Number{0};
    Number const balance = line->getFieldAmount(sfBalance);
    return pseudo > issue.account ? -balance : balance;
}

// `holder`'s balance of the vault's share MPT, zero without an MPToken.
[[nodiscard]] inline Number
holderShareBalance(ReadView const& view, Keylet const& vault, AccountID const& holder)
{
    auto const token = view.read(keylet::mptoken(view.read(vault)->at(sfShareMPTID), holder));
    return token ? Number{static_cast<std::int64_t>(token->at(sfMPTAmount))} : Number{0};
}

// Set `balance` on `account`'s trust line for `issue` (held by the low account when positive).
inline void
stageTrustLine(Sandbox& sb, AccountID const& account, Issue const& issue, Number const& balance)
{
    auto const line = sb.peek(keylet::trustLine(account, issue));
    if (!line)
        throw std::runtime_error("stageTrustLine: no trust line");
    STAmount held{Issue{issue.currency, noAccount()}, balance};
    if (account > issue.account)
        held.negate();
    line->setFieldAmount(sfBalance, held);
    sb.update(line);
}

// Staging writes ledger entries directly on a throwaway view and applies the transaction there
// with unlimited flags. It reaches states no transaction sequence can: a holder owning fewer
// shares than exist with nobody holding the rest, a pseudo-account balance set to the available
// assets, totals past the open limit. A test compares the model and C++ on the same pre-state; its
// verdict is not a claim that the state is reachable.
// Stage `staged` on `view`; `holder` is the account whose share MPToken and IOU balance are set.
inline void
stageVault(
    OpenView& view,
    Keylet const& vault,
    jtx::Account const& holder,
    StagedAmounts const& staged)
{
    Sandbox sb(&view, TapNone);
    auto const v = sb.peek(vault);
    if (!v)
        throw std::runtime_error("stageVault: no vault on the ledger");
    Asset const asset = v->at(sfAsset);
    auto const issuance = sb.peek(keylet::mptokenIssuance(v->at(sfShareMPTID)));
    v->at(sfAssetsAvailable) = Number{staged.available};
    v->at(sfAssetsDeployed) = Number{staged.deployed};
    v->at(sfYieldUnrealized) = Number{staged.yield};
    v->at(sfLossUnrealized) = Number{staged.loss};
    v->at(sfAssetsMaximum) = staged.maximum ? Number{*staged.maximum} : Number{0};
    {
        NumberRoundModeGuard const rg(Number::RoundingMode::Downward);
        v->at(sfAssetsTotal) = STAmount{asset, getAssetsTotal(v)};
    }
    if (staged.depositBlocked)
        v->setFlag(lsfVaultOwnerCanBlockDeposit | lsfVaultDepositBlocked);
    if (staged.subscriptionDate && staged.redemptionDate)
    {
        v->at(sfVaultKind) = std::to_underlying(VaultKind::ClosedEnded);
        v->at(sfSubscriptionDate) = *staged.subscriptionDate;
        v->at(sfRedemptionDate) = *staged.redemptionDate;
    }
    if (staged.earlyExitFeeRate)
        v->at(sfEarlyExitFeeRate) = *staged.earlyExitFeeRate;
    issuance->setFieldU64(sfOutstandingAmount, staged.sharesTotal);
    if (staged.holderShares)
    {
        auto const token = sb.peek(keylet::mptoken(v->at(sfShareMPTID), holder.id()));
        if (!token)
            throw std::runtime_error("stageVault: the holder has no share MPToken");
        token->setFieldU64(sfMPTAmount, *staged.holderShares);
        sb.update(token);
    }
    if (staged.depositorBalance)
    {
        stageTrustLine(
            sb, holder.id(), staged.depositorBalance->get<Issue>(), *staged.depositorBalance);
    }
    if (staged.pseudoHolding)
    {
        AccountID const pseudo = v->at(sfAccount);
        if (asset.native())
        {
            auto const account = sb.peek(keylet::account(pseudo));
            account->setFieldAmount(sfBalance, staged.available);
            sb.update(account);
        }
        else if (asset.holds<MPTIssue>())
        {
            auto const token = sb.peek(keylet::mptoken(asset.get<MPTIssue>().getMptID(), pseudo));
            token->setFieldU64(sfMPTAmount, staged.available.mantissa());
            sb.update(token);
        }
        else
        {
            stageTrustLine(sb, pseudo, asset.get<Issue>(), Number{staged.available});
        }
    }
    sb.update(v);
    sb.update(issuance);
    sb.apply(view);
}

// Stage `staged` on a copy of the open ledger, apply `tx` there, and discard the copy: the
// production submit path also applies to an OpenView of the current ledger.
[[nodiscard]] inline AppliedVaultTx
applyStaged(
    jtx::Env& env,
    Keylet const& vault,
    jtx::Account const& holder,
    StagedAmounts const& staged,
    json::Value const& tx)
{
    OpenView view{*env.current()};
    stageVault(view, vault, holder, staged);
    Asset const asset = view.read(vault)->at(sfAsset);
    Vault const pre = readVaultState(view, vault, asset);
    Number const heldBefore = pseudoHolding(view, vault);
    Number const sharesBefore = holderShareBalance(view, vault, holder.id());
    auto const jt = env.jt(tx);
    TER const ter = xrpl::apply(env.app(), view, *jt.stx, TapUnlimited, env.journal).ter;
    return {
        .pre = pre,
        .ter = ter,
        .post = readVaultState(view, vault, asset),
        .asset = asset,
        .storedTotal = Number{view.read(vault)->at(sfAssetsTotal)},
        .held = pseudoHolding(view, vault) - heldBefore,
        .heldShares = holderShareBalance(view, vault, holder.id()) - sharesBefore,
    };
}

[[nodiscard]] inline AppliedVaultTx
applyDeposit(
    jtx::Env& env,
    Keylet const& vault,
    jtx::Account const& depositor,
    StagedAmounts const& staged,
    STAmount const& amount,
    bool donate = false)
{
    jtx::Vault::DepositArgs args{.depositor = depositor, .id = vault.key, .amount = amount};
    if (donate)
        args.flags = tfVaultDonate;
    AppliedVaultTx applied = applyStaged(env, vault, depositor, staged, jtx::Vault::deposit(args));
    applied.assets = applied.post.assetsTotal - applied.pre.assetsTotal;
    applied.shares = applied.post.sharesTotal - applied.pre.sharesTotal;
    return applied;
}

[[nodiscard]] inline AppliedVaultTx
applyDeposit(
    jtx::Env& env,
    Keylet const& vault,
    jtx::Account const& depositor,
    StagedVault const& staged,
    STAmount const& amount,
    bool donate = false)
{
    return applyDeposit(env, vault, depositor, stagedAmounts(env, vault, staged), amount, donate);
}

// A list row's index and the vault or asset it runs on, prefixed to its failure messages.
[[nodiscard]] inline std::string
rowText(std::size_t index, std::string const& on = {})
{
    return (on.empty() ? "" : on + " ") + "row " + std::to_string(index) + ": ";
}

// The staged sample, prefixed to every failure message.
[[nodiscard]] inline std::string
sampleText(StagedAmounts const& s, STAmount const& amount)
{
    std::string t = "amount " + amount.getText() + ", available " + s.available.getText() +
        ", deployed " + s.deployed.getText() + ", yield " + s.yield.getText() + ", loss " +
        s.loss.getText() + ", sharesTotal " + std::to_string(s.sharesTotal);
    if (s.maximum)
        t += ", maximum " + s.maximum->getText();
    if (s.holderShares)
        t += ", holderShares " + std::to_string(*s.holderShares);
    if (s.subscriptionDate && s.redemptionDate)
    {
        t += ", subscription " + std::to_string(*s.subscriptionDate) + ", redemption " +
            std::to_string(*s.redemptionDate);
    }
    if (s.earlyExitFeeRate)
        t += ", fee rate " + std::to_string(*s.earlyExitFeeRate);
    return t + ": ";
}

// The staged sample in vault units, prefixed to every failure message.
[[nodiscard]] inline std::string
sampleText(StagedVault const& s)
{
    std::string t = "in vault units: available " + std::to_string(s.available) + ", deployed " +
        std::to_string(s.deployed) + ", yield " + std::to_string(s.yield) + ", loss " +
        std::to_string(s.loss) + ", sharesTotal " + std::to_string(s.sharesTotal);
    if (s.maximum)
        t += ", maximum " + std::to_string(*s.maximum);
    if (s.holderShares)
        t += ", holderShares " + std::to_string(*s.holderShares);
    if (s.subscriptionDate && s.redemptionDate)
    {
        t += ", subscription " + std::to_string(*s.subscriptionDate) + ", redemption " +
            std::to_string(*s.redemptionDate);
    }
    if (s.earlyExitFeeRate)
        t += ", fee rate " + std::to_string(*s.earlyExitFeeRate);
    return t + ": ";
}

[[nodiscard]] inline std::string
sampleText(StagedVault const& s, STAmount const& amount)
{
    return "amount " + amount.getText() + ", " + sampleText(s);
}

// The model's vault after the transaction equals C++'s.
inline void
expectSameVault(
    beast::unit_test::Suite& suite,
    std::string const& at,
    Vault const& lean,
    Vault const& cpp)
{
    auto const same = [&](char const* field, Number const& l, Number const& c) {
        suite.expect(l == c, at + field + " lean=" + to_string(l) + " cpp=" + to_string(c));
    };
    same("assetsTotal", lean.assetsTotal, cpp.assetsTotal);
    same("assetsAvailable", lean.assetsAvailable, cpp.assetsAvailable);
    same("assetsDeployed", lean.assetsDeployed, cpp.assetsDeployed);
    same("assetsReserved", lean.assetsReserved, cpp.assetsReserved);
    same("sharesTotal", lean.sharesTotal, cpp.sharesTotal);
    same("lossUnrealized", lean.lossUnrealized, cpp.lossUnrealized);
    same("yieldUnrealized", lean.yieldUnrealized, cpp.yieldUnrealized);
}

// The model's verdict as a TER, a model error as tefEXCEPTION followed by its kind.
[[nodiscard]] inline std::string
leanVerdictText(std::optional<LeanError> leanError, TER ter)
{
    return leanError ? "tefEXCEPTION (" + leanErrorText(*leanError) + ")" : transToken(ter);
}

// Both sides of one transaction return `expected`; when both succeed, every vault field is equal,
// and so are the assets and shares the model returns and what C++ moved, when the C++ side set it.
// A model error never matches: a row expecting tefEXCEPTION names its model error
// (expectCppOnlyRejection).
inline void
expectSame(
    beast::unit_test::Suite& suite,
    std::string const& at,
    AppliedVaultTx const& cpp,
    LeanVaultResult const& lean,
    TER expected)
{
    TER const leanTer = lean.error.value_or(tesSUCCESS);
    suite.expect(
        !lean.leanError && expected != tefEXCEPTION && leanTer == expected && cpp.ter == expected,
        at + "lean=" + leanVerdictText(lean.leanError, leanTer) + " cpp=" + transToken(cpp.ter) +
            " expected=" + transToken(expected));
    if (lean.leanError)
        return;
    if (leanTer != tesSUCCESS || cpp.ter != tesSUCCESS)
        return;

    auto const text = [](auto const& v) {
        using T = std::decay_t<decltype(v)>;
        if constexpr (std::is_same_v<T, Number>)
        {
            return to_string(v);
        }
        else if constexpr (std::is_same_v<T, bool>)
        {
            return std::string{v ? "true" : "false"};
        }
        else
        {
            return std::to_string(v);
        }
    };
    auto const same = [&](char const* field, auto const& l, auto const& c) {
        suite.expect(l == c, at + field + " lean=" + text(l) + " cpp=" + text(c));
    };
    auto const sameOptional = [&](char const* field, auto const& l, auto const& c) {
        auto const show = [&](auto const& o) { return o ? text(*o) : std::string{"none"}; };
        suite.expect(l == c, at + field + " lean=" + show(l) + " cpp=" + show(c));
    };
    Vault const& lv = lean.vault;
    Vault const& cv = cpp.post;
    same("assetsTotal", lv.assetsTotal, cv.assetsTotal);
    same("assetsAvailable", lv.assetsAvailable, cv.assetsAvailable);
    same("assetsDeployed", lv.assetsDeployed, cv.assetsDeployed);
    same("assetsReserved", lv.assetsReserved, cv.assetsReserved);
    sameOptional("assetsMaximum", lv.assetsMaximum, cv.assetsMaximum);
    same("numericType", int{lv.numericType}, int{cv.numericType});
    same("scale", int{lv.scale}, int{cv.scale});
    same("sharesTotal", lv.sharesTotal, cv.sharesTotal);
    same("lossUnrealized", lv.lossUnrealized, cv.lossUnrealized);
    same("yieldUnrealized", lv.yieldUnrealized, cv.yieldUnrealized);
    sameOptional("subscriptionDate", lv.subscriptionDate, cv.subscriptionDate);
    sameOptional("redemptionDate", lv.redemptionDate, cv.redemptionDate);
    sameOptional("earlyExitFeeRate", lv.earlyExitFeeRate, cv.earlyExitFeeRate);
    same("ownerCanBlockDeposit", lv.ownerCanBlockDeposit, cv.ownerCanBlockDeposit);
    same("depositBlocked", lv.depositBlocked, cv.depositBlocked);
    if (cpp.assets)
        same("assets", Number{lean.assets}, *cpp.assets);
    if (cpp.shares)
        same("shares", Number{lean.shares}, *cpp.shares);
    // C++ stores the total as the vault asset's amount, rounded down from available + deployed.
    if (cpp.storedTotal)
    {
        NumberRoundModeGuard const rg(Number::RoundingMode::Downward);
        same("stored assetsTotal", Number{STAmount{cpp.asset, lv.assetsTotal}}, *cpp.storedTotal);
    }
    if (cpp.held)
        same("pseudo-account holding", Number{lean.assets}, *cpp.held);
    if (cpp.heldShares)
        same("holder share balance", Number{lean.shares}, *cpp.heldShares);
}

// C++ returns `expected`, a TER the model has no counterpart for: a preflight rejection (tem) or
// a C++ exception (tefEXCEPTION). With a `leanError` the model must fail with exactly that error
// (notLawful: the fields break a model invariant; badInput: it cannot express them). With none
// the model must SUCCEED: no model error and no model TER (it normalizes the field).
inline void
expectCppOnlyRejection(
    beast::unit_test::Suite& suite,
    std::string const& at,
    AppliedVaultTx const& cpp,
    LeanVaultResult const& lean,
    TER expected,
    std::optional<LeanError> leanError)
{
    suite.expect(
        cpp.ter == expected && lean.leanError == leanError && (leanError || !lean.error),
        at + "lean=" + leanVerdictText(lean.leanError, lean.error.value_or(tesSUCCESS)) +
            " cpp=" + transToken(cpp.ter) + " expected=" + transToken(expected) +
            " with lean error " + leanErrorText(leanError));
}

// The check a list row asks for: a row naming a `leanError` is a C++-only rejection the model
// answers with that error; a row without one expects `expected` on both sides.
inline void
expectRow(
    beast::unit_test::Suite& suite,
    std::string const& at,
    AppliedVaultTx const& cpp,
    LeanVaultResult const& lean,
    TER expected,
    std::optional<LeanError> leanError)
{
    if (leanError)
        expectCppOnlyRejection(suite, at, cpp, lean, expected, leanError);
    else
        expectSame(suite, at, cpp, lean, expected);
}

struct AppliedVaultDelete
{
    Vault pre;
    TER ter;
    bool deleted;
};

// VaultDelete of a staged vault on a copy of the open ledger, discarded afterwards.
[[nodiscard]] inline AppliedVaultDelete
applyDelete(
    jtx::Env& env,
    Keylet const& vault,
    jtx::Account const& owner,
    StagedAmounts const& staged)
{
    OpenView view{*env.current()};
    stageVault(view, vault, owner, staged);
    Vault const pre = readVaultState(view, vault, view.read(vault)->at(sfAsset));
    auto const jt = env.jt(jtx::Vault::del({.owner = owner, .id = vault.key}));
    TER const ter = xrpl::apply(env.app(), view, *jt.stx, TapUnlimited, env.journal).ter;
    return {.pre = pre, .ter = ter, .deleted = !view.read(vault)};
}

// Both sides of a VaultDelete return `expected`, and the vault is gone exactly when C++ succeeds.
inline void
expectSame(
    beast::unit_test::Suite& suite,
    std::string const& at,
    AppliedVaultDelete const& cpp,
    LawfulTerResult const& lean,
    TER expected)
{
    suite.expect(
        !lean.leanError && lean.ter == expected && cpp.ter == expected,
        at + "lean=" + leanVerdictText(lean.leanError, lean.ter) + " cpp=" + transToken(cpp.ter) +
            " expected=" + transToken(expected));
    suite.expect(
        cpp.deleted == (cpp.ter == tesSUCCESS),
        at + (cpp.deleted ? "the vault is gone after " : "the vault is still there after ") +
            transToken(cpp.ter));
}

// A withdrawal of `amount` (vault assets, or shares) by `holder` from a staged vault whose
// pseudo-account holds the available assets and whose holder holds every share unless
// `holderShares` is set. Records what left the vault (an early-exit fee stays behind) and the
// shares burned.
[[nodiscard]] inline AppliedVaultTx
applyWithdraw(
    jtx::Env& env,
    Keylet const& vault,
    jtx::Account const& holder,
    StagedAmounts staged,
    STAmount const& amount)
{
    staged.pseudoHolding = true;
    if (!staged.holderShares)
        staged.holderShares = staged.sharesTotal;
    AppliedVaultTx applied = applyStaged(
        env,
        vault,
        holder,
        staged,
        jtx::Vault::withdraw({.depositor = holder, .id = vault.key, .amount = amount}));
    applied.assets = applied.pre.assetsAvailable - applied.post.assetsAvailable;
    applied.shares = applied.pre.sharesTotal - applied.post.sharesTotal;
    applied.held = -*applied.held;
    applied.heldShares = -*applied.heldShares;
    return applied;
}

[[nodiscard]] inline AppliedVaultTx
applyWithdraw(
    jtx::Env& env,
    Keylet const& vault,
    jtx::Account const& holder,
    StagedVault const& staged,
    STAmount const& amount)
{
    return applyWithdraw(env, vault, holder, stagedAmounts(env, vault, staged), amount);
}

// The model's withdrawal from the pre-state C++ saw, by the holder `applyWithdraw` staged: it
// waives the unrealized loss when that holder owns every share.
[[nodiscard]] inline LeanVaultResult
leanWithdraw(
    AppliedVaultTx const& cpp,
    StagedAmounts const& staged,
    STAmount const& amount,
    bool byShares,
    std::uint32_t parentCloseTime)
{
    std::uint64_t const held = staged.holderShares.value_or(staged.sharesTotal);
    return leanVaultWithdraw(
        cpp.pre,
        amount,
        byShares,
        parentCloseTime,
        held != 0 && held == staged.sharesTotal,
        Number{static_cast<std::int64_t>(held)});
}

// A clawback by `account` from `holder` of a staged vault whose pseudo-account holds the available
// assets and whose holder holds every share unless `holderShares` is set: the asset issuer claws
// `amount` of the asset, the vault owner burns `amount` shares; no amount claws everything.
// Records what left the vault and the shares burned.
[[nodiscard]] inline AppliedVaultTx
applyClawback(
    jtx::Env& env,
    Keylet const& vault,
    jtx::Account const& account,
    jtx::Account const& holder,
    StagedAmounts staged,
    std::optional<STAmount> const& amount)
{
    staged.pseudoHolding = true;
    if (!staged.holderShares)
        staged.holderShares = staged.sharesTotal;
    AppliedVaultTx applied = applyStaged(
        env,
        vault,
        holder,
        staged,
        jtx::Vault::clawback(
            {.issuer = account, .id = vault.key, .holder = holder, .amount = amount}));
    applied.assets = applied.pre.assetsAvailable - applied.post.assetsAvailable;
    applied.shares = applied.pre.sharesTotal - applied.post.sharesTotal;
    applied.held = -*applied.held;
    applied.heldShares = -*applied.heldShares;
    return applied;
}

// The model's issuer clawback from the pre-state C++ saw (an omitted amount is a zero `amount`): it
// waives the unrealized loss when the holder `applyClawback` staged owns every share.
[[nodiscard]] inline LeanVaultResult
leanClawback(
    AppliedVaultTx const& cpp,
    StagedAmounts const& staged,
    STAmount const& amount,
    MPTIssue const& shares)
{
    std::uint64_t const held = staged.holderShares.value_or(staged.sharesTotal);
    return leanVaultClawback(
        cpp.pre, amount, STAmount{shares, held}, held != 0 && held == staged.sharesTotal);
}

// The model's owner burn of `amount` shares (zero for all): canBurnShares, then burnShares of the
// holder's whole balance, which is what the result reports burned (no assets move).
[[nodiscard]] inline LeanVaultResult
leanOwnerBurn(AppliedVaultTx const& cpp, StagedAmounts const& staged, STAmount const& amount)
{
    STAmount const held{amount.get<MPTIssue>(), staged.holderShares.value_or(staged.sharesTotal)};
    LeanAmountResult const can = leanCanBurnShares(cpp.pre, amount, held);
    if (can.leanError || can.error)
        return {.leanError = can.leanError, .error = can.error};
    LeanBurnResult const burn = leanBurnShares(cpp.pre, held);
    if (burn.leanError || burn.error)
        return {.leanError = burn.leanError, .error = burn.error};
    return {.shares = held, .vault = burn.vault};
}

}  // namespace xrpl::test::formal_verification
