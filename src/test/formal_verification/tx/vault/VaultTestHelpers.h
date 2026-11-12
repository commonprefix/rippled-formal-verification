#pragma once

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
#include <cstdint>
#include <optional>
#include <stdexcept>
#include <string>
#include <type_traits>
#include <utility>

namespace xrpl::test::formal_verification {

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

struct AppliedVaultTx
{
    Vault pre;
    TER ter;
    Vault post;
    // What C++ moved, when the transaction reports it: compared with the model's assets / shares.
    std::optional<Number> assets{};
    std::optional<Number> shares{};
};

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
    auto const jt = env.jt(tx);
    TER const ter = xrpl::apply(env.app(), view, *jt.stx, TapUnlimited, env.journal).ter;
    return {.pre = pre, .ter = ter, .post = readVaultState(view, vault, asset)};
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
sampleText(StagedVault const& s, STAmount const& amount)
{
    std::string t = "amount " + amount.getText() + ", in vault units: available " +
        std::to_string(s.available) + ", deployed " + std::to_string(s.deployed) + ", yield " +
        std::to_string(s.yield) + ", loss " + std::to_string(s.loss) + ", sharesTotal " +
        std::to_string(s.sharesTotal);
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

// The model accepts the staged state as lawful and agrees with C++ on the verdict and, when both
// succeed, on the vault. Returns the C++ verdict.
inline TER
expectAgree(
    beast::unit_test::Suite& suite,
    std::string const& at,
    AppliedVaultTx const& cpp,
    LeanVaultResult const& lean)
{
    suite.expect(lean.leanError != LeanError::notLawful, at + "model: staged state not lawful");
    TER const leanTer = lean.leanError ? TER{tefEXCEPTION} : lean.error.value_or(tesSUCCESS);
    suite.expect(
        leanTer == cpp.ter, at + "lean=" + transToken(leanTer) + " cpp=" + transToken(cpp.ter));
    if (cpp.ter == tesSUCCESS && leanTer == tesSUCCESS)
        expectSameVault(suite, at, lean.vault, cpp.post);
    return cpp.ter;
}

// A deposit (or donation) on a throwaway view of `staged` and the model on the same state must
// agree, and a deposit never charges more than offered. Returns the C++ verdict.
inline TER
checkDeposit(
    beast::unit_test::Suite& suite,
    jtx::Env& env,
    Keylet const& vault,
    jtx::Account const& depositor,
    StagedAmounts const& staged,
    STAmount const& amount,
    bool donate = false)
{
    AppliedVaultTx const cpp = applyDeposit(env, vault, depositor, staged, amount, donate);
    LeanVaultResult const lean = leanVaultDeposit(cpp.pre, amount, donate, parentCloseTime(env));
    std::string const at = sampleText(staged, amount);
    if (expectAgree(suite, at, cpp, lean) != tesSUCCESS || lean.leanError || lean.error)
        return cpp.ter;
    Number const charged = cpp.post.assetsTotal - cpp.pre.assetsTotal;
    suite.expect(charged <= Number{amount}, at + "cpp charged " + to_string(charged));
    suite.expect(
        Number{lean.assets} <= Number{amount},
        at + "lean charged " + to_string(Number{lean.assets}));
    return cpp.ter;
}

// Both sides of one transaction return `expected`; when both succeed, every vault field is equal,
// and so are the assets and shares the model returns and what C++ moved, when the C++ side set it.
inline void
expectSame(
    beast::unit_test::Suite& suite,
    std::string const& at,
    AppliedVaultTx const& cpp,
    LeanVaultResult const& lean,
    TER expected)
{
    TER const leanTer = lean.leanError ? TER{tefEXCEPTION} : lean.error.value_or(tesSUCCESS);
    suite.expect(
        leanTer == expected && cpp.ter == expected,
        at + "lean=" + transToken(leanTer) + " cpp=" + transToken(cpp.ter) +
            " expected=" + transToken(expected));
    if (leanTer != tesSUCCESS || cpp.ter != tesSUCCESS)
        return;

    auto const text = [](auto const& v) {
        using T = std::decay_t<decltype(v)>;
        if constexpr (std::is_same_v<T, Number>)
            return to_string(v);
        else if constexpr (std::is_same_v<T, bool>)
            return std::string{v ? "true" : "false"};
        else
            return std::to_string(v);
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
}

// A withdrawal (by assets, or by shares when `amount` is in shares) from a staged vault whose
// pseudo-account holds the available assets and whose holder holds `holderShares` (all shares
// when unset). Both sides must agree, also on the payout: what left the vault (an early-exit fee
// stays behind), equal to `expectedPayout` when given.
inline AppliedVaultTx
checkWithdraw(
    beast::unit_test::Suite& suite,
    jtx::Env& env,
    Keylet const& vault,
    jtx::Account const& holder,
    StagedAmounts staged,
    STAmount const& amount,
    std::optional<Number> const& expectedPayout = std::nullopt)
{
    staged.pseudoHolding = true;
    if (!staged.holderShares)
        staged.holderShares = staged.sharesTotal;
    std::uint64_t const held = *staged.holderShares;
    bool const byShares = amount.asset() != Asset{env.le(vault)->at(sfAsset)};
    AppliedVaultTx const cpp = applyStaged(
        env,
        vault,
        holder,
        staged,
        jtx::Vault::withdraw({.depositor = holder, .id = vault.key, .amount = amount}));
    LeanVaultResult const lean = leanVaultWithdraw(
        cpp.pre,
        amount,
        byShares,
        parentCloseTime(env),
        held != 0 && held == staged.sharesTotal,
        Number{static_cast<std::int64_t>(held)});
    std::string const at = sampleText(staged, amount);
    if (expectAgree(suite, at, cpp, lean) != tesSUCCESS || lean.leanError || lean.error)
        return cpp;
    Number const cppPayout = cpp.pre.assetsAvailable - cpp.post.assetsAvailable;
    suite.expect(
        Number{lean.assets} == cppPayout,
        at + "payout lean=" + to_string(Number{lean.assets}) + " cpp=" + to_string(cppPayout));
    if (expectedPayout)
    {
        suite.expect(
            cppPayout == *expectedPayout,
            at + "payout " + to_string(cppPayout) + " expected " + to_string(*expectedPayout));
    }
    return cpp;
}

}  // namespace xrpl::test::formal_verification
