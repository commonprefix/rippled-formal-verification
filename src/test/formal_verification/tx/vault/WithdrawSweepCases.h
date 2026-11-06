#pragma once

#include <test/formal_verification/common/Sweep.h>
#include <test/formal_verification/tx/vault/DepositSweepCases.h>

#include <algorithm>
#include <cstdint>
#include <limits>
#include <string>
#include <vector>

namespace xrpl::test::formal_verification::withdraw_sweep {

// Hardcoded rows for the VaultWithdraw sweeps, in vault grid units (shares in shares), built the
// same way as the deposit rows: each row sits exactly on its cusp, the levels are the smallest
// value, an ordinary one (kOrdinaryUnits) and the largest that still reaches the cusp
// (kLargeUnits), and a sweep moves two values of each row by kAroundCusp. The withdrawer holds
// all shares unless a table says otherwise.

constexpr std::int64_t kInt64Max = std::numeric_limits<std::int64_t>::max();
constexpr std::int64_t kFeeRateMaximum = 100'000;

// A by-shares redemption of `shares` out of `sharesTotal` from a vault holding `nav` assets
// available and nothing deployed: the payout is nav * shares / sharesTotal.
struct RedeemCusp
{
    std::int64_t nav;
    std::int64_t sharesTotal;
    std::int64_t shares;
};

// Zero payout (XRP, MPT): 2 * nav * shares == shares total pays exactly half a unit, which rounds
// to even (0, tecPRECISION_LOSS); one share more pays one unit.
constexpr RedeemCusp kZeroPayoutCusps[] = {
    {.nav = 1, .sharesTotal = 2, .shares = 1},
    {.nav = 1, .sharesTotal = 2 * kOrdinaryUnits, .shares = kOrdinaryUnits},
    {.nav = kOrdinaryUnits, .sharesTotal = 2 * kOrdinaryUnits, .shares = 1},
    {.nav = 31'250, .sharesTotal = 2 * kOrdinaryUnits, .shares = 32'000},
    {.nav = 1, .sharesTotal = 2 * kLargeUnits, .shares = kLargeUnits},
    {.nav = kLargeUnits, .sharesTotal = 2 * kLargeUnits, .shares = 1},
    {.nav = 50'000'000, .sharesTotal = 2 * kLargeUnits, .shares = 80'000'000},
};
static_assert(std::ranges::all_of(kZeroPayoutCusps, [](RedeemCusp const& c) {
    return 2 * __int128{c.nav} * c.shares == c.sharesTotal;
}));

// Clamp to zero (IOU): nav * shares == shares total pays exactly one grid step; below it the
// payout floors to zero (tecPRECISION_LOSS). Shares totals stay below 10^16 (16-digit IOU).
constexpr RedeemCusp kClampToZeroCusps[] = {
    {.nav = 2, .sharesTotal = 2, .shares = 1},
    {.nav = 2, .sharesTotal = 2 * kOrdinaryUnits, .shares = kOrdinaryUnits},
    {.nav = kOrdinaryUnits, .sharesTotal = 10 * kOrdinaryUnits, .shares = 10},
    {.nav = kOrdinaryUnits, .sharesTotal = 1'000'000 * kOrdinaryUnits, .shares = 1'000'000},
    {.nav = kLargeUnits, .sharesTotal = 2 * kLargeUnits, .shares = 2},
};
static_assert(std::ranges::all_of(kClampToZeroCusps, [](RedeemCusp const& c) {
    return __int128{c.nav} * c.shares == c.sharesTotal && c.sharesTotal < 10'000'000'000'000'000;
}));

// Payout out of range (XRP): nav * shares == 10^17 * shares total pays exactly 10^17 drops, the
// largest XRP amount (here tecINSUFFICIENT_FUNDS). One drop more is out of the XRP range: C++
// throws a runtime_error the withdraw does not catch (tefEXCEPTION, a C++ robustness finding), the
// model an outOfRange error; both reject.
constexpr std::int64_t kXrpMaximumDrops = 100'000'000'000'000'000;
constexpr RedeemCusp kXrpPayoutRangeCusps[] = {
    {.nav = 1, .sharesTotal = 1, .shares = kXrpMaximumDrops},
    {.nav = kOrdinaryUnits, .sharesTotal = kOrdinaryUnits, .shares = kXrpMaximumDrops},
    {.nav = kOrdinaryUnits, .sharesTotal = 1, .shares = kXrpMaximumDrops / kOrdinaryUnits},
};
static_assert(std::ranges::all_of(kXrpPayoutRangeCusps, [](RedeemCusp const& c) {
    return __int128{c.nav} * c.shares == __int128{kXrpMaximumDrops} * c.sharesTotal;
}));

// Payout out of range (MPT): pays 2^63 - 2, one share more pays 2^63 (past the MPT maximum).
constexpr RedeemCusp kMptPayoutRangeCusps[] = {
    {.nav = 2, .sharesTotal = 1, .shares = kInt64Max / 2},
};
static_assert(std::ranges::all_of(kMptPayoutRangeCusps, [](RedeemCusp const& c) {
    return __int128{c.nav} * c.shares == kInt64Max - 1;
}));

// To-nearest switch (IOU): an odd nav redeemed by half the shares pays X + 1/2 units, X = (nav -
// 1) / 2, on both sides of X = 10^15, where the payout amount starts rounding to the grid itself.
// Both sides succeed; the post-state and payout are compared.
constexpr RedeemCusp kToNearestCusps[] = {
    {.nav = 2'000'000'000'000'000 - 1, .sharesTotal = 2, .shares = 1},
    {.nav = 2'000'000'000'000'000 + 1, .sharesTotal = 2, .shares = 1},
    {.nav = 2'000'000'000'000'000 + 3, .sharesTotal = 2, .shares = 1},
    {.nav = kLargeUnits + 1, .sharesTotal = 2, .shares = 1},
};
static_assert(std::ranges::all_of(kToNearestCusps, [](RedeemCusp const& c) {
    return c.nav % 2 == 1 && c.sharesTotal == 2 * c.shares;
}));

// Dust with a 100% early-exit fee (IOU): nav * shares / shares total is half the last digit of a
// 16-digit available nav, so the debit rounds the stored balance back unchanged (to even) and is
// refused (tecPRECISION_LOSS); half a digit more changes it. One even and one odd mantissa.
constexpr RedeemCusp kFullFeeDustCusps[] = {
    {.nav = 2'000'000'000'000'000'000, .sharesTotal = 4'000'000'000'000'000'000, .shares = 1'000},
    {.nav = 2'000'000'000'000'001'000, .sharesTotal = 4'000'000'000'000'002'000, .shares = 1'000},
};
static_assert(std::ranges::all_of(kFullFeeDustCusps, [](RedeemCusp const& c) {
    return 2 * __int128{c.nav} * c.shares == __int128{1'000} * c.sharesTotal;
}));

// Available assets: withdrawing exactly the available assets (with assets deployed, so not a
// final withdrawal) is the last that fits (tecINSUFFICIENT_FUNDS above). Price 1. The sweep moves
// the amount and the available assets.
struct AvailableCusp
{
    std::int64_t available;
    std::int64_t deployed;
    std::int64_t amount;
};

constexpr AvailableCusp kAvailableCusps[] = {
    {.available = 1, .deployed = 1, .amount = 1},
    {.available = 1, .deployed = kLargeUnits, .amount = 1},
    {.available = kOrdinaryUnits, .deployed = 1, .amount = kOrdinaryUnits},
    {.available = kOrdinaryUnits, .deployed = kOrdinaryUnits, .amount = kOrdinaryUnits},
    {.available = kLargeUnits, .deployed = 1, .amount = kLargeUnits},
    {.available = kLargeUnits, .deployed = kLargeUnits, .amount = kLargeUnits},
};
static_assert(std::ranges::all_of(kAvailableCusps, [](AvailableCusp const& c) {
    return c.amount == c.available && c.deployed > 0;
}));

// Early-exit fee consumes the payout (Investment): gross * (1e5 - rate) == 1e5 pays exactly one
// unit; less is refused (tecPRECISION_LOSS), and a rate of exactly 100% pays nothing and succeeds.
// The sweep moves the gross amount and the rate.
struct FeeCusp
{
    std::int64_t rate;
    std::int64_t gross;
};

constexpr FeeCusp kFeeConsumesPayoutCusps[] = {
    {.rate = 50'000, .gross = 2},
    {.rate = 90'000, .gross = 10},
    {.rate = 99'000, .gross = 100},
    {.rate = 99'990, .gross = 10'000},
    {.rate = 99'999, .gross = 100'000},
};
static_assert(std::ranges::all_of(kFeeConsumesPayoutCusps, [](FeeCusp const& c) {
    return c.gross * (kFeeRateMaximum - c.rate) == kFeeRateMaximum;
}));

// Net payout over available (Investment, 5% fee): gross * (1e5 - rate) == available * 1e5 nets
// exactly the available assets; one more is refused (tecINSUFFICIENT_FUNDS). Enough is deployed
// that the vault's assets cover every moved gross. The sweep moves the gross and the available.
struct NetOverAvailableCusp
{
    std::int64_t rate;
    std::int64_t gross;
    std::int64_t available;
    std::int64_t deployed;
};

constexpr NetOverAvailableCusp kNetOverAvailableCusps[] = {
    {.rate = 5'000, .gross = 20, .available = 19, .deployed = 5},
    {.rate = 5'000,
     .gross = 2 * kOrdinaryUnits,
     .available = 19 * kOrdinaryUnits / 10,
     .deployed = kOrdinaryUnits / 10 + 4},
    {.rate = 5'000,
     .gross = kLargeUnits,
     .available = 19 * kLargeUnits / 20,
     .deployed = kLargeUnits / 20 + 4},
};
static_assert(std::ranges::all_of(kNetOverAvailableCusps, [](NetOverAvailableCusp const& c) {
    return __int128{c.gross} * (kFeeRateMaximum - c.rate) ==
        __int128{c.available} * kFeeRateMaximum &&
        c.available + c.deployed >= c.gross + 4;
}));

// Final withdrawal: redeeming every share with nothing deployed pays all available assets; with
// assets deployed it is refused (tecHAS_OBLIGATIONS). Price 1 (shares total = available +
// deployed). The sweep moves the deployed assets and the shares.
struct FinalCusp
{
    std::int64_t available;
    std::int64_t deployed;
    std::int64_t shares;
};

constexpr FinalCusp kFinalCusps[] = {
    {.available = 2, .deployed = 0, .shares = 2},
    {.available = kOrdinaryUnits, .deployed = 0, .shares = kOrdinaryUnits},
    {.available = kLargeUnits, .deployed = 0, .shares = kLargeUnits},
};
static_assert(std::ranges::all_of(kFinalCusps, [](FinalCusp const& c) {
    return c.deployed == 0 && c.shares == c.available + c.deployed;
}));

// Fully impaired vault: nothing available and the whole deployed total lost, so the net asset
// value is zero and a by-shares redemption burns the shares for nothing (tesSUCCESS); one unit of
// net asset value makes the payout non-zero and the request fails. The withdrawer is not the sole
// holder (a sole holder waives the loss). The sweep moves the loss and the shares.
struct ImpairedCusp
{
    std::int64_t deployed;
    std::int64_t loss;
    std::int64_t sharesTotal;
    std::int64_t shares;
};

constexpr ImpairedCusp kImpairedCusps[] = {
    {.deployed = 2, .loss = 2, .sharesTotal = kOrdinaryUnits, .shares = 1},
    {.deployed = kOrdinaryUnits,
     .loss = kOrdinaryUnits,
     .sharesTotal = kOrdinaryUnits,
     .shares = 1},
    {.deployed = kLargeUnits, .loss = kLargeUnits, .sharesTotal = kLargeUnits, .shares = 1},
    {.deployed = kOrdinaryUnits, .loss = kOrdinaryUnits, .sharesTotal = 2, .shares = 1},
};
static_assert(std::ranges::all_of(kImpairedCusps, [](ImpairedCusp const& c) {
    return c.loss == c.deployed && c.shares == 1;
}));

// Sub-grid payout over available (IOU): with a tenth of a unit per share, redeeming 10 *
// available shares pays exactly the available assets; one share more pays a tenth over, which the
// check on the unclamped payout alone refuses (tecINSUFFICIENT_FUNDS). Below 10^15 units, where
// the payout still keeps sub-grid digits. The sweep moves the shares and the deployed assets.
struct SubGridCusp
{
    std::int64_t available;
    std::int64_t deployed;
    std::int64_t sharesTotal;
    std::int64_t shares;
};

constexpr SubGridCusp kSubGridOverAvailableCusps[] = {
    {.available = 1, .deployed = 1, .sharesTotal = 20, .shares = 10},
    {.available = kOrdinaryUnits,
     .deployed = 1,
     .sharesTotal = 10 * (kOrdinaryUnits + 1),
     .shares = 10 * kOrdinaryUnits},
    {.available = 999'999'999'999'999,
     .deployed = 1,
     .sharesTotal = 10 * 1'000'000'000'000'000,
     .shares = 10 * 999'999'999'999'999},
};
static_assert(std::ranges::all_of(kSubGridOverAvailableCusps, [](SubGridCusp const& c) {
    return __int128{c.available + c.deployed} * c.shares == __int128{c.available} * c.sharesTotal &&
        c.available < 1'000'000'000'000'000;
}));

// Decade-crossing outflow (IOU): the payout is truncated to the grid of available - amount, which
// is 10 units from 10^16 units up. Available assets are availableMantissa * 10 units (one
// mantissa step); each row leaves exactly 10^16 - 1 or 10^16. The sweep moves both values.
struct DecadeCusp
{
    std::int64_t availableMantissa;
    std::int64_t amount;
};

constexpr std::int64_t kSeventeenDigits = 10'000'000'000'000'000;
constexpr DecadeCusp kDecadeCusps[] = {
    {.availableMantissa = 1'000'000'000'000'000, .amount = 1},
    {.availableMantissa = 1'000'000'000'000'001, .amount = 10},
};
static_assert(std::ranges::all_of(kDecadeCusps, [](DecadeCusp const& c) {
    std::int64_t const left = c.availableMantissa * 10 - c.amount;
    return left == kSeventeenDigits - 1 || left == kSeventeenDigits;
}));

// Holder's shares: redeeming exactly the shares held is the last that fits
// (tecINSUFFICIENT_FUNDS above); one share is held by someone else. Price 1. The sweep moves the
// shares held and redeemed.
struct HolderCusp
{
    std::int64_t holderShares;
    std::int64_t shares;
};

constexpr HolderCusp kHolderSharesCusps[] = {
    {.holderShares = 1, .shares = 1},
    {.holderShares = kOrdinaryUnits, .shares = kOrdinaryUnits},
    {.holderShares = kLargeUnits, .shares = kLargeUnits},
};
static_assert(std::ranges::all_of(kHolderSharesCusps, [](HolderCusp const& c) {
    return c.shares == c.holderShares;
}));

// Sole-holder loss waiver: a holder of every share is priced at the assets total, any other at
// assets total - loss unrealized. Both sides succeed; the post-state and payout are compared. The
// sweep moves the holder's shares and the loss.
struct WaiverCusp
{
    std::int64_t total;
    std::int64_t deployed;
    std::int64_t loss;
    std::int64_t holderShares;
};

constexpr WaiverCusp kWaiverCusps[] = {
    {.total = kOrdinaryUnits, .deployed = 10, .loss = 3, .holderShares = kOrdinaryUnits},
    {.total = kLargeUnits,
     .deployed = 2 * kOrdinaryUnits,
     .loss = kOrdinaryUnits,
     .holderShares = kLargeUnits},
};
static_assert(std::ranges::all_of(kWaiverCusps, [](WaiverCusp const& c) {
    return c.holderShares == c.total && c.loss + 2 <= c.deployed;
}));

// By-assets share overflow (XRP, MPT): shares total * amount / nav == 2^63 - 1 shares, the
// largest share amount (here tecINSUFFICIENT_FUNDS); one more overflows (tecPATH_DRY).
struct ShareOverflowCusp
{
    std::int64_t nav;
    std::int64_t sharesTotal;
    std::int64_t amount;
};

constexpr ShareOverflowCusp kAssetsShareOverflowCusps[] = {
    {.nav = 1, .sharesTotal = kInt64Max / 7, .amount = 7},
};
static_assert(std::ranges::all_of(kAssetsShareOverflowCusps, [](ShareOverflowCusp const& c) {
    return __int128{c.sharesTotal} * c.amount == __int128{kInt64Max} * c.nav;
}));

// Every case the sweeps run, grouped by row. Dropped: non-positive amounts and shares, more
// shares redeemed than exist, a loss above the deployed assets, and fee rates above 100%.

// Zero shares by assets reuses the deposit rows: shares total * amount == assets total burns
// exactly one share.
inline std::vector<AroundCusp<PriceCusp>> const kZeroSharesByAssetsCases = aroundCusp(
    kZeroSharesCusps,
    &PriceCusp::sharesTotal,
    &PriceCusp::amount,
    [](PriceCusp const& c) { return c.sharesTotal >= 1 && c.amount >= 1 && c.amount <= c.total; });

template <std::size_t N>
std::vector<AroundCusp<RedeemCusp>>
redeemCases(RedeemCusp const (&rows)[N])
{
    return aroundCusp(rows, &RedeemCusp::sharesTotal, &RedeemCusp::shares, [](RedeemCusp const& c) {
        return c.sharesTotal >= 1 && c.shares >= 1 && c.shares <= c.sharesTotal;
    });
}

inline std::vector<AroundCusp<RedeemCusp>> const kZeroPayoutCases = redeemCases(kZeroPayoutCusps);
inline std::vector<AroundCusp<RedeemCusp>> const kClampToZeroBySharesCases =
    redeemCases(kClampToZeroCusps);
inline std::vector<AroundCusp<RedeemCusp>> const kFullFeeDustCases = redeemCases(kFullFeeDustCusps);
// Redeeming more shares than exist is the point here: only positive values are dropped.
inline std::vector<AroundCusp<RedeemCusp>> const kXrpPayoutRangeCases = aroundCusp(
    kXrpPayoutRangeCusps,
    &RedeemCusp::sharesTotal,
    &RedeemCusp::shares,
    [](RedeemCusp const& c) { return c.sharesTotal >= 1 && c.shares >= 1; });
inline std::vector<AroundCusp<RedeemCusp>> const kMptPayoutRangeCases = aroundCusp(
    kMptPayoutRangeCusps,
    &RedeemCusp::sharesTotal,
    &RedeemCusp::shares,
    [](RedeemCusp const& c) { return c.sharesTotal >= 1 && c.shares >= 1; });
// To-nearest rows move the nav and the shares.
inline std::vector<AroundCusp<RedeemCusp>> const kToNearestCases =
    aroundCusp(kToNearestCusps, &RedeemCusp::nav, &RedeemCusp::shares, [](RedeemCusp const& c) {
        return c.shares >= 1 && c.shares <= c.sharesTotal;
    });

inline std::vector<AroundCusp<AvailableCusp>> const kAvailableCases = aroundCusp(
    kAvailableCusps,
    &AvailableCusp::available,
    &AvailableCusp::amount,
    [](AvailableCusp const& c) { return c.available >= 0 && c.amount >= 1; });

inline std::vector<AroundCusp<FeeCusp>> const kFeeConsumesPayoutCases =
    aroundCusp(kFeeConsumesPayoutCusps, &FeeCusp::rate, &FeeCusp::gross, [](FeeCusp const& c) {
        return c.gross >= 1 && c.rate <= kFeeRateMaximum;
    });

inline std::vector<AroundCusp<NetOverAvailableCusp>> const kNetOverAvailableCases = aroundCusp(
    kNetOverAvailableCusps,
    &NetOverAvailableCusp::gross,
    &NetOverAvailableCusp::available,
    [](NetOverAvailableCusp const&) { return true; });

inline std::vector<AroundCusp<FinalCusp>> const kFinalCases =
    aroundCusp(kFinalCusps, &FinalCusp::deployed, &FinalCusp::shares, [](FinalCusp const& c) {
        return c.deployed >= 0 && c.shares >= 1 && c.shares <= c.available + c.deployed;
    });

inline std::vector<AroundCusp<ImpairedCusp>> const kImpairedCases = aroundCusp(
    kImpairedCusps,
    &ImpairedCusp::loss,
    &ImpairedCusp::shares,
    [](ImpairedCusp const& c) {
        return c.loss >= 0 && c.loss <= c.deployed && c.shares >= 1 && c.shares < c.sharesTotal;
    });

inline std::vector<AroundCusp<SubGridCusp>> const kSubGridOverAvailableCases = aroundCusp(
    kSubGridOverAvailableCusps,
    &SubGridCusp::deployed,
    &SubGridCusp::shares,
    [](SubGridCusp const& c) {
        return c.deployed >= 0 && c.shares >= 1 && c.shares < c.sharesTotal;
    });

inline std::vector<AroundCusp<DecadeCusp>> const kDecadeCases = aroundCusp(
    kDecadeCusps,
    &DecadeCusp::availableMantissa,
    &DecadeCusp::amount,
    [](DecadeCusp const& c) { return c.amount >= 1; });

inline std::vector<AroundCusp<HolderCusp>> const kHolderSharesCases = aroundCusp(
    kHolderSharesCusps,
    &HolderCusp::holderShares,
    &HolderCusp::shares,
    [](HolderCusp const& c) { return c.holderShares >= 1 && c.shares >= 1; });

inline std::vector<AroundCusp<WaiverCusp>> const kWaiverCases =
    aroundCusp(kWaiverCusps, &WaiverCusp::holderShares, &WaiverCusp::loss, [](WaiverCusp const& c) {
        return c.holderShares <= c.total && c.loss >= 0;
    });

inline std::vector<AroundCusp<ShareOverflowCusp>> const kAssetsShareOverflowCases = aroundCusp(
    kAssetsShareOverflowCusps,
    &ShareOverflowCusp::sharesTotal,
    &ShareOverflowCusp::amount,
    [](ShareOverflowCusp const&) { return true; });

// A row as it appears in failure messages.
inline std::string
describe(RedeemCusp const& c)
{
    return "nav " + std::to_string(c.nav) + ", sharesTotal " + std::to_string(c.sharesTotal) +
        ", shares " + std::to_string(c.shares);
}

inline std::string
describe(AvailableCusp const& c)
{
    return "available " + std::to_string(c.available) + ", deployed " + std::to_string(c.deployed) +
        ", amount " + std::to_string(c.amount);
}

inline std::string
describe(FeeCusp const& c)
{
    return "rate " + std::to_string(c.rate) + ", gross " + std::to_string(c.gross);
}

inline std::string
describe(NetOverAvailableCusp const& c)
{
    return "rate " + std::to_string(c.rate) + ", gross " + std::to_string(c.gross) +
        ", available " + std::to_string(c.available) + ", deployed " + std::to_string(c.deployed);
}

inline std::string
describe(FinalCusp const& c)
{
    return "available " + std::to_string(c.available) + ", deployed " + std::to_string(c.deployed) +
        ", shares " + std::to_string(c.shares);
}

inline std::string
describe(ImpairedCusp const& c)
{
    return "deployed " + std::to_string(c.deployed) + ", loss " + std::to_string(c.loss) +
        ", sharesTotal " + std::to_string(c.sharesTotal) + ", shares " + std::to_string(c.shares);
}

inline std::string
describe(SubGridCusp const& c)
{
    return "available " + std::to_string(c.available) + ", deployed " + std::to_string(c.deployed) +
        ", sharesTotal " + std::to_string(c.sharesTotal) + ", shares " + std::to_string(c.shares);
}

inline std::string
describe(DecadeCusp const& c)
{
    return "availableMantissa " + std::to_string(c.availableMantissa) + ", amount " +
        std::to_string(c.amount);
}

inline std::string
describe(HolderCusp const& c)
{
    return "holderShares " + std::to_string(c.holderShares) + ", shares " +
        std::to_string(c.shares);
}

inline std::string
describe(WaiverCusp const& c)
{
    return "total " + std::to_string(c.total) + ", deployed " + std::to_string(c.deployed) +
        ", loss " + std::to_string(c.loss) + ", holderShares " + std::to_string(c.holderShares);
}

inline std::string
describe(ShareOverflowCusp const& c)
{
    return "nav " + std::to_string(c.nav) + ", sharesTotal " + std::to_string(c.sharesTotal) +
        ", amount " + std::to_string(c.amount);
}

}  // namespace xrpl::test::formal_verification::withdraw_sweep
