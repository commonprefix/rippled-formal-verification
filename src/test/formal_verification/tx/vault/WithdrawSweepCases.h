#pragma once

#include <test/formal_verification/common/Sweep.h>
#include <test/formal_verification/tx/vault/DepositSweepCases.h>

#include <xrpl/protocol/Protocol.h>
#include <xrpl/protocol/STAmount.h>

#include <algorithm>
#include <cstddef>
#include <cstdint>
#include <string>
#include <vector>

namespace xrpl::test::formal_verification::withdraw_sweep {

// Hardcoded rows for the VaultWithdraw sweeps, in vault grid units (shares in shares), built the
// same way as the deposit rows: each row sits exactly on its cusp, the levels are the smallest
// value, an ordinary one (kOrdinaryUnits) and the largest that still reaches the cusp (at the bound
// each table names), and a sweep moves two values of each row by kAroundCusp. The withdrawer
// holds all shares unless a table says otherwise.

// The largest even shares total whose moves stay within the share cap.
constexpr std::int64_t kLargestEvenShares = kShareCap - 3;
static_assert(kLargestEvenShares % 2 == 0 && kLargestEvenShares + 2 <= kShareCap);

// The largest even IOU total whose moves stay within 16 digits.
constexpr std::int64_t kLargestEvenIouUnits = kIouMaxMantissa - 3;
static_assert(kLargestEvenIouUnits % 4 == 0 && kLargestEvenIouUnits + 2 <= kIouMaxMantissa);

// 2 * (h - 1) * h is the largest balanced zero-payout shares total within the share cap.
constexpr std::int64_t kBalancedHalf = 2'147'483'648;
static_assert(
    2 * __int128{kBalancedHalf - 1} * kBalancedHalf + 2 <= kShareCap &&
    2 * __int128{kBalancedHalf} * kBalancedHalf > kShareCap);

// A by-shares redemption of `shares` out of `sharesTotal` from a vault holding `nav` assets
// available and nothing deployed: the payout is nav * shares / sharesTotal.
struct RedeemCusp
{
    std::int64_t nav;
    std::int64_t sharesTotal;
    std::int64_t shares;
};

// Zero payout (XRP, MPT): 2 * nav * shares == shares total pays exactly half a unit, which rounds
// to even (0, tecPRECISION_LOSS); one share more pays one unit. Large rows sit at the share cap,
// and the nav at the XRP range.
constexpr RedeemCusp kZeroPayoutCusps[] = {
    {.nav = 1, .sharesTotal = 2, .shares = 1},
    {.nav = 1, .sharesTotal = 2 * kOrdinaryUnits, .shares = kOrdinaryUnits},
    {.nav = kOrdinaryUnits, .sharesTotal = 2 * kOrdinaryUnits, .shares = 1},
    {.nav = 31'250, .sharesTotal = 2 * kOrdinaryUnits, .shares = 32'000},
    {.nav = 1, .sharesTotal = kLargestEvenShares, .shares = kLargestEvenShares / 2},
    {.nav = kMaxNativeDrops, .sharesTotal = 2 * kMaxNativeDrops, .shares = 1},
    {
        .nav = kBalancedHalf - 1,
        .sharesTotal = 2 * (kBalancedHalf - 1) * kBalancedHalf,
        .shares = kBalancedHalf,
    },
};
static_assert(std::ranges::all_of(kZeroPayoutCusps, [](RedeemCusp const& c) {
    return 2 * __int128{c.nav} * c.shares == c.sharesTotal && c.sharesTotal + 2 <= kShareCap &&
        c.nav <= kMaxNativeDrops;
}));

// Clamp to zero (IOU): nav * shares == shares total pays exactly one grid step; below it the
// payout floors to zero (tecPRECISION_LOSS). Moved shares totals stay within 16 digits (IOU).
constexpr RedeemCusp kClampToZeroCusps[] = {
    {.nav = 2, .sharesTotal = 2, .shares = 1},
    {.nav = 2, .sharesTotal = 2 * kOrdinaryUnits, .shares = kOrdinaryUnits},
    {.nav = kOrdinaryUnits, .sharesTotal = 10 * kOrdinaryUnits, .shares = 10},
    {.nav = kOrdinaryUnits, .sharesTotal = 1'000'000 * kOrdinaryUnits, .shares = 1'000'000},
    {.nav = kLargestEvenIouUnits / 2, .sharesTotal = kLargestEvenIouUnits, .shares = 2},
    {.nav = 2, .sharesTotal = kLargestEvenIouUnits, .shares = kLargestEvenIouUnits / 2},
};
static_assert(std::ranges::all_of(kClampToZeroCusps, [](RedeemCusp const& c) {
    return __int128{c.nav} * c.shares == c.sharesTotal && c.sharesTotal + 2 <= kIouMaxMantissa;
}));

// Payout out of range (XRP): nav * shares == 10^17 * shares total pays exactly 10^17 drops, the
// largest XRP amount (here tecINSUFFICIENT_FUNDS). One drop more is out of the XRP range: C++
// throws a runtime_error the withdraw does not catch (tefEXCEPTION, a C++ robustness finding), the
// model an outOfRange error; both reject.
constexpr RedeemCusp kXrpPayoutRangeCusps[] = {
    {.nav = 1, .sharesTotal = 1, .shares = kMaxNativeDrops},
    {.nav = kOrdinaryUnits, .sharesTotal = kOrdinaryUnits, .shares = kMaxNativeDrops},
    {.nav = kOrdinaryUnits, .sharesTotal = 1, .shares = kMaxNativeDrops / kOrdinaryUnits},
};
static_assert(std::ranges::all_of(kXrpPayoutRangeCusps, [](RedeemCusp const& c) {
    return __int128{c.nav} * c.shares == __int128{kMaxNativeDrops} * c.sharesTotal;
}));

// Payout out of range (MPT): pays 2^63 - 2, one share more pays 2^63 (past the MPT maximum).
constexpr RedeemCusp kMptPayoutRangeCusps[] = {
    {.nav = 2, .sharesTotal = 1, .shares = kShareCap / 2},
};
static_assert(std::ranges::all_of(kMptPayoutRangeCusps, [](RedeemCusp const& c) {
    return __int128{c.nav} * c.shares == kShareCap - 1;
}));

// Payout out of range (IOU): a nav of the largest IOU amount (mantissa kIouMaxMantissa at exponent
// STAmount::kMaxOffset) redeemed by every share pays exactly that amount (a final withdrawal);
// one share more adds at least one mantissa unit and leaves the IOU range (tecPATH_DRY).
constexpr RedeemCusp kIouPayoutRangeCusps[] = {
    {.nav = kIouMaxMantissa, .sharesTotal = 1, .shares = 1},
    {.nav = kIouMaxMantissa, .sharesTotal = kOrdinaryUnits, .shares = kOrdinaryUnits},
    {.nav = kIouMaxMantissa, .sharesTotal = kIouMaxMantissa, .shares = kIouMaxMantissa},
};
static_assert(std::ranges::all_of(kIouPayoutRangeCusps, [](RedeemCusp const& c) {
    return c.nav == kIouMaxMantissa && c.shares == c.sharesTotal && c.nav / c.sharesTotal >= 1;
}));

// To-nearest switch (IOU): an odd nav redeemed by half the shares pays X + 1/2 units, X = (nav -
// 1) / 2, on both sides of X = 10^15, where the payout amount starts rounding to the grid itself.
// Both sides succeed; the post-state and payout are compared.
constexpr RedeemCusp kToNearestCusps[] = {
    {.nav = 2'000'000'000'000'000 - 1, .sharesTotal = 2, .shares = 1},
    {.nav = 2'000'000'000'000'000 + 1, .sharesTotal = 2, .shares = 1},
    {.nav = 2'000'000'000'000'000 + 3, .sharesTotal = 2, .shares = 1},
    {.nav = kIouMaxMantissa - 2, .sharesTotal = 2, .shares = 1},
};
static_assert(std::ranges::all_of(kToNearestCusps, [](RedeemCusp const& c) {
    return c.nav % 2 == 1 && c.sharesTotal == 2 * c.shares && c.nav + 2 <= kIouMaxMantissa;
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
// final withdrawal) is the last that fits (tecINSUFFICIENT_FUNDS above). Price 1; the holder owns
// all shares but one. The sweep moves the amount and the available assets. At least 5 deployed:
// the holder's shares then cover every moved amount, so only the available check decides. Moved
// totals stay within 16 digits (IOU).
constexpr AvailableCusp kAvailableCusps[] = {
    {.available = 1, .deployed = 5, .amount = 1},
    {.available = 1, .deployed = kIouMaxMantissa - 3, .amount = 1},
    {.available = kOrdinaryUnits, .deployed = 5, .amount = kOrdinaryUnits},
    {.available = kOrdinaryUnits, .deployed = kOrdinaryUnits, .amount = kOrdinaryUnits},
    {.available = kIouMaxMantissa - 7, .deployed = 5, .amount = kIouMaxMantissa - 7},
    {
        .available = 4'999'999'999'999'997,
        .deployed = 5'000'000'000'000'000,
        .amount = 4'999'999'999'999'997,
    },
};
static_assert(std::ranges::all_of(kAvailableCusps, [](AvailableCusp const& c) {
    std::int64_t const fewestHeld = (c.available - 2) + c.deployed - 1;
    return c.amount == c.available && fewestHeld >= c.amount + 2 &&
        c.available + 2 + c.deployed <= kIouMaxMantissa;
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
    return c.gross * (kMaxEarlyExitFeeRate.value() - c.rate) == kMaxEarlyExitFeeRate.value();
}));

// Net payout over available (Investment, 5% fee): gross * (1e5 - rate) == available * 1e5 nets
// exactly the available assets; one more is refused (tecINSUFFICIENT_FUNDS). Enough is deployed
// that the vault's assets cover every moved gross. The sweep moves the gross and the available.
// The large row is the largest multiple of 20 whose moved total stays within 16 digits (IOU).
struct NetOverAvailableCusp
{
    std::int64_t rate;
    std::int64_t gross;
    std::int64_t available;
    std::int64_t deployed;
};

constexpr NetOverAvailableCusp kNetOverAvailableCusps[] = {
    {.rate = 5'000, .gross = 20, .available = 19, .deployed = 5},
    {
        .rate = 5'000,
        .gross = 2 * kOrdinaryUnits,
        .available = 19 * kOrdinaryUnits / 10,
        .deployed = (kOrdinaryUnits / 10) + 4,
    },
    {
        .rate = 5'000,
        .gross = 9'999'999'999'999'980,
        .available = 9'499'999'999'999'981,
        .deployed = 500'000'000'000'003,
    },
};
static_assert(std::ranges::all_of(kNetOverAvailableCusps, [](NetOverAvailableCusp const& c) {
    return __int128{c.gross} * (kMaxEarlyExitFeeRate.value() - c.rate) ==
        __int128{c.available} * kMaxEarlyExitFeeRate.value() &&
        c.available + c.deployed >= c.gross + 4 && c.available + 2 + c.deployed <= kIouMaxMantissa;
}));

// Final withdrawal: redeeming every share with nothing deployed pays all available assets; with
// assets deployed it is refused (tecHAS_OBLIGATIONS). Price 1 (shares total = available +
// deployed). The sweep moves the deployed assets and the shares. Moved totals stay within 16
// digits (IOU).
struct FinalCusp
{
    std::int64_t available;
    std::int64_t deployed;
    std::int64_t shares;
};

constexpr FinalCusp kFinalCusps[] = {
    {.available = 2, .deployed = 0, .shares = 2},
    {.available = kOrdinaryUnits, .deployed = 0, .shares = kOrdinaryUnits},
    {.available = kIouMaxMantissa - 2, .deployed = 0, .shares = kIouMaxMantissa - 2},
};
static_assert(std::ranges::all_of(kFinalCusps, [](FinalCusp const& c) {
    return c.deployed == 0 && c.shares == c.available + c.deployed &&
        c.available + 2 <= kIouMaxMantissa;
}));

// Fully impaired vault: nothing available and the whole deployed total lost, so the net asset
// value is zero and a by-shares redemption burns the shares for nothing (tesSUCCESS); one unit of
// net asset value makes the payout non-zero and the request fails. The withdrawer is not the sole
// holder (a sole holder waives the loss). The sweep moves the loss and the shares. Large rows: the
// largest 16-digit deployed total (IOU), and the share cap.
struct ImpairedCusp
{
    std::int64_t deployed;
    std::int64_t loss;
    std::int64_t sharesTotal;
    std::int64_t shares;
};

constexpr ImpairedCusp kImpairedCusps[] = {
    {.deployed = 2, .loss = 2, .sharesTotal = kOrdinaryUnits, .shares = 1},
    {
        .deployed = kOrdinaryUnits,
        .loss = kOrdinaryUnits,
        .sharesTotal = kOrdinaryUnits,
        .shares = 1,
    },
    {
        .deployed = kIouMaxMantissa,
        .loss = kIouMaxMantissa,
        .sharesTotal = kOrdinaryUnits,
        .shares = 1,
    },
    {.deployed = kOrdinaryUnits, .loss = kOrdinaryUnits, .sharesTotal = kShareCap, .shares = 1},
    {.deployed = kOrdinaryUnits, .loss = kOrdinaryUnits, .sharesTotal = 2, .shares = 1},
};
static_assert(std::ranges::all_of(kImpairedCusps, [](ImpairedCusp const& c) {
    return c.loss == c.deployed && c.shares == 1 && c.deployed <= kIouMaxMantissa;
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
    {
        .available = kOrdinaryUnits,
        .deployed = 1,
        .sharesTotal = 10 * (kOrdinaryUnits + 1),
        .shares = 10 * kOrdinaryUnits,
    },
    {
        .available = 999'999'999'999'999,
        .deployed = 1,
        .sharesTotal = 10 * 1'000'000'000'000'000,
        .shares = 10 * 999'999'999'999'999,
    },
};
static_assert(std::ranges::all_of(kSubGridOverAvailableCusps, [](SubGridCusp const& c) {
    return __int128{c.available + c.deployed} * c.shares == __int128{c.available} * c.sharesTotal &&
        c.available < 1'000'000'000'000'000;
}));

// Holder's shares: redeeming exactly the shares held is the last that fits
// (tecINSUFFICIENT_FUNDS above); one share is held by someone else. Price 1. The sweep moves the
// shares held and redeemed. The available assets (holder + 1, moved) stay within 16 digits (IOU).
struct HolderCusp
{
    std::int64_t holderShares;
    std::int64_t shares;
};

constexpr HolderCusp kHolderSharesCusps[] = {
    {.holderShares = 1, .shares = 1},
    {.holderShares = kOrdinaryUnits, .shares = kOrdinaryUnits},
    {.holderShares = kIouMaxMantissa - 3, .shares = kIouMaxMantissa - 3},
};
static_assert(std::ranges::all_of(kHolderSharesCusps, [](HolderCusp const& c) {
    return c.shares == c.holderShares && c.holderShares + 3 <= kIouMaxMantissa;
}));

// Sole-holder loss waiver: a holder of every share is priced at the assets total, any other at
// assets total - loss unrealized. Both sides succeed; the post-state and payout are compared.
// Redeeming `shares` (price 1) pays `shares` waived and shares * (total - loss) / total not, at
// least a whole unit less, so integral assets see the waiver too. The sweep moves the holder's
// shares and the loss. The large total stays within 16 digits (IOU).
struct WaiverCusp
{
    std::int64_t total;
    std::int64_t deployed;
    std::int64_t loss;
    std::int64_t holderShares;
    std::int64_t shares;
};

constexpr WaiverCusp kWaiverCusps[] = {
    {.total = 8, .deployed = 4, .loss = 2, .holderShares = 8, .shares = 4},
    {
        .total = kOrdinaryUnits,
        .deployed = kOrdinaryUnits / 2,
        .loss = kOrdinaryUnits / 4,
        .holderShares = kOrdinaryUnits,
        .shares = 1'000,
    },
    {
        .total = kLargestEvenIouUnits,
        .deployed = kLargestEvenIouUnits / 2,
        .loss = kLargestEvenIouUnits / 4,
        .holderShares = kLargestEvenIouUnits,
        .shares = 1'000,
    },
};
static_assert(std::ranges::all_of(kWaiverCusps, [](WaiverCusp const& c) {
    return c.holderShares == c.total && c.loss + 2 <= c.deployed &&
        c.shares <= c.total - c.deployed && c.shares <= c.total - 2 &&
        __int128{c.shares} * c.loss >= c.total && c.total <= kIouMaxMantissa;
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
    {.nav = 1, .sharesTotal = kShareCap / 7, .amount = 7},
};
static_assert(std::ranges::all_of(kAssetsShareOverflowCusps, [](ShareOverflowCusp const& c) {
    return __int128{c.sharesTotal} * c.amount == __int128{kShareCap} * c.nav;
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
template <std::size_t N>
std::vector<AroundCusp<RedeemCusp>>
payoutRangeCases(RedeemCusp const (&rows)[N])
{
    return aroundCusp(rows, &RedeemCusp::sharesTotal, &RedeemCusp::shares, [](RedeemCusp const& c) {
        return c.sharesTotal >= 1 && c.shares >= 1;
    });
}

inline std::vector<AroundCusp<RedeemCusp>> const kXrpPayoutRangeCases =
    payoutRangeCases(kXrpPayoutRangeCusps);
inline std::vector<AroundCusp<RedeemCusp>> const kMptPayoutRangeCases =
    payoutRangeCases(kMptPayoutRangeCusps);
inline std::vector<AroundCusp<RedeemCusp>> const kIouPayoutRangeCases =
    payoutRangeCases(kIouPayoutRangeCusps);
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
        return c.gross >= 1 && c.rate <= kMaxEarlyExitFeeRate.value();
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
describe(HolderCusp const& c)
{
    return "holderShares " + std::to_string(c.holderShares) + ", shares " +
        std::to_string(c.shares);
}

inline std::string
describe(WaiverCusp const& c)
{
    return "total " + std::to_string(c.total) + ", deployed " + std::to_string(c.deployed) +
        ", loss " + std::to_string(c.loss) + ", holderShares " + std::to_string(c.holderShares) +
        ", shares " + std::to_string(c.shares);
}

inline std::string
describe(ShareOverflowCusp const& c)
{
    return "nav " + std::to_string(c.nav) + ", sharesTotal " + std::to_string(c.sharesTotal) +
        ", amount " + std::to_string(c.amount);
}

}  // namespace xrpl::test::formal_verification::withdraw_sweep
