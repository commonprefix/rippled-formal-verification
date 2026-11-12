#pragma once

#include <test/formal_verification/common/Sweep.h>
#include <test/formal_verification/tx/vault/DepositSweepCases.h>

#include <algorithm>
#include <cstdint>
#include <string>
#include <vector>

namespace xrpl::test::formal_verification::clawback_sweep {

// Hardcoded rows for the VaultClawback sweeps, in vault grid units (shares in shares). Each row
// sits exactly on its cusp; a sweep moves two of its values by kAroundCusp so every row crosses.
// The zero shares and clamp to zero sweeps reuse the deposit price rows (kZeroSharesCases,
// kClampToZeroCases): at price shares total / assets total the same rows recover exactly one
// share, or exactly one unit. The decade crossing sweep reuses kDecadeCases.

// Holder value: a holder of `holderShares` out of `sharesTotal` shares, at price 1, clawed back
// exactly what the shares are worth. A larger amount burns more shares than the holder owns. The
// holder never holds every share (a sole holder's request clamps to the available assets). The
// sweep moves the amount and the holder's shares. The available assets (the shares total) stay
// within 16 digits (IOU).
struct HolderValueCusp
{
    std::int64_t holderShares;
    std::int64_t sharesTotal;
    std::int64_t amount;
};

constexpr HolderValueCusp kHolderValueCusps[] = {
    {.holderShares = 1, .sharesTotal = 2, .amount = 1},
    {.holderShares = kOrdinaryUnits, .sharesTotal = kOrdinaryUnits + 1, .amount = kOrdinaryUnits},
    {.holderShares = kOrdinaryUnits, .sharesTotal = 2 * kOrdinaryUnits, .amount = kOrdinaryUnits},
    {
        .holderShares = kIouMaxMantissa - 1,
        .sharesTotal = kIouMaxMantissa,
        .amount = kIouMaxMantissa - 1,
    },
    {
        .holderShares = kIouMaxMantissa / 2,
        .sharesTotal = 2 * (kIouMaxMantissa / 2),
        .amount = kIouMaxMantissa / 2,
    },
};
static_assert(std::ranges::all_of(kHolderValueCusps, [](HolderValueCusp const& c) {
    return c.amount == c.holderShares && c.holderShares < c.sharesTotal &&
        c.sharesTotal <= kIouMaxMantissa;
}));

// Owner burn: the owner may burn a holder's shares of an insolvent vault (shares, no assets), and
// only all of them (amount equal to the holder's shares, or 0 for all). The first table moves the
// amount and the available assets, the second (a holder with no shares) the holder's shares and
// the available assets. The large row sits at the share cap: the model accepts 2^63 - 1 shares.
struct BurnCusp
{
    std::int64_t available;
    std::int64_t sharesTotal;
    std::int64_t holderShares;
    std::int64_t amount;
};

constexpr BurnCusp kBurnCusps[] = {
    {.available = 0, .sharesTotal = 1, .holderShares = 1, .amount = 1},
    {
        .available = 0,
        .sharesTotal = kOrdinaryUnits,
        .holderShares = kOrdinaryUnits,
        .amount = kOrdinaryUnits,
    },
    {
        .available = 0,
        .sharesTotal = kShareCap,
        .holderShares = kShareCap,
        .amount = kShareCap,
    },
    {.available = 0, .sharesTotal = kOrdinaryUnits, .holderShares = 1, .amount = 1},
};
static_assert(std::ranges::all_of(kBurnCusps, [](BurnCusp const& c) {
    return c.available == 0 && c.amount == c.holderShares && c.holderShares <= c.sharesTotal;
}));

constexpr BurnCusp kBurnNoSharesCusps[] = {
    {.available = 0, .sharesTotal = kOrdinaryUnits, .holderShares = 0, .amount = 0},
};
static_assert(std::ranges::all_of(kBurnNoSharesCusps, [](BurnCusp const& c) {
    return c.holderShares == 0 && c.amount == 0;
}));

// Clamp to available: a sole holder of a vault with assets deployed claws back exactly the
// available assets; any larger amount is reduced to them and the shares re-derived. Both sides
// succeed; the post-states are compared. The sweep moves the amount and the available assets.
// Moved totals stay within 16 digits (IOU).
constexpr AvailableCusp kAvailableCusps[] = {
    {.available = 3, .deployed = 1, .amount = 3},
    {.available = kOrdinaryUnits, .deployed = 1, .amount = kOrdinaryUnits},
    {.available = kOrdinaryUnits, .deployed = kOrdinaryUnits, .amount = kOrdinaryUnits},
    {.available = 3, .deployed = kOrdinaryUnits, .amount = 3},
    {.available = 3, .deployed = kIouMaxMantissa - 5, .amount = 3},
    {.available = kIouMaxMantissa - 3, .deployed = 1, .amount = kIouMaxMantissa - 3},
    {
        .available = 4'999'999'999'999'998,
        .deployed = 4'999'999'999'999'999,
        .amount = 4'999'999'999'999'998,
    },
};
static_assert(std::ranges::all_of(kAvailableCusps, [](AvailableCusp const& c) {
    return c.amount == c.available && c.available + 2 + c.deployed <= kIouMaxMantissa;
}));

// Sole-holder loss waiver: a holder of every share is priced at the assets total, any other at
// assets total - loss unrealized, so clawing back `amount` (price 1) burns `amount` shares waived
// and amount * total / (total - loss) not, at least one share more. Both sides succeed; the
// post-states are compared. The sweep moves the holder's shares and the loss. The large total
// stays within 16 digits (IOU).
struct WaiverCusp
{
    std::int64_t total;
    std::int64_t deployed;
    std::int64_t loss;
    std::int64_t holderShares;
    std::int64_t amount;
};

constexpr WaiverCusp kWaiverCusps[] = {
    {.total = 12, .deployed = 6, .loss = 4, .holderShares = 12, .amount = 4},
    {
        .total = kOrdinaryUnits,
        .deployed = kOrdinaryUnits / 2,
        .loss = kOrdinaryUnits / 4,
        .holderShares = kOrdinaryUnits,
        .amount = kOrdinaryUnits / 10,
    },
    {
        .total = kIouMaxMantissa - 3,
        .deployed = (kIouMaxMantissa - 3) / 2,
        .loss = (kIouMaxMantissa - 3) / 4,
        .holderShares = kIouMaxMantissa - 3,
        .amount = kOrdinaryUnits,
    },
};
static_assert(std::ranges::all_of(kWaiverCusps, [](WaiverCusp const& c) {
    // The most shares a moved case burns: the largest loss, unwaived.
    __int128 const mostBurned = __int128{c.amount} * c.total / (c.total - c.loss - 2);
    return c.holderShares == c.total && c.loss + 2 <= c.deployed &&
        c.amount <= c.total - c.deployed && mostBurned <= c.total - 2 &&
        __int128{c.amount} * c.loss >= c.total - c.loss && c.total <= kIouMaxMantissa;
}));

// Coarse claw-all (IOU): available assets of mantissa `mantissa` at `exponent` grid steps above
// the vault grid, so one mantissa ULP is 10^exponent units, and `deployed` exactly half of it. A
// sole holder's claw-all converts available + deployed to 16 digits: the half-ULP tie rounds to
// the even mantissa, so on an even mantissa every share would be burned with assets still
// deployed (tecHAS_OBLIGATIONS), on an odd one the amount clamps and the claw-all succeeds. The
// sweep moves the mantissa (flipping its parity) and the deployed assets.
struct CoarseClawAllCusp
{
    std::int64_t mantissa;
    int exponent;
    std::int64_t deployed;
};

constexpr CoarseClawAllCusp kCoarseClawAllCusps[] = {
    {.mantissa = 2'000'000'000'000'000, .exponent = 1, .deployed = 5},
    {.mantissa = 2'000'000'000'000'001, .exponent = 1, .deployed = 5},
    {.mantissa = 9'999'999'999'999'998, .exponent = 1, .deployed = 5},
    {.mantissa = 2'000'000'000'000'000, .exponent = 2, .deployed = 50},
};
static_assert(std::ranges::all_of(kCoarseClawAllCusps, [](CoarseClawAllCusp const& c) {
    std::int64_t ulp = 1;
    for (int i = 0; i < c.exponent; ++i)
        ulp *= 10;
    return c.mantissa >= 1'000'000'000'000'000 && c.mantissa < 10'000'000'000'000'000 &&
        2 * c.deployed == ulp;
}));

// Shares a sole holder's clawback of the coarse claw-all rows owns.
constexpr std::int64_t kCoarseShares = kOrdinaryUnits;

// Share overflow: shares total * amount / assets total is the largest share count that still fits
// 2^63 - 1; one more share overflows the conversion (tecPATH_DRY). The sweep moves the shares
// total and the amount.
constexpr PriceCusp kShareOverflowCusps[] = {
    {.total = 1, .sharesTotal = 1'317'624'576'693'539'401, .amount = 7},
    {.total = 1, .sharesTotal = 3'074'457'345'618'258'602, .amount = 3},
};
static_assert(std::ranges::all_of(kShareOverflowCusps, [](PriceCusp const& c) {
    constexpr __int128 kMax = std::numeric_limits<std::int64_t>::max();
    return sharesBought(c) <= kMax &&
        sharesBought({.total = c.total, .sharesTotal = c.sharesTotal + 1, .amount = c.amount}) >
        kMax &&
        c.sharesTotal + 2 <= kShareCap;
}));

// Every case the sweeps run. An amount below 1 is the claw-all request, not a cusp case, and is
// dropped (except in the burn tables, where 0 is in the domain); so is a holder that owns every
// share, or more than exist.

inline std::vector<AroundCusp<HolderValueCusp>> const kHolderValueCases = aroundCusp(
    kHolderValueCusps,
    &HolderValueCusp::amount,
    &HolderValueCusp::holderShares,
    [](HolderValueCusp const& c) {
        return c.amount >= 1 && c.holderShares >= 1 && c.holderShares < c.sharesTotal;
    });

inline std::vector<AroundCusp<BurnCusp>> const kBurnCases =
    aroundCusp(kBurnCusps, &BurnCusp::amount, &BurnCusp::available, [](BurnCusp const& c) {
        return c.amount >= 0 && c.available >= 0;
    });

inline std::vector<AroundCusp<BurnCusp>> const kBurnNoSharesCases = aroundCusp(
    kBurnNoSharesCusps,
    &BurnCusp::holderShares,
    &BurnCusp::available,
    [](BurnCusp const& c) { return c.holderShares >= 0 && c.available >= 0; });

inline std::vector<AroundCusp<AvailableCusp>> const kAvailableCases = aroundCusp(
    kAvailableCusps,
    &AvailableCusp::amount,
    &AvailableCusp::available,
    [](AvailableCusp const& c) { return c.amount >= 1 && c.available >= 1; });

inline std::vector<AroundCusp<CoarseClawAllCusp>> const kCoarseClawAllCases = aroundCusp(
    kCoarseClawAllCusps,
    &CoarseClawAllCusp::mantissa,
    &CoarseClawAllCusp::deployed,
    [](CoarseClawAllCusp const& c) { return c.deployed >= 1; });

inline std::vector<AroundCusp<PriceCusp>> const kShareOverflowCases =
    priceCases(kShareOverflowCusps);

inline std::vector<AroundCusp<WaiverCusp>> const kWaiverCases =
    aroundCusp(kWaiverCusps, &WaiverCusp::holderShares, &WaiverCusp::loss, [](WaiverCusp const& c) {
        return c.holderShares <= c.total && c.loss >= 0;
    });

// A row as it appears in failure messages.
inline std::string
describe(HolderValueCusp const& c)
{
    return "holder shares " + std::to_string(c.holderShares) + ", sharesTotal " +
        std::to_string(c.sharesTotal) + ", amount " + std::to_string(c.amount);
}

inline std::string
describe(BurnCusp const& c)
{
    return "available " + std::to_string(c.available) + ", sharesTotal " +
        std::to_string(c.sharesTotal) + ", holder shares " + std::to_string(c.holderShares) +
        ", amount " + std::to_string(c.amount);
}

inline std::string
describe(WaiverCusp const& c)
{
    return "total " + std::to_string(c.total) + ", deployed " + std::to_string(c.deployed) +
        ", loss " + std::to_string(c.loss) + ", holderShares " + std::to_string(c.holderShares) +
        ", amount " + std::to_string(c.amount);
}

inline std::string
describe(CoarseClawAllCusp const& c)
{
    return "available mantissa " + std::to_string(c.mantissa) + " at +" +
        std::to_string(c.exponent) + ", deployed " + std::to_string(c.deployed);
}

}  // namespace xrpl::test::formal_verification::clawback_sweep
