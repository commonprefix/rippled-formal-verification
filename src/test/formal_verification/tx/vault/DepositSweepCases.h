#pragma once

#include <test/formal_verification/common/Sweep.h>
#include <test/formal_verification/tx/vault/VaultTestHelpers.h>

#include <algorithm>
#include <cstddef>
#include <cstdint>
#include <limits>
#include <string>
#include <vector>

namespace xrpl::test::formal_verification {

// Hardcoded rows for the VaultDeposit sweeps, in vault grid units. Each row sits exactly on its
// cusp; a sweep moves two of its values by kAroundCusp so every row crosses. The levels are the
// smallest value, an ordinary one and the largest that still reaches the cusp, and each level is
// split as (smallest, largest), (largest, smallest) and (balanced). A table has no large level when
// only the open limit bounds it. The static_asserts check that every row is on its cusp.

// The ordinary level shared by the tables.
constexpr std::int64_t kOrdinaryUnits = 1'000'000'000;
// Large level of the withdraw, clawback and create tables.
constexpr std::int64_t kLargeUnits = 4'000'000'000'000'000;

// Open limit: yield unrealized + assets total + amount == kOpenLimitUnits, the last deposit that
// fits. The sweep moves the total and the amount.
struct OpenLimitCusp
{
    std::int64_t yield;
    std::int64_t total;
    std::int64_t amount;
};

constexpr OpenLimitCusp kOpenLimitCusps[] = {
    {.yield = 0, .total = 1, .amount = kOpenLimitUnits - 1},
    {.yield = 0, .total = kOpenLimitUnits - 1, .amount = 1},
    {.yield = 0, .total = kOpenLimitUnits / 2, .amount = kOpenLimitUnits / 2},
    {.yield = kOrdinaryUnits, .total = 1, .amount = kOpenLimitUnits - kOrdinaryUnits - 1},
    {.yield = kOrdinaryUnits, .total = kOpenLimitUnits - kOrdinaryUnits - 1, .amount = 1},
    {.yield = kOpenLimitUnits - 2, .total = 1, .amount = 1},
};
static_assert(std::ranges::all_of(kOpenLimitCusps, [](OpenLimitCusp const& c) {
    return c.yield + c.total + c.amount == kOpenLimitUnits;
}));

// Assets maximum: assets total + amount == maximum, the last deposit that fits. No row near the
// open limit: there the open limit rejects too, with the same verdict. The sweep moves the total
// and the amount.
struct AssetsMaximumCusp
{
    std::int64_t maximum;
    std::int64_t total;
    std::int64_t amount;
};

constexpr AssetsMaximumCusp kAssetsMaximumCusps[] = {
    {.maximum = 2, .total = 1, .amount = 1},
    {.maximum = kOrdinaryUnits, .total = 1, .amount = kOrdinaryUnits - 1},
    {.maximum = kOrdinaryUnits, .total = kOrdinaryUnits - 1, .amount = 1},
    {.maximum = kOrdinaryUnits, .total = kOrdinaryUnits / 2, .amount = kOrdinaryUnits / 2},
};
static_assert(std::ranges::all_of(kAssetsMaximumCusps, [](AssetsMaximumCusp const& c) {
    return c.total + c.amount == c.maximum;
}));

// A deposit into a vault whose share price is not 1: shared by the zero shares, clamp to zero,
// charge rounding and share mint cap tables. Those sweeps move the shares total and the amount.
struct PriceCusp
{
    std::int64_t total;
    std::int64_t sharesTotal;
    std::int64_t amount;
};

// The shares a deposit buys, trunc(shares total * amount / assets total).
constexpr __int128
sharesBought(PriceCusp const& c)
{
    return __int128{c.sharesTotal} * c.amount / c.total;
}

// Zero shares: shares total * amount == assets total buys exactly one share; one unit less of
// either buys none.
constexpr PriceCusp kZeroSharesCusps[] = {
    {.total = 2, .sharesTotal = 1, .amount = 2},
    {.total = 2, .sharesTotal = 2, .amount = 1},
    {.total = kOrdinaryUnits, .sharesTotal = 1, .amount = kOrdinaryUnits},
    {.total = kOrdinaryUnits, .sharesTotal = kOrdinaryUnits, .amount = 1},
    {.total = kOrdinaryUnits, .sharesTotal = 31'250, .amount = 32'000},
};
static_assert(std::ranges::all_of(kZeroSharesCusps, [](PriceCusp const& c) {
    return __int128{c.sharesTotal} * c.amount == c.total;
}));

// Clamp to zero: a one-unit deposit into shares total == k * assets total buys k shares whose
// charge is exactly one unit; one share more or less floors the charge to zero. The large shares
// totals are the largest whose moves stay below 10^16: IOU arithmetic carries 16 digits, so past
// it the one-share difference is lost.
constexpr PriceCusp kClampToZeroCusps[] = {
    {.total = 2, .sharesTotal = 2, .amount = 1},
    {.total = 2, .sharesTotal = 2'000, .amount = 1},
    {.total = 2, .sharesTotal = 9'999'999'999'999'996, .amount = 1},
    {.total = kOrdinaryUnits, .sharesTotal = kOrdinaryUnits, .amount = 1},
    {.total = kOrdinaryUnits, .sharesTotal = 1'000 * kOrdinaryUnits, .amount = 1},
    {.total = kOrdinaryUnits, .sharesTotal = 9'999'999'000'000'000, .amount = 1},
};
static_assert(std::ranges::all_of(kClampToZeroCusps, [](PriceCusp const& c) {
    return c.amount == 1 && c.sharesTotal % c.total == 0 &&
        c.sharesTotal + 2 < 10'000'000'000'000'000;
}));

// Every moved row of a price table mints under the 2^63 cap, so only the share mint cap sweep
// reaches it.
constexpr bool
underMintCap(PriceCusp const& c)
{
    PriceCusp const top{.total = c.total, .sharesTotal = c.sharesTotal + 2, .amount = c.amount + 2};
    return top.sharesTotal + sharesBought(top) <= std::numeric_limits<std::int64_t>::max();
}

// Charge rounding: an odd assets total T, shares total 2N (N < T) and amount (T + 1) / 2 buy N
// shares charged exactly T / 2, a half-unit tie. Both sides succeed at the row itself.
constexpr PriceCusp kChargeRoundingCusps[] = {
    {.total = 3, .sharesTotal = 2, .amount = 2},
    {.total = 3, .sharesTotal = 4, .amount = 2},
    {.total = kOrdinaryUnits + 1, .sharesTotal = 2, .amount = kOrdinaryUnits / 2 + 1},
    {.total = kOrdinaryUnits + 1,
     .sharesTotal = 2 * kOrdinaryUnits,
     .amount = kOrdinaryUnits / 2 + 1},
    {.total = kOrdinaryUnits + 1, .sharesTotal = kOrdinaryUnits, .amount = kOrdinaryUnits / 2 + 1},
};
static_assert(std::ranges::all_of(kChargeRoundingCusps, [](PriceCusp const& c) {
    return 2 * (__int128{c.total} * sharesBought(c) % c.sharesTotal) == c.sharesTotal;
}));

static_assert(std::ranges::all_of(kZeroSharesCusps, underMintCap));
static_assert(std::ranges::all_of(kClampToZeroCusps, underMintCap));
static_assert(std::ranges::all_of(kChargeRoundingCusps, underMintCap));

// Share mint cap: shares total + shares bought == 2^63 - 1, the last mint that fits.
constexpr PriceCusp kShareMintCapCusps[] = {
    {.total = 8'000'000'000'000'000,
     .sharesTotal = std::numeric_limits<std::int64_t>::max() - 1'152,
     .amount = 1},
};
static_assert(std::ranges::all_of(kShareMintCapCusps, [](PriceCusp const& c) {
    return c.sharesTotal + sharesBought(c) == std::numeric_limits<std::int64_t>::max();
}));

// Sub-grid amount: mantissa 10^15 at exponent -(scale + 15) is exactly one grid step, the
// smallest amount that does not round to zero. The sweep moves the mantissa.
constexpr std::int64_t kOneGridStepMantissa = 1'000'000'000'000'000;

// Share overflow: on a first IOU deposit this mantissa at exponent 3 - scale mints
// 9'223'372'036'854'775'000 shares, the last 16-digit amount below 2^63. The sweep moves it.
constexpr std::int64_t kShareOverflowMantissa = 9'223'372'036'854'775;
static_assert(
    __int128{kShareOverflowMantissa} * 1'000 <= std::numeric_limits<std::int64_t>::max() &&
    __int128{kShareOverflowMantissa + 1} * 1'000 > std::numeric_limits<std::int64_t>::max());

// Every case the sweeps run: each row above with its two moved values offset by kAroundCusp,
// grouped by row. A moved value below 1 is not a deposit (or an empty vault) and is dropped.

inline std::vector<AroundCusp<OpenLimitCusp>> const kOpenLimitCases = aroundCusp(
    kOpenLimitCusps,
    &OpenLimitCusp::total,
    &OpenLimitCusp::amount,
    [](OpenLimitCusp const& c) { return c.total >= 1 && c.amount >= 1; });

// Also dropped: a vault that already holds more than its maximum.
inline std::vector<AroundCusp<AssetsMaximumCusp>> const kAssetsMaximumCases = aroundCusp(
    kAssetsMaximumCusps,
    &AssetsMaximumCusp::total,
    &AssetsMaximumCusp::amount,
    [](AssetsMaximumCusp const& c) {
        return c.total >= 1 && c.amount >= 1 && c.total <= c.maximum;
    });

// Price rows move the shares total and the amount.
template <std::size_t N>
std::vector<AroundCusp<PriceCusp>>
priceCases(PriceCusp const (&rows)[N])
{
    return aroundCusp(rows, &PriceCusp::sharesTotal, &PriceCusp::amount, [](PriceCusp const& c) {
        return c.sharesTotal >= 1 && c.amount >= 1;
    });
}

inline std::vector<AroundCusp<PriceCusp>> const kZeroSharesCases = priceCases(kZeroSharesCusps);
inline std::vector<AroundCusp<PriceCusp>> const kClampToZeroCases = priceCases(kClampToZeroCusps);
inline std::vector<AroundCusp<PriceCusp>> const kChargeRoundingCases =
    priceCases(kChargeRoundingCusps);
inline std::vector<AroundCusp<PriceCusp>> const kShareMintCapCases = priceCases(kShareMintCapCusps);
inline std::vector<AroundCusp<std::int64_t>> const kOneGridStepCases =
    aroundCusp(kOneGridStepMantissa);
inline std::vector<AroundCusp<std::int64_t>> const kShareOverflowCases =
    aroundCusp(kShareOverflowMantissa);

// A row as it appears in failure messages.
inline std::string
describe(OpenLimitCusp const& c)
{
    return "yield " + std::to_string(c.yield) + ", total " + std::to_string(c.total) + ", amount " +
        std::to_string(c.amount);
}

inline std::string
describe(AssetsMaximumCusp const& c)
{
    return "maximum " + std::to_string(c.maximum) + ", total " + std::to_string(c.total) +
        ", amount " + std::to_string(c.amount);
}

inline std::string
describe(PriceCusp const& c)
{
    return "total " + std::to_string(c.total) + ", sharesTotal " + std::to_string(c.sharesTotal) +
        ", amount " + std::to_string(c.amount);
}

}  // namespace xrpl::test::formal_verification
