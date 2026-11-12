#pragma once

#include <test/formal_verification/common/Sweep.h>
#include <test/formal_verification/tx/vault/VaultTestHelpers.h>

#include <xrpl/protocol/Protocol.h>
#include <xrpl/protocol/STAmount.h>
#include <xrpl/protocol/TER.h>

#include <algorithm>
#include <cstddef>
#include <cstdint>
#include <limits>
#include <string>
#include <vector>

namespace xrpl::test::formal_verification {

// Hardcoded rows shared by the vault sweeps, in vault grid units. Each row sits exactly on its
// cusp; a sweep moves two of its values by kAroundCusp so every row crosses. The levels are the
// smallest value, an ordinary one and the largest that still reaches the cusp, and each level is
// split as (smallest, largest), (largest, smallest) and (balanced). A table has no large level when
// only the open limit bounds it. The static_asserts check that every row is on its cusp.

// The ordinary level shared by the tables.
constexpr std::int64_t kOrdinaryUnits = 1'000'000'000;

// Bounds the large levels sit at: the largest 16-digit IOU mantissa (a one-unit difference past it
// is lost), the XRP range in drops, and the 2^63 - 1 share (and MPT) cap.
constexpr auto kIouMaxMantissa = static_cast<std::int64_t>(STAmount::kMaxValue);
constexpr auto kMaxNativeDrops = static_cast<std::int64_t>(STAmount::kMaxNativeN);
constexpr std::int64_t kShareCap = std::numeric_limits<std::int64_t>::max();
static_assert(kShareCap == static_cast<std::int64_t>(kMaxMpTokenAmount));

// A deposit into a vault whose share price is not 1: shared by the zero shares and clamp to zero
// tables. Those sweeps move the shares total and the amount.
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

// Available assets at price 1 (withdraw, clawback): an amount of exactly the available assets with
// `deployed` assets still in the vault. Each table says what lies past it.
struct AvailableCusp
{
    std::int64_t available;
    std::int64_t deployed;
    std::int64_t amount;
};

// Decade-crossing outflow (IOU, withdraw and clawback): the outflow is truncated to the grid of
// available - amount, which is 10 units from 10^16 units up. Available assets are
// availableMantissa * 10 units (one mantissa step); each row leaves exactly 10^16 - 1 or 10^16, at
// price 1 and with the account holding all shares but one. The sweep moves both values.
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
    std::int64_t const left = (c.availableMantissa * 10) - c.amount;
    return left == kSeventeenDigits - 1 || left == kSeventeenDigits;
}));

// Every case the sweeps run: each row above with its two moved values offset by kAroundCusp,
// grouped by row. A moved value below 1 is not a deposit (or an empty vault) and is dropped.

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
inline std::vector<AroundCusp<DecadeCusp>> const kDecadeCases = aroundCusp(
    kDecadeCusps,
    &DecadeCusp::availableMantissa,
    &DecadeCusp::amount,
    [](DecadeCusp const& c) { return c.amount >= 1; });

// A row as it appears in failure messages.
inline std::string
describe(PriceCusp const& c)
{
    return "total " + std::to_string(c.total) + ", sharesTotal " + std::to_string(c.sharesTotal) +
        ", amount " + std::to_string(c.amount);
}

inline std::string
describe(AvailableCusp const& c)
{
    return "available " + std::to_string(c.available) + ", deployed " + std::to_string(c.deployed) +
        ", amount " + std::to_string(c.amount);
}

inline std::string
describe(DecadeCusp const& c)
{
    return "availableMantissa " + std::to_string(c.availableMantissa) + ", amount " +
        std::to_string(c.amount);
}

}  // namespace xrpl::test::formal_verification
