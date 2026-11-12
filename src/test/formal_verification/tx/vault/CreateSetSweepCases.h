#pragma once

#include <test/formal_verification/common/Sweep.h>
#include <test/formal_verification/tx/vault/DepositSweepCases.h>
#include <test/formal_verification/tx/vault/VaultTestHelpers.h>

#include <xrpl/protocol/Asset.h>
#include <xrpl/protocol/Protocol.h>
#include <xrpl/protocol/STAmount.h>

#include <algorithm>
#include <cstddef>
#include <cstdint>
#include <string>
#include <vector>

namespace xrpl::test::formal_verification {

namespace create_set_sweep {

constexpr bool
hasAtMost16Digits(std::int64_t mantissa)
{
    while (mantissa % 10 == 0 && mantissa != 0)
        mantissa /= 10;
    return mantissa <= static_cast<std::int64_t>(STAmount::kMaxValue);
}

}  // namespace create_set_sweep

// VaultCreate schedule: subscription date at P + subscription, redemption date `gap` later.
struct ScheduleCusp
{
    std::int64_t subscription;
    std::int64_t gap;
};

// A subscription date equal to the parent close time P is already expired (P + 1 is the first
// accepted date); the smallest and largest lawful gaps also sit on the investment period bounds.
constexpr ScheduleCusp kScheduleCusps[] = {
    {.subscription = 0, .gap = kMinInvestmentPeriod},
    {.subscription = 0, .gap = 1'000'000},
    {.subscription = 0, .gap = std::int64_t{kMaxInvestmentPeriod} - 1},
};
static_assert(std::ranges::all_of(kScheduleCusps, [](ScheduleCusp const& c) {
    return c.subscription == 0 && c.gap >= kMinInvestmentPeriod && c.gap < kMaxInvestmentPeriod;
}));

// An AssetsMaximum of mantissa * 10^exponent grid steps (10^-scale).
struct MaximumGridCusp
{
    std::int64_t mantissa;
    std::int64_t exponent;
};

// The maximum must lie on the vault grid with at most 16 digits. One grid step and an ordinary
// value go off the grid at any move; the largest 16-digit value only at +2 (17 digits); a
// 16-digit value above 1e16 steps at any move. The last row is the largest exponent whose +2
// move still normalizes inside the IOU exponent range at every scale.
constexpr MaximumGridCusp kMaximumGridCusps[] = {
    {.mantissa = 1'000'000'000'000'000, .exponent = -15},
    {.mantissa = 1'000'000'000'000'000, .exponent = -6},
    {.mantissa = 9'999'999'999'999'999, .exponent = 0},
    {.mantissa = 10'000'000'000'000'010, .exponent = 0},
    {.mantissa = 9'999'999'999'999'999, .exponent = STAmount::kMaxOffset - 1},
};
static_assert(std::ranges::all_of(kMaximumGridCusps, [](MaximumGridCusp const& c) {
    std::int64_t m = c.mantissa;
    for (std::int64_t e = c.exponent; e < 0; ++e)
    {
        if (m % 10 != 0)
            return false;
        m /= 10;
    }
    return create_set_sweep::hasAtMost16Digits(c.mantissa) && c.exponent < STAmount::kMaxOffset;
}));

// An AssetsMaximum of mantissa * 10^exponent asset units, at the edge of what the asset can
// represent: one unit above is refused.
struct MaximumRangeCusp
{
    std::int64_t mantissa;
    std::int64_t exponent;
};

constexpr MaximumRangeCusp kXrpMaximumRangeCusps[] = {
    {.mantissa = static_cast<std::int64_t>(STAmount::kMaxNativeN), .exponent = 0},
};
// The last multiple of 10 below 2^63: the mantissa cannot pass int64 at exponent 0.
constexpr MaximumRangeCusp kMptMaximumRangeCusps[] = {
    {.mantissa = static_cast<std::int64_t>(kMaxMpTokenAmount / 10), .exponent = 1},
};
constexpr MaximumRangeCusp kIouMaximumRangeCusps[] = {
    {.mantissa = static_cast<std::int64_t>(STAmount::kMaxValue), .exponent = STAmount::kMaxOffset},
};
static_assert(std::ranges::all_of(kXrpMaximumRangeCusps, [](MaximumRangeCusp const& c) {
    return c.exponent == 0 && c.mantissa == STAmount::kMaxNativeN;
}));
static_assert(std::ranges::all_of(kMptMaximumRangeCusps, [](MaximumRangeCusp const& c) {
    return c.exponent == 1 && __int128{c.mantissa} * 10 <= kMaxMpTokenAmount &&
        __int128{c.mantissa + 1} * 10 > kMaxMpTokenAmount;
}));
static_assert(std::ranges::all_of(kIouMaximumRangeCusps, [](MaximumRangeCusp const& c) {
    return c.exponent == STAmount::kMaxOffset && c.mantissa == STAmount::kMaxValue;
}));

// VaultSet: a maximum equal to the assets total (available + deployed) is the smallest accepted
// one; a maximum of 0 removes the cap.
struct SetMaximumCusp
{
    std::int64_t available;
    std::int64_t deployed;
    std::int64_t maximum;
};

constexpr SetMaximumCusp kSetMaximumCusps[] = {
    {.available = 2, .deployed = 0, .maximum = 2},
    {.available = 1, .deployed = 1, .maximum = 2},
    {.available = kOrdinaryUnits, .deployed = 0, .maximum = kOrdinaryUnits},
    {.available = 1, .deployed = kOrdinaryUnits - 1, .maximum = kOrdinaryUnits},
    {.available = kOrdinaryUnits - 1, .deployed = 1, .maximum = kOrdinaryUnits},
    {.available = kOrdinaryUnits / 2, .deployed = kOrdinaryUnits / 2, .maximum = kOrdinaryUnits},
};

// The largest assets total in grid units, per asset kind: the XRP drops range, the MPT amount cap
// and 16 IOU digits. The maximum and the staged amounts cannot pass it.
constexpr std::int64_t kXrpLargestTotal = static_cast<std::int64_t>(STAmount::kMaxNativeN);
constexpr std::int64_t kMptLargestTotal = static_cast<std::int64_t>(kMaxMpTokenAmount);
constexpr std::int64_t kIouLargestTotal = static_cast<std::int64_t>(STAmount::kMaxValue);

template <std::int64_t Largest>
constexpr SetMaximumCusp kSetMaximumLargeCusps[] = {
    {.available = Largest, .deployed = 0, .maximum = Largest},
    {.available = 1, .deployed = Largest - 1, .maximum = Largest},
    {.available = Largest - 1, .deployed = 1, .maximum = Largest},
    {.available = Largest / 2, .deployed = Largest - (Largest / 2), .maximum = Largest},
};

constexpr bool
onSetMaximumCusp(SetMaximumCusp const& c)
{
    return c.maximum == c.available + c.deployed;
}
static_assert(std::ranges::all_of(kSetMaximumCusps, onSetMaximumCusp));
static_assert(std::ranges::all_of(kSetMaximumLargeCusps<kXrpLargestTotal>, onSetMaximumCusp));
static_assert(std::ranges::all_of(kSetMaximumLargeCusps<kMptLargestTotal>, onSetMaximumCusp));
static_assert(std::ranges::all_of(kSetMaximumLargeCusps<kIouLargestTotal>, onSetMaximumCusp));

// VaultDelete: an empty vault with no shares is the only deletable state.
struct DeleteCusp
{
    std::int64_t available;
    std::int64_t sharesTotal;
};

constexpr DeleteCusp kDeleteCusps[] = {{.available = 0, .sharesTotal = 0}};

inline std::vector<AroundCusp<ScheduleCusp>> const kScheduleCases = aroundCusp(
    kScheduleCusps,
    &ScheduleCusp::subscription,
    &ScheduleCusp::gap,
    [](ScheduleCusp const&) { return true; });
inline std::vector<AroundCusp<std::int64_t>> const kEarlyExitFeeCases =
    aroundCusp(std::int64_t{kMaxEarlyExitFeeRate.value()});
inline std::vector<AroundCusp<std::int64_t>> const kScaleCases =
    aroundCusp(kFixedPrecisionVaultMaximumIouScale);
// A negative maximum is malformed; 0 is no cap.
inline std::vector<AroundCusp<std::int64_t>> const kMaximumSignCases = aroundCusp(0);
inline std::vector<AroundCusp<MaximumGridCusp>> const kMaximumGridCases =
    aroundCusp(kMaximumGridCusps, &MaximumGridCusp::mantissa, [](MaximumGridCusp const&) {
        return true;
    });

template <std::size_t N>
std::vector<AroundCusp<MaximumRangeCusp>>
maximumRangeCases(MaximumRangeCusp const (&rows)[N])
{
    return aroundCusp(
        rows, &MaximumRangeCusp::mantissa, [](MaximumRangeCusp const&) { return true; });
}

inline std::vector<AroundCusp<MaximumRangeCusp>> const kXrpMaximumRangeCases =
    maximumRangeCases(kXrpMaximumRangeCusps);
inline std::vector<AroundCusp<MaximumRangeCusp>> const kMptMaximumRangeCases =
    maximumRangeCases(kMptMaximumRangeCusps);
inline std::vector<AroundCusp<MaximumRangeCusp>> const kIouMaximumRangeCases =
    maximumRangeCases(kIouMaximumRangeCusps);

// The range rows of the asset's kind.
inline std::vector<AroundCusp<MaximumRangeCusp>> const&
maximumRangeCases(Asset const& asset)
{
    if (asset.native())
        return kXrpMaximumRangeCases;
    return asset.holds<MPTIssue>() ? kMptMaximumRangeCases : kIouMaximumRangeCases;
}

inline std::vector<AroundCusp<SetMaximumCusp>> const kSetMaximumCases = aroundCusp(
    kSetMaximumCusps,
    &SetMaximumCusp::maximum,
    &SetMaximumCusp::available,
    [](SetMaximumCusp const& c) { return c.available >= 0 && c.maximum >= 0; });

// Also dropped: a total or maximum past the largest; that edge is the range sweep's.
template <std::int64_t Largest>
inline std::vector<AroundCusp<SetMaximumCusp>> const kSetMaximumLargeCases = aroundCusp(
    kSetMaximumLargeCusps<Largest>,
    &SetMaximumCusp::maximum,
    &SetMaximumCusp::available,
    [](SetMaximumCusp const& c) {
        return c.available >= 0 && c.maximum <= Largest &&
            __int128{c.available} + c.deployed <= Largest;
    });

// The large rows of the asset's kind.
inline std::vector<AroundCusp<SetMaximumCusp>> const&
setMaximumLargeCases(Asset const& asset)
{
    if (asset.native())
        return kSetMaximumLargeCases<kXrpLargestTotal>;
    return asset.holds<MPTIssue>() ? kSetMaximumLargeCases<kMptLargestTotal>
                                   : kSetMaximumLargeCases<kIouLargestTotal>;
}

// A vault with shares must hold assets or be insolvent; no shares means no assets.
inline std::vector<AroundCusp<DeleteCusp>> const kDeleteCases = aroundCusp(
    kDeleteCusps,
    &DeleteCusp::available,
    &DeleteCusp::sharesTotal,
    [](DeleteCusp const& c) {
        return c.available >= 0 && c.sharesTotal >= 0 && (c.sharesTotal > 0 || c.available == 0);
    });

// A row as it appears in failure messages.
inline std::string
describe(ScheduleCusp const& c)
{
    return "subscription P + " + std::to_string(c.subscription) + ", gap " + std::to_string(c.gap);
}

inline std::string
describe(MaximumGridCusp const& c)
{
    return "maximum " + std::to_string(c.mantissa) + "e" + std::to_string(c.exponent) +
        " grid steps";
}

inline std::string
describe(MaximumRangeCusp const& c)
{
    return "maximum " + std::to_string(c.mantissa) + "e" + std::to_string(c.exponent);
}

inline std::string
describe(SetMaximumCusp const& c)
{
    return "available " + std::to_string(c.available) + ", deployed " + std::to_string(c.deployed) +
        ", maximum " + std::to_string(c.maximum);
}

inline std::string
describe(DeleteCusp const& c)
{
    return "available " + std::to_string(c.available) + ", sharesTotal " +
        std::to_string(c.sharesTotal);
}

}  // namespace xrpl::test::formal_verification
