#pragma once

#include <test/formal_verification/common/Sweep.h>

#include <xrpl/protocol/Protocol.h>

#include <algorithm>
#include <cstdint>
#include <optional>
#include <string>
#include <vector>

namespace xrpl::test::formal_verification::closed_ended_sweep {

// A phase boundary date placed at P + offset (P: the parent close time), the other date `gap`
// away, on a vault with an early-exit fee `rate` (tenth-bips) or no fee field. On the cusp
// (offset 0) the boundary still lets the transaction through. Only the offset moves: the gap and
// rate do not decide the phase.
struct PhaseDateCusp
{
    std::optional<std::uint32_t> rate;
    std::int64_t gap;
    std::int64_t offset;
};

// Lawful investment periods: kMinInvestmentPeriod, an ordinary one and kMaxInvestmentPeriod - 1
// (the maximum is exclusive).
inline constexpr std::int64_t kOrdinaryGap = 1'000'000;

inline constexpr PhaseDateCusp kPhaseDateCusps[] = {
    {.rate = std::nullopt, .gap = kMinInvestmentPeriod, .offset = 0},
    {.rate = std::nullopt, .gap = kOrdinaryGap, .offset = 0},
    {.rate = std::nullopt, .gap = kMaxInvestmentPeriod - 1, .offset = 0},
};

// The same boundaries with an early-exit fee rate: the smallest, an ordinary one and 100%.
inline constexpr PhaseDateCusp kFeePhaseCusps[] = {
    {.rate = 1, .gap = kMinInvestmentPeriod, .offset = 0},
    {.rate = 1, .gap = kOrdinaryGap, .offset = 0},
    {.rate = 1, .gap = kMaxInvestmentPeriod - 1, .offset = 0},
    {.rate = 5'000, .gap = kMinInvestmentPeriod, .offset = 0},
    {.rate = 5'000, .gap = kOrdinaryGap, .offset = 0},
    {.rate = 5'000, .gap = kMaxInvestmentPeriod - 1, .offset = 0},
    {.rate = kMaxEarlyExitFeeRate.value(), .gap = kMinInvestmentPeriod, .offset = 0},
    {.rate = kMaxEarlyExitFeeRate.value(), .gap = kOrdinaryGap, .offset = 0},
    {.rate = kMaxEarlyExitFeeRate.value(), .gap = kMaxInvestmentPeriod - 1, .offset = 0},
};

constexpr bool
onCusp(PhaseDateCusp const& c)
{
    return c.offset == 0 && c.gap >= kMinInvestmentPeriod && c.gap < kMaxInvestmentPeriod;
}

static_assert(std::ranges::all_of(kPhaseDateCusps, onCusp));
static_assert(std::ranges::all_of(kFeePhaseCusps, onCusp));

// Every case tested: the boundary moved by kAroundCusp.
inline std::vector<AroundCusp<PhaseDateCusp>> const kPhaseDateCases =
    aroundCusp(kPhaseDateCusps, &PhaseDateCusp::offset, [](PhaseDateCusp const&) { return true; });
inline std::vector<AroundCusp<PhaseDateCusp>> const kFeePhaseCases =
    aroundCusp(kFeePhaseCusps, &PhaseDateCusp::offset, [](PhaseDateCusp const&) { return true; });

// A row as it appears in failure messages.
inline std::string
describe(PhaseDateCusp const& c)
{
    return (c.rate ? "rate " + std::to_string(*c.rate) + ", " : std::string{}) + "gap " +
        std::to_string(c.gap) + ", offset " + std::to_string(c.offset);
}

}  // namespace xrpl::test::formal_verification::closed_ended_sweep
