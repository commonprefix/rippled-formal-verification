#pragma once

#include <test/formal_verification/common/Sweep.h>

#include <cstddef>
#include <cstdint>
#include <string>
#include <vector>

namespace xrpl::test::formal_verification::closed_ended_sweep {

// Lawful investment periods (redemption date - subscription date), in seconds.
inline constexpr std::int64_t kSmallestGap = 180;
inline constexpr std::int64_t kOrdinaryGap = 1'000'000;
inline constexpr std::int64_t kLargestGap = 946'708'559;

// A phase boundary date placed at P + offset (P: the parent close time), the other date `gap`
// away. On the cusp (offset 0) the boundary still lets the transaction through.
struct PhaseDateCusp
{
    std::int64_t gap;
    std::int64_t offset;
};

inline constexpr PhaseDateCusp kPhaseDateCusps[] = {
    {.gap = kSmallestGap, .offset = 0},
    {.gap = kOrdinaryGap, .offset = 0},
    {.gap = kLargestGap, .offset = 0},
};

// The same boundaries for a vault with an early-exit fee rate (tenth-bips): the smallest, an
// ordinary one and 100%.
struct FeePhaseCusp
{
    std::uint32_t rate;
    std::int64_t gap;
    std::int64_t offset;
};

inline constexpr FeePhaseCusp kFeePhaseCusps[] = {
    {.rate = 1, .gap = kSmallestGap, .offset = 0},
    {.rate = 1, .gap = kOrdinaryGap, .offset = 0},
    {.rate = 1, .gap = kLargestGap, .offset = 0},
    {.rate = 5'000, .gap = kSmallestGap, .offset = 0},
    {.rate = 5'000, .gap = kOrdinaryGap, .offset = 0},
    {.rate = 5'000, .gap = kLargestGap, .offset = 0},
    {.rate = 100'000, .gap = kSmallestGap, .offset = 0},
    {.rate = 100'000, .gap = kOrdinaryGap, .offset = 0},
    {.rate = 100'000, .gap = kLargestGap, .offset = 0},
};

template <class Row>
constexpr bool
lawfulGap(Row const& c)
{
    return c.gap >= kSmallestGap && c.gap <= kLargestGap;
}

template <class Row, std::size_t N>
constexpr bool
onCusp(Row const (&rows)[N])
{
    for (Row const& c : rows)
    {
        if (c.offset != 0 || !lawfulGap(c))
            return false;
    }
    return true;
}

static_assert(onCusp(kPhaseDateCusps));
static_assert(onCusp(kFeePhaseCusps));
static_assert(kLargestGap + 1 == 946'708'560, "one below the 30-year investment period maximum");

// Every case tested: the boundary moved by kAroundCusp, and the gap too while it stays lawful.
inline std::vector<AroundCusp<PhaseDateCusp>> const kPhaseDateCases = aroundCusp(
    kPhaseDateCusps,
    &PhaseDateCusp::offset,
    &PhaseDateCusp::gap,
    lawfulGap<PhaseDateCusp>);
inline std::vector<AroundCusp<FeePhaseCusp>> const kFeePhaseCases =
    aroundCusp(kFeePhaseCusps, &FeePhaseCusp::offset, &FeePhaseCusp::gap, lawfulGap<FeePhaseCusp>);

// A row as it appears in failure messages.
inline std::string
describe(PhaseDateCusp const& c)
{
    return "gap " + std::to_string(c.gap) + ", offset " + std::to_string(c.offset);
}

inline std::string
describe(FeePhaseCusp const& c)
{
    return "rate " + std::to_string(c.rate) + ", gap " + std::to_string(c.gap) + ", offset " +
        std::to_string(c.offset);
}

}  // namespace xrpl::test::formal_verification::closed_ended_sweep
