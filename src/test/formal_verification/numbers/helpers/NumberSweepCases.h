#pragma once

#include <test/formal_verification/common/Sweep.h>

#include <xrpl/basics/Number.h>
#include <xrpl/protocol/STAmount.h>
#include <xrpl/protocol/TER.h>

#include <cstddef>
#include <cstdint>
#include <limits>
#include <span>
#include <string>
#include <vector>

// Cusp rows for the number suites: each row sits on a normalization, range or rounding edge, and
// its two moved values (mantissa ULPs or exponent steps) cross it.
namespace xrpl::test::formal_verification::number_sweep {

using Wide = __int128;

constexpr std::int64_t kMaxRep = std::numeric_limits<std::int64_t>::max();
constexpr std::int64_t kNumberMinMantissa = 1'000'000'000'000'000'000;
constexpr std::uint64_t kNumberMaxMantissa =
    (static_cast<std::uint64_t>(kNumberMinMantissa) * 10) - 1;
constexpr std::int64_t kIouMinMantissa = static_cast<std::int64_t>(STAmount::kMinValue);
constexpr std::int64_t kIouMaxMantissa = static_cast<std::int64_t>(STAmount::kMaxValue);

constexpr Wide
pow10(int n)
{
    Wide r = 1;
    for (int i = 0; i < n; ++i)
        r *= 10;
    return r;
}

constexpr Wide
wideAbs(std::int64_t m)
{
    return m < 0 ? -Wide{m} : Wide{m};
}

inline constexpr Number::RoundingMode kRoundingModes[] = {
    Number::RoundingMode::ToNearest,
    Number::RoundingMode::TowardsZero,
    Number::RoundingMode::Downward,
    Number::RoundingMode::Upward};

// For sweeps whose every case is exact, so the mode never matters.
inline constexpr Number::RoundingMode kToNearestOnly[] = {Number::RoundingMode::ToNearest};

inline std::string
modeName(Number::RoundingMode mode)
{
    switch (mode)
    {
        case Number::RoundingMode::ToNearest:
            return "to nearest";
        case Number::RoundingMode::TowardsZero:
            return "towards zero";
        case Number::RoundingMode::Downward:
            return "downward";
        default:
            return "upward";
    }
}

// Runs `sweep(mode)` on the large mantissa scale under each mode, restoring both afterwards.
template <class Fn>
void
forEachMode(Fn sweep, std::span<Number::RoundingMode const> modes = kRoundingModes)
{
    NumberMantissaScaleGuard const sg(MantissaRange::MantissaScale::Large330);
    for (auto const mode : modes)
    {
        SaveNumberRoundMode const save{Number::setround(mode)};
        sweep(mode);
    }
}

// The crossing check compares verdicts, so each outcome class gets one: the operation threw
// (tecPATH_DRY), its result is zero (tecPRECISION_LOSS), or it returned a value (tesSUCCESS).
inline TER
cppVerdict(bool threw, bool zero)
{
    if (threw)
        return tecPATH_DRY;
    return zero ? TER{tecPRECISION_LOSS} : TER{tesSUCCESS};
}

// Two signed mantissas at one exponent, combined by add or sub.
struct MantissaPair
{
    std::int64_t a;
    std::int64_t b;
    int exponent;
};

// Two Number factors.
struct Factors
{
    std::int64_t a;
    std::int64_t b;
    int ea;
    int eb;
};

// A signed (mantissa, exponent) pair before normalization.
struct Scaled
{
    std::int64_t mantissa;
    std::int64_t exponent;
};

// A sign and the unsigned mantissa base + offset, for cusps past int64; only offset and exponent
// move.
struct Unsigned
{
    std::uint64_t base;
    std::int64_t offset;
    std::int64_t exponent;
    bool negative;
};

constexpr std::uint64_t
mantissaOf(Unsigned const& r)
{
    return r.offset < 0 ? r.base - static_cast<std::uint64_t>(-r.offset)
                        : r.base + static_cast<std::uint64_t>(r.offset);
}

// A signed IOU mantissa at an exponent, rounded to `scale`.
struct ScaledTo
{
    std::int64_t mantissa;
    std::int64_t exponent;
    std::int64_t scale;
};

// ---- Number ----

inline constexpr int kNumberMaxExponent = Number::kMaxExponent;
inline constexpr int kNumberMinExponent = Number::kMinExponent;
inline constexpr Wide kMaxRepUp = Number::kMaxRepUp;

// Add at the largest exponent: a sum of magnitude up to kMaxRepUp (stored as
// 922337203685477581e1) fits, one more overflows. The negative rows round the in-between sums
// away from zero under Downward, towards it under TowardsZero.
inline constexpr MantissaPair kSumOverflowCusps[] = {
    {kNumberMinMantissa, 8'223'372'036'854'775'810, kNumberMaxExponent},
    {8'223'372'036'854'775'810, kNumberMinMantissa, kNumberMaxExponent},
    {4'611'686'018'427'387'905, 4'611'686'018'427'387'905, kNumberMaxExponent},
    {-kNumberMinMantissa, -8'223'372'036'854'775'810, kNumberMaxExponent},
    {-4'611'686'018'427'387'905, -4'611'686'018'427'387'905, kNumberMaxExponent},
};

// Sub at the largest exponent with operands of opposite signs (-a - b, a - -b): the same sums.
inline constexpr MantissaPair kDifferenceOverflowCusps[] = {
    {-kNumberMinMantissa, 8'223'372'036'854'775'810, kNumberMaxExponent},
    {-4'611'686'018'427'387'905, 4'611'686'018'427'387'905, kNumberMaxExponent},
    {8'223'372'036'854'775'810, -kNumberMinMantissa, kNumberMaxExponent},
};

// The sums past kMaxRep at the smallest exponent, where the exponent bump is a rounding, not an
// overflow (both sides succeed). Exponent 0 is covered by the add and sub tests.
inline constexpr MantissaPair kSumRoundingCusps[] = {
    {kNumberMinMantissa, kMaxRep - kNumberMinMantissa, kNumberMinExponent},
    {kMaxRep / 2, kMaxRep - kMaxRep / 2, kNumberMinExponent},
};

// Sub at the smallest exponent: a - b == the smallest mantissa, one less needs exponent - 1 and
// underflows to zero.
inline constexpr MantissaPair kDifferenceUnderflowCusps[] = {
    {2 * kNumberMinMantissa, kNumberMinMantissa, kNumberMinExponent},
    {kMaxRep, kMaxRep - kNumberMinMantissa, kNumberMinExponent},
    {5'000'000'000'000'000'000, 4'000'000'000'000'000'000, kNumberMinExponent},
};

// Mul at the largest exponent: a product up to kMaxRepUp * 1e18 fits in every rounding mode; from
// (kMaxRepUp + 1) * 1e18 its 19 leading digits pass kMaxRepUp and it overflows in every mode.
inline constexpr Factors kProductOverflowCusps[] = {
    {kNumberMinMantissa, kMaxRep, kNumberMaxExponent - 18, 0},
    {kMaxRep, kNumberMinMantissa, 0, kNumberMaxExponent - 18},
    {3'037'000'499'976'049'692, 3'037'000'499'976'049'693, 16'375, 16'375},
};

// Mul at the smallest exponent: a product of 1e37 or more takes exponent ea + eb + 19 and is the
// first that does not underflow to zero.
inline constexpr Factors kProductUnderflowCusps[] = {
    {2'000'000'000'000'000'000, 5'000'000'000'000'000'000, kNumberMinExponent, -19},
    {5'000'000'000'000'000'000, 2'000'000'000'000'000'000, -19, kNumberMinExponent},
    {3'162'277'660'168'379'331, 3'162'277'660'168'379'331, -16'393, -16'394},
};

// to_rep of m * 10^-1 with m ending in 5: the exact half between two integers. ToNearest rounds a
// tie up only from an odd integer part, so both parities are needed; the negative rows tell
// Downward, Upward and TowardsZero apart.
inline constexpr std::int64_t kToRepHalfMantissas[] = {
    kNumberMinMantissa + 5,
    kNumberMinMantissa + 15,
    5'000'000'000'000'000'005,
    kMaxRep - 2,
    -(kNumberMinMantissa + 5),
    -(kNumberMinMantissa + 15),
};

// normalize at the exponent bounds: at the largest exponent a mantissa past kMaxRepUp, or past the
// largest mantissa, overflows; at the smallest, a mantissa that cannot reach the smallest one, or a
// smaller exponent, is zero.
inline constexpr Unsigned kNormalizeBoundCusps[] = {
    {Number::kMaxRepUp, 0, kNumberMaxExponent, false},
    {Number::kMaxRepUp, 0, kNumberMaxExponent, true},
    {kNumberMaxMantissa, 0, kNumberMaxExponent, false},
    {kNumberMinMantissa, 0, kNumberMinExponent, false},
    {kNumberMinMantissa, 0, kNumberMinExponent, true},
    {1, 0, kNumberMinExponent + 18, false},
};

// ---- IOUAmount ----

// Normalizing (mantissa, exponent): past the largest mantissa at the largest exponent overflows,
// below the smallest at the smallest exponent is zero; 17 digits round into the overflow, away from
// zero under Downward on the negative row.
inline constexpr Scaled kIouRangeCusps[] = {
    {kIouMaxMantissa, STAmount::kMaxOffset},
    {kIouMinMantissa, STAmount::kMinOffset},
    {99'999'999'999'999'994, STAmount::kMaxOffset - 1},
    {-kIouMaxMantissa, STAmount::kMaxOffset},
    {-kIouMinMantissa, STAmount::kMinOffset},
    {-99'999'999'999'999'994, STAmount::kMaxOffset - 1},
};

// Add at the largest exponent up to the largest mantissa.
inline constexpr MantissaPair kIouSumOverflowCusps[] = {
    {kIouMinMantissa, kIouMaxMantissa - kIouMinMantissa, STAmount::kMaxOffset},
    {kIouMaxMantissa - kIouMinMantissa, kIouMinMantissa, STAmount::kMaxOffset},
    {5'000'000'000'000'000, 4'999'999'999'999'999, STAmount::kMaxOffset},
};

// Sub at the smallest exponent: a - b down to the smallest mantissa is a value, one less is zero.
inline constexpr MantissaPair kIouDifferenceUnderflowCusps[] = {
    {2 * kIouMinMantissa - 1, kIouMinMantissa, STAmount::kMinOffset},
    {kIouMaxMantissa, kIouMaxMantissa - kIouMinMantissa + 1, STAmount::kMinOffset},
    {5'000'000'000'000'000, 4'000'000'000'000'001, STAmount::kMinOffset},
};

// Number m * 10^e to IOU, m as mantissa() reports it (stored times 10, 19 digits). At the top it is
// kIouMaxMantissa + 1/2 at exponent 80, the ToNearest tie that carries into exponent 81 and
// overflows; at the bottom it is the smallest IOU, one less rounds to zero or back up into range.
inline constexpr Scaled kIouOfNumberCusps[] = {
    {999'999'999'999'999'950, STAmount::kMaxOffset - 2},
    {-999'999'999'999'999'950, STAmount::kMaxOffset - 2},
    {kNumberMinMantissa, STAmount::kMinOffset - 3},
    {-kNumberMinMantissa, STAmount::kMinOffset - 3},
};

// ---- IntAmount ----

// Number m * 10^e to int64: the largest |m| that fits, at exponent 0 (int64 max itself; its moves
// past it are not int64 and are skipped), 1, 9 and 18, on both sides.
inline constexpr Scaled kIntOfNumberCusps[] = {
    {kMaxRep, 0},
    {922'337'203'685'477'580, 1},
    {9'223'372'036, 9},
    {9, 18},
    {-kMaxRep, 0},
    {-922'337'203'685'477'580, 1},
};

// int64 to Number: -kMaxRep is exact; one below, INT64_MIN has magnitude 2^63, strictly between
// kMaxRep and kMaxRepUp, where the rounding mode picks the Number.
inline constexpr std::int64_t kIntToNumberCusps[] = {-kMaxRep};

// ---- STAmount ----

// The checked constructor per asset: XRP up to 1e17 drops, MPT up to int64 max, IOU as
// kIouRangeCusps.
inline constexpr Scaled kXrpCheckedCusps[] = {
    {static_cast<std::int64_t>(STAmount::kMaxNativeN), 0},
    {static_cast<std::int64_t>(STAmount::kMaxNativeN / 10), 1},
    {1, 17},
    {-static_cast<std::int64_t>(STAmount::kMaxNativeN), 0},
};
inline constexpr Unsigned kMptCheckedCusps[] = {
    {kMaxRep, 0, 0, false},
    {kMaxRep, 0, 0, true},
    {922'337'203'685'477'580, 0, 1, false},
    {9'223'372'036'854'775, 0, 3, false},
    {9, 0, 18, false},
};

// roundToScale of an IOU: below `scale` it rounds at 10^scale, from `scale` up it returns the
// value. Tie rows sit half a unit below `scale`, with both parities of the kept digits and both
// signs; no-op rows sit at exponent == scale and move only the exponent.
inline constexpr ScaledTo kRoundToScaleTies[] = {
    {kIouMinMantissa + 5, -1, 0},
    {kIouMinMantissa + 15, -1, 0},
    {-(kIouMinMantissa + 5), -1, 0},
    {-(kIouMinMantissa + 15), -1, 0},
    {kIouMaxMantissa - 4, -11, -10},
};
inline constexpr ScaledTo kRoundToScaleNoOps[] = {
    {kIouMinMantissa + 5, 0, 0},
    {-(kIouMinMantissa + 5), 0, 0},
    {kIouMaxMantissa, -10, -10},
};

// ---- Row checks ----

constexpr bool
numberMantissa(std::int64_t m)
{
    return wideAbs(m) >= kNumberMinMantissa && wideAbs(m) <= kMaxRep;
}

constexpr bool
iouMantissa(std::int64_t m)
{
    return wideAbs(m) >= kIouMinMantissa && wideAbs(m) <= kIouMaxMantissa;
}

constexpr bool
allOf(auto const& rows, auto pred)
{
    for (auto const& r : rows)
    {
        if (!pred(r))
            return false;
    }
    return true;
}

constexpr bool
anyOf(auto const& rows, auto pred)
{
    return !allOf(rows, [&](auto const& r) { return !pred(r); });
}

// The largest factor a row's moves run: kAroundCusp's +2, kept within the mantissa range.
constexpr Wide
largestMove(std::int64_t m)
{
    return m > kMaxRep - 2 ? Wide{kMaxRep} : Wide{m} + 2;
}

// int64 max fits, the next mantissa does not.
constexpr bool
int64Bound(Wide m, std::int64_t e)
{
    return m * pow10(e) <= kMaxRep && (m + 1) * pow10(e) > kMaxRep;
}

static_assert(allOf(kSumOverflowCusps, [](MantissaPair r) {
    return (r.a < 0) == (r.b < 0) && wideAbs(r.a) + wideAbs(r.b) == kMaxRepUp;
}));
static_assert(allOf(kDifferenceOverflowCusps, [](MantissaPair r) {
    return (r.a < 0) != (r.b < 0) && wideAbs(r.a) + wideAbs(r.b) == kMaxRepUp;
}));
static_assert(allOf(kSumRoundingCusps, [](MantissaPair r) { return r.a + r.b == kMaxRep; }));
static_assert(allOf(kDifferenceUnderflowCusps, [](MantissaPair r) {
    return r.a - r.b == kNumberMinMantissa;
}));
constexpr Wide kProductFits = kMaxRepUp * pow10(18);
constexpr Wide kProductOverflows = (kMaxRepUp + 1) * pow10(18);
static_assert(allOf(kProductOverflowCusps, [](Factors r) {
    return Wide{r.a} * r.b <= kProductFits &&
        largestMove(r.a) * largestMove(r.b) >= kProductOverflows &&
        r.ea + r.eb + 18 == kNumberMaxExponent;
}));
static_assert(allOf(kProductUnderflowCusps, [](Factors r) {
    return Wide{r.a} * r.b <= pow10(37) && largestMove(r.a) * largestMove(r.b) > pow10(37) &&
        r.ea + r.eb + 19 == kNumberMinExponent;
}));
static_assert(allOf(kToRepHalfMantissas, [](std::int64_t m) {
    return wideAbs(m) % 10 == 5 && numberMantissa(m);
}));
static_assert(anyOf(kToRepHalfMantissas, [](std::int64_t m) { return wideAbs(m) / 10 % 2 == 1; }));
static_assert(anyOf(kToRepHalfMantissas, [](std::int64_t m) { return wideAbs(m) / 10 % 2 == 0; }));
static_assert(allOf(kNormalizeBoundCusps, [](Unsigned r) {
    bool const top = r.exponent == kNumberMaxExponent &&
        (r.base == Number::kMaxRepUp || r.base == kNumberMaxMantissa);
    bool const bottom = r.exponent >= kNumberMinExponent && r.exponent <= kNumberMinExponent + 18 &&
        Wide{r.base} * pow10(r.exponent - kNumberMinExponent) == kNumberMinMantissa;
    return r.offset == 0 && (top || bottom);
}));
static_assert(allOf(kIouRangeCusps, [](Scaled r) {
    Wide const m = wideAbs(r.mantissa);
    return (m == kIouMaxMantissa && r.exponent == STAmount::kMaxOffset) ||
        (m == kIouMinMantissa && r.exponent == STAmount::kMinOffset) ||
        (m == Wide{kIouMaxMantissa} * 10 + 4 && r.exponent == STAmount::kMaxOffset - 1);
}));
static_assert(allOf(kIouSumOverflowCusps, [](MantissaPair r) {
    return r.a + r.b == kIouMaxMantissa && iouMantissa(r.a) && iouMantissa(r.b);
}));
static_assert(allOf(kIouDifferenceUnderflowCusps, [](MantissaPair r) {
    return r.a - r.b == kIouMinMantissa - 1 && iouMantissa(r.a) && iouMantissa(r.b);
}));
static_assert(allOf(kIouOfNumberCusps, [](Scaled r) {
    Wide const m = wideAbs(r.mantissa);
    return (m * 2 == (Wide{kIouMaxMantissa} * 2 + 1) * 100 &&
            r.exponent == STAmount::kMaxOffset - 2) ||
        (m == kNumberMinMantissa && r.exponent == STAmount::kMinOffset - 3);
}));
static_assert(allOf(kIntOfNumberCusps, [](Scaled r) {
    return int64Bound(wideAbs(r.mantissa), r.exponent);
}));
static_assert(allOf(kIntToNumberCusps, [](std::int64_t v) {
    return Wide{v} - 1 == std::numeric_limits<std::int64_t>::min();
}));
static_assert(allOf(kMptCheckedCusps, [](Unsigned r) {
    return r.offset == 0 && int64Bound(r.base, r.exponent);
}));
static_assert(allOf(kXrpCheckedCusps, [](Scaled r) {
    return wideAbs(r.mantissa) * pow10(r.exponent) == STAmount::kMaxNativeN;
}));
static_assert(allOf(kRoundToScaleTies, [](ScaledTo r) {
    return wideAbs(r.mantissa) % 10 == 5 && iouMantissa(r.mantissa) && r.exponent == r.scale - 1;
}));
static_assert(anyOf(kRoundToScaleTies, [](ScaledTo r) {
    return wideAbs(r.mantissa) / 10 % 2 == 1;
}));
static_assert(anyOf(kRoundToScaleTies, [](ScaledTo r) {
    return wideAbs(r.mantissa) / 10 % 2 == 0;
}));
static_assert(allOf(kRoundToScaleNoOps, [](ScaledTo r) {
    return iouMantissa(r.mantissa) && r.exponent == r.scale;
}));

// ---- Generated cases ----

// Each value moved by kAroundCusp; a move past int64 is skipped.
template <std::size_t N>
std::vector<AroundCusp<std::int64_t>>
aroundEach(std::int64_t const (&values)[N])
{
    std::vector<AroundCusp<std::int64_t>> groups;
    for (std::int64_t const v : values)
    {
        AroundCusp<std::int64_t> group{.cusp = v, .cases = {}};
        for (std::int64_t const d : kAroundCusp)
        {
            std::int64_t moved = 0;
            if (!__builtin_add_overflow(v, d, &moved))
                group.cases.push_back(moved);
        }
        groups.push_back(group);
    }
    return groups;
}

template <std::size_t N>
std::vector<AroundCusp<MantissaPair>>
numberPairCases(MantissaPair const (&rows)[N])
{
    return aroundCusp(rows, &MantissaPair::a, &MantissaPair::b, [](MantissaPair const& r) {
        return numberMantissa(r.a) && numberMantissa(r.b);
    });
}

template <std::size_t N>
std::vector<AroundCusp<MantissaPair>>
iouPairCases(MantissaPair const (&rows)[N])
{
    return aroundCusp(rows, &MantissaPair::a, &MantissaPair::b, [](MantissaPair const& r) {
        return iouMantissa(r.a) && iouMantissa(r.b);
    });
}

template <std::size_t N>
std::vector<AroundCusp<Factors>>
factorCases(Factors const (&rows)[N])
{
    return aroundCusp(rows, &Factors::a, &Factors::b, [](Factors const& r) {
        return numberMantissa(r.a) && numberMantissa(r.b);
    });
}

// A move never flips the sign of its row's mantissa.
template <std::size_t N>
std::vector<AroundCusp<Scaled>>
scaledCases(Scaled const (&rows)[N])
{
    std::vector<AroundCusp<Scaled>> groups;
    for (Scaled const& row : rows)
    {
        Scaled const one[] = {row};
        groups.push_back(aroundCusp(
                             one,
                             &Scaled::mantissa,
                             &Scaled::exponent,
                             [negative = row.mantissa < 0](Scaled const& r) {
                                 return negative ? r.mantissa <= 0 : r.mantissa >= 0;
                             })
                             .front());
    }
    return groups;
}

template <std::size_t N>
std::vector<AroundCusp<Unsigned>>
unsignedCases(Unsigned const (&rows)[N])
{
    return aroundCusp(rows, &Unsigned::offset, &Unsigned::exponent, [](Unsigned const& r) {
        return r.offset >= 0 || r.base >= static_cast<std::uint64_t>(-r.offset);
    });
}

inline std::vector<AroundCusp<MantissaPair>> const kSumOverflowCases =
    numberPairCases(kSumOverflowCusps);
inline std::vector<AroundCusp<MantissaPair>> const kDifferenceOverflowCases =
    numberPairCases(kDifferenceOverflowCusps);
inline std::vector<AroundCusp<MantissaPair>> const kSumRoundingCases =
    numberPairCases(kSumRoundingCusps);
inline std::vector<AroundCusp<MantissaPair>> const kDifferenceUnderflowCases =
    numberPairCases(kDifferenceUnderflowCusps);
inline std::vector<AroundCusp<Factors>> const kProductOverflowCases =
    factorCases(kProductOverflowCusps);
inline std::vector<AroundCusp<Factors>> const kProductUnderflowCases =
    factorCases(kProductUnderflowCusps);
inline std::vector<AroundCusp<std::int64_t>> const kToRepHalfCases =
    aroundEach(kToRepHalfMantissas);
inline std::vector<AroundCusp<Unsigned>> const kNormalizeBoundCases =
    unsignedCases(kNormalizeBoundCusps);
inline std::vector<AroundCusp<Scaled>> const kIouRangeCases = scaledCases(kIouRangeCusps);
inline std::vector<AroundCusp<MantissaPair>> const kIouSumOverflowCases =
    iouPairCases(kIouSumOverflowCusps);
inline std::vector<AroundCusp<MantissaPair>> const kIouDifferenceUnderflowCases =
    iouPairCases(kIouDifferenceUnderflowCusps);
inline std::vector<AroundCusp<Scaled>> const kIouOfNumberCases = scaledCases(kIouOfNumberCusps);
inline std::vector<AroundCusp<Scaled>> const kIntOfNumberCases = scaledCases(kIntOfNumberCusps);
inline std::vector<AroundCusp<std::int64_t>> const kIntToNumberCases =
    aroundEach(kIntToNumberCusps);
inline std::vector<AroundCusp<Scaled>> const kXrpCheckedCases = scaledCases(kXrpCheckedCusps);
inline std::vector<AroundCusp<Unsigned>> const kMptCheckedCases = unsignedCases(kMptCheckedCusps);
inline std::vector<AroundCusp<ScaledTo>> const kRoundToScaleTieCases =
    aroundCusp(kRoundToScaleTies, &ScaledTo::mantissa, [](ScaledTo const& r) {
        return iouMantissa(r.mantissa);
    });
inline std::vector<AroundCusp<ScaledTo>> const kRoundToScaleNoOpCases =
    aroundCusp(kRoundToScaleNoOps, &ScaledTo::exponent, [](ScaledTo const&) { return true; });

// A row as it appears in failure messages.
inline std::string
describe(MantissaPair const& r)
{
    return "a " + std::to_string(r.a) + ", b " + std::to_string(r.b) + ", exponent " +
        std::to_string(r.exponent);
}

inline std::string
describe(Factors const& r)
{
    return "a " + std::to_string(r.a) + "e" + std::to_string(r.ea) + ", b " + std::to_string(r.b) +
        "e" + std::to_string(r.eb);
}

inline std::string
describe(Scaled const& r)
{
    return std::to_string(r.mantissa) + "e" + std::to_string(r.exponent);
}

inline std::string
describe(Unsigned const& r)
{
    return (r.negative ? "-" : "") + std::to_string(mantissaOf(r)) + "e" +
        std::to_string(r.exponent);
}

inline std::string
describe(ScaledTo const& r)
{
    return std::to_string(r.mantissa) + "e" + std::to_string(r.exponent) + " to scale " +
        std::to_string(r.scale);
}

}  // namespace xrpl::test::formal_verification::number_sweep
