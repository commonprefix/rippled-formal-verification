#pragma once

#include <test/formal_verification/common/Sweep.h>

#include <xrpl/basics/Number.h>
#include <xrpl/protocol/TER.h>

#include <cstdint>
#include <exception>
#include <initializer_list>
#include <limits>
#include <string>
#include <vector>

// Cusp rows for the number suites: each row sits on a normalization, range or rounding edge, and
// its two moved values (mantissa ULPs or exponent steps) cross it.
namespace xrpl::test::formal_verification::number_sweep {

using Wide = __int128;

constexpr std::int64_t kMaxRep = std::numeric_limits<std::int64_t>::max();
constexpr std::int64_t kNumberMinMantissa = 1'000'000'000'000'000'000;
constexpr std::int64_t kIouMinMantissa = 1'000'000'000'000'000;
constexpr std::int64_t kIouMaxMantissa = 9'999'999'999'999'999;
constexpr int kIouMinExponent = -96;
constexpr int kIouMaxExponent = 80;
constexpr std::int64_t kXrpMaxDrops = 100'000'000'000'000'000;

constexpr Wide
pow10(int n)
{
    Wide r = 1;
    for (int i = 0; i < n; ++i)
        r *= 10;
    return r;
}

inline constexpr Number::RoundingMode kRoundingModes[] = {
    Number::RoundingMode::ToNearest,
    Number::RoundingMode::TowardsZero,
    Number::RoundingMode::Downward,
    Number::RoundingMode::Upward};

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

// The crossing check compares verdicts, so each outcome class gets one: the operation threw
// (tecPATH_DRY), its result is zero (tecPRECISION_LOSS), or it returned a value (tesSUCCESS).
template <class Op>
TER
cppVerdict(Op op)
{
    try
    {
        return op() ? TER{tecPRECISION_LOSS} : TER{tesSUCCESS};
    }
    catch (std::exception const&)
    {
        return tecPATH_DRY;
    }
}

// Two mantissas at one exponent, combined by add or sub.
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

// A value and a uint32 ratio, for mulRatio.
struct Ratio
{
    std::int64_t value;
    std::int64_t num;
    std::int64_t den;
};

// A (mantissa, exponent) pair before normalization.
struct Scaled
{
    std::int64_t mantissa;
    std::int64_t exponent;
};

// ---- Number ----

// Add at the largest exponent: a mantissa sum up to kMaxRepUp (stored as 922337203685477581e1)
// fits, one more overflows.
inline constexpr int kNumberMaxExponent = Number::kMaxExponent;
inline constexpr int kNumberMinExponent = Number::kMinExponent;
inline constexpr Wide kMaxRepUp = Number::kMaxRepUp;
inline constexpr MantissaPair kSumOverflowCusps[] = {
    {kNumberMinMantissa, 8'223'372'036'854'775'810, kNumberMaxExponent},
    {8'223'372'036'854'775'810, kNumberMinMantissa, kNumberMaxExponent},
    {4'611'686'018'427'387'905, 4'611'686'018'427'387'905, kNumberMaxExponent},
};

// The same sums where the exponent bump is a rounding, not an overflow (both sides succeed).
inline constexpr MantissaPair kSumRoundingCusps[] = {
    {kNumberMinMantissa, kMaxRep - kNumberMinMantissa, 0},
    {kMaxRep - kNumberMinMantissa, kNumberMinMantissa, 0},
    {kMaxRep / 2, kMaxRep - kMaxRep / 2, 0},
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

// Mul at the largest exponent: a product whose 19 leading digits round past kMaxRepUp overflows;
// up to kMaxRepUp * 1e18 it fits in every rounding mode, from (kMaxRepUp + 10) * 1e18 in none.
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

// to_rep of m * 10^-1 with m ending in 5: the exact half between two integers.
inline constexpr std::int64_t kToRepHalfMantissas[] = {
    kNumberMinMantissa + 5,
    5'000'000'000'000'000'005,
    kMaxRep - 2,
};

// ---- IOUAmount ----

// Normalizing (mantissa, exponent): past the largest mantissa at the largest exponent overflows,
// below the smallest at the smallest exponent is zero; 17 digits round into the overflow.
inline constexpr Scaled kIouRangeCusps[] = {
    {kIouMaxMantissa, kIouMaxExponent},
    {kIouMinMantissa, kIouMinExponent},
    {99'999'999'999'999'994, kIouMaxExponent - 1},
};

// Add at the largest exponent up to the largest mantissa; sub at the smallest exponent down to
// the smallest mantissa.
inline constexpr MantissaPair kIouSumOverflowCusps[] = {
    {kIouMinMantissa, kIouMaxMantissa - kIouMinMantissa, kIouMaxExponent},
    {kIouMaxMantissa - kIouMinMantissa, kIouMinMantissa, kIouMaxExponent},
    {5'000'000'000'000'000, 4'999'999'999'999'999, kIouMaxExponent},
};
inline constexpr MantissaPair kIouDifferenceUnderflowCusps[] = {
    {2 * kIouMinMantissa, kIouMinMantissa, kIouMinExponent},
    {kIouMaxMantissa, kIouMaxMantissa - kIouMinMantissa, kIouMinExponent},
    {6'000'000'000'000'000, 5'000'000'000'000'000, kIouMinExponent},
};

// mulRatio at the largest exponent: value * num / den == the largest mantissa.
inline constexpr Ratio kIouMulRatioCusps[] = {
    {1'111'111'111'111'111, 900'000'000, 100'000'000},
    {3'333'333'333'333'333, 3'000'000'000, 1'000'000'000},
    {kIouMaxMantissa, 1'000'000'000, 1'000'000'000},
};

// ---- IntAmount ----

// Number m * 10^e to int64: the largest m that fits, at small, middle and large exponents.
inline constexpr Scaled kIntOfNumberCusps[] = {
    {922'337'203'685'477'580, 1},
    {9'223'372'036, 9},
    {9, 18},
};

// mulRatio: value * num / den == int64 max (or the last value under it).
inline constexpr Ratio kIntMulRatioCusps[] = {
    {2'147'483'648, 4'294'967'295, 1},
    {188'232'082'384'791'343, 490'000'000, 10'000'000},
    {1'317'624'576'693'539'401, 700'000'000, 100'000'000},
    {kMaxRep - 2, 1'000'000'000, 1'000'000'000},
};

// ---- STAmount ----

// The checked constructor per asset: XRP up to 1e17 drops, MPT up to int64 max, IOU as
// kIouRangeCusps.
inline constexpr Scaled kXrpCheckedCusps[] = {
    {kXrpMaxDrops, 0},
    {kXrpMaxDrops / 10, 1},
    {1, 17},
};
inline constexpr Scaled kMptCheckedCusps[] = {
    {922'337'203'685'477'580, 1},
    {9'223'372'036'854'775, 3},
    {9, 18},
};

// ---- Row checks ----

constexpr bool
numberMantissa(std::int64_t m)
{
    return m >= kNumberMinMantissa && m <= kMaxRep;
}

constexpr bool
iouMantissa(std::int64_t m)
{
    return m >= kIouMinMantissa && m <= kIouMaxMantissa;
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

static_assert(allOf(kSumOverflowCusps, [](MantissaPair r) {
    return Wide{r.a} + r.b == kMaxRepUp;
}));
static_assert(allOf(kSumRoundingCusps, [](MantissaPair r) { return r.a + r.b == kMaxRep; }));
static_assert(allOf(kDifferenceUnderflowCusps, [](MantissaPair r) {
    return r.a - r.b == kNumberMinMantissa;
}));
constexpr Wide kProductFits = kMaxRepUp * pow10(18);
constexpr Wide kProductOverflows = (kMaxRepUp + 10) * pow10(18);
static_assert(allOf(kProductOverflowCusps, [](Factors r) {
    return Wide{r.a} * r.b <= kProductFits &&
        (Wide{r.a} + 2) * (Wide{r.b} + 2) > kProductOverflows &&
        r.ea + r.eb + 18 == kNumberMaxExponent;
}));
static_assert(allOf(kProductUnderflowCusps, [](Factors r) {
    return Wide{r.a} * r.b <= pow10(37) && (Wide{r.a} + 2) * (Wide{r.b} + 2) > pow10(37) &&
        r.ea + r.eb + 19 == kNumberMinExponent;
}));
static_assert(allOf(kToRepHalfMantissas, [](std::int64_t m) { return m % 10 == 5; }));
static_assert(allOf(kIouSumOverflowCusps, [](MantissaPair r) {
    return r.a + r.b == kIouMaxMantissa && iouMantissa(r.a) && iouMantissa(r.b);
}));
static_assert(allOf(kIouDifferenceUnderflowCusps, [](MantissaPair r) {
    return r.a - r.b == kIouMinMantissa && iouMantissa(r.a) && iouMantissa(r.b);
}));
static_assert(allOf(kIouMulRatioCusps, [](Ratio r) {
    return Wide{r.value} * r.num == Wide{kIouMaxMantissa} * r.den && iouMantissa(r.value) &&
        r.num <= std::numeric_limits<std::uint32_t>::max();
}));
// int64 max fits, the largest move does not.
static_assert(allOf(kIntOfNumberCusps, [](Scaled r) {
    return Wide{r.mantissa} * pow10(r.exponent) <= kMaxRep &&
        Wide{r.mantissa + 1} * pow10(r.exponent) > kMaxRep;
}));
static_assert(allOf(kMptCheckedCusps, [](Scaled r) {
    return Wide{r.mantissa} * pow10(r.exponent) <= kMaxRep &&
        Wide{r.mantissa + 1} * pow10(r.exponent) > kMaxRep;
}));
static_assert(allOf(kXrpCheckedCusps, [](Scaled r) {
    return Wide{r.mantissa} * pow10(r.exponent) == kXrpMaxDrops;
}));
static_assert(allOf(kIntMulRatioCusps, [](Ratio r) {
    return Wide{r.value} * r.num <= Wide{kMaxRep} * r.den &&
        Wide{r.value + 2} * (r.num + 2) > Wide{kMaxRep} * r.den &&
        r.num <= std::numeric_limits<std::uint32_t>::max();
}));

// ---- Generated cases ----

inline std::vector<AroundCusp<std::int64_t>>
aroundEach(std::initializer_list<std::int64_t> values)
{
    std::vector<AroundCusp<std::int64_t>> groups;
    for (std::int64_t const v : values)
    {
        groups.push_back(aroundCusp(v).front());
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

template <std::size_t N>
std::vector<AroundCusp<Scaled>>
scaledCases(Scaled const (&rows)[N])
{
    return aroundCusp(rows, &Scaled::mantissa, &Scaled::exponent, [](Scaled const& r) {
        return r.mantissa >= 0;
    });
}

template <std::size_t N>
std::vector<AroundCusp<Ratio>>
ratioCases(Ratio const (&rows)[N], bool iou)
{
    return aroundCusp(rows, &Ratio::value, &Ratio::num, [iou](Ratio const& r) {
        return (iou ? iouMantissa(r.value) : r.value >= 0) && r.num >= 0 &&
            r.num <= std::numeric_limits<std::uint32_t>::max();
    });
}

inline std::vector<AroundCusp<MantissaPair>> const kSumOverflowCases =
    numberPairCases(kSumOverflowCusps);
inline std::vector<AroundCusp<MantissaPair>> const kSumRoundingCases =
    numberPairCases(kSumRoundingCusps);
inline std::vector<AroundCusp<MantissaPair>> const kDifferenceUnderflowCases =
    numberPairCases(kDifferenceUnderflowCusps);
inline std::vector<AroundCusp<Factors>> const kProductOverflowCases =
    factorCases(kProductOverflowCusps);
inline std::vector<AroundCusp<Factors>> const kProductUnderflowCases =
    factorCases(kProductUnderflowCusps);
inline std::vector<AroundCusp<std::int64_t>> const kToRepHalfCases =
    aroundEach({kToRepHalfMantissas[0], kToRepHalfMantissas[1], kToRepHalfMantissas[2]});
inline std::vector<AroundCusp<Scaled>> const kIouRangeCases = scaledCases(kIouRangeCusps);
inline std::vector<AroundCusp<MantissaPair>> const kIouSumOverflowCases =
    iouPairCases(kIouSumOverflowCusps);
inline std::vector<AroundCusp<MantissaPair>> const kIouDifferenceUnderflowCases =
    iouPairCases(kIouDifferenceUnderflowCusps);
inline std::vector<AroundCusp<Ratio>> const kIouMulRatioCases = ratioCases(kIouMulRatioCusps, true);
inline std::vector<AroundCusp<Scaled>> const kIntOfNumberCases = scaledCases(kIntOfNumberCusps);
inline std::vector<AroundCusp<Ratio>> const kIntMulRatioCases =
    ratioCases(kIntMulRatioCusps, false);
inline std::vector<AroundCusp<Scaled>> const kXrpCheckedCases = scaledCases(kXrpCheckedCusps);
inline std::vector<AroundCusp<Scaled>> const kMptCheckedCases = scaledCases(kMptCheckedCusps);

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
describe(Ratio const& r)
{
    return "value " + std::to_string(r.value) + ", ratio " + std::to_string(r.num) + "/" +
        std::to_string(r.den);
}

inline std::string
describe(Scaled const& r)
{
    return std::to_string(r.mantissa) + "e" + std::to_string(r.exponent);
}

}  // namespace xrpl::test::formal_verification::number_sweep
