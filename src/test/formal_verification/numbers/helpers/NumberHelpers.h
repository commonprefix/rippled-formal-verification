#pragma once

#include <test/formal_verification/ffi/protocol/NumberFFI.h>
#include <test/formal_verification/ffi/protocol/STAmountFFI.h>

#include <xrpl/basics/Number.h>
#include <xrpl/beast/unit_test.h>
#include <xrpl/protocol/STAmount.h>
#include <xrpl/protocol/TER.h>

#include <cstddef>
#include <cstdint>
#include <span>
#include <sstream>
#include <string>

namespace xrpl::test::formal_verification {

constexpr std::int64_t kIouMinMantissa = static_cast<std::int64_t>(STAmount::kMinValue);
constexpr std::int64_t kIouMaxMantissa = static_cast<std::int64_t>(STAmount::kMaxValue);

inline constexpr Number::RoundingMode kRoundingModes[] = {
    Number::RoundingMode::ToNearest,
    Number::RoundingMode::TowardsZero,
    Number::RoundingMode::Downward,
    Number::RoundingMode::Upward};

// For lists whose every result is exact, so the mode never matters.
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

// Each outcome class gets a verdict: the operation threw (tecPATH_DRY), its result is zero
// (tecPRECISION_LOSS), or it returned a value (tesSUCCESS).
inline TER
cppVerdict(bool threw, bool zero)
{
    if (threw)
        return tecPATH_DRY;
    return zero ? TER{tecPRECISION_LOSS} : TER{tesSUCCESS};
}

// A result value as the C++ type reports it: a signed mantissa and an exponent.
struct ScaledValue
{
    std::int64_t mantissa;
    int exponent;

    bool
    operator==(ScaledValue const&) const = default;
};

inline std::string
resultText(ScaledValue const& v)
{
    return std::to_string(v.mantissa) + "e" + std::to_string(v.exponent);
}

// Opens one test case and calls check(index, row, mode) for every row under each of `modes`, on the
// large mantissa scale; a row with a `mode` runs under that mode only.
template <class Case, std::size_t N, class Check>
void
runRows(
    beast::unit_test::Suite& suite,
    std::string const& name,
    Case const (&rows)[N],
    Check check,
    std::span<Number::RoundingMode const> modes = kRoundingModes)
{
    suite.testcase(name);
    NumberMantissaScaleGuard const sg(MantissaRange::MantissaScale::Large330);
    for (auto const mode : modes)
    {
        SaveNumberRoundMode const save{Number::setround(mode)};
        for (std::size_t i = 0; i < N; ++i)
        {
            if constexpr (requires { rows[i].mode; })
            {
                if (rows[i].mode && *rows[i].mode != mode)
                    continue;
            }
            check(i, rows[i], mode);
        }
    }
}

// Magnitude of an int64 without UB at INT64_MIN.
inline uint64_t
magnitude(int64_t m) noexcept
{
    return m < 0 ? (0u - static_cast<uint64_t>(m)) : static_cast<uint64_t>(m);
}

// Lean uses sign-magnitude, C++ folds both into a signed mantissa().
inline bool
fieldsEqual(LeanNumberResult const& lean, Number const& cpp)
{
    auto m = cpp.mantissa();
    return lean.mantissa == magnitude(m) && lean.exponent == cpp.exponent() &&
        lean.negative == (m < 0);
}

inline std::string
format(LeanNumberResult const& r)
{
    std::stringstream ss;
    ss << (r.negative ? "-" : "+") << r.mantissa << "e" << r.exponent;
    return ss.str();
}

inline std::string
format(Number const& n)
{
    auto m = n.mantissa();
    std::stringstream ss;
    ss << (m < 0 ? "-" : "+") << magnitude(m) << "e" << n.exponent();
    return ss.str();
}

inline std::string
format(LeanSTAmountResult const& r)
{
    std::stringstream ss;
    ss << "nt=" << static_cast<int>(r.numericType) << " " << (r.isNegative ? "-" : "+") << r.mValue
       << "e" << r.mOffset;
    return ss.str();
}

inline std::string
format(STAmount const& s)
{
    std::stringstream ss;
    int const nt = (s.native() || s.asset().holds<MPTIssue>()) ? 0 : 1;
    ss << "nt=" << nt << " " << (s.negative() ? "-" : "+") << s.mantissa() << "e" << s.exponent();
    return ss.str();
}

}  // namespace xrpl::test::formal_verification
