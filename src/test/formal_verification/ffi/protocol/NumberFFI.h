#pragma once

#include <test/formal_verification/ffi/LeanObjectFFI.h>

#include <xrpl/basics/Number.h>

#include <lean/lean.h>

#include <cstdint>
#include <limits>
#include <stdexcept>

extern "C" {
lean_object*
lean_number_build(uint8_t negative, uint64_t mantissa, int64_t exponent);
uint8_t
lean_rounding_mode_build(uint8_t mode);
uint8_t
lean_number_negative(lean_object* number);
uint64_t
lean_number_mantissa(lean_object* number);
int64_t
lean_number_exponent(lean_object* number);
}

namespace xrpl::test::formal_verification {

struct LeanNumber
{
    uint8_t negative;
    uint64_t mantissa;
    uint64_t exponent;
};

struct LeanNumberResult : LeanNumber
{
    bool ok;
};

class NumberFFI : public LeanObjectFFI
{
public:
    using LeanObjectFFI::LeanObjectFFI;
    using CppType = Number;

    static NumberFFI
    build(Number const& n)
    {
        std::int64_t m = n.mantissa();
        std::uint8_t negative = m < 0 ? 1 : 0;
        std::uint64_t magnitude =
            m < 0 ? 0u - static_cast<std::uint64_t>(m) : static_cast<std::uint64_t>(m);
        return NumberFFI(lean_number_build(negative, magnitude, n.exponent()));
    }

    Number
    read() const
    {
        std::uint64_t const magnitude = leanGet<std::uint64_t>(lean_number_mantissa);
        bool const negative = leanGet<std::uint8_t>(lean_number_negative) != 0;
        int const exponent = static_cast<int>(leanGet<std::int64_t>(lean_number_exponent));
        return Number{negative, magnitude, exponent, Number::Normalized{}};
    }

    LeanNumberResult
    readResult() const
    {
        uint64_t mantissa = leanGet<std::uint64_t>(lean_number_mantissa);
        int64_t exponent = leanGet<std::int64_t>(lean_number_exponent);
        uint8_t const negative = leanGet<std::uint8_t>(lean_number_negative);
        if (mantissa > static_cast<uint64_t>(std::numeric_limits<int64_t>::max()))
        {
            mantissa /= 10;
            ++exponent;
        }
        LeanNumberResult r;
        r.negative = negative;
        r.mantissa = mantissa;
        r.exponent = static_cast<uint64_t>(exponent);
        r.ok = true;
        return r;
    }

    // Erroring op: `Except String Number`. ok mirrors the Except being `.ok`.
    static LeanNumberResult
    fromExcept(lean_object* exceptOwned)
    {
        LeanExcept<NumberFFI> const e = readExcept<NumberFFI>(exceptOwned);
        if (!e.value)
        {
            LeanNumberResult r{};
            r.ok = false;
            return r;
        }
        return e.value->readResult();
    }

    // Pure op (e.g. neg): the Number object directly (never raises), so ok is always true.
    static LeanNumberResult
    fromObject(lean_object* objOwned)
    {
        return NumberFFI(objOwned).readResult();
    }
};

static_assert(LeanWrapper<NumberFFI>);

// Number::RoundingMode -> a Lean `rounding_mode` value, constructed by lean_rounding_mode_build
// (the ops take a `rounding_mode`, not a raw byte). rounding_mode is a uint8 tag at the ABI.
inline uint8_t
toLeanMode(Number::RoundingMode mode)
{
    uint8_t tag;
    switch (mode)
    {
        case Number::RoundingMode::ToNearest:
            tag = 0;
            break;
        case Number::RoundingMode::TowardsZero:
            tag = 1;
            break;
        case Number::RoundingMode::Downward:
            tag = 2;
            break;
        case Number::RoundingMode::Upward:
            tag = 3;
            break;
        default:
            throw std::logic_error("toLeanMode: unknown Number::RoundingMode");
    }
    return lean_rounding_mode_build(tag);
}

}  // namespace xrpl::test::formal_verification
