#pragma once

#include <test/formal_verification/ffi/protocol/NumberFFI.h>
#include <test/formal_verification/numbers/helpers/NumberGenerators.h>
#include <test/formal_verification/numbers/helpers/NumberHelpers.h>

#include <xrpl/basics/Number.h>
#include <xrpl/beast/unit_test/suite.h>

#include <lean/lean.h>

#include <cstdint>
#include <optional>
#include <stdexcept>
#include <string>

extern "C" {
lean_object*
lean_number_mul(lean_object*, lean_object*, uint8_t);
lean_object*
lean_number_div(lean_object*, lean_object*, uint8_t);
lean_object*
lean_number_add(lean_object*, lean_object*, uint8_t);
lean_object*
lean_number_sub(lean_object*, lean_object*, uint8_t);
lean_object*
lean_number_normalize(lean_object*, uint8_t);
uint8_t
lean_number_eq(lean_object*, lean_object*);
uint8_t
lean_number_ne(lean_object*, lean_object*);
uint8_t
lean_number_lt(lean_object*, lean_object*);
uint8_t
lean_number_le(lean_object*, lean_object*);
uint8_t
lean_number_gt(lean_object*, lean_object*);
uint8_t
lean_number_ge(lean_object*, lean_object*);
}

// Helpers of NumberFindings_test.cpp. A check runs one operation in the Lean model and in C++
// under the current rounding mode and expects the same result.
namespace xrpl::test::formal_verification {

// The Number of the pair for the model, with the same sign, mantissa and exponent as in C++.
inline lean_object*
leanNumber(NumberPair const& pair)
{
    LeanNumber const& number = pair.leanNum;
    return lean_number_build(
        number.negative, number.mantissa, static_cast<int64_t>(number.exponent));
}

// x op y in C++, where op is one of + - * /. No value when the operation throws an overflow.
inline std::optional<Number>
compute(Number const& x, char op, Number const& y)
{
    try
    {
        switch (op)
        {
            case '+':
                return x + y;
            case '-':
                return x - y;
            case '*':
                return x * y;
            default:
                return x / y;
        }
    }
    catch (std::overflow_error const&)
    {
        return std::nullopt;
    }
}

// x op y in the model, where op is one of + - * /.
inline LeanNumberResult
leanCompute(NumberPair const& x, char op, NumberPair const& y)
{
    uint8_t const mode = toLeanMode(Number::getround());
    switch (op)
    {
        case '+':
            return NumberFFI::fromExcept(lean_number_add(leanNumber(x), leanNumber(y), mode));
        case '-':
            return NumberFFI::fromExcept(lean_number_sub(leanNumber(x), leanNumber(y), mode));
        case '*':
            return NumberFFI::fromExcept(lean_number_mul(leanNumber(x), leanNumber(y), mode));
        default:
            return NumberFFI::fromExcept(lean_number_div(leanNumber(x), leanNumber(y), mode));
    }
}

// The Number that the constructor makes of the sign, mantissa and exponent. No value when it
// throws an overflow.
inline std::optional<Number>
construct(bool negative, std::uint64_t mantissa, int exponent)
{
    try
    {
        return Number{negative, mantissa, exponent, Number::Normalized{}};
    }
    catch (std::overflow_error const&)
    {
        return std::nullopt;
    }
}

// The model and C++ must both fail, both return zero, or return the same sign, mantissa and
// exponent. No C++ value means that C++ threw an overflow.
inline void
checkResult(
    beast::unit_test::Suite& suite,
    std::string const& label,
    LeanNumberResult const& lean,
    std::optional<Number> const& cpp)
{
    bool same = lean.ok == cpp.has_value();
    if (lean.ok && cpp)
        same = (lean.mantissa == 0 && cpp->mantissa() == 0) || fieldsEqual(lean, *cpp);
    std::string const results = std::string{": lean="} + (lean.ok ? format(lean) : "error") +
        " cpp=" + (cpp ? format(*cpp) : "threw");
    suite.expect(same, label + results, __FILE__, __LINE__);
}

// x op y is the same in the model and in C++, where op is one of + - * /.
inline void
checkBinOp(beast::unit_test::Suite& suite, NumberPair const& x, char op, NumberPair const& y)
{
    std::string const label = "(" + format(x.cppNum) + ") " + op + " (" + format(y.cppNum) + ") [" +
        to_string(Number::getround()) + "]";
    checkResult(suite, label, leanCompute(x, op, y), compute(x.cppNum, op, y.cppNum));
}

// Normalizing the sign, mantissa and exponent is the same in the model and in the constructor.
inline void
checkNormalize(beast::unit_test::Suite& suite, bool negative, std::uint64_t mantissa, int exponent)
{
    std::string const label = std::string{"normalize("} + (negative ? "-" : "") +
        std::to_string(mantissa) + "e" + std::to_string(exponent) + ") [" +
        to_string(Number::getround()) + "]";
    LeanNumberResult const lean = NumberFFI::fromExcept(lean_number_normalize(
        lean_number_build(negative ? 1 : 0, mantissa, exponent), toLeanMode(Number::getround())));
    checkResult(suite, label, lean, construct(negative, mantissa, exponent));
}

// Every comparison operator gives the same answer for x and y in the model and in C++.
inline void
checkCompare(beast::unit_test::Suite& suite, NumberPair const& x, NumberPair const& y)
{
    Number const& a = x.cppNum;
    Number const& b = y.cppNum;
    bool const same = (lean_number_eq(leanNumber(x), leanNumber(y)) != 0) == (a == b) &&
        (lean_number_ne(leanNumber(x), leanNumber(y)) != 0) == (a != b) &&
        (lean_number_lt(leanNumber(x), leanNumber(y)) != 0) == (a < b) &&
        (lean_number_le(leanNumber(x), leanNumber(y)) != 0) == (a <= b) &&
        (lean_number_gt(leanNumber(x), leanNumber(y)) != 0) == (a > b) &&
        (lean_number_ge(leanNumber(x), leanNumber(y)) != 0) == (a >= b);
    std::string const label = "(" + format(a) + ") ? (" + format(b) + ")";
    suite.expect(same, label + ": the model and C++ differ", __FILE__, __LINE__);
}

}  // namespace xrpl::test::formal_verification
