#pragma once

#include <cstdint>
#include <string>

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

struct LeanSTAmount
{
    uint8_t numericType;
    uint64_t mValue;
    int64_t mOffset;
    uint8_t isNegative;
};

struct LeanSTAmountResult : LeanSTAmount
{
    bool ok;
    std::string error;
};

struct LeanIOUResult
{
    int64_t mantissa;
    int64_t exponent;
    bool ok;
};

}  // namespace xrpl::test::formal_verification
