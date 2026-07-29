#pragma once

#include <test/formal_verification/ffi/LeanObjectFFI.h>
#include <test/formal_verification/ffi/protocol/NumericTypeFFI.h>

#include <xrpl/protocol/Asset.h>
#include <xrpl/protocol/Issue.h>
#include <xrpl/protocol/MPTIssue.h>
#include <xrpl/protocol/STAmount.h>

#include <lean/lean.h>

#include <cstdint>

extern "C" {
lean_object*
lean_st_amount_build(lean_object* numericType, uint64_t mantissa, int64_t offset, uint8_t negative);
lean_object*
lean_st_amount_numeric_type(lean_object* amount);
uint64_t
lean_st_amount_mantissa(lean_object* amount);
int64_t
lean_st_amount_offset(lean_object* amount);
uint8_t
lean_st_amount_negative(lean_object* amount);
}

namespace xrpl::test::formal_verification {

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
};

class STAmountFFI : public LeanObjectFFI
{
public:
    using LeanObjectFFI::LeanObjectFFI;
    using CppType = STAmount;

    static STAmountFFI
    build(STAmount const& s)
    {
        return STAmountFFI(leanCall(
            lean_st_amount_build,
            NumericTypeFFI::fromAsset(s.asset()),
            s.mantissa(),
            s.exponent(),
            static_cast<std::uint8_t>(s.negative() ? 1 : 0)));
    }

    static STAmountFFI
    build(std::uint8_t tag, std::uint64_t mValue, std::int64_t mOffset, std::uint8_t isNeg)
    {
        return STAmountFFI(
            leanCall(lean_st_amount_build, NumericTypeFFI::build(tag), mValue, mOffset, isNeg));
    }

    STAmount
    read() const
    {
        bool const integral = leanGetObj<NumericTypeFFI>(lean_st_amount_numeric_type);
        std::uint64_t const mantissa = leanGet<std::uint64_t>(lean_st_amount_mantissa);
        int const exponent = static_cast<int>(leanGet<std::int64_t>(lean_st_amount_offset));
        bool const negative = leanGet<std::uint8_t>(lean_st_amount_negative) != 0;
        Asset const placeholder = integral ? Asset{noMPT()} : Asset{noIssue()};
        return STAmount{placeholder, mantissa, exponent, negative};
    }

    // Read the raw model fields into a LeanSTAmountResult. Deliberately not read(): that rebuilds a
    // xrpld STAmount and would throw/normalize on the extreme raw fields the number tests stage.
    LeanSTAmountResult
    readResult() const
    {
        LeanSTAmountResult r{};
        r.ok = true;
        r.numericType = static_cast<std::uint8_t>(
            leanGetObj<NumericTypeFFI>(lean_st_amount_numeric_type) ? 1 : 0);
        r.mValue = leanGet<std::uint64_t>(lean_st_amount_mantissa);
        r.mOffset = leanGet<std::int64_t>(lean_st_amount_offset);
        r.isNegative = leanGet<std::uint8_t>(lean_st_amount_negative);
        return r;
    }

    // Decode an `Except String STAmount` (erroring op)
    static LeanSTAmountResult
    fromExcept(lean_object* exceptOwned)
    {
        LeanExcept<STAmountFFI> const e = readExcept<STAmountFFI>(exceptOwned);
        if (!e.value)
            return LeanSTAmountResult{{}, false};
        return e.value->readResult();
    }

    static LeanSTAmountResult
    fromObject(lean_object* objOwned)
    {
        return STAmountFFI(objOwned).readResult();
    }
};

static_assert(LeanWrapper<STAmountFFI>);

}  // namespace xrpl::test::formal_verification
