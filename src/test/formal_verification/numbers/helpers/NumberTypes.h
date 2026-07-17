#pragma once

#include <test/formal_verification/ffi/protocol/STAmountFFI.h>

#include <lean/lean.h>

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

// Read the raw model fields off a returned STAmount object. Deliberately not STAmountFFI::read:
// that rebuilds a rippled STAmount and would throw/normalize on the extreme raw fields staged by
// the number tests. Each accessor consumes its arg; borrow() does the matching inc.
inline LeanSTAmountResult
readSTAmountFields(STAmountFFI const& s)
{
    LeanSTAmountResult r{};
    r.ok = true;
    r.numericType = static_cast<uint8_t>(
        NumericTypeFFI(lean_st_amount_numeric_type(s.borrow())).isIntegral() ? 1 : 0);
    r.mValue = lean_st_amount_mantissa(s.borrow());
    r.mOffset = lean_st_amount_offset(s.borrow());
    r.isNegative = lean_st_amount_negative(s.borrow());
    return r;
}

// Erroring op: `Except String STAmount`. ok mirrors the Except being `.ok`.
inline LeanSTAmountResult
readSTAmountExcept(lean_object* exceptOwned)
{
    LeanExcept<STAmountFFI> const e = readExcept<STAmountFFI>(exceptOwned);
    if (!e.value)
    {
        LeanSTAmountResult r{};
        r.ok = false;
        r.error = e.error;
        return r;
    }
    return readSTAmountFields(*e.value);
}

// Pure op: the STAmount object directly (never raises), so ok is always true.
inline LeanSTAmountResult
readSTAmountObject(lean_object* objOwned)
{
    STAmountFFI const obj(objOwned);
    return readSTAmountFields(obj);
}

// A fresh boxed NumericType for one consuming FFI call. Each @[export] op consumes its object
// args, so a wrapper is never reused across two calls.
inline lean_object*
ntObj(uint8_t tag)
{
    return NumericTypeFFI::build(tag).give();
}

// Build a Lean STAmount from raw fields, with a fresh boxed NumericType (consumed by build).
inline lean_object*
buildSt(uint8_t tag, uint64_t mValue, int64_t mOffset, uint8_t isNeg)
{
    return lean_st_amount_build(ntObj(tag), mValue, mOffset, isNeg);
}

struct LeanIOUResult
{
    int64_t mantissa;
    int64_t exponent;
    bool ok;
};

}  // namespace xrpl::test::formal_verification
