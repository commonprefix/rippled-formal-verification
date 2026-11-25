#pragma once

#include <test/formal_verification/ffi/LeanObjectFFI.h>

#include <xrpl/protocol/IOUAmount.h>

#include <lean/lean.h>

#include <cstdint>

extern "C" {
lean_object*
lean_iou_amount_build(int64_t mantissa, int64_t exponent);
int64_t
lean_iou_amount_mantissa(lean_object* amount);
int64_t
lean_iou_amount_exponent(lean_object* amount);
}

namespace xrpl::test::formal_verification {

struct LeanIOUAmount
{
    int64_t mantissa;
    int64_t exponent;
};

struct LeanIOUResult : LeanIOUAmount
{
    bool ok;
};

class IOUAmountFFI : public LeanObjectFFI
{
public:
    using LeanObjectFFI::LeanObjectFFI;
    using CppType = IOUAmount;

    static IOUAmountFFI
    build(IOUAmount const& a)
    {
        return IOUAmountFFI(lean_iou_amount_build(a.mantissa(), a.exponent()));
    }

    IOUAmount
    read() const
    {
        std::int64_t mantissa = leanGet<std::int64_t>(lean_iou_amount_mantissa);
        int exponent = static_cast<int>(leanGet<std::int64_t>(lean_iou_amount_exponent));
        return IOUAmount{mantissa, exponent};
    }

    LeanIOUResult
    readResult() const
    {
        LeanIOUResult r;
        r.mantissa = leanGet<std::int64_t>(lean_iou_amount_mantissa);
        r.exponent = leanGet<std::int64_t>(lean_iou_amount_exponent);
        r.ok = true;
        return r;
    }

    // `Except String IOUAmount`: the model IOUAmount fields (a.mantissa/a.exponent) on ok.
    static LeanIOUResult
    fromExcept(lean_object* exceptOwned)
    {
        LeanExcept<IOUAmountFFI> const e = readExcept<IOUAmountFFI>(exceptOwned);
        if (!e.value)
            return LeanIOUResult{{}, false};
        return e.value->readResult();
    }
};

static_assert(LeanWrapper<IOUAmountFFI>);

}  // namespace xrpl::test::formal_verification
