#pragma once

#include <test/formal_verification/ffi/LeanObjectFFI.h>

#include <xrpl/protocol/Asset.h>
#include <xrpl/protocol/MPTIssue.h>

#include <lean/lean.h>

#include <cstdint>

// NumericType is now a boxed inductive (integral carries per-kind bounds, plus fractional).
extern "C" {
lean_object*
lean_numeric_type_build(uint8_t tag);
uint8_t
lean_numeric_type_is_integral(lean_object* numericType);
}

namespace xrpl::test::formal_verification {

class NumericTypeFFI : public LeanObjectFFI
{
public:
    using LeanObjectFFI::LeanObjectFFI;
    using CppType = bool;

    // 3-way model tag: 0 = native (XRP, 10^17), 1 = int64 (MPT, 2^63-1), 2 = fractional (IOU).
    static std::uint8_t
    tagOf(Asset const& a)
    {
        return a.native() ? 0 : a.holds<MPTIssue>() ? 1 : 2;
    }

    static NumericTypeFFI
    build(std::uint8_t tag)
    {
        return NumericTypeFFI(lean_numeric_type_build(tag));
    }

    static NumericTypeFFI
    fromAsset(Asset const& a)
    {
        return build(tagOf(a));
    }

    bool
    isIntegral() const
    {
        return leanGet<std::uint8_t>(lean_numeric_type_is_integral) != 0;
    }

    bool
    read() const
    {
        return isIntegral();
    }
};

}  // namespace xrpl::test::formal_verification
