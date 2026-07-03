#pragma once

#include <test/formal_verification/ffi/LeanObjectFFI.h>
#include <test/formal_verification/ffi/protocol/STAmountFFI.h>
#include <test/formal_verification/ffi/protocol/TerFFI.h>
#include <test/formal_verification/ffi/protocol/XRPAmountFFI.h>

#include <xrpl/protocol/STAmount.h>
#include <xrpl/protocol/XRPAmount.h>

#include "test/formal_verification/numbers/helpers/NumberTypes.h"
#include <lean/lean.h>

#include <cstdint>

namespace xrpl::test::formal_verification {

// Outcome of a Lean view op returning a value of type T
// `threw` reports a model error (message in `error`), otherwise `value` holds the result
// template <class T>
// struct LeanResult
// {
//     bool threw{};
//     T value;
//     std::string error;
// };

struct LeanTerResult
{
    bool threw;
    int32_t code;

    static LeanTerResult
    fromLean(lean_object* obj)
    {
        LeanObjOwner const guard{obj};
        return {
            .threw = (lean_ctor_get_uint8(obj, 4) == 1),
            .code = static_cast<int32_t>(lean_ctor_get_uint32(obj, 0)),
        };
    };
};

// Mirrors FFIRoundedDepositResult. status: 0 = rounded (STAmount fields valid),
// 1 = rejected (code valid), 2 = threw. Offsets follow Lean's scalar layout:
// 8-byte group in decl order (code@0, mValue@8, mOffset@16), then 1-byte group
// (assetKind@24, mIsNegative@25, status@26).
struct LeanRoundedDepositResult
{
    uint8_t status;
    int32_t code;
    uint8_t assetKind;
    uint64_t mValue;
    int64_t mOffset;
    bool mIsNegative;

    bool
    threw() const
    {
        return status == 2;
    }
    bool
    rejected() const
    {
        return status == 1;
    }
    bool
    rounded() const
    {
        return status == 0;
    }

    static LeanRoundedDepositResult
    fromLean(lean_object* obj)
    {
        LeanObjOwner const guard{obj};
        return {
            .status = lean_ctor_get_uint8(obj, 26),
            .code = static_cast<int32_t>(lean_ctor_get_uint64(obj, 0)),
            .assetKind = lean_ctor_get_uint8(obj, 24),
            .mValue = lean_ctor_get_uint64(obj, 8),
            .mOffset = static_cast<int64_t>(lean_ctor_get_uint64(obj, 16)),
            .mIsNegative = lean_ctor_get_uint8(obj, 25) != 0,
        };
    }
};

}  // namespace xrpl::test::formal_verification
