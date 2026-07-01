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

}  // namespace xrpl::test::formal_verification
