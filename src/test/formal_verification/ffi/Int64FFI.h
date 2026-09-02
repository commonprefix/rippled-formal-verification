#pragma once

#include <test/formal_verification/ffi/LeanObjectFFI.h>

#include <cstdint>

namespace xrpl::test::formal_verification {

// Scalar wrapper so `Except String Int64` decodes through the one `readExcept<W>`.
class Int64FFI : public LeanObjectFFI
{
public:
    using LeanObjectFFI::LeanObjectFFI;
    using CppType = int64_t;
    int64_t
    read() const
    {
        return leanSelf(leanI64);
    }
};

}  // namespace xrpl::test::formal_verification
