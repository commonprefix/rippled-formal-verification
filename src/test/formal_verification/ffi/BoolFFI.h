#pragma once

#include <test/formal_verification/ffi/LeanObjectFFI.h>

namespace xrpl::test::formal_verification {

// Scalar wrapper so `Except String Bool` decodes through the one `readExcept<W>`.
class BoolFFI : public LeanObjectFFI
{
public:
    using LeanObjectFFI::LeanObjectFFI;
    using CppType = bool;
    bool
    read() const
    {
        return leanSelf(leanBool);
    }
};

}  // namespace xrpl::test::formal_verification
