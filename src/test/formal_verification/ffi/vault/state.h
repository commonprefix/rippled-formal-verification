#pragma once

#include <test/formal_verification/ffi/LeanObjectFFI.h>
#include <test/formal_verification/ffi/protocol/AssetFFI.h>
#include <test/formal_verification/ffi/protocol/NumberFFI.h>
#include <test/formal_verification/ffi/protocol/STAmountFFI.h>

#include <xrpl/basics/Number.h>
#include <xrpl/protocol/Asset.h>
#include <xrpl/protocol/STAmount.h>

#include <lean/lean.h>

namespace xrpl::test::formal_verification {

struct VaultState
{
    Number assetsTotal;
    Asset asset;
};

extern "C" {
lean_object*
lean_vault_state_build(lean_object* assetsTotal, lean_object* asset);
}

class VaultStateFFI : public LeanObjectFFI
{
public:
    using LeanObjectFFI::LeanObjectFFI;
    using CppType = VaultState;

    static VaultStateFFI
    build(VaultState const& state)
    {
        return VaultStateFFI(leanCall(
            lean_vault_state_build,
            NumberFFI::build(state.assetsTotal),
            AssetFFI::build(state.asset)));
    }
};

}  // namespace xrpl::test::formal_verification
