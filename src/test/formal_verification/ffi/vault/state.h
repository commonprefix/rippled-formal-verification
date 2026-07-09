#pragma once

#include <test/formal_verification/ffi/LeanObjectFFI.h>
#include <test/formal_verification/ffi/protocol/AssetFFI.h>
#include <test/formal_verification/ffi/protocol/NumberFFI.h>
#include <test/formal_verification/ffi/protocol/STAmountFFI.h>

#include <xrpl/basics/Number.h>
#include <xrpl/protocol/Asset.h>
#include <xrpl/protocol/STAmount.h>

#include <lean/lean.h>

#include <cstdint>

namespace xrpl::test::formal_verification {

struct VaultState
{
    Number assetsTotal;
    Asset asset;
    std::uint8_t scale{};
    Number sharesTotal;
    Asset sharesAsset;
    Number interestUnrealized;
};

extern "C" {
lean_object*
lean_vault_state_build(
    lean_object* assetsTotal,
    lean_object* asset,
    uint8_t scale,
    lean_object* sharesTotal,
    lean_object* sharesAsset,
    lean_object* interestUnrealized);
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
            AssetFFI::build(state.asset),
            state.scale,
            NumberFFI::build(state.sharesTotal),
            AssetFFI::build(state.sharesAsset),
            NumberFFI::build(state.interestUnrealized)));
    }
};

}  // namespace xrpl::test::formal_verification
