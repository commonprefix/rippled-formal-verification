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
    Number assetsAvailable;
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
    lean_object* assetsAvailable,
    lean_object* asset,
    uint8_t scale,
    lean_object* sharesTotal,
    lean_object* sharesAsset,
    lean_object* interestUnrealized);
lean_object*
lean_vault_state_assets_total(lean_object* vs);
lean_object*
lean_vault_state_assets_available(lean_object* vs);
lean_object*
lean_vault_state_asset(lean_object* vs);
uint8_t
lean_vault_state_scale(lean_object* vs);
lean_object*
lean_vault_state_shares_total(lean_object* vs);
lean_object*
lean_vault_state_shares_asset(lean_object* vs);
lean_object*
lean_vault_state_interest_unrealized(lean_object* vs);
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
            NumberFFI::build(state.assetsAvailable),
            AssetFFI::build(state.asset),
            state.scale,
            NumberFFI::build(state.sharesTotal),
            AssetFFI::build(state.sharesAsset),
            NumberFFI::build(state.interestUnrealized)));
    }

    VaultState
    read() const
    {
        return VaultState{
            .assetsTotal = leanGetObj<NumberFFI>(lean_vault_state_assets_total),
            .assetsAvailable = leanGetObj<NumberFFI>(lean_vault_state_assets_available),
            .asset = leanGetObj<AssetFFI>(lean_vault_state_asset),
            .scale = leanGet<std::uint8_t>(lean_vault_state_scale),
            .sharesTotal = leanGetObj<NumberFFI>(lean_vault_state_shares_total),
            .sharesAsset = leanGetObj<AssetFFI>(lean_vault_state_shares_asset),
            .interestUnrealized = leanGetObj<NumberFFI>(lean_vault_state_interest_unrealized)};
    }
};

static_assert(LeanWrapper<VaultStateFFI>);

}  // namespace xrpl::test::formal_verification
