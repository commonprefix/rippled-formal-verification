#pragma once

#include <test/formal_verification/ffi/LeanObjectFFI.h>
#include <test/formal_verification/ffi/protocol/NumberFFI.h>
#include <test/formal_verification/ffi/protocol/NumericTypeFFI.h>
#include <test/formal_verification/ffi/protocol/STAmountFFI.h>

#include <xrpl/basics/Number.h>

#include <lean/lean.h>

#include <cstdint>

namespace xrpl::test::formal_verification {

struct VaultState
{
    Number assetsTotal;
    Number assetsAvailable;
    // sfAssetsMaximum is default-valued: absent on the ledger means no cap. assetsMaximum is
    // meaningful only when hasMaximum is true (the accessor reads an absent field as 0).
    bool hasMaximum{};
    Number assetsMaximum;
    // 3-way tag from the underlying asset: 0 = native (XRP), 1 = int64 (MPT), 2 = fractional (IOU).
    std::uint8_t numericType{};
    std::uint8_t scale{};
    Number sharesTotal;
    Number lossUnrealized;
};

extern "C" {
lean_object*
lean_vault_state_build(
    lean_object* assetsTotal,
    lean_object* assetsAvailable,
    uint8_t hasMaximum,
    lean_object* assetsMaximum,
    lean_object* numericType,
    uint8_t scale,
    lean_object* sharesTotal,
    lean_object* lossUnrealized);
uint8_t
lean_vault_state_has_maximum(lean_object* vs);
lean_object*
lean_vault_state_assets_total(lean_object* vs);
lean_object*
lean_vault_state_assets_available(lean_object* vs);
lean_object*
lean_vault_state_assets_maximum(lean_object* vs);
lean_object*
lean_vault_state_numeric_type(lean_object* vs);
uint8_t
lean_vault_state_numeric_tag(lean_object* vs);
uint8_t
lean_vault_state_scale(lean_object* vs);
lean_object*
lean_vault_state_shares_total(lean_object* vs);
lean_object*
lean_vault_state_loss_unrealized(lean_object* vs);
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
            static_cast<std::uint8_t>(state.hasMaximum),
            NumberFFI::build(state.assetsMaximum),
            NumericTypeFFI::build(state.numericType),
            state.scale,
            NumberFFI::build(state.sharesTotal),
            NumberFFI::build(state.lossUnrealized)));
    }

    VaultState
    read() const
    {
        return VaultState{
            .assetsTotal = leanGetObj<NumberFFI>(lean_vault_state_assets_total),
            .assetsAvailable = leanGetObj<NumberFFI>(lean_vault_state_assets_available),
            .hasMaximum = leanGet<std::uint8_t>(lean_vault_state_has_maximum) != 0,
            .assetsMaximum = leanGetObj<NumberFFI>(lean_vault_state_assets_maximum),
            .numericType = leanGet<std::uint8_t>(lean_vault_state_numeric_tag),
            .scale = leanGet<std::uint8_t>(lean_vault_state_scale),
            .sharesTotal = leanGetObj<NumberFFI>(lean_vault_state_shares_total),
            .lossUnrealized = leanGetObj<NumberFFI>(lean_vault_state_loss_unrealized)};
    }
};

static_assert(LeanWrapper<VaultStateFFI>);

}  // namespace xrpl::test::formal_verification
