#pragma once

#include <test/formal_verification/ffi/LeanObjectFFI.h>
#include <test/formal_verification/ffi/protocol/NumberFFI.h>
#include <test/formal_verification/ffi/protocol/NumericTypeFFI.h>
#include <test/formal_verification/ffi/protocol/STAmountFFI.h>

#include <xrpl/basics/Number.h>
#include <xrpl/protocol/TER.h>

#include <lean/lean.h>

#include <cstdint>
#include <optional>

namespace xrpl::test::formal_verification {

struct LawfulVault
{
    Number assetsTotal{};
    Number assetsAvailable{};
    // sfAssetsMaximum is default-valued: absent on the ledger (nullopt) means no cap.
    std::optional<Number> assetsMaximum;
    // 3-way tag from the underlying asset: 0 = native (XRP), 1 = int64 (MPT), 2 = fractional (IOU).
    std::uint8_t numericType{};
    std::uint8_t scale{};
    Number sharesTotal{};
    Number lossUnrealized{};
};

// Result of a lawful-vault query
struct LawfulTerResult
{
    std::optional<LeanError> leanError;
    TER ter{};
};

extern "C" {
lean_object*
lean_lawful_vault_build(
    lean_object* assetsTotal,
    lean_object* assetsAvailable,
    lean_object* assetsMaximum,
    lean_object* numericType,
    uint8_t scale,
    lean_object* sharesTotal,
    lean_object* lossUnrealized);
lean_object*
lean_lawful_vault_assets_total(lean_object* v);
lean_object*
lean_lawful_vault_assets_available(lean_object* v);
lean_object*
lean_lawful_vault_assets_maximum(lean_object* v);
uint8_t
lean_lawful_vault_numeric_tag(lean_object* v);
uint8_t
lean_lawful_vault_scale(lean_object* v);
lean_object*
lean_lawful_vault_shares_total(lean_object* v);
lean_object*
lean_lawful_vault_loss_unrealized(lean_object* v);
}

class LawfulVaultFFI : public LeanObjectFFI
{
public:
    using LeanObjectFFI::LeanObjectFFI;
    using CppType = LawfulVault;

    // Validate the fields; `nullopt` if the model rejects them (not lawful).
    static std::optional<LawfulVaultFFI>
    build(LawfulVault const& state)
    {
        auto e = readExcept<LawfulVaultFFI>(leanCall(
            lean_lawful_vault_build,
            NumberFFI::build(state.assetsTotal),
            NumberFFI::build(state.assetsAvailable),
            state.assetsMaximum ? leanSome(NumberFFI::build(*state.assetsMaximum)) : leanNone(),
            NumericTypeFFI::build(state.numericType),
            state.scale,
            NumberFFI::build(state.sharesTotal),
            NumberFFI::build(state.lossUnrealized)));
        return std::move(e.value);
    }

    // Read the fields of this lawful handle through its getters.
    LawfulVault
    read() const
    {
        return LawfulVault{
            .assetsTotal = leanGetObj<NumberFFI>(lean_lawful_vault_assets_total),
            .assetsAvailable = leanGetObj<NumberFFI>(lean_lawful_vault_assets_available),
            .assetsMaximum = leanGetOpt<NumberFFI>(lean_lawful_vault_assets_maximum),
            .numericType = leanGet(lean_lawful_vault_numeric_tag),
            .scale = leanGet(lean_lawful_vault_scale),
            .sharesTotal = leanGetObj<NumberFFI>(lean_lawful_vault_shares_total),
            .lossUnrealized = leanGetObj<NumberFFI>(lean_lawful_vault_loss_unrealized)};
    }
};

}  // namespace xrpl::test::formal_verification
