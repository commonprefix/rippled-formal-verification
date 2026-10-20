#pragma once

#include <test/formal_verification/ffi/LeanObjectFFI.h>
#include <test/formal_verification/ffi/protocol/NumberFFI.h>
#include <test/formal_verification/ffi/protocol/NumericTypeFFI.h>
#include <test/formal_verification/ffi/protocol/STAmountFFI.h>

#include <xrpl/basics/Number.h>
#include <xrpl/protocol/STAmount.h>
#include <xrpl/protocol/TER.h>

#include <lean/lean.h>

#include <cstdint>
#include <optional>

namespace xrpl::test::formal_verification {

struct Vault
{
    // Derived (assetsAvailable + assetsDeployed): read back from the model, never sent to it.
    Number assetsTotal{};
    Number assetsAvailable{};
    Number assetsDeployed{};
    Number assetsReserved{};
    // sfAssetsMaximum is default-valued: absent on the ledger (nullopt) means no cap.
    std::optional<Number> assetsMaximum;
    // 3-way tag from the underlying asset: 0 = native (XRP), 1 = int64 (MPT), 2 = fractional (IOU).
    std::uint8_t numericType{};
    std::uint8_t scale{};
    Number sharesTotal{};
    Number lossUnrealized{};
    Number yieldUnrealized{};
    // Closed-ended vaults only: both dates set, or neither.
    std::optional<std::uint32_t> subscriptionDate;
    std::optional<std::uint32_t> redemptionDate;
    std::optional<std::uint32_t> earlyExitFeeRate;
    bool ownerCanBlockDeposit{};
    bool depositBlocked{};
};

// Result of a lawful-vault query
struct LawfulTerResult
{
    std::optional<LeanError> leanError;
    TER ter{};
};

extern "C" {
lean_object*
lean_vault_build(
    lean_object* assetsAvailable,
    lean_object* assetsDeployed,
    lean_object* assetsReserved,
    lean_object* assetsMaximum,
    lean_object* numericType,
    uint8_t scale,
    lean_object* sharesTotal,
    lean_object* lossUnrealized,
    lean_object* yieldUnrealized,
    lean_object* subscriptionDate,
    lean_object* redemptionDate,
    lean_object* earlyExitFeeRate,
    uint8_t ownerCanBlockDeposit,
    uint8_t depositBlocked);
lean_object*
lean_vault_assets_total(lean_object* v);
lean_object*
lean_vault_assets_available(lean_object* v);
lean_object*
lean_vault_assets_deployed(lean_object* v);
lean_object*
lean_vault_assets_reserved(lean_object* v);
lean_object*
lean_vault_assets_maximum(lean_object* v);
uint8_t
lean_vault_numeric_tag(lean_object* v);
uint8_t
lean_vault_scale(lean_object* v);
lean_object*
lean_vault_shares_total(lean_object* v);
lean_object*
lean_vault_loss_unrealized(lean_object* v);
lean_object*
lean_vault_yield_unrealized(lean_object* v);
lean_object*
lean_vault_subscription_date(lean_object* v);
lean_object*
lean_vault_redemption_date(lean_object* v);
lean_object*
lean_vault_early_exit_fee_rate(lean_object* v);
uint8_t
lean_vault_owner_can_block_deposit(lean_object* v);
uint8_t
lean_vault_deposit_blocked(lean_object* v);

lean_object*
lean_ter_amount_code(lean_object* r);
lean_object*
lean_ter_amount_value(lean_object* r);
lean_object*
lean_ter_vault_code(lean_object* r);
lean_object*
lean_ter_vault_value(lean_object* r);
lean_object*
lean_ter_vault_amounts_code(lean_object* r);
lean_object*
lean_ter_vault_amounts_value(lean_object* r);

lean_object*
lean_vault_amounts_assets(lean_object* r);
lean_object*
lean_vault_amounts_shares(lean_object* r);
lean_object*
lean_vault_amounts_vault(lean_object* r);
}

class VaultFFI : public LeanObjectFFI
{
public:
    using LeanObjectFFI::LeanObjectFFI;
    using CppType = Vault;

    // Validate the fields; `nullopt` if the model rejects them (not lawful).
    static std::optional<VaultFFI>
    build(Vault const& state)
    {
        auto e = readExcept<VaultFFI>(leanCall(
            lean_vault_build,
            NumberFFI::build(state.assetsAvailable),
            NumberFFI::build(state.assetsDeployed),
            NumberFFI::build(state.assetsReserved),
            state.assetsMaximum ? leanSome(NumberFFI::build(*state.assetsMaximum)) : leanNone(),
            NumericTypeFFI::build(state.numericType),
            state.scale,
            NumberFFI::build(state.sharesTotal),
            NumberFFI::build(state.lossUnrealized),
            NumberFFI::build(state.yieldUnrealized),
            leanOptU32(state.subscriptionDate),
            leanOptU32(state.redemptionDate),
            leanOptU32(state.earlyExitFeeRate),
            static_cast<uint8_t>(state.ownerCanBlockDeposit ? 1 : 0),
            static_cast<uint8_t>(state.depositBlocked ? 1 : 0)));
        return std::move(e.value);
    }

    // Read the fields of this lawful handle through its getters.
    Vault
    read() const
    {
        auto total = readExcept<NumberFFI>(leanGet(lean_vault_assets_total));
        return Vault{
            .assetsTotal = total.value ? total.value->read() : Number{},
            .assetsAvailable = leanGetObj<NumberFFI>(lean_vault_assets_available),
            .assetsDeployed = leanGetObj<NumberFFI>(lean_vault_assets_deployed),
            .assetsReserved = leanGetObj<NumberFFI>(lean_vault_assets_reserved),
            .assetsMaximum = leanGetOpt<NumberFFI>(lean_vault_assets_maximum),
            .numericType = leanGet(lean_vault_numeric_tag),
            .scale = leanGet(lean_vault_scale),
            .sharesTotal = leanGetObj<NumberFFI>(lean_vault_shares_total),
            .lossUnrealized = leanGetObj<NumberFFI>(lean_vault_loss_unrealized),
            .yieldUnrealized = leanGetObj<NumberFFI>(lean_vault_yield_unrealized),
            .subscriptionDate = leanGetOptU32(lean_vault_subscription_date),
            .redemptionDate = leanGetOptU32(lean_vault_redemption_date),
            .earlyExitFeeRate = leanGetOptU32(lean_vault_early_exit_fee_rate),
            .ownerCanBlockDeposit = leanGet(lean_vault_owner_can_block_deposit) != 0,
            .depositBlocked = leanGet(lean_vault_deposit_blocked) != 0};
    }
};

// The inner `Except TER α` of a model `TerExcept α` result: the TER code on rejection, else the value.
class TerExceptFFI : public LeanObjectFFI
{
public:
    using LeanObjectFFI::LeanObjectFFI;

    std::optional<TER>
    ter(lean_object* (*codeFn)(lean_object*)) const
    {
        auto const code = leanGetOptU32(codeFn);
        return code ? std::optional<TER>{TER::fromInt(static_cast<std::int32_t>(*code))}
                    : std::nullopt;
    }

    template <class W>
    std::optional<W>
    value(lean_object* (*valueFn)(lean_object*)) const
    {
        return leanOptWrapped<W>(valueFn(borrow()));
    }
};

// Vault operation result. assets/shares carry the vault asset and the share MPT, vault is the full
// post-operation lawful vault state; all three are set only when neither error is.
struct LeanVaultResult
{
    std::optional<LeanError> leanError;
    std::optional<TER> error;
    STAmount assets{};
    STAmount shares{};
    Vault vault;
};

class VaultWithAmountsFFI : public LeanObjectFFI
{
public:
    using LeanObjectFFI::LeanObjectFFI;

    LeanVaultResult
    read() const
    {
        return {
            .assets = leanGetObj<STAmountFFI>(lean_vault_amounts_assets),
            .shares = leanGetObj<STAmountFFI>(lean_vault_amounts_shares),
            .vault = leanGetObj<VaultFFI>(lean_vault_amounts_vault),
        };
    }
};

// Unpack an owned `Except Error (Except TER VaultWithAmounts)`.
inline LeanVaultResult
readVaultResult(lean_object* owned)
{
    LeanExcept<TerExceptFFI> const e = readExcept<TerExceptFFI>(owned);
    if (!e.value)
        return {.leanError = e.error};
    if (auto const ter = e.value->ter(lean_ter_vault_amounts_code))
        return {.error = ter};
    return e.value->value<VaultWithAmountsFFI>(lean_ter_vault_amounts_value)->read();
}

// An STAmount or the TER that rejects it, unless the model errors.
struct LeanAmountResult
{
    std::optional<LeanError> leanError;
    std::optional<TER> error;
    std::optional<STAmount> amount;
};

// Unpack an owned `Except Error (Except TER STAmount)`.
inline LeanAmountResult
readAmountResult(lean_object* owned)
{
    LeanExcept<TerExceptFFI> const e = readExcept<TerExceptFFI>(owned);
    if (!e.value)
        return {.leanError = e.error};
    if (auto const ter = e.value->ter(lean_ter_amount_code))
        return {.error = ter};
    return {.amount = e.value->value<STAmountFFI>(lean_ter_amount_value)->read()};
}

// Unpack an owned `Except Error Int32` holding a TER code.
inline LawfulTerResult
readTerCode(lean_object* owned)
{
    LeanObjectFFI const e(owned);
    if (!exceptOk(e.raw()))
        return {.leanError = static_cast<LeanError>(lean_obj_tag(exceptVal(e.raw())))};
    return {.ter = TER::fromInt(static_cast<std::int32_t>(lean_unbox_uint32(exceptVal(e.raw()))))};
}

}  // namespace xrpl::test::formal_verification
