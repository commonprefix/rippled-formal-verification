#pragma once

#include <test/formal_verification/ffi/LeanObjectFFI.h>
#include <test/formal_verification/ffi/protocol/STAmountFFI.h>
#include <test/formal_verification/ffi/vault/VaultFFI.h>

#include <xrpl/protocol/STAmount.h>
#include <xrpl/protocol/TER.h>

#include <lean/lean.h>

#include <cstdint>
#include <optional>

extern "C" {
lean_object*
lean_vault_clawback(
    lean_object* v,
    lean_object* assets,
    lean_object* holderShares,
    uint8_t waiveUnrealizedLoss);
lean_object*
lean_vault_burn_shares(lean_object* v, lean_object* sharesDestroyed);
lean_object*
lean_can_burn_shares(lean_object* vault, lean_object* amount, lean_object* holderShares);
}

namespace xrpl::test::formal_verification {

inline LeanVaultResult
leanVaultClawback(
    Vault const& state,
    STAmount const& assets,
    STAmount const& holderShares,
    bool waiveUnrealizedLoss = false)
{
    auto lawful = VaultFFI::build(state);
    if (!lawful)
        return {.leanError = LeanError::notLawful};
    return readVaultResult(leanCall(
        lean_vault_clawback,
        *lawful,
        STAmountFFI::build(assets),
        STAmountFFI::build(holderShares),
        static_cast<uint8_t>(waiveUnrealizedLoss ? 1 : 0)));
}

// Owner-burn: destroy `sharesDestroyed` shares, returning the new lawful vault state (sharesTotal).
struct LeanBurnResult
{
    std::optional<LeanError> leanError;
    std::optional<TER> error;
    Vault vault;
};

inline LeanBurnResult
leanBurnShares(Vault const& state, STAmount const& sharesDestroyed)
{
    auto lawful = VaultFFI::build(state);
    if (!lawful)
        return {.leanError = LeanError::notLawful};
    LeanExcept<TerExceptFFI> const e = readExcept<TerExceptFFI>(
        leanCall(lean_vault_burn_shares, *lawful, STAmountFFI::build(sharesDestroyed)));
    if (!e.value)
        return {.leanError = e.error};
    if (auto const ter = e.value->ter(lean_ter_vault_code))
        return {.error = ter};
    return {.vault = e.value->value<VaultFFI>(lean_ter_vault_value)->read()};
}

// The shares an owner burn would destroy (all outstanding), or the TER that forbids it.
inline LeanAmountResult
leanCanBurnShares(Vault const& state, STAmount const& amount, STAmount const& holderShares)
{
    auto lawful = VaultFFI::build(state);
    if (!lawful)
        return {.leanError = LeanError::notLawful};
    return readAmountResult(leanCall(
        lean_can_burn_shares,
        *lawful,
        STAmountFFI::build(amount),
        STAmountFFI::build(holderShares)));
}
}  // namespace xrpl::test::formal_verification
