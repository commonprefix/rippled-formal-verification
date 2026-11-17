#pragma once

#include <test/formal_verification/ffi/LeanObjectFFI.h>
#include <test/formal_verification/ffi/protocol/STAmountFFI.h>
#include <test/formal_verification/ffi/vault/VaultFFI.h>

#include <xrpl/protocol/STAmount.h>

#include <lean/lean.h>

#include <cstdint>

extern "C" {
lean_object*
lean_vault_deposit(
    lean_object* v,
    lean_object* amount,
    uint8_t isDonation,
    uint32_t parentCloseTime);
lean_object*
lean_rounded_deposit_amount(lean_object* vault, lean_object* amount);
}

namespace xrpl::test::formal_verification {

inline LeanVaultResult
leanVaultDeposit(
    Vault const& state,
    STAmount const& amount,
    bool isDonation,
    std::uint32_t parentCloseTime)
{
    auto lawful = VaultFFI::build(state);
    if (!lawful)
        return {.leanError = LeanError::notLawful};
    return readVaultResult(leanCall(
        lean_vault_deposit,
        *lawful,
        STAmountFFI::build(amount),
        static_cast<uint8_t>(isDonation ? 1 : 0),
        parentCloseTime));
}

// Rounding result: exactly one of amount (rounded) / error (rejected TER, e.g.
// tecPRECISION_LOSS) is set, unless the model errors.
inline LeanAmountResult
leanRoundedDepositAmount(Vault const& state, STAmount const& amount)
{
    auto lawful = VaultFFI::build(state);
    if (!lawful)
        return {.leanError = LeanError::notLawful};
    return readAmountResult(
        leanCall(lean_rounded_deposit_amount, *lawful, STAmountFFI::build(amount)));
}
}  // namespace xrpl::test::formal_verification
