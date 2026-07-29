#pragma once

#include <test/formal_verification/ffi/LeanObjectFFI.h>
#include <test/formal_verification/ffi/protocol/NumberFFI.h>
#include <test/formal_verification/ffi/protocol/NumericTypeFFI.h>
#include <test/formal_verification/ffi/vault/VaultStateFFI.h>

#include <xrpl/basics/Number.h>

#include <lean/lean.h>

#include <cstdint>

extern "C" {
lean_object*
lean_vault_create(
    uint8_t hasMaximum,
    lean_object* assetsMaximum,
    lean_object* numericType,
    uint8_t scale);
}

namespace xrpl::test::formal_verification {

// The vault state Vault.create initializes. assetsMaximum is meaningful only when hasMaximum.
[[nodiscard]] inline VaultState
leanVaultCreate(
    bool hasMaximum,
    Number const& assetsMaximum,
    std::uint8_t numericType,
    std::uint8_t scale)
{
    return VaultStateFFI(leanCall(
                             lean_vault_create,
                             static_cast<std::uint8_t>(hasMaximum),
                             NumberFFI::build(assetsMaximum),
                             NumericTypeFFI::build(numericType),
                             scale))
        .read();
}

}  // namespace xrpl::test::formal_verification
