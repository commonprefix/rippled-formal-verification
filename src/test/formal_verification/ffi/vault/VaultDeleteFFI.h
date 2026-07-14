#pragma once

#include <test/formal_verification/ffi/LeanObjectFFI.h>
#include <test/formal_verification/ffi/vault/VaultStateFFI.h>

#include <xrpl/protocol/TER.h>

#include <lean/lean.h>

#include <cstdint>

extern "C" {
int32_t
lean_can_vault_delete(lean_object* vault);
}

namespace xrpl::test::formal_verification {

[[nodiscard]] inline TER
leanCanVaultDelete(VaultState const& state)
{
    int32_t const code = leanCall(lean_can_vault_delete, VaultStateFFI::build(state));
    return TER::fromInt(code);
}

}  // namespace xrpl::test::formal_verification
