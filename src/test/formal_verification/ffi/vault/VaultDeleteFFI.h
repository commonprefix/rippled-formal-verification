#pragma once

#include <test/formal_verification/ffi/LeanObjectFFI.h>
#include <test/formal_verification/ffi/vault/VaultFFI.h>

#include <xrpl/protocol/TER.h>

#include <lean/lean.h>

#include <cstdint>

extern "C" {
int32_t
lean_can_vault_delete(lean_object* vault);
}

namespace xrpl::test::formal_verification {

[[nodiscard]] inline LawfulTerResult
leanCanVaultDelete(Vault const& state)
{
    auto lawful = VaultFFI::build(state);
    if (!lawful)
        return {.leanError = LeanError::notLawful};
    int32_t const code = leanCall(lean_can_vault_delete, *lawful);
    return {.ter = TER::fromInt(code)};
}

}  // namespace xrpl::test::formal_verification
