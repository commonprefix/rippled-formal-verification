#pragma once

#include <test/formal_verification/ffi/LeanObjectFFI.h>
#include <test/formal_verification/ffi/vault/VaultFFI.h>

#include <lean/lean.h>

extern "C" {
lean_object*
lean_can_vault_delete(lean_object* vault);
}

namespace xrpl::test::formal_verification {

[[nodiscard]] inline LawfulTerResult
leanCanVaultDelete(Vault const& state)
{
    auto lawful = VaultFFI::build(state);
    if (!lawful)
        return {.leanError = LeanError::notLawful};
    return readTerCode(leanCall(lean_can_vault_delete, *lawful));
}

}  // namespace xrpl::test::formal_verification
