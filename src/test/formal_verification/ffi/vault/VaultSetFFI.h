#pragma once

#include <test/formal_verification/ffi/LeanObjectFFI.h>
#include <test/formal_verification/ffi/protocol/NumberFFI.h>
#include <test/formal_verification/ffi/vault/VaultFFI.h>

#include <xrpl/basics/Number.h>
#include <xrpl/protocol/TER.h>

#include <lean/lean.h>

#include <cstdint>

extern "C" {
int32_t
lean_can_vault_set(lean_object* vault, lean_object* assetsMaximum);
}

namespace xrpl::test::formal_verification {

[[nodiscard]] inline LawfulTerResult
leanCanVaultSet(Vault const& state, Number const& assetsMaximum)
{
    auto lawful = VaultFFI::build(state);
    if (!lawful)
        return {.leanError = LeanError::notLawful};
    int32_t const code = leanCall(lean_can_vault_set, *lawful, NumberFFI::build(assetsMaximum));
    return {.ter = TER::fromInt(code)};
}

}  // namespace xrpl::test::formal_verification
