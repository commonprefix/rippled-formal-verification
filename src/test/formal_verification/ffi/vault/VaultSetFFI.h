#pragma once

#include <test/formal_verification/ffi/LeanObjectFFI.h>
#include <test/formal_verification/ffi/protocol/NumberFFI.h>
#include <test/formal_verification/ffi/vault/VaultFFI.h>

#include <xrpl/basics/Number.h>

#include <lean/lean.h>

#include <cstdint>
#include <optional>

extern "C" {
lean_object*
lean_can_vault_update(
    lean_object* vault,
    lean_object* assetsMaximum,
    uint8_t blockDeposit,
    uint8_t unblockDeposit);
}

namespace xrpl::test::formal_verification {

[[nodiscard]] inline LawfulTerResult
leanCanVaultUpdate(
    Vault const& state,
    std::optional<Number> const& assetsMaximum,
    bool blockDeposit = false,
    bool unblockDeposit = false)
{
    auto lawful = VaultFFI::build(state);
    if (!lawful)
        return {.leanError = LeanError::notLawful};
    return readTerCode(leanCall(
        lean_can_vault_update,
        *lawful,
        assetsMaximum ? leanSome(NumberFFI::build(*assetsMaximum)) : leanNone(),
        static_cast<uint8_t>(blockDeposit ? 1 : 0),
        static_cast<uint8_t>(unblockDeposit ? 1 : 0)));
}

}  // namespace xrpl::test::formal_verification
