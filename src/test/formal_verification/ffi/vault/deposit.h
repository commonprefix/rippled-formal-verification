#pragma once

#include <test/formal_verification/common/Result.h>
#include <test/formal_verification/ffi/vault/state.h>

#include <xrpl/protocol/TER.h>

#include <lean/lean.h>

#include <stdexcept>

extern "C" {
lean_object*
lean_can_deposit(lean_object* state, lean_object* amount, bool accountIsIssuer);
}

namespace xrpl::test::formal_verification {

inline TER
leanCanDeposit(VaultState const& state, STAmount const& amount, bool accountIsIssuer)
{
    lean_object* raw = leanCall(
        lean_can_deposit, VaultStateFFI::build(state), STAmountFFI::build(amount), accountIsIssuer);

    LeanTerResult const result = LeanTerResult::fromLean(raw);
    if (result.threw)
    {
        throw std::runtime_error("Lean canDeposit model error");
    }

    return TER::fromInt(result.code);
}

}  // namespace xrpl::test::formal_verification
