#pragma once

#include <test/formal_verification/common/Result.h>
#include <test/formal_verification/ffi/vault/state.h>

#include <xrpl/protocol/TER.h>

#include <lean/lean.h>

#include <optional>

extern "C" {
lean_object*
lean_can_deposit(lean_object* state, lean_object* amount, lean_object* accountBalance);
}

namespace xrpl::test::formal_verification {

inline LeanTerResult
leanCanDeposit(
    VaultState const& state,
    STAmount const& amount,
    std::optional<STAmount> accountBalance)
{
    lean_object* raw = leanCall(
        lean_can_deposit,
        VaultStateFFI::build(state),
        STAmountFFI::build(amount),
        leanOptHandle<STAmountFFI>(accountBalance));

    return LeanTerResult::fromLean(raw);
}

}  // namespace xrpl::test::formal_verification
