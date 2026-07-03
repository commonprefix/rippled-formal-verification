#pragma once

#include <test/formal_verification/common/Result.h>
#include <test/formal_verification/ffi/vault/state.h>

#include <xrpl/protocol/TER.h>

#include <lean/lean.h>

#include <optional>

extern "C" {
lean_object*
lean_rounded_deposit_amount(lean_object* state, lean_object* amount);
}

namespace xrpl::test::formal_verification {

inline LeanRoundedDepositResult
leanRoundedDepositAmount(VaultState const& state, STAmount const& amount)
{
    return LeanRoundedDepositResult::fromLean(leanCall(
        lean_rounded_deposit_amount, VaultStateFFI::build(state), STAmountFFI::build(amount)));
}

}  // namespace xrpl::test::formal_verification
