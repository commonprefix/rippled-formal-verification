#pragma once

#include <test/formal_verification/ffi/LeanObjectFFI.h>
#include <test/formal_verification/ffi/protocol/STAmountFFI.h>
#include <test/formal_verification/ffi/vault/VaultStateFFI.h>

#include <xrpl/protocol/STAmount.h>
#include <xrpl/protocol/TER.h>

#include <lean/lean.h>

#include <cstdint>
#include <optional>

extern "C" {
lean_object*
lean_vault_deposit(lean_object* state, lean_object* amount, uint8_t isDonation);
lean_object*
lean_rounded_deposit_amount(lean_object* state, lean_object* amount);

lean_object*
lean_rounded_deposit_result_amount(lean_object* r);
lean_object*
lean_rounded_deposit_result_code(lean_object* r);

lean_object*
lean_deposit_result_amount(lean_object* r);
lean_object*
lean_deposit_result_shares(lean_object* r);
lean_object*
lean_deposit_result_vault(lean_object* r);
lean_object*
lean_deposit_result_error(lean_object* r);
}

namespace xrpl::test::formal_verification {

// Rounding result. Exactly one of amount (rounded) / error (rejected TER, e.g.
// tecPRECISION_LOSS) is set, unless threw (the model raised).
struct LeanRoundingResult
{
    bool threw{};
    std::optional<TER> error;
    std::optional<STAmount> amount;
};

class RoundingResultFFI : public LeanObjectFFI
{
public:
    using LeanObjectFFI::LeanObjectFFI;

    LeanRoundingResult
    read() const
    {
        auto const code = leanGetOptU32(lean_rounded_deposit_result_code);
        return {
            .threw = false,
            .error = code ? std::optional<TER>{TER::fromInt(static_cast<std::int32_t>(*code))}
                          : std::nullopt,
            .amount = leanGetOpt<STAmountFFI>(lean_rounded_deposit_result_amount),
        };
    }
};

// Vault deposit result. amountDeposit/sharesIssued carry the vault asset and the share MPT.
// Vault is the full post-deposit vault state.
struct LeanDepositResult
{
    bool threw{};
    std::optional<TER> error;
    STAmount amountDeposit;
    STAmount sharesIssued;
    VaultState vault;
};

class DepositResultFFI : public LeanObjectFFI
{
public:
    using LeanObjectFFI::LeanObjectFFI;

    LeanDepositResult
    read() const
    {
        auto const error = leanGetOptU32(lean_deposit_result_error);
        return {
            .threw = false,
            .error = error ? std::optional<TER>{TER::fromInt(static_cast<std::int32_t>(*error))}
                           : std::nullopt,
            .amountDeposit = leanGetObj<STAmountFFI>(lean_deposit_result_amount),
            .sharesIssued = leanGetObj<STAmountFFI>(lean_deposit_result_shares),
            .vault = leanGetObj<VaultStateFFI>(lean_deposit_result_vault),
        };
    }
};

inline LeanDepositResult
leanVaultDeposit(VaultState const& state, STAmount const& amount, bool isDonation)
{
    LeanExcept<DepositResultFFI> const e = readExcept<DepositResultFFI>(leanCall(
        lean_vault_deposit,
        VaultStateFFI::build(state),
        STAmountFFI::build(amount),
        static_cast<uint8_t>(isDonation ? 1 : 0)));
    if (!e.value)
    {
        LeanDepositResult result;
        result.threw = true;
        return result;
    }
    return e.value->read();
}

inline LeanRoundingResult
leanRoundedDepositAmount(VaultState const& state, STAmount const& amount)
{
    LeanExcept<RoundingResultFFI> const e = readExcept<RoundingResultFFI>(leanCall(
        lean_rounded_deposit_amount, VaultStateFFI::build(state), STAmountFFI::build(amount)));
    if (!e.value)
        return {.threw = true, .error = std::nullopt, .amount = std::nullopt};
    return e.value->read();
}
}  // namespace xrpl::test::formal_verification
