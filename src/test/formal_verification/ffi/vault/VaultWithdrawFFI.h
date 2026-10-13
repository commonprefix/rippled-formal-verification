#pragma once

#include <test/formal_verification/ffi/LeanObjectFFI.h>
#include <test/formal_verification/ffi/protocol/STAmountFFI.h>
#include <test/formal_verification/ffi/vault/VaultFFI.h>

#include <xrpl/protocol/STAmount.h>
#include <xrpl/protocol/TER.h>

#include <lean/lean.h>

#include <cstdint>
#include <optional>

extern "C" {
lean_object*
lean_shares_to_assets_withdraw(
    lean_object* vault,
    lean_object* shares,
    uint8_t waiveUnrealizedLoss);
lean_object*
lean_mk_withdraw_amount(lean_object* amount, uint8_t byShares);
lean_object*
lean_vault_withdraw(lean_object* v, lean_object* amount, uint8_t waiveUnrealizedLoss);

lean_object*
lean_withdraw_result_assets(lean_object* r);
lean_object*
lean_withdraw_result_shares(lean_object* r);
lean_object*
lean_withdraw_result_vault(lean_object* r);
lean_object*
lean_withdraw_result_error(lean_object* r);
}

namespace xrpl::test::formal_verification {

class WithdrawAmountFFI : public LeanObjectFFI
{
public:
    using LeanObjectFFI::LeanObjectFFI;

    static WithdrawAmountFFI
    build(STAmount const& amount, bool byShares)
    {
        return WithdrawAmountFFI(leanCall(
            lean_mk_withdraw_amount,
            STAmountFFI::build(amount),
            static_cast<std::uint8_t>(byShares ? 1 : 0)));
    }
};

// Shares-to-assets conversion result. The assets are valid only when no leanError.
struct LeanSharesToAssetsResult
{
    std::optional<LeanError> leanError;
    STAmount assets;
};

inline LeanSharesToAssetsResult
leanSharesToAssetsWithdraw(Vault const& state, STAmount const& shares, bool waiveUnrealizedLoss)
{
    auto lawful = VaultFFI::build(state);
    if (!lawful)
        return {.leanError = LeanError::notLawful, .assets = STAmount{}};
    LeanExcept<STAmountFFI> const e = readExcept<STAmountFFI>(leanCall(
        lean_shares_to_assets_withdraw,
        *lawful,
        STAmountFFI::build(shares),
        static_cast<uint8_t>(waiveUnrealizedLoss ? 1 : 0)));
    if (!e.value)
        return {.leanError = e.error, .assets = STAmount{}};
    return {.assets = e.value->read()};
}

struct LeanWithdrawResult
{
    std::optional<LeanError> leanError;
    std::optional<TER> error;
    STAmount assets{};
    STAmount shares{};
    Vault vault;
};

class WithdrawResultFFI : public LeanObjectFFI
{
public:
    using LeanObjectFFI::LeanObjectFFI;

    LeanWithdrawResult
    read() const
    {
        auto const error = leanGetOptU32(lean_withdraw_result_error);
        return {
            .error = error ? std::optional<TER>{TER::fromInt(static_cast<std::int32_t>(*error))}
                           : std::nullopt,
            .assets = leanGetObj<STAmountFFI>(lean_withdraw_result_assets),
            .shares = leanGetObj<STAmountFFI>(lean_withdraw_result_shares),
            .vault = leanGetObj<VaultFFI>(lean_withdraw_result_vault),
        };
    }
};

inline LeanWithdrawResult
leanVaultWithdraw(
    Vault const& state,
    STAmount const& amount,
    bool byShares,
    bool waiveUnrealizedLoss = false)
{
    auto lawful = VaultFFI::build(state);
    if (!lawful)
        return {.leanError = LeanError::notLawful};
    LeanExcept<WithdrawResultFFI> const e = readExcept<WithdrawResultFFI>(leanCall(
        lean_vault_withdraw,
        *lawful,
        WithdrawAmountFFI::build(amount, byShares),
        static_cast<std::uint8_t>(waiveUnrealizedLoss ? 1 : 0)));
    if (!e.value)
        return {.leanError = e.error};
    return e.value->read();
}
}  // namespace xrpl::test::formal_verification
