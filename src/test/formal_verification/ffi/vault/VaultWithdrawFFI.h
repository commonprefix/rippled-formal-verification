#pragma once

#include <test/formal_verification/ffi/LeanObjectFFI.h>
#include <test/formal_verification/ffi/protocol/STAmountFFI.h>
#include <test/formal_verification/ffi/vault/VaultFFI.h>

#include <xrpl/protocol/STAmount.h>

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
lean_vault_withdraw(
    lean_object* v,
    lean_object* amount,
    uint8_t waiveUnrealizedLoss,
    uint32_t parentCloseTime);
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

inline LeanVaultResult
leanVaultWithdraw(
    Vault const& state,
    STAmount const& amount,
    bool byShares,
    std::uint32_t parentCloseTime,
    bool waiveUnrealizedLoss = false)
{
    auto lawful = VaultFFI::build(state);
    if (!lawful)
        return {.leanError = LeanError::notLawful};
    return readVaultResult(leanCall(
        lean_vault_withdraw,
        *lawful,
        WithdrawAmountFFI::build(amount, byShares),
        static_cast<std::uint8_t>(waiveUnrealizedLoss ? 1 : 0),
        parentCloseTime));
}
}  // namespace xrpl::test::formal_verification
