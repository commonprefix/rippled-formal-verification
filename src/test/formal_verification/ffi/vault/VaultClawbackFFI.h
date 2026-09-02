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
lean_vault_clawback(lean_object* v, lean_object* assets, lean_object* holderShares);
lean_object*
lean_vault_burn_shares(lean_object* v, lean_object* sharesDestroyed);
lean_object*
lean_can_burn_shares(lean_object* vault);

lean_object*
lean_clawback_result_assets(lean_object* r);
lean_object*
lean_clawback_result_shares(lean_object* r);
lean_object*
lean_clawback_result_vault(lean_object* r);
lean_object*
lean_clawback_result_error(lean_object* r);

lean_object*
lean_can_burn_result_assets(lean_object* r);
lean_object*
lean_can_burn_result_code(lean_object* r);
}

namespace xrpl::test::formal_verification {

struct LeanClawbackResult
{
    std::optional<LeanError> leanError;
    std::optional<TER> error;
    STAmount assets{};
    STAmount shares{};
    Vault vault;
};

class ClawbackResultFFI : public LeanObjectFFI
{
public:
    using LeanObjectFFI::LeanObjectFFI;

    LeanClawbackResult
    read() const
    {
        auto const error = leanGetOptU32(lean_clawback_result_error);
        return {
            .error = error ? std::optional<TER>{TER::fromInt(static_cast<std::int32_t>(*error))}
                           : std::nullopt,
            .assets = leanGetObj<STAmountFFI>(lean_clawback_result_assets),
            .shares = leanGetObj<STAmountFFI>(lean_clawback_result_shares),
            .vault = leanGetObj<VaultFFI>(lean_clawback_result_vault),
        };
    }
};

inline LeanClawbackResult
leanVaultClawback(Vault const& state, STAmount const& assets, STAmount const& holderShares)
{
    auto lawful = VaultFFI::build(state);
    if (!lawful)
        return {.leanError = LeanError::notLawful};
    LeanExcept<ClawbackResultFFI> const e = readExcept<ClawbackResultFFI>(leanCall(
        lean_vault_clawback,
        *lawful,
        STAmountFFI::build(assets),
        STAmountFFI::build(holderShares)));
    if (!e.value)
        return {.leanError = e.error};
    return e.value->read();
}

// Owner-burn: destroy `sharesDestroyed` shares, returning the new lawful vault state (sharesTotal).
struct LeanBurnResult
{
    std::optional<LeanError> leanError;
    Vault vault;
};

inline LeanBurnResult
leanBurnShares(Vault const& state, STAmount const& sharesDestroyed)
{
    auto lawful = VaultFFI::build(state);
    if (!lawful)
        return {.leanError = LeanError::notLawful};
    LeanExcept<VaultFFI> const e = readExcept<VaultFFI>(
        leanCall(lean_vault_burn_shares, *lawful, STAmountFFI::build(sharesDestroyed)));
    if (!e.value)
        return {.leanError = e.error};
    return {.vault = e.value->read()};
}

struct LeanCanBurnResult
{
    std::optional<LeanError> leanError;
    std::optional<TER> error;
    std::optional<STAmount> assets;
};

class CanBurnResultFFI : public LeanObjectFFI
{
public:
    using LeanObjectFFI::LeanObjectFFI;

    LeanCanBurnResult
    read() const
    {
        auto const code = leanGetOptU32(lean_can_burn_result_code);
        return {
            .error = code ? std::optional<TER>{TER::fromInt(static_cast<std::int32_t>(*code))}
                          : std::nullopt,
            .assets = leanGetOpt<STAmountFFI>(lean_can_burn_result_assets),
        };
    }
};

inline LeanCanBurnResult
leanCanBurnShares(Vault const& state)
{
    auto lawful = VaultFFI::build(state);
    if (!lawful)
        return {.leanError = LeanError::notLawful, .error = std::nullopt, .assets = std::nullopt};
    LeanExcept<CanBurnResultFFI> const e =
        readExcept<CanBurnResultFFI>(leanCall(lean_can_burn_shares, *lawful));
    if (!e.value)
        return {.leanError = e.error, .error = std::nullopt, .assets = std::nullopt};
    return e.value->read();
}
}  // namespace xrpl::test::formal_verification
