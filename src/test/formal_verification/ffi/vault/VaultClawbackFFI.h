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
lean_vault_clawback(lean_object* state, lean_object* assets, lean_object* holderShares);
lean_object*
lean_vault_burn_shares(lean_object* state, lean_object* sharesDestroyed);
lean_object*
lean_can_burn_shares(lean_object* state);

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
    bool threw{};
    std::optional<TER> error;
    STAmount assets;
    STAmount shares;
    VaultState vault;
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
            .threw = false,
            .error = error ? std::optional<TER>{TER::fromInt(static_cast<std::int32_t>(*error))}
                           : std::nullopt,
            .assets = leanGetObj<STAmountFFI>(lean_clawback_result_assets),
            .shares = leanGetObj<STAmountFFI>(lean_clawback_result_shares),
            .vault = leanGetObj<VaultStateFFI>(lean_clawback_result_vault),
        };
    }
};

inline LeanClawbackResult
leanVaultClawback(VaultState const& state, STAmount const& assets, STAmount const& holderShares)
{
    LeanExcept<ClawbackResultFFI> const e = readExcept<ClawbackResultFFI>(leanCall(
        lean_vault_clawback,
        VaultStateFFI::build(state),
        STAmountFFI::build(assets),
        STAmountFFI::build(holderShares)));
    if (!e.value)
    {
        LeanClawbackResult result;
        result.threw = true;
        return result;
    }
    return e.value->read();
}

// Owner-burn: destroy `sharesDestroyed` shares, returning the new vault state (sharesTotal only).
struct LeanBurnResult
{
    bool threw{};
    VaultState vault;
};

inline LeanBurnResult
leanBurnShares(VaultState const& state, STAmount const& sharesDestroyed)
{
    LeanExcept<VaultStateFFI> const e = readExcept<VaultStateFFI>(leanCall(
        lean_vault_burn_shares, VaultStateFFI::build(state), STAmountFFI::build(sharesDestroyed)));
    if (!e.value)
    {
        LeanBurnResult result;
        result.threw = true;
        return result;
    }
    return {.threw = false, .vault = e.value->read()};
}

struct LeanCanBurnResult
{
    bool threw{};
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
            .threw = false,
            .error = code ? std::optional<TER>{TER::fromInt(static_cast<std::int32_t>(*code))}
                          : std::nullopt,
            .assets = leanGetOpt<STAmountFFI>(lean_can_burn_result_assets),
        };
    }
};

inline LeanCanBurnResult
leanCanBurnShares(VaultState const& state)
{
    LeanExcept<CanBurnResultFFI> const e =
        readExcept<CanBurnResultFFI>(leanCall(lean_can_burn_shares, VaultStateFFI::build(state)));
    if (!e.value)
        return {.threw = true, .error = std::nullopt, .assets = std::nullopt};
    return e.value->read();
}
}  // namespace xrpl::test::formal_verification
