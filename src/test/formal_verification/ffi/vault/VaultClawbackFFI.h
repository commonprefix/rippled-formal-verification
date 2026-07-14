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
lean_mk_clawback_amount(lean_object* amount, uint8_t byShares);
lean_object*
lean_vault_clawback(lean_object* state, lean_object* amount);
lean_object*
lean_can_clawback_vault_shares(lean_object* state);

lean_object*
lean_clawback_result_assets(lean_object* r);
lean_object*
lean_clawback_result_shares(lean_object* r);
lean_object*
lean_clawback_result_vault(lean_object* r);
lean_object*
lean_clawback_result_error(lean_object* r);

lean_object*
lean_can_clawback_result_assets(lean_object* r);
lean_object*
lean_can_clawback_result_code(lean_object* r);
}

namespace xrpl::test::formal_verification {

class ClawbackAmountFFI : public LeanObjectFFI
{
public:
    using LeanObjectFFI::LeanObjectFFI;

    static ClawbackAmountFFI
    build(STAmount const& amount, bool byShares)
    {
        return ClawbackAmountFFI(leanCall(
            lean_mk_clawback_amount,
            STAmountFFI::build(amount),
            static_cast<std::uint8_t>(byShares ? 1 : 0)));
    }
};

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
leanVaultClawback(VaultState const& state, STAmount const& amount, bool byShares)
{
    LeanExcept<ClawbackResultFFI> const e = readExcept<ClawbackResultFFI>(leanCall(
        lean_vault_clawback,
        VaultStateFFI::build(state),
        ClawbackAmountFFI::build(amount, byShares)));
    if (!e.value)
    {
        LeanClawbackResult result;
        result.threw = true;
        return result;
    }
    return e.value->read();
}

struct LeanCanClawbackResult
{
    bool threw{};
    std::optional<TER> error;
    std::optional<STAmount> assets;
};

class CanClawbackResultFFI : public LeanObjectFFI
{
public:
    using LeanObjectFFI::LeanObjectFFI;

    LeanCanClawbackResult
    read() const
    {
        auto const code = leanGetOptU32(lean_can_clawback_result_code);
        return {
            .threw = false,
            .error = code ? std::optional<TER>{TER::fromInt(static_cast<std::int32_t>(*code))}
                          : std::nullopt,
            .assets = leanGetOpt<STAmountFFI>(lean_can_clawback_result_assets),
        };
    }
};

inline LeanCanClawbackResult
leanCanClawbackVaultShares(VaultState const& state)
{
    LeanExcept<CanClawbackResultFFI> const e = readExcept<CanClawbackResultFFI>(
        leanCall(lean_can_clawback_vault_shares, VaultStateFFI::build(state)));
    if (!e.value)
        return {.threw = true, .error = std::nullopt, .assets = std::nullopt};
    return e.value->read();
}
}  // namespace xrpl::test::formal_verification
