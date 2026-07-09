#pragma once

#include <test/formal_verification/common/Result.h>
#include <test/formal_verification/ffi/vault/state.h>

#include <xrpl/basics/Number.h>
#include <xrpl/protocol/Asset.h>
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
}

namespace xrpl::test::formal_verification {

// Rounded-deposit result in C++ primitives. amount carries the vault asset (valid when !threw and
// no error); error holds the rejection TER (e.g. tecPRECISION_LOSS) when set.
struct LeanRoundedDepositAmountResult
{
    bool threw{};
    std::optional<TER> error;
    STAmount amount;
};

// Raw parse of FFIRoundedDepositResult. status: 0 = ok, 1 = threw. code: 0 = rounded, else the
// rejection TER. 8-byte group @0,8,16; 1-byte group @24,25,26. decode() resolves the concrete
// vault asset the FFI can't carry.
struct LeanRoundedDepositAmountResultFFI
{
    uint8_t status;
    int64_t code;
    uint8_t assetKind;
    uint64_t mValue;
    int64_t mOffset;
    bool mIsNegative;

    [[nodiscard]] LeanRoundedDepositAmountResult
    decode(Asset const& asset) const
    {
        auto const amount = [&]() -> STAmount {
            if (asset.native() && mOffset == 0)
                return STAmount{mValue, mIsNegative};
            return STAmount{asset, mValue, static_cast<int>(mOffset), mIsNegative};
        };
        return {
            .threw = status == 1,
            .error = code != 0 ? std::optional<TER>{TER::fromInt(static_cast<int32_t>(code))}
                               : std::nullopt,
            .amount = amount(),
        };
    }

    static LeanRoundedDepositAmountResultFFI
    fromLean(lean_object* obj)
    {
        LeanObjOwner const guard{obj};
        return {
            .status = lean_ctor_get_uint8(obj, 26),
            .code = static_cast<int64_t>(lean_ctor_get_uint64(obj, 0)),
            .assetKind = lean_ctor_get_uint8(obj, 24),
            .mValue = lean_ctor_get_uint64(obj, 8),
            .mOffset = static_cast<int64_t>(lean_ctor_get_uint64(obj, 16)),
            .mIsNegative = lean_ctor_get_uint8(obj, 25) != 0,
        };
    }
};

// Vault deposit result in C++ primitives. amountDeposit'/sharesIssued carry the vault asset and
// the share MPT respectively; newState is the full post-deposit vault state. Fields are only
// meaningful when !threw; error holds the model's TER when the deposit was rejected.
struct LeanDepositResult
{
    bool threw{};
    std::optional<TER> error;
    STAmount amountDeposit;
    STAmount sharesIssued;
    VaultState newState;
};

// Raw parse of FFIDepositResult. status: 0 = ok, 1 = threw. hasError: TER in `code`.
// 8-byte group @0,8,…,80; 1-byte group @88..96. decode() turns it into the usable
// LeanDepositResult, folding the changed totals into the caller's pre-deposit vault state.
struct LeanDepositResultFFI
{
    uint8_t status;
    bool hasError;
    int64_t code;
    uint8_t amountKind;
    uint64_t amountValue;
    int64_t amountOffset;
    bool amountNegative;
    uint8_t sharesKind;
    uint64_t sharesValue;
    int64_t sharesOffset;
    bool sharesNegative;
    uint64_t assetsTotalMantissa;
    int64_t assetsTotalExponent;
    bool assetsTotalNegative;
    uint64_t assetsAvailableMantissa;
    int64_t assetsAvailableExponent;
    bool assetsAvailableNegative;
    uint64_t sharesTotalMantissa;
    int64_t sharesTotalExponent;
    bool sharesTotalNegative;

    // `state` is the pre-deposit vault; the deposit only changes the totals, so the new state is
    // `state` with assetsTotal/assetsAvailable/sharesTotal overwritten by the model's results.
    [[nodiscard]] LeanDepositResult
    decode(VaultState const& state) const
    {
        auto const stAmount = [](Asset const& a, uint64_t value, int64_t offset, bool negative) {
            if (a.native() && offset == 0)
                return STAmount{value, negative};
            return STAmount{a, value, static_cast<int>(offset), negative};
        };
        auto const number = [](uint64_t mantissa, int64_t exponent, bool negative) {
            auto const m = static_cast<std::int64_t>(mantissa);
            return Number{negative ? -m : m, static_cast<int>(exponent)};
        };
        VaultState newState = state;
        newState.assetsTotal =
            number(assetsTotalMantissa, assetsTotalExponent, assetsTotalNegative);
        newState.assetsAvailable =
            number(assetsAvailableMantissa, assetsAvailableExponent, assetsAvailableNegative);
        newState.sharesTotal =
            number(sharesTotalMantissa, sharesTotalExponent, sharesTotalNegative);
        return {
            .threw = status == 1,
            .error = hasError ? std::optional<TER>{TER::fromInt(static_cast<int32_t>(code))}
                              : std::nullopt,
            .amountDeposit = stAmount(state.asset, amountValue, amountOffset, amountNegative),
            .sharesIssued = stAmount(state.sharesAsset, sharesValue, sharesOffset, sharesNegative),
            .newState = newState,
        };
    }

    static LeanDepositResultFFI
    fromLean(lean_object* obj)
    {
        LeanObjOwner const guard{obj};
        return {
            .status = lean_ctor_get_uint8(obj, 96),
            .hasError = lean_ctor_get_uint8(obj, 95) != 0,
            .code = static_cast<int64_t>(lean_ctor_get_uint64(obj, 80)),
            .amountKind = lean_ctor_get_uint8(obj, 88),
            .amountValue = lean_ctor_get_uint64(obj, 0),
            .amountOffset = static_cast<int64_t>(lean_ctor_get_uint64(obj, 8)),
            .amountNegative = lean_ctor_get_uint8(obj, 89) != 0,
            .sharesKind = lean_ctor_get_uint8(obj, 90),
            .sharesValue = lean_ctor_get_uint64(obj, 16),
            .sharesOffset = static_cast<int64_t>(lean_ctor_get_uint64(obj, 24)),
            .sharesNegative = lean_ctor_get_uint8(obj, 91) != 0,
            .assetsTotalMantissa = lean_ctor_get_uint64(obj, 32),
            .assetsTotalExponent = static_cast<int64_t>(lean_ctor_get_uint64(obj, 40)),
            .assetsTotalNegative = lean_ctor_get_uint8(obj, 92) != 0,
            .assetsAvailableMantissa = lean_ctor_get_uint64(obj, 48),
            .assetsAvailableExponent = static_cast<int64_t>(lean_ctor_get_uint64(obj, 56)),
            .assetsAvailableNegative = lean_ctor_get_uint8(obj, 93) != 0,
            .sharesTotalMantissa = lean_ctor_get_uint64(obj, 64),
            .sharesTotalExponent = static_cast<int64_t>(lean_ctor_get_uint64(obj, 72)),
            .sharesTotalNegative = lean_ctor_get_uint8(obj, 94) != 0,
        };
    }
};

inline LeanDepositResult
leanVaultDeposit(VaultState const& state, STAmount const& amount, bool isDonation)
{
    return LeanDepositResultFFI::fromLean(leanCall(
                                              lean_vault_deposit,
                                              VaultStateFFI::build(state),
                                              STAmountFFI::build(amount),
                                              static_cast<uint8_t>(isDonation ? 1 : 0)))
        .decode(state);
}

inline LeanRoundedDepositAmountResult
leanRoundedDepositAmount(VaultState const& state, STAmount const& amount)
{
    return LeanRoundedDepositAmountResultFFI::fromLean(leanCall(
                                                           lean_rounded_deposit_amount,
                                                           VaultStateFFI::build(state),
                                                           STAmountFFI::build(amount)))
        .decode(state.asset);
}

// TEMPORARY (rounding-mode probe): rounded deposit with the roundToScale mode chosen by caller.
inline LeanRoundedDepositAmountResult
leanRoundedDepositAmountMode(
    VaultState const& state,
    STAmount const& amount,
    Number::RoundingMode mode)
{
    return LeanRoundedDepositAmountResultFFI::fromLean(leanCall(
                                                           lean_rounded_deposit_amount_mode,
                                                           VaultStateFFI::build(state),
                                                           STAmountFFI::build(amount),
                                                           toLeanMode(mode)))
        .decode(state.asset);
}

// TEMPORARY (rounding-mode probe): both the scale-computation mode and the final roundToScale
// mode chosen by caller. Production is (ToNearest, Downward).
inline LeanRoundedDepositAmountResult
leanRoundedDepositAmountModes(
    VaultState const& state,
    STAmount const& amount,
    Number::RoundingMode scaleRounding,
    Number::RoundingMode roundMode)
{
    return LeanRoundedDepositAmountResultFFI::fromLean(leanCall(
                                                           lean_rounded_deposit_amount_modes,
                                                           VaultStateFFI::build(state),
                                                           STAmountFFI::build(amount),
                                                           toLeanMode(scaleRounding),
                                                           toLeanMode(roundMode)))
        .decode(state.asset);
}

}  // namespace xrpl::test::formal_verification
