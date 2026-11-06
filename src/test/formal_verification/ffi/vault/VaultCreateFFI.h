#pragma once

#include <test/formal_verification/ffi/LeanObjectFFI.h>
#include <test/formal_verification/ffi/protocol/NumberFFI.h>
#include <test/formal_verification/ffi/protocol/NumericTypeFFI.h>
#include <test/formal_verification/ffi/vault/VaultFFI.h>

#include <xrpl/basics/Number.h>

#include <lean/lean.h>

#include <cstdint>
#include <optional>

extern "C" {
lean_object*
lean_can_vault_create(
    lean_object* scale,
    lean_object* assetsMaximum,
    lean_object* subscriptionDate,
    lean_object* redemptionDate,
    uint32_t parentCloseTime,
    lean_object* numericType);
lean_object*
lean_vault_create(
    lean_object* scale,
    lean_object* assetsMaximum,
    lean_object* subscriptionDate,
    lean_object* redemptionDate,
    lean_object* earlyExitFeeRate,
    uint8_t ownerCanBlockDeposit,
    lean_object* numericType);
}

namespace xrpl::test::formal_verification {

// The VaultCreate transaction fields the model reads.
struct VaultCreateArgs
{
    std::optional<std::uint8_t> scale;
    std::optional<Number> assetsMaximum;
    std::optional<std::uint32_t> subscriptionDate;
    std::optional<std::uint32_t> redemptionDate;
    std::optional<std::uint32_t> earlyExitFeeRate;
    bool ownerCanBlockDeposit{};
    // 3-way tag from the underlying asset: 0 = native (XRP), 1 = int64 (MPT), 2 = fractional (IOU).
    std::uint8_t numericType{};
};

[[nodiscard]] inline LawfulTerResult
leanCanVaultCreate(VaultCreateArgs const& args, std::uint32_t parentCloseTime)
{
    return readTerCode(leanCall(
        lean_can_vault_create,
        leanOptU8(args.scale),
        args.assetsMaximum ? leanSome(NumberFFI::build(*args.assetsMaximum)) : leanNone(),
        leanOptU32(args.subscriptionDate),
        leanOptU32(args.redemptionDate),
        parentCloseTime,
        NumericTypeFFI::build(args.numericType)));
}

// The empty vault VaultCreate writes, or the model error (notLawful: the fields break an
// invariant).
struct LeanCreateResult
{
    std::optional<LeanError> leanError;
    Vault vault;
};

[[nodiscard]] inline LeanCreateResult
leanVaultCreate(VaultCreateArgs const& args)
{
    LeanExcept<VaultFFI> const e = readExcept<VaultFFI>(leanCall(
        lean_vault_create,
        leanOptU8(args.scale),
        args.assetsMaximum ? leanSome(NumberFFI::build(*args.assetsMaximum)) : leanNone(),
        leanOptU32(args.subscriptionDate),
        leanOptU32(args.redemptionDate),
        leanOptU32(args.earlyExitFeeRate),
        static_cast<uint8_t>(args.ownerCanBlockDeposit ? 1 : 0),
        NumericTypeFFI::build(args.numericType)));
    if (!e.value)
        return {.leanError = e.error};
    return {.vault = e.value->read()};
}

}  // namespace xrpl::test::formal_verification
