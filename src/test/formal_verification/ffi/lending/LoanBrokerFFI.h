#pragma once

#include <test/formal_verification/ffi/LeanObjectFFI.h>
#include <test/formal_verification/ffi/protocol/NumberFFI.h>
#include <test/formal_verification/ffi/protocol/NumericTypeFFI.h>
#include <test/formal_verification/ffi/protocol/STAmountFFI.h>
#include <test/formal_verification/ffi/vault/VaultFFI.h>

#include <xrpl/basics/Number.h>
#include <xrpl/protocol/STAmount.h>
#include <xrpl/protocol/TER.h>

#include <lean/lean.h>

#include <cstdint>
#include <optional>

namespace xrpl::test::formal_verification {

// The model's loan broker. Amounts are in the vault asset; loanCount is the broker's owner count.
struct LoanBroker
{
    // 3-way tag from the vault asset: 0 = native (XRP), 1 = int64 (MPT), 2 = fractional (IOU).
    std::uint8_t numericType{};
    std::uint16_t managementFeeRate{};
    std::uint32_t coverRateMinimum{};
    std::uint32_t coverRateLiquidation{};
    Number debtTotal{};
    Number debtMaximum{};
    Number coverAvailable{};
    std::uint32_t loanCount{};
};

// The LoanBrokerSet fields the model reads on create.
struct LoanBrokerSetArgs
{
    std::optional<Number> debtMaximum;
    std::optional<std::uint16_t> managementFeeRate;
    std::optional<std::uint32_t> coverRateMinimum;
    std::optional<std::uint32_t> coverRateLiquidation;
};

extern "C" {
lean_object*
lean_loan_broker_build(
    lean_object* numericType,
    uint16_t managementFeeRate,
    uint32_t coverRateMinimum,
    uint32_t coverRateLiquidation,
    lean_object* debtTotal,
    lean_object* debtMaximum,
    lean_object* coverAvailable,
    uint32_t loanCount);
uint16_t
lean_loan_broker_management_fee_rate(lean_object* lb);
uint32_t
lean_loan_broker_cover_rate_minimum(lean_object* lb);
uint32_t
lean_loan_broker_cover_rate_liquidation(lean_object* lb);
lean_object*
lean_loan_broker_debt_total(lean_object* lb);
lean_object*
lean_loan_broker_debt_maximum(lean_object* lb);
lean_object*
lean_loan_broker_cover_available(lean_object* lb);
uint32_t
lean_loan_broker_loan_count(lean_object* lb);

lean_object*
lean_can_loan_broker_create(lean_object* pool, lean_object* debtMaximum, lean_object* numericType);
lean_object*
lean_loan_broker_create(
    lean_object* debtMaximum,
    lean_object* managementFeeRate,
    lean_object* coverRateMinimum,
    lean_object* coverRateLiquidation,
    lean_object* numericType);
lean_object*
lean_can_loan_broker_update(lean_object* lb, lean_object* pool, lean_object* debtMaximum);
lean_object*
lean_loan_broker_update(lean_object* lb, lean_object* debtMaximum);

lean_object*
lean_can_cover_deposit(lean_object* lb, lean_object* pool, lean_object* amount);
lean_object*
lean_cover_deposit(lean_object* lb, lean_object* pool, lean_object* amount);
lean_object*
lean_can_cover_withdraw(lean_object* lb, lean_object* pool, lean_object* amount);
lean_object*
lean_cover_withdraw(lean_object* lb, lean_object* pool, lean_object* amount);
lean_object*
lean_can_cover_clawback(lean_object* lb, lean_object* pool, lean_object* amount);
lean_object*
lean_cover_clawback(lean_object* lb, lean_object* pool, lean_object* amount);

lean_object*
lean_can_loan_broker_delete(lean_object* lb, lean_object* pool);
lean_object*
lean_loan_broker_rounded_cover(lean_object* lb);

lean_object*
lean_ter_cover_result_code(lean_object* r);
lean_object*
lean_ter_cover_result_value(lean_object* r);
lean_object*
lean_cover_result_amount(lean_object* r);
lean_object*
lean_cover_result_broker(lean_object* r);
}

class LoanBrokerFFI : public LeanObjectFFI
{
public:
    using LeanObjectFFI::LeanObjectFFI;
    using CppType = LoanBroker;

    // Validate the fields; `nullopt` if the model rejects them (not lawful).
    static std::optional<LoanBrokerFFI>
    build(LoanBroker const& state)
    {
        auto e = readExcept<LoanBrokerFFI>(leanCall(
            lean_loan_broker_build,
            NumericTypeFFI::build(state.numericType),
            state.managementFeeRate,
            state.coverRateMinimum,
            state.coverRateLiquidation,
            NumberFFI::build(state.debtTotal),
            NumberFFI::build(state.debtMaximum),
            NumberFFI::build(state.coverAvailable),
            state.loanCount));
        return std::move(e.value);
    }

    // Read the fields of this lawful handle. The numeric type is not read back: the model's tag
    // is only recoverable through the vault, and the caller already knows the asset.
    LoanBroker
    read(std::uint8_t numericType) const
    {
        return LoanBroker{
            .numericType = numericType,
            .managementFeeRate = leanGet(lean_loan_broker_management_fee_rate),
            .coverRateMinimum = leanGet(lean_loan_broker_cover_rate_minimum),
            .coverRateLiquidation = leanGet(lean_loan_broker_cover_rate_liquidation),
            .debtTotal = leanGetObj<NumberFFI>(lean_loan_broker_debt_total),
            .debtMaximum = leanGetObj<NumberFFI>(lean_loan_broker_debt_maximum),
            .coverAvailable = leanGetObj<NumberFFI>(lean_loan_broker_cover_available),
            .loanCount = leanGet(lean_loan_broker_loan_count)};
    }
};

inline lean_object*
leanOptU16(std::optional<std::uint16_t> const& o)
{
    return o ? leanSome(lean_box(*o)) : leanNone();
}

inline lean_object*
leanOptNumber(std::optional<Number> const& o)
{
    return o ? leanSome(NumberFFI::build(*o)) : leanNone();
}

// A broker the model built (create/update), or the model error (notLawful: an invariant breaks).
struct LeanBrokerResult
{
    std::optional<LeanError> leanError;
    LoanBroker broker;
};

// A cover operation result: the amount moved and the post-operation broker, set only when neither
// error is.
struct LeanCoverResult
{
    std::optional<LeanError> leanError;
    std::optional<TER> error;
    STAmount amount{};
    LoanBroker broker;
};

class CoverResultFFI : public LeanObjectFFI
{
public:
    using LeanObjectFFI::LeanObjectFFI;

    LeanCoverResult
    read(std::uint8_t numericType) const
    {
        return {
            .amount = leanGetObj<STAmountFFI>(lean_cover_result_amount),
            .broker = leanGetWrapped<LoanBrokerFFI>(lean_cover_result_broker).read(numericType)};
    }
};

// Unpack an owned `Except Error (Except TER LoanBrokerCoverResult)`.
inline LeanCoverResult
readCoverResult(lean_object* owned, std::uint8_t numericType)
{
    LeanExcept<TerExceptFFI> const e = readExcept<TerExceptFFI>(owned);
    if (!e.value)
        return {.leanError = e.error};
    if (auto const ter = e.value->ter(lean_ter_cover_result_code))
        return {.error = ter};
    return e.value->value<CoverResultFFI>(lean_ter_cover_result_value)->read(numericType);
}

// Build both handles; nullopt when either state is not lawful.
struct BrokerAndPool
{
    LoanBrokerFFI broker;
    VaultFFI pool;
};

inline std::optional<BrokerAndPool>
buildBrokerAndPool(LoanBroker const& broker, Vault const& pool)
{
    auto lb = LoanBrokerFFI::build(broker);
    auto v = VaultFFI::build(pool);
    if (!lb || !v)
        return std::nullopt;
    return BrokerAndPool{std::move(*lb), std::move(*v)};
}

[[nodiscard]] inline LawfulTerResult
leanCanLoanBrokerCreate(
    Vault const& pool,
    std::optional<Number> const& debtMaximum,
    std::uint8_t numericType)
{
    auto v = VaultFFI::build(pool);
    if (!v)
        return {.leanError = LeanError::notLawful};
    return readTerCode(leanCall(
        lean_can_loan_broker_create,
        *v,
        leanOptNumber(debtMaximum),
        NumericTypeFFI::build(numericType)));
}

[[nodiscard]] inline LeanBrokerResult
leanLoanBrokerCreate(LoanBrokerSetArgs const& args, std::uint8_t numericType)
{
    LeanExcept<LoanBrokerFFI> const e = readExcept<LoanBrokerFFI>(leanCall(
        lean_loan_broker_create,
        leanOptNumber(args.debtMaximum),
        leanOptU16(args.managementFeeRate),
        leanOptU32(args.coverRateMinimum),
        leanOptU32(args.coverRateLiquidation),
        NumericTypeFFI::build(numericType)));
    if (!e.value)
        return {.leanError = e.error};
    return {.broker = e.value->read(numericType)};
}

[[nodiscard]] inline LawfulTerResult
leanCanLoanBrokerUpdate(
    LoanBroker const& broker,
    Vault const& pool,
    std::optional<Number> const& debtMaximum)
{
    auto h = buildBrokerAndPool(broker, pool);
    if (!h)
        return {.leanError = LeanError::notLawful};
    return readTerCode(
        leanCall(lean_can_loan_broker_update, h->broker, h->pool, leanOptNumber(debtMaximum)));
}

[[nodiscard]] inline LeanBrokerResult
leanLoanBrokerUpdate(LoanBroker const& broker, std::optional<Number> const& debtMaximum)
{
    auto lb = LoanBrokerFFI::build(broker);
    if (!lb)
        return {.leanError = LeanError::notLawful};
    LeanExcept<LoanBrokerFFI> const e = readExcept<LoanBrokerFFI>(
        leanCall(lean_loan_broker_update, *lb, leanOptNumber(debtMaximum)));
    if (!e.value)
        return {.leanError = e.error};
    return {.broker = e.value->read(broker.numericType)};
}

[[nodiscard]] inline LawfulTerResult
leanCanCoverDeposit(LoanBroker const& broker, Vault const& pool, STAmount const& amount)
{
    auto h = buildBrokerAndPool(broker, pool);
    if (!h)
        return {.leanError = LeanError::notLawful};
    return readTerCode(
        leanCall(lean_can_cover_deposit, h->broker, h->pool, STAmountFFI::build(amount)));
}

[[nodiscard]] inline LeanCoverResult
leanCoverDeposit(LoanBroker const& broker, Vault const& pool, STAmount const& amount)
{
    auto h = buildBrokerAndPool(broker, pool);
    if (!h)
        return {.leanError = LeanError::notLawful};
    return readCoverResult(
        leanCall(lean_cover_deposit, h->broker, h->pool, STAmountFFI::build(amount)),
        broker.numericType);
}

[[nodiscard]] inline LawfulTerResult
leanCanCoverWithdraw(LoanBroker const& broker, Vault const& pool, STAmount const& amount)
{
    auto h = buildBrokerAndPool(broker, pool);
    if (!h)
        return {.leanError = LeanError::notLawful};
    return readTerCode(
        leanCall(lean_can_cover_withdraw, h->broker, h->pool, STAmountFFI::build(amount)));
}

[[nodiscard]] inline LeanCoverResult
leanCoverWithdraw(LoanBroker const& broker, Vault const& pool, STAmount const& amount)
{
    auto h = buildBrokerAndPool(broker, pool);
    if (!h)
        return {.leanError = LeanError::notLawful};
    return readCoverResult(
        leanCall(lean_cover_withdraw, h->broker, h->pool, STAmountFFI::build(amount)),
        broker.numericType);
}

inline lean_object*
leanOptAmount(std::optional<STAmount> const& o)
{
    return o ? leanSome(STAmountFFI::build(*o)) : leanNone();
}

[[nodiscard]] inline LawfulTerResult
leanCanCoverClawback(
    LoanBroker const& broker,
    Vault const& pool,
    std::optional<STAmount> const& amount)
{
    auto h = buildBrokerAndPool(broker, pool);
    if (!h)
        return {.leanError = LeanError::notLawful};
    return readTerCode(
        leanCall(lean_can_cover_clawback, h->broker, h->pool, leanOptAmount(amount)));
}

[[nodiscard]] inline LeanCoverResult
leanCoverClawback(
    LoanBroker const& broker,
    Vault const& pool,
    std::optional<STAmount> const& amount)
{
    auto h = buildBrokerAndPool(broker, pool);
    if (!h)
        return {.leanError = LeanError::notLawful};
    return readCoverResult(
        leanCall(lean_cover_clawback, h->broker, h->pool, leanOptAmount(amount)),
        broker.numericType);
}

[[nodiscard]] inline LawfulTerResult
leanCanLoanBrokerDelete(LoanBroker const& broker, Vault const& pool)
{
    auto h = buildBrokerAndPool(broker, pool);
    if (!h)
        return {.leanError = LeanError::notLawful};
    return readTerCode(leanCall(lean_can_loan_broker_delete, h->broker, h->pool));
}

// The cover LoanBrokerDelete returns to the owner, or the model error.
struct LeanRoundedCoverResult
{
    std::optional<LeanError> leanError;
    STAmount amount{};
};

[[nodiscard]] inline LeanRoundedCoverResult
leanLoanBrokerRoundedCover(LoanBroker const& broker)
{
    auto lb = LoanBrokerFFI::build(broker);
    if (!lb)
        return {.leanError = LeanError::notLawful};
    LeanExcept<STAmountFFI> const e =
        readExcept<STAmountFFI>(leanCall(lean_loan_broker_rounded_cover, *lb));
    if (!e.value)
        return {.leanError = e.error};
    return {.amount = e.value->read()};
}

}  // namespace xrpl::test::formal_verification
