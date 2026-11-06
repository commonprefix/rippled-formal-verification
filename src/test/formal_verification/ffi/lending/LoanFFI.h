#pragma once

#include <test/formal_verification/ffi/LeanObjectFFI.h>
#include <test/formal_verification/ffi/lending/LoanBrokerFFI.h>
#include <test/formal_verification/ffi/protocol/NumberFFI.h>
#include <test/formal_verification/ffi/vault/VaultFFI.h>

#include <xrpl/basics/Number.h>
#include <xrpl/protocol/TER.h>

#include <lean/lean.h>

#include <cstdint>
#include <optional>

namespace xrpl::test::formal_verification {

// The model's loan, with the broker it belongs to. The schedule's payment total is a LoanSet
// field only, so the test carries it.
struct Loan
{
    LoanBroker broker;
    std::uint32_t interestRate{};
    std::uint32_t lateInterestRate{};
    std::uint32_t closeInterestRate{};
    std::uint32_t overpaymentInterestRate{};
    std::uint32_t overpaymentFee{};
    Number originationFee{};
    Number serviceFee{};
    Number latePaymentFee{};
    Number closePaymentFee{};
    std::uint32_t paymentInterval{};
    std::uint32_t paymentTotal{};
    std::uint32_t gracePeriod{};
    std::uint32_t startDate{};
    std::uint32_t paymentRemaining{};
    Number periodicPayment{};
    Number principalOutstanding{};
    Number totalValueOutstanding{};
    Number managementFeeOutstanding{};
    std::int32_t loanScale{};
    std::uint32_t previousPaymentDueDate{};
    std::uint32_t nextPaymentDueDate{};
    bool isPending{};
    bool isImpaired{};
    bool isDefault{};
    bool allowsOverpayment{};
};

// The LoanSet transaction fields the model reads. A start date makes it a two-step proposal.
struct LoanSetArgs
{
    Number principal{};
    std::uint32_t interestRate{};
    std::uint32_t lateInterestRate{};
    std::uint32_t closeInterestRate{};
    std::uint32_t overpaymentInterestRate{};
    std::uint32_t overpaymentFee{};
    Number originationFee{};
    Number serviceFee{};
    Number latePaymentFee{};
    Number closePaymentFee{};
    std::optional<std::uint32_t> paymentInterval;
    std::optional<std::uint32_t> paymentTotal;
    std::optional<std::uint32_t> gracePeriod;
    std::optional<std::uint32_t> startDate;
    bool allowsOverpayment{};
};

enum class PaymentType : std::uint8_t { regular = 0, late = 1, full = 2, overpayment = 3 };
enum class ManageAction : std::uint8_t { impair = 0, unimpair = 1, defaultLoan = 2 };

extern "C" {
lean_object*
lean_loan_build(
    lean_object* broker,
    uint32_t interestRate,
    uint32_t lateInterestRate,
    uint32_t closeInterestRate,
    uint32_t overpaymentInterestRate,
    uint32_t overpaymentFee,
    lean_object* originationFee,
    lean_object* serviceFee,
    lean_object* latePaymentFee,
    lean_object* closePaymentFee,
    uint32_t paymentInterval,
    uint32_t paymentTotal,
    uint32_t gracePeriod,
    uint32_t startDate,
    uint32_t paymentRemaining,
    lean_object* periodicPayment,
    lean_object* principalOutstanding,
    lean_object* totalValueOutstanding,
    lean_object* managementFeeOutstanding,
    int32_t loanScale,
    uint32_t previousPaymentDueDate,
    uint32_t nextPaymentDueDate,
    uint8_t isPending,
    uint8_t isImpaired,
    uint8_t isDefault,
    uint8_t allowsOverpayment);
lean_object*
lean_loan_broker(lean_object* loan);
uint32_t
lean_loan_payment_remaining(lean_object* loan);
lean_object*
lean_loan_periodic_payment(lean_object* loan);
lean_object*
lean_loan_principal_outstanding(lean_object* loan);
lean_object*
lean_loan_total_value_outstanding(lean_object* loan);
lean_object*
lean_loan_management_fee_outstanding(lean_object* loan);
int32_t
lean_loan_scale(lean_object* loan);
uint32_t
lean_loan_previous_payment_due_date(lean_object* loan);
uint32_t
lean_loan_next_payment_due_date(lean_object* loan);
uint8_t
lean_loan_is_pending(lean_object* loan);
uint8_t
lean_loan_is_impaired(lean_object* loan);
uint8_t
lean_loan_is_default(lean_object* loan);
uint8_t
lean_loan_allows_overpayment(lean_object* loan);

lean_object*
lean_can_loan_create(
    lean_object* broker,
    lean_object* pool,
    lean_object* principal,
    lean_object* originationFee,
    lean_object* serviceFee,
    lean_object* latePaymentFee,
    lean_object* closePaymentFee,
    lean_object* paymentInterval,
    lean_object* paymentTotal,
    lean_object* gracePeriod,
    uint32_t startDate,
    uint32_t ledgerCloseTime,
    uint32_t parentCloseTime,
    uint8_t twoStep);
lean_object*
lean_loan_create(
    lean_object* broker,
    lean_object* pool,
    lean_object* principal,
    uint32_t interestRate,
    uint32_t lateInterestRate,
    uint32_t closeInterestRate,
    uint32_t overpaymentInterestRate,
    uint32_t overpaymentFee,
    lean_object* originationFee,
    lean_object* serviceFee,
    lean_object* latePaymentFee,
    lean_object* closePaymentFee,
    lean_object* paymentInterval,
    lean_object* paymentTotal,
    lean_object* gracePeriod,
    uint32_t startDate,
    uint32_t ledgerCloseTime,
    uint8_t twoStep,
    uint8_t allowsOverpayment);
lean_object*
lean_can_loan_accept(lean_object* loan, lean_object* pool, uint32_t parentCloseTime);
lean_object*
lean_loan_accept(lean_object* loan, lean_object* pool);
lean_object*
lean_can_loan_pay(lean_object* loan, uint8_t paymentType);
lean_object*
lean_loan_pay(
    lean_object* loan,
    lean_object* pool,
    uint8_t paymentType,
    lean_object* amount,
    uint32_t now);
lean_object*
lean_can_loan_manage(lean_object* loan, uint8_t action, uint32_t now);
lean_object*
lean_loan_manage(lean_object* loan, lean_object* pool, uint8_t action, uint32_t now);
lean_object*
lean_can_loan_delete(lean_object* loan);
lean_object*
lean_loan_delete(lean_object* loan, lean_object* pool);

lean_object*
lean_ter_loan_amounts_code(lean_object* r);
lean_object*
lean_ter_loan_amounts_value(lean_object* r);
lean_object*
lean_loan_amounts_loan(lean_object* r);
lean_object*
lean_loan_amounts_pool(lean_object* r);
lean_object*
lean_loan_amounts_to_pool(lean_object* r);
lean_object*
lean_loan_amounts_to_broker(lean_object* r);
lean_object*
lean_ter_broker_pool_code(lean_object* r);
lean_object*
lean_ter_broker_pool_value(lean_object* r);
lean_object*
lean_broker_pool_broker(lean_object* r);
lean_object*
lean_broker_pool_pool(lean_object* r);
}

class LoanFFI : public LeanObjectFFI
{
public:
    using LeanObjectFFI::LeanObjectFFI;
    using CppType = Loan;

    // Validate the fields; `nullopt` if the model rejects the loan or its broker (not lawful).
    static std::optional<LoanFFI>
    build(Loan const& s)
    {
        auto broker = LoanBrokerFFI::build(s.broker);
        if (!broker)
            return std::nullopt;
        auto e = readExcept<LoanFFI>(leanCall(
            lean_loan_build,
            *broker,
            s.interestRate,
            s.lateInterestRate,
            s.closeInterestRate,
            s.overpaymentInterestRate,
            s.overpaymentFee,
            NumberFFI::build(s.originationFee),
            NumberFFI::build(s.serviceFee),
            NumberFFI::build(s.latePaymentFee),
            NumberFFI::build(s.closePaymentFee),
            s.paymentInterval,
            s.paymentTotal,
            s.gracePeriod,
            s.startDate,
            s.paymentRemaining,
            NumberFFI::build(s.periodicPayment),
            NumberFFI::build(s.principalOutstanding),
            NumberFFI::build(s.totalValueOutstanding),
            NumberFFI::build(s.managementFeeOutstanding),
            s.loanScale,
            s.previousPaymentDueDate,
            s.nextPaymentDueDate,
            static_cast<uint8_t>(s.isPending ? 1 : 0),
            static_cast<uint8_t>(s.isImpaired ? 1 : 0),
            static_cast<uint8_t>(s.isDefault ? 1 : 0),
            static_cast<uint8_t>(s.allowsOverpayment ? 1 : 0)));
        return std::move(e.value);
    }

    // Read the mutable fields back; the configuration fields are copied from `like` since the
    // model never changes them.
    Loan
    read(Loan const& like) const
    {
        Loan l = like;
        l.broker = leanGetWrapped<LoanBrokerFFI>(lean_loan_broker).read(like.broker.numericType);
        l.paymentRemaining = leanGet(lean_loan_payment_remaining);
        l.periodicPayment = leanGetObj<NumberFFI>(lean_loan_periodic_payment);
        l.principalOutstanding = leanGetObj<NumberFFI>(lean_loan_principal_outstanding);
        l.totalValueOutstanding = leanGetObj<NumberFFI>(lean_loan_total_value_outstanding);
        l.managementFeeOutstanding = leanGetObj<NumberFFI>(lean_loan_management_fee_outstanding);
        l.loanScale = leanGet(lean_loan_scale);
        l.previousPaymentDueDate = leanGet(lean_loan_previous_payment_due_date);
        l.nextPaymentDueDate = leanGet(lean_loan_next_payment_due_date);
        l.isPending = leanGet(lean_loan_is_pending) != 0;
        l.isImpaired = leanGet(lean_loan_is_impaired) != 0;
        l.isDefault = leanGet(lean_loan_is_default) != 0;
        l.allowsOverpayment = leanGet(lean_loan_allows_overpayment) != 0;
        return l;
    }
};

// A loan operation result: the loan, its pool and the amounts moved, set only when neither error
// is.
struct LeanLoanResult
{
    std::optional<LeanError> leanError;
    std::optional<TER> error;
    Loan loan;
    Vault pool;
    Number amountToPool{};
    Number amountToBroker{};
};

class LoanAmountsFFI : public LeanObjectFFI
{
public:
    using LeanObjectFFI::LeanObjectFFI;

    LeanLoanResult
    read(Loan const& like) const
    {
        return {
            .loan = leanGetWrapped<LoanFFI>(lean_loan_amounts_loan).read(like),
            .pool = leanGetObj<VaultFFI>(lean_loan_amounts_pool),
            .amountToPool = leanGetObj<NumberFFI>(lean_loan_amounts_to_pool),
            .amountToBroker = leanGetObj<NumberFFI>(lean_loan_amounts_to_broker)};
    }
};

// Unpack an owned `Except Error (Except TER (LoanWithAmounts Vault))`.
inline LeanLoanResult
readLoanResult(lean_object* owned, Loan const& like)
{
    LeanExcept<TerExceptFFI> const e = readExcept<TerExceptFFI>(owned);
    if (!e.value)
        return {.leanError = e.error};
    if (auto const ter = e.value->ter(lean_ter_loan_amounts_code))
        return {.error = ter};
    return e.value->value<LoanAmountsFFI>(lean_ter_loan_amounts_value)->read(like);
}

// A LoanDelete result: the broker and its pool.
struct LeanBrokerPoolResult
{
    std::optional<LeanError> leanError;
    std::optional<TER> error;
    LoanBroker broker;
    Vault pool;
};

class BrokerPoolFFI : public LeanObjectFFI
{
public:
    using LeanObjectFFI::LeanObjectFFI;

    LeanBrokerPoolResult
    read(std::uint8_t numericType) const
    {
        return {
            .broker = leanGetWrapped<LoanBrokerFFI>(lean_broker_pool_broker).read(numericType),
            .pool = leanGetObj<VaultFFI>(lean_broker_pool_pool)};
    }
};

inline LeanBrokerPoolResult
readBrokerPoolResult(lean_object* owned, std::uint8_t numericType)
{
    LeanExcept<TerExceptFFI> const e = readExcept<TerExceptFFI>(owned);
    if (!e.value)
        return {.leanError = e.error};
    if (auto const ter = e.value->ter(lean_ter_broker_pool_code))
        return {.error = ter};
    return e.value->value<BrokerPoolFFI>(lean_ter_broker_pool_value)->read(numericType);
}

struct LoanAndPool
{
    LoanFFI loan;
    VaultFFI pool;
};

inline std::optional<LoanAndPool>
buildLoanAndPool(Loan const& loan, Vault const& pool)
{
    auto l = LoanFFI::build(loan);
    auto v = VaultFFI::build(pool);
    if (!l || !v)
        return std::nullopt;
    return LoanAndPool{std::move(*l), std::move(*v)};
}

[[nodiscard]] inline LawfulTerResult
leanCanLoanCreate(
    LoanBroker const& broker,
    Vault const& pool,
    LoanSetArgs const& a,
    std::uint32_t ledgerCloseTime,
    std::uint32_t parentCloseTime)
{
    auto h = buildBrokerAndPool(broker, pool);
    if (!h)
        return {.leanError = LeanError::notLawful};
    return readTerCode(leanCall(
        lean_can_loan_create,
        h->broker,
        h->pool,
        NumberFFI::build(a.principal),
        NumberFFI::build(a.originationFee),
        NumberFFI::build(a.serviceFee),
        NumberFFI::build(a.latePaymentFee),
        NumberFFI::build(a.closePaymentFee),
        leanOptU32(a.paymentInterval),
        leanOptU32(a.paymentTotal),
        leanOptU32(a.gracePeriod),
        a.startDate.value_or(0),
        ledgerCloseTime,
        parentCloseTime,
        static_cast<uint8_t>(a.startDate ? 1 : 0)));
}

// `like` supplies the configuration fields of the loan the model builds (the test knows them).
[[nodiscard]] inline LeanLoanResult
leanLoanCreate(
    LoanBroker const& broker,
    Vault const& pool,
    LoanSetArgs const& a,
    std::uint32_t ledgerCloseTime,
    Loan const& like)
{
    auto h = buildBrokerAndPool(broker, pool);
    if (!h)
        return {.leanError = LeanError::notLawful};
    return readLoanResult(
        leanCall(
            lean_loan_create,
            h->broker,
            h->pool,
            NumberFFI::build(a.principal),
            a.interestRate,
            a.lateInterestRate,
            a.closeInterestRate,
            a.overpaymentInterestRate,
            a.overpaymentFee,
            NumberFFI::build(a.originationFee),
            NumberFFI::build(a.serviceFee),
            NumberFFI::build(a.latePaymentFee),
            NumberFFI::build(a.closePaymentFee),
            leanOptU32(a.paymentInterval),
            leanOptU32(a.paymentTotal),
            leanOptU32(a.gracePeriod),
            a.startDate.value_or(0),
            ledgerCloseTime,
            static_cast<uint8_t>(a.startDate ? 1 : 0),
            static_cast<uint8_t>(a.allowsOverpayment ? 1 : 0)),
        like);
}

[[nodiscard]] inline LawfulTerResult
leanCanLoanAccept(Loan const& loan, Vault const& pool, std::uint32_t parentCloseTime)
{
    auto h = buildLoanAndPool(loan, pool);
    if (!h)
        return {.leanError = LeanError::notLawful};
    return readTerCode(leanCall(lean_can_loan_accept, h->loan, h->pool, parentCloseTime));
}

[[nodiscard]] inline LeanLoanResult
leanLoanAccept(Loan const& loan, Vault const& pool)
{
    auto h = buildLoanAndPool(loan, pool);
    if (!h)
        return {.leanError = LeanError::notLawful};
    return readLoanResult(leanCall(lean_loan_accept, h->loan, h->pool), loan);
}

[[nodiscard]] inline LawfulTerResult
leanCanLoanPay(Loan const& loan, PaymentType type)
{
    auto l = LoanFFI::build(loan);
    if (!l)
        return {.leanError = LeanError::notLawful};
    return readTerCode(leanCall(lean_can_loan_pay, *l, static_cast<uint8_t>(type)));
}

[[nodiscard]] inline LeanLoanResult
leanLoanPay(
    Loan const& loan,
    Vault const& pool,
    PaymentType type,
    Number const& amount,
    std::uint32_t now)
{
    auto h = buildLoanAndPool(loan, pool);
    if (!h)
        return {.leanError = LeanError::notLawful};
    return readLoanResult(
        leanCall(
            lean_loan_pay,
            h->loan,
            h->pool,
            static_cast<uint8_t>(type),
            NumberFFI::build(amount),
            now),
        loan);
}

[[nodiscard]] inline LawfulTerResult
leanCanLoanManage(Loan const& loan, ManageAction action, std::uint32_t now)
{
    auto l = LoanFFI::build(loan);
    if (!l)
        return {.leanError = LeanError::notLawful};
    return readTerCode(leanCall(lean_can_loan_manage, *l, static_cast<uint8_t>(action), now));
}

[[nodiscard]] inline LeanLoanResult
leanLoanManage(Loan const& loan, Vault const& pool, ManageAction action, std::uint32_t now)
{
    auto h = buildLoanAndPool(loan, pool);
    if (!h)
        return {.leanError = LeanError::notLawful};
    return readLoanResult(
        leanCall(lean_loan_manage, h->loan, h->pool, static_cast<uint8_t>(action), now), loan);
}

[[nodiscard]] inline LawfulTerResult
leanCanLoanDelete(Loan const& loan)
{
    auto l = LoanFFI::build(loan);
    if (!l)
        return {.leanError = LeanError::notLawful};
    return readTerCode(leanCall(lean_can_loan_delete, *l));
}

[[nodiscard]] inline LeanBrokerPoolResult
leanLoanDelete(Loan const& loan, Vault const& pool)
{
    auto h = buildLoanAndPool(loan, pool);
    if (!h)
        return {.leanError = LeanError::notLawful};
    return readBrokerPoolResult(
        leanCall(lean_loan_delete, h->loan, h->pool), loan.broker.numericType);
}

}  // namespace xrpl::test::formal_verification
