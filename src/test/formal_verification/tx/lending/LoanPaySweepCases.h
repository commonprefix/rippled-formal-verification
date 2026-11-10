#pragma once

#include <test/formal_verification/common/Sweep.h>
#include <test/formal_verification/tx/lending/LendingTestHelpers.h>

#include <algorithm>
#include <cstdint>
#include <string>
#include <vector>

// Cusp rows for the LoanPay, LoanManage and Loan sweeps. The staging they use is in
// LendingTestHelpers.h.
namespace xrpl::test::formal_verification::loan_pay_sweep {

// ---- LoanPay rows. Loans have no interest and two installments unless a row says otherwise. ----

constexpr std::int64_t kOrdinary = 1'000'000'000;
// The sweep vaults hold 9e9 units, the largest principal any row borrows.
constexpr std::int64_t kSweepSeed = 9'000'000'000;

// A payment of `amount` when the next payment falls due `dueOffset` seconds after the parent
// close time. Regular, full and overpayments are late (tecEXPIRED) once dueOffset < 0; a late
// payment is too soon (tecTOO_SOON) while dueOffset >= 0. The amount is the exact amount due.
struct DueDateCusp
{
    PaymentType type;
    std::int64_t principal;
    std::int64_t dueOffset;
    std::int64_t amount;
};

[[nodiscard]] constexpr std::int64_t
exactDue(PaymentType type, std::int64_t principal)
{
    return type == PaymentType::full ? principal : principal / 2;
}

constexpr DueDateCusp kDueDateCusps[] = {
    {PaymentType::regular, 2, 0, 1},
    {PaymentType::regular, 2 * kOrdinary, 0, kOrdinary},
    {PaymentType::regular, kSweepSeed, 0, kSweepSeed / 2},
    {PaymentType::late, 2, 0, 1},
    {PaymentType::late, 2 * kOrdinary, 0, kOrdinary},
    {PaymentType::late, kSweepSeed, 0, kSweepSeed / 2},
    {PaymentType::full, 2, 0, 2},
    {PaymentType::full, 2 * kOrdinary, 0, 2 * kOrdinary},
    {PaymentType::full, kSweepSeed, 0, kSweepSeed},
    {PaymentType::overpayment, 2, 0, 1},
    {PaymentType::overpayment, 2 * kOrdinary, 0, kOrdinary},
    {PaymentType::overpayment, kSweepSeed, 0, kSweepSeed / 2},
};

[[nodiscard]] constexpr bool
onDueDateCusp(DueDateCusp const& c)
{
    return c.dueOffset == 0 && c.principal % 2 == 0 && c.amount == exactDue(c.type, c.principal);
}

static_assert(std::ranges::all_of(kDueDateCusps, onDueDateCusp));

// A late payment of `amount` `lateBy` seconds after the due date, at a 100% late interest rate:
// principal 31'536'000 * k makes the late interest exactly k * lateBy units, so the amount due is
// principal / installments + service fee + late fee + k * lateBy. Below it is
// tecINSUFFICIENT_PAYMENT; lateBy <= 0 is not late (tecTOO_SOON).
constexpr std::int64_t kSecondsPerYear = 31'536'000;

struct LateInterestCusp
{
    std::int64_t k;
    std::uint32_t installments;
    std::int64_t serviceFee;
    std::int64_t lateFee;
    std::int64_t lateBy;
    std::int64_t amount;
};

constexpr LateInterestCusp kLateInterestCusps[] = {
    {1, 2, 0, 0, 1, kSecondsPerYear / 2 + 1},
    {32, 2, 0, 0, 1'000, 32 * kSecondsPerYear / 2 + 32'000},
    {285, 1, 0, 0, 1, 285 * kSecondsPerYear + 285},
    {1, 2, kOrdinary, 0, 1, kSecondsPerYear / 2 + kOrdinary + 1},
    {1, 2, 0, kOrdinary, 1, kSecondsPerYear / 2 + kOrdinary + 1},
};

[[nodiscard]] constexpr bool
onLateInterestCusp(LateInterestCusp const& c)
{
    std::int64_t const principal = kSecondsPerYear * c.k;
    return principal % c.installments == 0 && principal <= kSweepSeed &&
        c.amount == principal / c.installments + c.serviceFee + c.lateFee + c.k * c.lateBy;
}

static_assert(std::ranges::all_of(kLateInterestCusps, onLateInterestCusp));

// A regular payment of `amount` against one installment plus its service fee: below it is
// tecINSUFFICIENT_PAYMENT.
struct ServiceFeeCusp
{
    std::int64_t installment;
    std::int64_t serviceFee;
    std::int64_t amount;
};

constexpr ServiceFeeCusp kServiceFeeCusps[] = {
    {1, kOrdinary - 1, kOrdinary},
    {kOrdinary - 1, 1, kOrdinary},
    {kOrdinary / 2, kOrdinary / 2, kOrdinary},
    {kSweepSeed / 2, kOrdinary, kSweepSeed / 2 + kOrdinary},
};

static_assert(std::ranges::all_of(kServiceFeeCusps, [](ServiceFeeCusp const& c) {
    return c.amount == c.installment + c.serviceFee && 2 * c.installment <= kSweepSeed;
}));

// A full payment of `amount`: the principal, the close interest principal * closeRate / 1e5
// (exact) and the close payment fee. Below it is tecINSUFFICIENT_PAYMENT.
struct FullPaymentCusp
{
    std::int64_t principal;
    std::uint32_t closeRate;
    std::int64_t closeFee;
    std::int64_t amount;
};

constexpr FullPaymentCusp kFullPaymentCusps[] = {
    {2, 0, 0, 2},
    {kOrdinary, 10'000, 0, kOrdinary + kOrdinary / 10},
    {kOrdinary, 0, kOrdinary, 2 * kOrdinary},
    {4'000'000'000, 100'000, 0, 8'000'000'000},
};

static_assert(std::ranges::all_of(kFullPaymentCusps, [](FullPaymentCusp const& c) {
    return c.principal * c.closeRate % 100'000 == 0 &&
        c.amount == c.principal + c.principal * c.closeRate / 100'000 + c.closeFee;
}));

inline std::vector<AroundCusp<DueDateCusp>> const kDueDateCases = aroundCusp(
    kDueDateCusps,
    &DueDateCusp::dueOffset,
    &DueDateCusp::amount,
    [](DueDateCusp const& c) { return c.amount >= 1; });
inline std::vector<AroundCusp<LateInterestCusp>> const kLateInterestCases = aroundCusp(
    kLateInterestCusps,
    &LateInterestCusp::lateBy,
    &LateInterestCusp::amount,
    [](LateInterestCusp const& c) { return c.amount >= 1; });
inline std::vector<AroundCusp<ServiceFeeCusp>> const kServiceFeeCases = aroundCusp(
    kServiceFeeCusps,
    &ServiceFeeCusp::serviceFee,
    &ServiceFeeCusp::amount,
    [](ServiceFeeCusp const& c) { return c.serviceFee >= 0 && c.amount >= 1; });
inline std::vector<AroundCusp<FullPaymentCusp>> const kFullPaymentCases = aroundCusp(
    kFullPaymentCusps,
    &FullPaymentCusp::closeFee,
    &FullPaymentCusp::amount,
    [](FullPaymentCusp const& c) { return c.closeFee >= 0 && c.amount >= 1; });

// ---- LoanManage rows ----

// A default once the parent close time passes due date + grace period (exclusive). The due date
// is staged at now - cuspGrace + dueOffset, so the row (grace == cuspGrace, dueOffset 0) defaults
// exactly one second later; below it is tecTOO_SOON.
struct DefaultCusp
{
    std::uint32_t interval;
    std::int64_t cuspGrace;
    std::int64_t grace;
    std::int64_t dueOffset;
};

constexpr DefaultCusp kDefaultCusps[] = {
    {600, 60, 60, 0},
    {600, 600, 600, 0},
    {2'592'000, 86'400, 86'400, 0},
    {2'592'000, 2'592'000, 2'592'000, 0},
};

static_assert(std::ranges::all_of(kDefaultCusps, [](DefaultCusp const& c) {
    return c.grace == c.cuspGrace && c.dueOffset == 0 && c.grace >= 60 && c.grace <= c.interval;
}));

// An impairment adds the loan's principal to the vault's unrealized loss; past the deployed
// assets it is tecLIMIT_EXCEEDED. Rows sit at loss + principal == deployed.
struct LossCapCusp
{
    std::int64_t deployed;
    std::int64_t principal;
    std::int64_t loss;
};

constexpr LossCapCusp kLossCapCusps[] = {
    {1, 1, 0},
    {kOrdinary, 1, kOrdinary - 1},
    {kOrdinary, kOrdinary, 0},
    {kOrdinary, kOrdinary / 2, kOrdinary / 2},
    {kSweepSeed, kSweepSeed - 1, 1},
};

static_assert(std::ranges::all_of(kLossCapCusps, [](LossCapCusp const& c) {
    return c.loss + c.principal == c.deployed && c.principal <= kSweepSeed;
}));

inline std::vector<AroundCusp<DefaultCusp>> const kDefaultCases = aroundCusp(
    kDefaultCusps,
    &DefaultCusp::grace,
    &DefaultCusp::dueOffset,
    [](DefaultCusp const& c) { return c.grace >= 60 && c.grace <= c.interval; });
// An impairment once the parent close time passes the due date (staged at now + offset).
inline std::vector<AroundCusp<std::int64_t>> const kImpairDueCases = aroundCusp(0);
inline std::vector<AroundCusp<LossCapCusp>> const kLossCapCases =
    aroundCusp(kLossCapCusps, &LossCapCusp::loss, &LossCapCusp::deployed, [](LossCapCusp const& c) {
        return c.loss >= 0 && c.loss <= c.deployed;
    });

// ---- Loan lawfulness rows: rates are capped at 100%, 60 <= grace period <= payment interval ----

constexpr std::int64_t kRateCap = 100'000;
inline std::vector<AroundCusp<std::int64_t>> const kRateCapCases = aroundCusp(kRateCap);
inline std::vector<AroundCusp<std::int64_t>> const kGraceCases = [] {
    auto cases = aroundCusp(60);
    cases.push_back(aroundCusp(600).front());
    return cases;
}();

[[nodiscard]] inline std::string
describe(DueDateCusp const& c)
{
    return "type " + std::to_string(static_cast<int>(c.type)) + ", principal " +
        std::to_string(c.principal) + ", due offset " + std::to_string(c.dueOffset) + ", amount " +
        std::to_string(c.amount);
}

[[nodiscard]] inline std::string
describe(LateInterestCusp const& c)
{
    return "k " + std::to_string(c.k) + ", installments " + std::to_string(c.installments) +
        ", service fee " + std::to_string(c.serviceFee) + ", late fee " +
        std::to_string(c.lateFee) + ", late by " + std::to_string(c.lateBy) + ", amount " +
        std::to_string(c.amount);
}

[[nodiscard]] inline std::string
describe(ServiceFeeCusp const& c)
{
    return "installment " + std::to_string(c.installment) + ", service fee " +
        std::to_string(c.serviceFee) + ", amount " + std::to_string(c.amount);
}

[[nodiscard]] inline std::string
describe(FullPaymentCusp const& c)
{
    return "principal " + std::to_string(c.principal) + ", close rate " +
        std::to_string(c.closeRate) + ", close fee " + std::to_string(c.closeFee) + ", amount " +
        std::to_string(c.amount);
}

[[nodiscard]] inline std::string
describe(DefaultCusp const& c)
{
    return "interval " + std::to_string(c.interval) + ", grace " + std::to_string(c.grace) +
        " (cusp " + std::to_string(c.cuspGrace) + "), due offset " + std::to_string(c.dueOffset);
}

[[nodiscard]] inline std::string
describe(LossCapCusp const& c)
{
    return "deployed " + std::to_string(c.deployed) + ", principal " + std::to_string(c.principal) +
        ", loss " + std::to_string(c.loss);
}

}  // namespace xrpl::test::formal_verification::loan_pay_sweep
