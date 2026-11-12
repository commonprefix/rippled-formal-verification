#pragma once

#include <test/formal_verification/common/Sweep.h>
#include <test/formal_verification/tx/lending/LendingTestHelpers.h>
#include <test/formal_verification/tx/lending/LoanSetSweepCases.h>

#include <algorithm>
#include <cstdint>
#include <string>
#include <vector>

// Cusp rows for the LoanPay, LoanManage and Loan sweeps. The staging they use is in
// LendingTestHelpers.h. A table has no large level when only the vault's seed bounds it.
namespace xrpl::test::formal_verification::loan_pay_sweep {

using loan_set_sweep::kOrdinaryUnits;
using loan_set_sweep::kRateScale;
using loan_set_sweep::kZeroCases;

// ---- LoanPay rows. Loans have no interest and two installments unless a row says otherwise. ----

// What the sweep vaults hold; every row's principal stays within it.
constexpr std::int64_t kSweepSeed = loan_set_sweep::kSeedUnits;
// What the LoanPay sweep fixture's IOU owner keeps (1'000), so its cover deposits stay below it.
constexpr std::int64_t kOwnerUnits = 1'000'000'000;

// A payment of `amount` when the next payment falls due `dueOffset` seconds after the parent
// close time. Regular, full and overpayments are late (tecEXPIRED) once dueOffset < 0; a late
// payment is too soon (tecTOO_SOON) while dueOffset >= 0. The amount is the exact amount due.
struct DueDateCusp
{
    PaymentType type;
    std::int64_t principal;
    std::int64_t dueOffset{};
    std::int64_t amount;
};

[[nodiscard]] constexpr std::int64_t
exactDue(PaymentType type, std::int64_t principal)
{
    return type == PaymentType::full ? principal : principal / 2;
}

constexpr DueDateCusp kDueDateCusps[] = {
    {.type = PaymentType::regular, .principal = 2, .amount = 1},
    {.type = PaymentType::regular, .principal = 2 * kOrdinaryUnits, .amount = kOrdinaryUnits},
    {.type = PaymentType::late, .principal = 2, .amount = 1},
    {.type = PaymentType::late, .principal = 2 * kOrdinaryUnits, .amount = kOrdinaryUnits},
    {.type = PaymentType::full, .principal = 2, .amount = 2},
    {.type = PaymentType::full, .principal = 2 * kOrdinaryUnits, .amount = 2 * kOrdinaryUnits},
    {.type = PaymentType::overpayment, .principal = 2, .amount = 1},
    {.type = PaymentType::overpayment, .principal = 2 * kOrdinaryUnits, .amount = kOrdinaryUnits},
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
    {
        .k = 1,
        .installments = 2,
        .serviceFee = 0,
        .lateFee = 0,
        .lateBy = 1,
        .amount = (kSecondsPerYear / 2) + 1,
    },
    {
        .k = 32,
        .installments = 2,
        .serviceFee = 0,
        .lateFee = 0,
        .lateBy = 1'000,
        .amount = (32 * kSecondsPerYear / 2) + 32'000,
    },
    {
        .k = 1,
        .installments = 1,
        .serviceFee = 0,
        .lateFee = 0,
        .lateBy = 1'000,
        .amount = kSecondsPerYear + 1'000,
    },
    {
        .k = 1,
        .installments = 2,
        .serviceFee = kOrdinaryUnits,
        .lateFee = 0,
        .lateBy = 1,
        .amount = (kSecondsPerYear / 2) + kOrdinaryUnits + 1,
    },
    {
        .k = 1,
        .installments = 2,
        .serviceFee = 0,
        .lateFee = kOrdinaryUnits,
        .lateBy = 1,
        .amount = (kSecondsPerYear / 2) + kOrdinaryUnits + 1,
    },
};

[[nodiscard]] constexpr bool
onLateInterestCusp(LateInterestCusp const& c)
{
    std::int64_t const principal = kSecondsPerYear * c.k;
    return principal % c.installments == 0 && principal <= kSweepSeed &&
        c.amount == (principal / c.installments) + c.serviceFee + c.lateFee + (c.k * c.lateBy);
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
    {.installment = 1, .serviceFee = kOrdinaryUnits - 1, .amount = kOrdinaryUnits},
    {.installment = kOrdinaryUnits - 1, .serviceFee = 1, .amount = kOrdinaryUnits},
    {.installment = kOrdinaryUnits / 2, .serviceFee = kOrdinaryUnits / 2, .amount = kOrdinaryUnits},
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
    {.principal = 2, .closeRate = 0, .closeFee = 0, .amount = 2},
    {
        .principal = kOrdinaryUnits,
        .closeRate = 10'000,
        .closeFee = 0,
        .amount = kOrdinaryUnits + (kOrdinaryUnits / 10),
    },
    {.principal = kOrdinaryUnits,
     .closeRate = 0,
     .closeFee = kOrdinaryUnits,
     .amount = 2 * kOrdinaryUnits},
    // The close rate at its 100% cap.
    {.principal = kOrdinaryUnits,
     .closeRate = 100'000,
     .closeFee = 0,
     .amount = 2 * kOrdinaryUnits},
};

static_assert(std::ranges::all_of(kFullPaymentCusps, [](FullPaymentCusp const& c) {
    return c.principal * c.closeRate % 100'000 == 0 && c.closeRate <= kRateScale &&
        c.amount == c.principal + (c.principal * c.closeRate / 100'000) + c.closeFee;
}));

// A full payment of the whole principal: one installment left is tecKILLED, two can be paid off.
// The principal splits into up to three installments.
struct InstallmentsCusp
{
    std::int64_t principal;
    std::int64_t total;
};

constexpr InstallmentsCusp kFullPaymentRemainingCusps[] = {
    {.principal = 6, .total = 1},
    {.principal = 2 * kOrdinaryUnits, .total = 1},
};

static_assert(std::ranges::all_of(kFullPaymentRemainingCusps, [](InstallmentsCusp const& c) {
    return c.total == 1 && loan_set_sweep::paymentCountPasses(c.total + 1, c.principal) &&
        loan_set_sweep::paymentCountPasses(c.total + 2, c.principal);
}));

// The broker's fee (a one-unit service fee) goes to the owner once the cover reaches the minimum
// cover ceil(debt * rate / 1e5), else into the cover. The verdict does not change across it.
struct FeeRoutingCusp
{
    std::int64_t principal;
    std::uint32_t rate;
    std::int64_t cover;
};

constexpr FeeRoutingCusp kFeeRoutingCusps[] = {
    {.principal = 2, .rate = 1, .cover = 1},
    {.principal = 2 * kOrdinaryUnits, .rate = 10'000, .cover = 200'000'000},
    {.principal = (2 * kOrdinaryUnits) + 2, .rate = 10'000, .cover = 200'000'001},
    {.principal = kOrdinaryUnits / 2, .rate = 100'000, .cover = kOrdinaryUnits / 2},
};

static_assert(std::ranges::all_of(kFeeRoutingCusps, [](FeeRoutingCusp const& c) {
    return c.cover == loan_set_sweep::minimumCover(c.principal, c.rate) && c.principal % 2 == 0 &&
        c.rate <= kRateScale && c.cover + 2 <= kOwnerUnits;
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
inline std::vector<AroundCusp<InstallmentsCusp>> const kFullPaymentRemainingCases =
    aroundCusp(kFullPaymentRemainingCusps, &InstallmentsCusp::total, [](InstallmentsCusp const& c) {
        return c.total >= 1;
    });
inline std::vector<AroundCusp<FeeRoutingCusp>> const kFeeRoutingCases =
    aroundCusp(kFeeRoutingCusps, &FeeRoutingCusp::cover, [](FeeRoutingCusp const& c) {
        return c.cover >= 0;
    });

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
    {.interval = 600, .cuspGrace = 60, .grace = 60, .dueOffset = 0},
    {.interval = 600, .cuspGrace = 600, .grace = 600, .dueOffset = 0},
    {.interval = 2'592'000, .cuspGrace = 86'400, .grace = 86'400, .dueOffset = 0},
    {.interval = 2'592'000, .cuspGrace = 2'592'000, .grace = 2'592'000, .dueOffset = 0},
};

static_assert(std::ranges::all_of(kDefaultCusps, [](DefaultCusp const& c) {
    return c.grace == c.cuspGrace && c.dueOffset == 0 && c.grace >= 60 && c.grace <= c.interval;
}));

// The cover a default moves into the vault: min(min(minimumCover * 20%, principal), cover), with
// minimumCover = (debt + principal) * rate / 1e5 and the staged 20% liquidation rate. `debt` is
// another loan's principal. The verdict does not change across either cusp.
struct DefaultCoverCusp
{
    std::int64_t debt;
    std::int64_t principal;
    std::uint32_t rate;
    std::int64_t cover;
};

// The liquidation share (debt + principal) * rate / 5e5 is exactly the principal; the cover is
// above both.
constexpr DefaultCoverCusp kDefaultPrincipalCusps[] = {
    {.debt = 16, .principal = 4, .rate = 100'000, .cover = 20},
    {.debt = 400'000'000, .principal = 100'000'000, .rate = 100'000, .cover = 200'000'010},
    {.debt = 900'000'000, .principal = 100'000'000, .rate = 50'000, .cover = 200'000'010},
};

static_assert(std::ranges::all_of(kDefaultPrincipalCusps, [](DefaultCoverCusp const& c) {
    return (c.debt + c.principal) * c.rate == 5 * kRateScale * c.principal &&
        c.cover >= 2 * (c.principal + 2) && c.rate <= kRateScale;
}));

// The liquidation share is exactly the cover, below the principal.
constexpr DefaultCoverCusp kDefaultAvailableCusps[] = {
    {.debt = 0, .principal = 5, .rate = 100'000, .cover = 1},
    {.debt = 0, .principal = 500'000, .rate = 1, .cover = 1},
    {.debt = 0, .principal = 5 * kOrdinaryUnits, .rate = 10'000, .cover = 100'000'000},
    {.debt = kOrdinaryUnits, .principal = kOrdinaryUnits, .rate = 100'000, .cover = 400'000'000},
};

static_assert(std::ranges::all_of(kDefaultAvailableCusps, [](DefaultCoverCusp const& c) {
    return (c.debt + c.principal) * c.rate == 5 * kRateScale * c.cover &&
        c.cover + 2 < c.principal && c.debt + c.principal <= kSweepSeed;
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
    {.deployed = 1, .principal = 1, .loss = 0},
    {.deployed = kOrdinaryUnits, .principal = 1, .loss = kOrdinaryUnits - 1},
    {.deployed = kOrdinaryUnits, .principal = kOrdinaryUnits, .loss = 0},
    {.deployed = kOrdinaryUnits, .principal = kOrdinaryUnits / 2, .loss = kOrdinaryUnits / 2},
};

static_assert(std::ranges::all_of(kLossCapCusps, [](LossCapCusp const& c) {
    return c.loss + c.principal == c.deployed && c.principal <= kSweepSeed;
}));

inline std::vector<AroundCusp<DefaultCusp>> const kDefaultCases = aroundCusp(
    kDefaultCusps,
    &DefaultCusp::grace,
    &DefaultCusp::dueOffset,
    [](DefaultCusp const& c) { return c.grace >= 60 && c.grace <= c.interval; });
inline std::vector<AroundCusp<DefaultCoverCusp>> const kDefaultPrincipalCases = aroundCusp(
    kDefaultPrincipalCusps,
    &DefaultCoverCusp::debt,
    &DefaultCoverCusp::principal,
    [](DefaultCoverCusp const& c) { return c.debt >= 1 && c.principal >= 1; });
inline std::vector<AroundCusp<DefaultCoverCusp>> const kDefaultAvailableCases =
    aroundCusp(kDefaultAvailableCusps, &DefaultCoverCusp::cover, [](DefaultCoverCusp const& c) {
        return c.cover >= 0;
    });
inline std::vector<AroundCusp<LossCapCusp>> const kLossCapCases =
    aroundCusp(kLossCapCusps, &LossCapCusp::loss, &LossCapCusp::deployed, [](LossCapCusp const& c) {
        return c.loss >= 0 && c.loss <= c.deployed;
    });

// ---- Loan lawfulness rows: rates are capped at 100%, 60 <= grace period <= payment interval ----

constexpr std::int64_t kRateCap = kRateScale;
inline std::vector<AroundCusp<std::int64_t>> const kRateCapCases = aroundCusp(kRateCap);
inline std::vector<AroundCusp<std::int64_t>> const kGraceCases = [] {
    auto cases = aroundCusp(60);
    cases.push_back(aroundCusp(600).front());
    return cases;
}();
// The payment interval's 60 s minimum.
inline std::vector<AroundCusp<std::int64_t>> const kIntervalMinimumCases = aroundCusp(60);

[[nodiscard]] inline std::string
describe(DueDateCusp const& c)
{
    return "type " + paymentTypeName(c.type) + ", principal " + std::to_string(c.principal) +
        ", due offset " + std::to_string(c.dueOffset) + ", amount " + std::to_string(c.amount);
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
describe(InstallmentsCusp const& c)
{
    return "principal " + std::to_string(c.principal) + ", total " + std::to_string(c.total);
}

[[nodiscard]] inline std::string
describe(FeeRoutingCusp const& c)
{
    return "principal " + std::to_string(c.principal) + ", rate " + std::to_string(c.rate) +
        ", cover " + std::to_string(c.cover);
}

[[nodiscard]] inline std::string
describe(DefaultCoverCusp const& c)
{
    return "debt " + std::to_string(c.debt) + ", principal " + std::to_string(c.principal) +
        ", rate " + std::to_string(c.rate) + ", cover " + std::to_string(c.cover);
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
