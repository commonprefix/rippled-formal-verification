#pragma once

#include <test/formal_verification/common/Sweep.h>
#include <test/formal_verification/tx/lending/LendingTestHelpers.h>

#include <algorithm>
#include <cstdint>
#include <limits>
#include <string>
#include <vector>

// Cusp rows for the lending sweeps (LoanSet, LoanAccept, LoanBrokerSet and the cover
// transactions); their staging is in LendingTestHelpers.h. All amounts are in grid units of the
// fixture vault (IOU scale 6: 1e-6, MPT: 1).
namespace xrpl::test::formal_verification::loan_set_sweep {

// The sweep fixture's vault holds this much; a debt loan plus the swept loan stay within it.
inline constexpr std::int64_t kSeedUnits = 10'000'000'000;
inline constexpr std::int64_t kOrdinaryUnits = 1'000'000'000;
inline constexpr std::int64_t kLargeUnits = 9'000'000'000;
// IOU only: the open limit is reachable for cover (the owner holds 1e16 units).
inline constexpr std::int64_t kOpenLimit = 9'000'000'000'000'000;
inline constexpr std::int64_t kRateScale = 100'000;

constexpr std::int64_t
ceilDiv(__int128 a, std::int64_t b)
{
    return static_cast<std::int64_t>((a + b - 1) / b);
}

// ---- LoanSet ----------------------------------------------------------------------------------

// Debt already taken plus the new principal reaches the limit exactly: the debt maximum, or (for
// the assets available) the vault's assets.
struct DebtCusp
{
    std::int64_t limit;
    std::int64_t debt;
    std::int64_t principal;
};

inline constexpr DebtCusp kDebtMaximumCusps[] = {
    {2, 1, 1},
    {kOrdinaryUnits, 1, kOrdinaryUnits - 1},
    {kOrdinaryUnits, kOrdinaryUnits - 1, 1},
    {kOrdinaryUnits, kOrdinaryUnits / 2, kOrdinaryUnits / 2},
    {kLargeUnits, kLargeUnits - 1, 1},
    {kLargeUnits, 1, kLargeUnits - 1}};

inline constexpr DebtCusp kAssetsAvailableCusps[] = {
    {kSeedUnits, 0, kSeedUnits},
    {kSeedUnits, kSeedUnits - 1, 1},
    {kSeedUnits, kSeedUnits - kOrdinaryUnits, kOrdinaryUnits},
    {kSeedUnits, kSeedUnits / 2, kSeedUnits / 2}};

constexpr bool
onDebtCusp(DebtCusp const& c)
{
    return c.debt + c.principal == c.limit && c.limit <= kSeedUnits;
}

static_assert(std::ranges::all_of(kDebtMaximumCusps, onDebtCusp));
static_assert(std::ranges::all_of(kAssetsAvailableCusps, onDebtCusp));

// The broker's minimum cover at origination: cover == ceil((debt + principal) * rate / 1e5).
struct CoverCusp
{
    std::int64_t debt;
    std::int64_t principal;
    std::uint32_t rate;
    std::int64_t cover;
};

inline constexpr CoverCusp kOriginationCoverCusps[] = {
    {0, 1, 1, 1},
    {0, 100'000, 1, 1},
    {0, kOrdinaryUnits, 10'000, 100'000'000},
    {0, kOrdinaryUnits + 1, 10'000, 100'000'001},
    {kOrdinaryUnits, kOrdinaryUnits, 1, 20'000},
    {0, kLargeUnits, 100'000, kLargeUnits}};

static_assert(std::ranges::all_of(kOriginationCoverCusps, [](CoverCusp const& c) {
    return c.cover == ceilDiv(__int128{c.debt + c.principal} * c.rate, kRateScale) &&
        c.debt + c.principal + 2 <= kSeedUnits;
}));

// Zero interest, interval 60: the loan passes iff P > (N - 1) * ceil(P / N), and a neighbour of
// each row fails (MPT only; an IOU principal splits into fractional installments).
struct PaymentCountCusp
{
    std::int64_t count;
    std::int64_t principal;
};

constexpr bool
paymentCountPasses(std::int64_t n, std::int64_t p)
{
    return p > (n - 1) * ceilDiv(p, n);
}

inline constexpr PaymentCountCusp kPaymentCountCusps[] = {
    {2, 2},
    {3, 3},
    {3, 5},
    {100, 100},
    {100, 4'951},
    {100, 5'000},
    {100, 9'802},
    {31'623, 999'950'885},
    {1'000'000, 1'000'000}};

static_assert(std::ranges::all_of(kPaymentCountCusps, [](PaymentCountCusp const& c) {
    return paymentCountPasses(c.count, c.principal) &&
        (!paymentCountPasses(c.count, c.principal - 1) ||
         !paymentCountPasses(c.count, c.principal + 1));
}));

// Two-step loan starting kBufferStart after the parent close time: the redemption date sits
// exactly interval * count + 60 after the start (the last moment the schedule still fits). The
// principal is kBufferInstallment units per installment, so the payment-count guard holds.
inline constexpr std::uint32_t kBufferStart = 1'000;
inline constexpr std::int64_t kBufferInstallment = 500;

struct RedemptionBufferCusp
{
    std::int64_t interval;
    std::int64_t count;
    std::int64_t redemption;  // seconds after the start date
};

inline constexpr RedemptionBufferCusp kRedemptionBufferCusps[] = {
    {60, 1, 120},
    {1'000'000, 1, 1'000'060},
    {100, 10'000, 1'000'060},
    {1'000, 1'000, 1'000'060},
    {945'999'960, 1, 946'000'020},
    {60, 15'766'666, 946'000'020},
    {30'000, 31'533, 945'990'060}};

// The vault's investment window must stay below 946'708'560 s with the subscription date staged
// kBufferStart before the parent close time.
static_assert(std::ranges::all_of(kRedemptionBufferCusps, [](RedemptionBufferCusp const& c) {
    return c.redemption == c.interval * c.count + 60 && c.interval >= 60 &&
        c.redemption + 2 * kBufferStart + 2 < 946'708'560 &&
        (c.count + 2) * kBufferInstallment <= kSeedUnits;
}));

// Exact-interest loan (interval 3'153'600 s at 100%, one payment): the interest due is
// ceil(P / 10). Rows put the vault's assets total + yield + interest exactly at the open limit
// (IOU: 9e15 units; the vault's assets total is kSeedUnits).
inline constexpr std::uint32_t kExactInterestInterval = 3'153'600;
inline constexpr std::uint32_t kExactInterestRate = 100'000;

struct OpenZoneCusp
{
    std::int64_t yield;
    std::int64_t principal;
};

inline constexpr OpenZoneCusp kOpenZoneCusps[] = {
    {kOpenLimit - kSeedUnits - 1, 10},
    {kOpenLimit - kSeedUnits - kOrdinaryUnits / 10, kOrdinaryUnits},
    {kOpenLimit - kSeedUnits - kLargeUnits / 10, kLargeUnits}};

static_assert(std::ranges::all_of(kOpenZoneCusps, [](OpenZoneCusp const& c) {
    return c.principal % 10 == 0 && c.principal + 2 <= kSeedUnits &&
        kSeedUnits + c.yield + c.principal / 10 == kOpenLimit;
}));

// Origination fee equal to the principal (the largest fee C++ accepts).
struct OriginationFeeCusp
{
    std::int64_t principal;
    std::int64_t fee;
};

inline constexpr OriginationFeeCusp kOriginationFeeCusps[] = {
    {1, 1},
    {kOrdinaryUnits, kOrdinaryUnits},
    {kLargeUnits, kLargeUnits}};

static_assert(std::ranges::all_of(kOriginationFeeCusps, [](OriginationFeeCusp const& c) {
    return c.fee == c.principal && c.principal + 2 <= kSeedUnits;
}));

// One grid step written with a 16-digit mantissa: 1e15 at exponent level - scale - 15; a moved
// mantissa leaves the grid (IOU only).
inline constexpr std::int64_t kOneStepMantissa = 1'000'000'000'000'000;
inline constexpr int kGridLevels[] = {0, 9};
// A debt maximum is not bounded by the vault's assets: one more level.
inline constexpr int kBrokerGridLevels[] = {0, 9, 14};

// ---- LoanBrokerSet ------------------------------------------------------------------------------

// Debt maximum right at the debt maximum cap 2^63 - 1, as a 16-digit mantissa at exponent 3.
inline constexpr std::int64_t kDebtCapMantissa = 9'223'372'036'854'775;
static_assert(
    static_cast<__int128>(kDebtCapMantissa) * 1'000 <= std::numeric_limits<std::int64_t>::max() &&
    static_cast<__int128>(kDebtCapMantissa + 1) * 1'000 > std::numeric_limits<std::int64_t>::max());

// 1e16 units: the smallest value a 16-digit IOU mantissa cannot hold to the unit once moved up.
inline constexpr std::int64_t kSixteenDigitMantissa = 10'000'000'000'000'000;

// An update of the debt maximum to exactly the broker's debt.
struct DebtUpdateCusp
{
    std::int64_t debt;
    std::int64_t maximum;
};

inline constexpr DebtUpdateCusp kDebtUpdateCusps[] = {
    {1, 1},
    {kOrdinaryUnits, kOrdinaryUnits},
    {kLargeUnits, kLargeUnits}};

static_assert(std::ranges::all_of(kDebtUpdateCusps, [](DebtUpdateCusp const& c) {
    return c.debt == c.maximum && c.debt + 2 <= kSeedUnits;
}));

// ---- Cover ------------------------------------------------------------------------------------

// Cover plus a deposit reaches the open limit exactly (IOU).
struct CoverAmountCusp
{
    std::int64_t cover;
    std::int64_t amount;
};

inline constexpr CoverAmountCusp kCoverOpenLimitCusps[] = {
    {0, kOpenLimit},
    {1, kOpenLimit - 1},
    {kOpenLimit - 1, 1},
    {kOpenLimit / 2, kOpenLimit / 2},
    {kOrdinaryUnits, kOpenLimit - kOrdinaryUnits}};

static_assert(std::ranges::all_of(kCoverOpenLimitCusps, [](CoverAmountCusp const& c) {
    return c.cover + c.amount == kOpenLimit;
}));

// Withdrawing the whole cover, with no debt.
inline constexpr CoverAmountCusp kCoverWithdrawAllCusps[] = {
    {1, 1},
    {kOrdinaryUnits, kOrdinaryUnits},
    {kLargeUnits, kLargeUnits}};

static_assert(std::ranges::all_of(kCoverWithdrawAllCusps, [](CoverAmountCusp const& c) {
    return c.cover == c.amount;
}));

// A cover with a one-step amount (mantissa moved, see kOneStepMantissa at level 0).
struct SubGridCusp
{
    std::int64_t cover;
    std::int64_t mantissa;
};

inline constexpr SubGridCusp kSubGridDepositCusps[] = {
    {0, kOneStepMantissa},
    {kOrdinaryUnits, kOneStepMantissa},
    {kOpenLimit - 3, kOneStepMantissa}};

inline constexpr SubGridCusp kSubGridTakeCusps[] = {
    {1, kOneStepMantissa},
    {kOrdinaryUnits, kOneStepMantissa},
    {kOpenLimit - 2, kOneStepMantissa}};

// The minimum cover ceil(debt * rate / 1e5) left after withdrawing `amount` from `cover`.
struct MinimumCoverCusp
{
    std::int64_t debt;
    std::uint32_t rate;
    std::int64_t cover;
    std::int64_t amount;
};

inline constexpr MinimumCoverCusp kMinimumCoverCusps[] = {
    {1, 1, 2, 1},
    {100'000, 1, 2, 1},
    {kOrdinaryUnits, 10'000, 100'000'001, 1},
    {kOrdinaryUnits, 10'000, kOrdinaryUnits, 900'000'000},
    {kOrdinaryUnits, 10'000, 200'000'000, 100'000'000},
    {kOrdinaryUnits + 1, 10'000, 100'000'002, 1},
    {kOrdinaryUnits, 1, 10'000 + kOrdinaryUnits, kOrdinaryUnits},
    {kLargeUnits, 100'000, kLargeUnits + 1, 1}};

constexpr std::int64_t
minimumCover(std::int64_t debt, std::uint32_t rate)
{
    return ceilDiv(__int128{debt} * rate, kRateScale);
}

static_assert(std::ranges::all_of(kMinimumCoverCusps, [](MinimumCoverCusp const& c) {
    return c.cover - c.amount == minimumCover(c.debt, c.rate) && c.debt + 2 <= kSeedUnits;
}));

// No excess cover: cover == the minimum cover (a clawback without an amount claws the excess).
inline constexpr MinimumCoverCusp kNoExcessCusps[] = {
    {0, 1, 0, 0},
    {1, 1, 1, 0},
    {100'000, 1, 1, 0},
    {kOrdinaryUnits, 10'000, 100'000'000, 0},
    {kOrdinaryUnits + 1, 10'000, 100'000'001, 0},
    {kLargeUnits, 100'000, kLargeUnits, 0}};

static_assert(std::ranges::all_of(kNoExcessCusps, [](MinimumCoverCusp const& c) {
    return c.cover == minimumCover(c.debt, c.rate) && c.debt + 2 <= kSeedUnits;
}));

// ---- Generated case lists ---------------------------------------------------------------------

inline std::vector<AroundCusp<DebtCusp>> const kDebtMaximumCases =
    aroundCusp(kDebtMaximumCusps, &DebtCusp::debt, &DebtCusp::principal, [](DebtCusp const& c) {
        return c.debt >= 0 && c.principal >= 1 && c.debt <= c.limit;
    });
inline std::vector<AroundCusp<DebtCusp>> const kAssetsAvailableCases =
    aroundCusp(kAssetsAvailableCusps, &DebtCusp::debt, &DebtCusp::principal, [](DebtCusp const& c) {
        return c.debt >= 0 && c.principal >= 1 && c.debt <= c.limit;
    });
inline std::vector<AroundCusp<CoverCusp>> const kOriginationCoverCases = aroundCusp(
    kOriginationCoverCusps,
    &CoverCusp::cover,
    &CoverCusp::principal,
    [](CoverCusp const& c) { return c.cover >= 0 && c.principal >= 1; });
inline std::vector<AroundCusp<PaymentCountCusp>> const kPaymentCountCases = aroundCusp(
    kPaymentCountCusps,
    &PaymentCountCusp::principal,
    &PaymentCountCusp::count,
    [](PaymentCountCusp const& c) { return c.principal >= 1 && c.count >= 1; });
inline std::vector<AroundCusp<RedemptionBufferCusp>> const kRedemptionBufferCases = aroundCusp(
    kRedemptionBufferCusps,
    &RedemptionBufferCusp::redemption,
    &RedemptionBufferCusp::count,
    [](RedemptionBufferCusp const& c) { return c.count >= 1; });
inline std::vector<AroundCusp<OpenZoneCusp>> const kOpenZoneCases = aroundCusp(
    kOpenZoneCusps,
    &OpenZoneCusp::yield,
    &OpenZoneCusp::principal,
    [](OpenZoneCusp const&) { return true; });
inline std::vector<AroundCusp<OriginationFeeCusp>> const kOriginationFeeCases = aroundCusp(
    kOriginationFeeCusps,
    &OriginationFeeCusp::principal,
    &OriginationFeeCusp::fee,
    [](OriginationFeeCusp const& c) { return c.principal >= 1 && c.fee >= 0; });
inline std::vector<AroundCusp<std::int64_t>> const kOneStepCases = aroundCusp(kOneStepMantissa);
// A date offset from the parent close time.
inline std::vector<AroundCusp<std::int64_t>> const kDateCases = aroundCusp(0);
inline std::vector<AroundCusp<std::int64_t>> const kDebtCapCases = aroundCusp(kDebtCapMantissa);
inline std::vector<AroundCusp<std::int64_t>> const kSixteenDigitCases =
    aroundCusp(kSixteenDigitMantissa);
inline std::vector<AroundCusp<DebtUpdateCusp>> const kDebtUpdateCases = aroundCusp(
    kDebtUpdateCusps,
    &DebtUpdateCusp::debt,
    &DebtUpdateCusp::maximum,
    [](DebtUpdateCusp const& c) { return c.debt >= 0 && c.maximum >= 0; });
inline std::vector<AroundCusp<CoverAmountCusp>> const kCoverOpenLimitCases = aroundCusp(
    kCoverOpenLimitCusps,
    &CoverAmountCusp::cover,
    &CoverAmountCusp::amount,
    [](CoverAmountCusp const& c) {
        return c.cover >= 0 && c.cover <= kOpenLimit && c.amount >= 1;
    });
inline std::vector<AroundCusp<CoverAmountCusp>> const kCoverWithdrawAllCases = aroundCusp(
    kCoverWithdrawAllCusps,
    &CoverAmountCusp::cover,
    &CoverAmountCusp::amount,
    [](CoverAmountCusp const& c) { return c.cover >= 0 && c.amount >= 1; });
inline std::vector<AroundCusp<SubGridCusp>> const kSubGridDepositCases = aroundCusp(
    kSubGridDepositCusps,
    &SubGridCusp::cover,
    &SubGridCusp::mantissa,
    [](SubGridCusp const& c) { return c.cover >= 0; });
inline std::vector<AroundCusp<SubGridCusp>> const kSubGridTakeCases = aroundCusp(
    kSubGridTakeCusps,
    &SubGridCusp::cover,
    &SubGridCusp::mantissa,
    [](SubGridCusp const& c) { return c.cover >= 0; });
inline std::vector<AroundCusp<MinimumCoverCusp>> const kMinimumCoverCases = aroundCusp(
    kMinimumCoverCusps,
    &MinimumCoverCusp::cover,
    &MinimumCoverCusp::amount,
    [](MinimumCoverCusp const& c) { return c.cover >= 0 && c.amount >= 1; });
inline std::vector<AroundCusp<MinimumCoverCusp>> const kNoExcessCases = aroundCusp(
    kNoExcessCusps,
    &MinimumCoverCusp::cover,
    &MinimumCoverCusp::debt,
    [](MinimumCoverCusp const& c) { return c.cover >= 0 && c.debt >= 0; });

// A row as it appears in failure messages.
inline std::string
describe(DebtCusp const& c)
{
    return "limit " + std::to_string(c.limit) + ", debt " + std::to_string(c.debt) +
        ", principal " + std::to_string(c.principal);
}

inline std::string
describe(CoverCusp const& c)
{
    return "debt " + std::to_string(c.debt) + ", principal " + std::to_string(c.principal) +
        ", rate " + std::to_string(c.rate) + ", cover " + std::to_string(c.cover);
}

inline std::string
describe(PaymentCountCusp const& c)
{
    return "count " + std::to_string(c.count) + ", principal " + std::to_string(c.principal);
}

inline std::string
describe(RedemptionBufferCusp const& c)
{
    return "interval " + std::to_string(c.interval) + ", count " + std::to_string(c.count) +
        ", redemption " + std::to_string(c.redemption);
}

inline std::string
describe(OpenZoneCusp const& c)
{
    return "yield " + std::to_string(c.yield) + ", principal " + std::to_string(c.principal);
}

inline std::string
describe(OriginationFeeCusp const& c)
{
    return "principal " + std::to_string(c.principal) + ", fee " + std::to_string(c.fee);
}

inline std::string
describe(DebtUpdateCusp const& c)
{
    return "debt " + std::to_string(c.debt) + ", maximum " + std::to_string(c.maximum);
}

inline std::string
describe(CoverAmountCusp const& c)
{
    return "cover " + std::to_string(c.cover) + ", amount " + std::to_string(c.amount);
}

inline std::string
describe(SubGridCusp const& c)
{
    return "cover " + std::to_string(c.cover) + ", mantissa " + std::to_string(c.mantissa);
}

inline std::string
describe(MinimumCoverCusp const& c)
{
    return "debt " + std::to_string(c.debt) + ", rate " + std::to_string(c.rate) + ", cover " +
        std::to_string(c.cover) + ", amount " + std::to_string(c.amount);
}

}  // namespace xrpl::test::formal_verification::loan_set_sweep
