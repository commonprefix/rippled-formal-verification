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
// fixture vault (IOU scale 6: 1e-6, MPT: 1). A table has no large level when only the vault's seed
// or the open limit bounds it.
namespace xrpl::test::formal_verification::loan_set_sweep {

// The sweep fixture's vault holds this much; a debt loan plus the swept loan stay within it.
inline constexpr std::int64_t kSeedUnits = 10'000'000'000;
inline constexpr std::int64_t kOrdinaryUnits = 1'000'000'000;
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
    {.limit = 2, .debt = 1, .principal = 1},
    {.limit = kOrdinaryUnits, .debt = 1, .principal = kOrdinaryUnits - 1},
    {.limit = kOrdinaryUnits, .debt = kOrdinaryUnits - 1, .principal = 1},
    {.limit = kOrdinaryUnits, .debt = kOrdinaryUnits / 2, .principal = kOrdinaryUnits / 2},
};

inline constexpr DebtCusp kAssetsAvailableCusps[] = {
    {.limit = kSeedUnits, .debt = 0, .principal = kSeedUnits},
    {.limit = kSeedUnits, .debt = kSeedUnits - 1, .principal = 1},
    {.limit = kSeedUnits, .debt = kSeedUnits - kOrdinaryUnits, .principal = kOrdinaryUnits},
    {.limit = kSeedUnits, .debt = kSeedUnits / 2, .principal = kSeedUnits / 2},
};

// A debt maximum row stays lendable one unit past its limit.
static_assert(std::ranges::all_of(kDebtMaximumCusps, [](DebtCusp const& c) {
    return c.debt + c.principal == c.limit && c.limit < kSeedUnits;
}));
static_assert(std::ranges::all_of(kAssetsAvailableCusps, [](DebtCusp const& c) {
    return c.debt + c.principal == c.limit && c.limit == kSeedUnits;
}));

// The broker's minimum cover at origination: cover == ceil((debt + principal) * rate / 1e5).
struct CoverCusp
{
    std::int64_t debt;
    std::int64_t principal;
    std::uint32_t rate;
    std::int64_t cover;
};

inline constexpr CoverCusp kOriginationCoverCusps[] = {
    {.debt = 0, .principal = 1, .rate = 1, .cover = 1},
    {.debt = 0, .principal = 100'000, .rate = 1, .cover = 1},
    {.debt = 0, .principal = kOrdinaryUnits, .rate = 10'000, .cover = 100'000'000},
    {.debt = 0, .principal = kOrdinaryUnits + 1, .rate = 10'000, .cover = 100'000'001},
    {.debt = kOrdinaryUnits, .principal = kOrdinaryUnits, .rate = 1, .cover = 20'000},
    // The rate at its 100% cap.
    {.debt = 0, .principal = kOrdinaryUnits, .rate = kRateScale, .cover = kOrdinaryUnits},
};

static_assert(std::ranges::all_of(kOriginationCoverCusps, [](CoverCusp const& c) {
    return c.cover == ceilDiv(__int128{c.debt + c.principal} * c.rate, kRateScale) &&
        c.rate <= kRateScale && c.debt + c.principal + 2 <= kSeedUnits;
}));

// Zero interest, interval 60: the loan passes iff P > (N - 1) * ceil(P / N), and a neighbour of
// each row fails. The rounded installment is on the vault grid, so this holds in grid units for
// an IOU as for an MPT.
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
    {.count = 2, .principal = 2},
    {.count = 3, .principal = 3},
    {.count = 3, .principal = 5},
    {.count = 100, .principal = 100},
    {.count = 100, .principal = 4'951},
    {.count = 100, .principal = 5'000},
    {.count = 100, .principal = 9'802},
    {.count = 31'623, .principal = 999'950'885},
    {.count = 1'000'000, .principal = 1'000'000},
};

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
    {.interval = 60, .count = 1, .redemption = 120},
    {.interval = 1'000'000, .count = 1, .redemption = 1'000'060},
    {.interval = 100, .count = 10'000, .redemption = 1'000'060},
    {.interval = 1'000, .count = 1'000, .redemption = 1'000'060},
    {.interval = 945'999'960, .count = 1, .redemption = 946'000'020},
    {.interval = 60, .count = 15'766'666, .redemption = 946'000'020},
    {.interval = 30'000, .count = 31'533, .redemption = 945'990'060},
};

// The vault's investment window must stay below 946'708'560 s with the subscription date staged
// kBufferStart before the parent close time.
static_assert(std::ranges::all_of(kRedemptionBufferCusps, [](RedemptionBufferCusp const& c) {
    return c.redemption == (c.interval * c.count) + 60 && c.interval >= 60 &&
        c.redemption + (2 * kBufferStart) + 2 < 946'708'560 &&
        (c.count + 2) * kBufferInstallment <= kSeedUnits;
}));

// Exact-interest loan (interval 3'153'600 s at 100%, one payment): the interest due is
// ceil(P / 10). Rows put the vault's assets total + yield + interest exactly at the open limit
// (9e15 units; the vault's assets total is kSeedUnits).
inline constexpr std::uint32_t kExactInterestInterval = 3'153'600;
inline constexpr std::uint32_t kExactInterestRate = 100'000;

struct OpenZoneCusp
{
    std::int64_t yield;
    std::int64_t principal;
};

inline constexpr OpenZoneCusp kOpenZoneCusps[] = {
    {.yield = kOpenLimitUnits - kSeedUnits - 1, .principal = 10},
    {.yield = kOpenLimitUnits - kSeedUnits - (kOrdinaryUnits / 10), .principal = kOrdinaryUnits},
};

static_assert(std::ranges::all_of(kOpenZoneCusps, [](OpenZoneCusp const& c) {
    return c.principal % 10 == 0 && c.principal + 2 <= kSeedUnits &&
        kSeedUnits + c.yield + (c.principal / 10) == kOpenLimitUnits;
}));

// Origination fee equal to the principal (the largest fee C++ accepts).
struct OriginationFeeCusp
{
    std::int64_t principal;
    std::int64_t fee;
};

inline constexpr OriginationFeeCusp kOriginationFeeCusps[] = {
    {.principal = 1, .fee = 1},
    {.principal = kOrdinaryUnits, .fee = kOrdinaryUnits},
};

static_assert(std::ranges::all_of(kOriginationFeeCusps, [](OriginationFeeCusp const& c) {
    return c.fee == c.principal && c.principal + 2 <= kSeedUnits;
}));

// One grid step written with a 16-digit mantissa (see gridStep); a moved mantissa leaves the grid.
inline constexpr std::int64_t kOneStepMantissa = 1'000'000'000'000'000;
inline constexpr int kGridLevels[] = {0, 9};
// A debt maximum is not bounded by the vault's assets: one more level.
inline constexpr int kBrokerGridLevels[] = {0, 9, 14};

// A two-step loan whose last grace period ends exactly at the protocol's last second:
// interval * total + grace == 2^32 - 1 - start. One second more is tecKILLED. The large rows use
// all the time there is (start 0).
inline constexpr std::int64_t kMaxTime = 0xFFFF'FFFF;

struct TimeLimitCusp
{
    std::int64_t start;
    std::int64_t interval;
    std::int64_t total;
    std::int64_t grace;
};

inline constexpr TimeLimitCusp kTimeLimitCusps[] = {
    {.start = kMaxTime - 120, .interval = 60, .total = 1, .grace = 60},
    {.start = kMaxTime - 600'600, .interval = 600, .total = 1'000, .grace = 600},
    {.start = 0, .interval = kMaxTime - 60, .total = 1, .grace = 60},
    {.start = 0, .interval = 64, .total = 67'108'863, .grace = 63},
};

static_assert(std::ranges::all_of(kTimeLimitCusps, [](TimeLimitCusp const& c) {
    return (c.interval * c.total) + c.grace == kMaxTime - c.start && c.start >= 0 &&
        c.grace >= 60 && c.grace <= c.interval;
}));

// The principal of a time limit loan; no swept case reaches the checks that read it.
inline constexpr std::int64_t kTimeLimitPrincipal = kOrdinaryUnits;

// ---- LoanBrokerSet ------------------------------------------------------------------------------

// A debt maximum or MPT amount right at the cap 2^63 - 1, as a 16-digit mantissa at exponent 3.
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
    {.debt = 1, .maximum = 1},
    {.debt = kOrdinaryUnits, .maximum = kOrdinaryUnits},
};

static_assert(std::ranges::all_of(kDebtUpdateCusps, [](DebtUpdateCusp const& c) {
    return c.debt == c.maximum && c.debt + 2 <= kSeedUnits;
}));

// Rate caps of a new broker (preflight temINVALID above them).
inline constexpr std::int64_t kManagementFeeCap = 10'000;

// ---- Cover ------------------------------------------------------------------------------------

// Cover plus a deposit reaches the open limit exactly.
struct CoverAmountCusp
{
    std::int64_t cover;
    std::int64_t amount;
};

inline constexpr CoverAmountCusp kCoverOpenLimitCusps[] = {
    {.cover = 0, .amount = kOpenLimitUnits},
    {.cover = 1, .amount = kOpenLimitUnits - 1},
    {.cover = kOpenLimitUnits - 1, .amount = 1},
    {.cover = kOpenLimitUnits / 2, .amount = kOpenLimitUnits / 2},
    {.cover = kOrdinaryUnits, .amount = kOpenLimitUnits - kOrdinaryUnits},
};

static_assert(std::ranges::all_of(kCoverOpenLimitCusps, [](CoverAmountCusp const& c) {
    return c.cover + c.amount == kOpenLimitUnits;
}));

// Withdrawing the whole cover, with no debt. The large row is the largest cover that can be
// staged two units up (the open limit bounds the cover).
inline constexpr CoverAmountCusp kCoverWithdrawAllCusps[] = {
    {.cover = 1, .amount = 1},
    {.cover = kOrdinaryUnits, .amount = kOrdinaryUnits},
    {.cover = kOpenLimitUnits - 2, .amount = kOpenLimitUnits - 2},
};

static_assert(std::ranges::all_of(kCoverWithdrawAllCusps, [](CoverAmountCusp const& c) {
    return c.cover == c.amount && c.cover + 2 <= kOpenLimitUnits;
}));

// A cover with a one-step amount (mantissa moved, see kOneStepMantissa at level 0).
struct SubGridCusp
{
    std::int64_t cover;
    std::int64_t mantissa;
};

// The large deposit row: the cover two units up plus the one-unit deposit reaches the open limit.
inline constexpr SubGridCusp kSubGridDepositCusps[] = {
    {.cover = 0, .mantissa = kOneStepMantissa},
    {.cover = kOrdinaryUnits, .mantissa = kOneStepMantissa},
    {.cover = kOpenLimitUnits - 3, .mantissa = kOneStepMantissa},
};

static_assert(std::ranges::all_of(kSubGridDepositCusps, [](SubGridCusp const& c) {
    return c.mantissa == kOneStepMantissa && c.cover + 2 + 1 <= kOpenLimitUnits;
}));

// The large take row: the cover two units up still fits the open limit.
inline constexpr SubGridCusp kSubGridTakeCusps[] = {
    {.cover = 1, .mantissa = kOneStepMantissa},
    {.cover = kOrdinaryUnits, .mantissa = kOneStepMantissa},
    {.cover = kOpenLimitUnits - 2, .mantissa = kOneStepMantissa},
};

static_assert(std::ranges::all_of(kSubGridTakeCusps, [](SubGridCusp const& c) {
    return c.mantissa == kOneStepMantissa && c.cover >= 1 && c.cover + 2 <= kOpenLimitUnits;
}));

// The minimum cover ceil(debt * rate / 1e5) left after withdrawing `amount` from `cover`; for a
// clawback, `amount` is exactly the excess over the minimum cover.
struct MinimumCoverCusp
{
    std::int64_t debt;
    std::uint32_t rate;
    std::int64_t cover;
    std::int64_t amount;
};

inline constexpr MinimumCoverCusp kMinimumCoverCusps[] = {
    {.debt = 1, .rate = 1, .cover = 2, .amount = 1},
    {.debt = 100'000, .rate = 1, .cover = 2, .amount = 1},
    {.debt = kOrdinaryUnits, .rate = 10'000, .cover = 100'000'001, .amount = 1},
    {.debt = kOrdinaryUnits, .rate = 10'000, .cover = kOrdinaryUnits, .amount = 900'000'000},
    {.debt = kOrdinaryUnits, .rate = 10'000, .cover = 200'000'000, .amount = 100'000'000},
    {.debt = kOrdinaryUnits + 1, .rate = 10'000, .cover = 100'000'002, .amount = 1},
    {.debt = kOrdinaryUnits, .rate = 1, .cover = 10'000 + kOrdinaryUnits, .amount = kOrdinaryUnits},
    {.debt = kOrdinaryUnits, .rate = kRateScale, .cover = kOrdinaryUnits + 1, .amount = 1},
};

constexpr std::int64_t
minimumCover(std::int64_t debt, std::uint32_t rate)
{
    return ceilDiv(__int128{debt} * rate, kRateScale);
}

static_assert(std::ranges::all_of(kMinimumCoverCusps, [](MinimumCoverCusp const& c) {
    return c.cover - c.amount == minimumCover(c.debt, c.rate) && c.debt + 2 <= kSeedUnits;
}));

// No excess cover: cover == the minimum cover (a clawback without an amount claws the excess).
struct NoExcessCusp
{
    std::int64_t debt;
    std::uint32_t rate;
    std::int64_t cover;
};

inline constexpr NoExcessCusp kNoExcessCusps[] = {
    {.debt = 0, .rate = 1, .cover = 0},
    {.debt = 1, .rate = 1, .cover = 1},
    {.debt = 100'000, .rate = 1, .cover = 1},
    {.debt = kOrdinaryUnits, .rate = 10'000, .cover = 100'000'000},
    {.debt = kOrdinaryUnits + 1, .rate = 10'000, .cover = 100'000'001},
    {.debt = kOrdinaryUnits, .rate = kRateScale, .cover = kOrdinaryUnits},
};

static_assert(std::ranges::all_of(kNoExcessCusps, [](NoExcessCusp const& c) {
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
// Open gap: C++ rejects a principal <= 0 or a zero count (temINVALID), the model creates the
// loan. Those moves are dropped until the model checks them.
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
// A fee moved below zero reaches preflight's temINVALID; a principal <= 0 is dropped (open gap,
// see kPaymentCountCases).
inline std::vector<AroundCusp<OriginationFeeCusp>> const kOriginationFeeCases = aroundCusp(
    kOriginationFeeCusps,
    &OriginationFeeCusp::principal,
    &OriginationFeeCusp::fee,
    [](OriginationFeeCusp const& c) { return c.principal >= 1; });
inline std::vector<AroundCusp<TimeLimitCusp>> const kTimeLimitCases = aroundCusp(
    kTimeLimitCusps,
    &TimeLimitCusp::grace,
    &TimeLimitCusp::total,
    [](TimeLimitCusp const& c) { return c.grace >= 60 && c.grace <= c.interval && c.total >= 1; });
inline std::vector<AroundCusp<std::int64_t>> const kOneStepCases = aroundCusp(kOneStepMantissa);
// A value moved around zero: a date offset from the parent close time, or a fee or debt maximum
// at its minimum.
inline std::vector<AroundCusp<std::int64_t>> const kZeroCases = aroundCusp(0);
inline std::vector<AroundCusp<std::int64_t>> const kManagementFeeCapCases =
    aroundCusp(kManagementFeeCap);
inline std::vector<AroundCusp<std::int64_t>> const kCoverRateCapCases = aroundCusp(kRateScale);
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
        return c.cover >= 0 && c.cover <= kOpenLimitUnits && c.amount >= 1;
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
inline std::vector<AroundCusp<NoExcessCusp>> const kNoExcessCases = aroundCusp(
    kNoExcessCusps,
    &NoExcessCusp::cover,
    &NoExcessCusp::debt,
    [](NoExcessCusp const& c) { return c.cover >= 0 && c.debt >= 0; });

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
describe(TimeLimitCusp const& c)
{
    return "start " + std::to_string(c.start) + ", interval " + std::to_string(c.interval) +
        ", total " + std::to_string(c.total) + ", grace " + std::to_string(c.grace);
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
describe(NoExcessCusp const& c)
{
    return "debt " + std::to_string(c.debt) + ", rate " + std::to_string(c.rate) + ", cover " +
        std::to_string(c.cover);
}

inline std::string
describe(MinimumCoverCusp const& c)
{
    return "debt " + std::to_string(c.debt) + ", rate " + std::to_string(c.rate) + ", cover " +
        std::to_string(c.cover) + ", amount " + std::to_string(c.amount);
}

}  // namespace xrpl::test::formal_verification::loan_set_sweep
