#pragma once

#include <test/formal_verification/common/Sweep.h>
#include <test/formal_verification/tx/vault/DepositSweepCases.h>
#include <test/formal_verification/tx/vault/VaultTestHelpers.h>

#include <cstddef>
#include <cstdint>
#include <optional>
#include <string>
#include <vector>

namespace xrpl::test::formal_verification {

namespace create_set_sweep {

// Each row with its member `value` moved by every offset in kAroundCusp, keeping the moved rows
// `valid` accepts.
template <class Row, std::size_t N, class Valid>
std::vector<AroundCusp<Row>>
aroundCuspOf(Row const (&rows)[N], std::int64_t Row::* value, Valid valid)
{
    std::vector<AroundCusp<Row>> groups;
    for (Row const& row : rows)
    {
        AroundCusp<Row> group{.cusp = row, .cases = {}};
        for (std::int64_t const d : kAroundCusp)
        {
            Row moved = row;
            moved.*value += d;
            if (valid(moved))
                group.cases.push_back(moved);
        }
        groups.push_back(group);
    }
    return groups;
}

// A vault on grid scale `scale` (IOU only; none keeps the default), with no deposit.
[[nodiscard]] inline Keylet
createVaultAt(
    jtx::Env& env,
    jtx::Account const& owner,
    Asset const& asset,
    std::optional<std::uint8_t> scale = std::nullopt)
{
    jtx::Vault v{env};
    auto [tx, keylet] = v.create({.owner = owner, .asset = asset});
    if (scale)
        tx[sfScale] = *scale;
    env(tx);
    env.close();
    return keylet;
}

constexpr bool
hasAtMost16Digits(std::int64_t mantissa)
{
    while (mantissa % 10 == 0 && mantissa != 0)
        mantissa /= 10;
    return mantissa < 10'000'000'000'000'000;
}

}  // namespace create_set_sweep

// The investment period (redemption minus subscription date) of a closed-ended vault.
constexpr std::int64_t kMinInvestmentPeriod = 180;
constexpr std::int64_t kMaxInvestmentPeriod = 946'708'559;  // below 30 years
constexpr std::int64_t kMaxEarlyExitFeeRate = 100'000;      // 100% in tenth-bips
constexpr std::int64_t kMaxVaultScale = 10;
constexpr std::int64_t kXrpMaximumDrops = 100'000'000'000'000'000;

// VaultCreate schedule: subscription date at P + subscription, redemption date `gap` later.
struct ScheduleCusp
{
    std::int64_t subscription;
    std::int64_t gap;
};

// A subscription date equal to the parent close time P is already expired (P + 1 is the first
// accepted date); the smallest and largest gaps also sit on the investment period bounds.
constexpr ScheduleCusp kScheduleCusps[] = {
    {0, kMinInvestmentPeriod},
    {0, 1'000'000},
    {0, kMaxInvestmentPeriod},
};

static_assert([] {
    for (auto const& c : kScheduleCusps)
    {
        if (c.subscription != 0 || c.gap < kMinInvestmentPeriod || c.gap > kMaxInvestmentPeriod)
            return false;
    }
    return true;
}());

// An AssetsMaximum of mantissa * 10^exponent grid steps (10^-scale).
struct MaximumGridCusp
{
    std::int64_t mantissa;
    std::int64_t exponent;
};

// The maximum must lie on the vault grid with at most 16 digits. One grid step and an ordinary
// value go off the grid at any move; the largest 16-digit value only at +2 (17 digits); a
// 16-digit value above 1e16 steps at any move.
constexpr MaximumGridCusp kMaximumGridCusps[] = {
    {1'000'000'000'000'000, -15},
    {1'000'000'000'000'000, -6},
    {9'999'999'999'999'999, 0},
    {10'000'000'000'000'010, 0},
};

static_assert([] {
    for (auto const& c : kMaximumGridCusps)
    {
        std::int64_t m = c.mantissa;
        for (std::int64_t e = c.exponent; e < 0; ++e)
        {
            if (m % 10 != 0)
                return false;
            m /= 10;
        }
        if (!create_set_sweep::hasAtMost16Digits(c.mantissa))
            return false;
    }
    return true;
}());

// VaultSet: a maximum equal to the assets total (available + deployed) is the smallest accepted
// one; a maximum of 0 removes the cap.
struct SetMaximumCusp
{
    std::int64_t available;
    std::int64_t deployed;
    std::int64_t maximum;
};

constexpr SetMaximumCusp kSetMaximumCusps[] = {
    {2, 0, 2},
    {1, 1, 2},
    {kOrdinaryUnits, 0, kOrdinaryUnits},
    {1, kOrdinaryUnits - 1, kOrdinaryUnits},
    {kOrdinaryUnits - 1, 1, kOrdinaryUnits},
    {kOrdinaryUnits / 2, kOrdinaryUnits / 2, kOrdinaryUnits},
    {kLargeUnits, 0, kLargeUnits},
    {1, kLargeUnits - 1, kLargeUnits},
    {kLargeUnits - 1, 1, kLargeUnits},
    {kLargeUnits / 2, kLargeUnits / 2, kLargeUnits},
};

static_assert([] {
    for (auto const& c : kSetMaximumCusps)
    {
        if (c.maximum != c.available + c.deployed)
            return false;
    }
    return true;
}());

// VaultDelete: an empty vault with no shares is the only deletable state.
struct DeleteCusp
{
    std::int64_t available;
    std::int64_t sharesTotal;
};

constexpr DeleteCusp kDeleteCusps[] = {{0, 0}};

inline std::vector<AroundCusp<ScheduleCusp>> const kScheduleCases = aroundCusp(
    kScheduleCusps,
    &ScheduleCusp::subscription,
    &ScheduleCusp::gap,
    [](ScheduleCusp const&) { return true; });
inline std::vector<AroundCusp<std::int64_t>> const kEarlyExitFeeCases =
    aroundCusp(kMaxEarlyExitFeeRate);
inline std::vector<AroundCusp<std::int64_t>> const kScaleCases = aroundCusp(kMaxVaultScale);
// A negative maximum is malformed; 0 is no cap.
inline std::vector<AroundCusp<std::int64_t>> const kMaximumSignCases = aroundCusp(0);
inline std::vector<AroundCusp<std::int64_t>> const kXrpMaximumCases = aroundCusp(kXrpMaximumDrops);
inline std::vector<AroundCusp<MaximumGridCusp>> const kMaximumGridCases =
    create_set_sweep::aroundCuspOf(
        kMaximumGridCusps,
        &MaximumGridCusp::mantissa,
        [](MaximumGridCusp const&) { return true; });
inline std::vector<AroundCusp<SetMaximumCusp>> const kSetMaximumCases = aroundCusp(
    kSetMaximumCusps,
    &SetMaximumCusp::maximum,
    &SetMaximumCusp::available,
    [](SetMaximumCusp const& c) { return c.available >= 0 && c.maximum >= 0; });
// A vault with shares must hold assets or be insolvent; no shares means no assets.
inline std::vector<AroundCusp<DeleteCusp>> const kDeleteCases = aroundCusp(
    kDeleteCusps,
    &DeleteCusp::available,
    &DeleteCusp::sharesTotal,
    [](DeleteCusp const& c) {
        return c.available >= 0 && c.sharesTotal >= 0 && (c.sharesTotal > 0 || c.available == 0);
    });

// A row as it appears in failure messages.
inline std::string
describe(ScheduleCusp const& c)
{
    return "subscription P + " + std::to_string(c.subscription) + ", gap " + std::to_string(c.gap);
}

inline std::string
describe(MaximumGridCusp const& c)
{
    return "maximum " + std::to_string(c.mantissa) + "e" + std::to_string(c.exponent) +
        " grid steps";
}

inline std::string
describe(SetMaximumCusp const& c)
{
    return "available " + std::to_string(c.available) + ", deployed " + std::to_string(c.deployed) +
        ", maximum " + std::to_string(c.maximum);
}

inline std::string
describe(DeleteCusp const& c)
{
    return "available " + std::to_string(c.available) + ", sharesTotal " +
        std::to_string(c.sharesTotal);
}

}  // namespace xrpl::test::formal_verification
