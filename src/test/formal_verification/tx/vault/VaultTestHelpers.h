#pragma once

#include <test/formal_verification/ffi/vault/VaultStateFFI.h>
#include <test/jtx/Account.h>
#include <test/jtx/Env.h>
#include <test/jtx/amount.h>
#include <test/jtx/flags.h>
#include <test/jtx/pay.h>
#include <test/jtx/trust.h>
#include <test/jtx/vault.h>

#include <xrpl/basics/Number.h>
#include <xrpl/ledger/OpenView.h>
#include <xrpl/ledger/Sandbox.h>
#include <xrpl/protocol/Asset.h>
#include <xrpl/protocol/Indexes.h>
#include <xrpl/protocol/MPTIssue.h>
#include <xrpl/protocol/SField.h>
#include <xrpl/protocol/STAmount.h>
#include <xrpl/protocol/STLedgerEntry.h>
#include <xrpl/protocol/STNumber.h>

#include <cstdint>

namespace xrpl::test::formal_verification {

inline Keylet
createVault(jtx::Env& env, jtx::Account const& owner, Asset const& asset)
{
    jtx::Vault vault{env};
    auto const [jv, keylet] = vault.create({.owner = owner, .asset = asset});
    env(jv);
    env.close();
    return keylet;
}

// Snapshot the on-ledger vault into the model's VaultState DTO
inline VaultState
readVaultState(jtx::Env& env, Keylet const& vaultKeylet, Asset const& asset)
{
    auto const vaultSle = env.le(vaultKeylet);
    auto const shareMptId = vaultSle->at(sfShareMPTID);
    return VaultState{
        .assetsTotal = vaultSle->at(sfAssetsTotal),
        .assetsAvailable = vaultSle->at(sfAssetsAvailable),
        .hasMaximum = vaultSle->isFieldPresent(sfAssetsMaximum),
        .assetsMaximum = vaultSle->at(sfAssetsMaximum),
        .numericType = NumericTypeFFI::tagOf(asset),
        .scale = vaultSle->at(sfScale),
        .sharesTotal = Number{static_cast<std::int64_t>(
            env.le(keylet::mptokenIssuance(shareMptId))->at(sfOutstandingAmount))},
        .lossUnrealized = vaultSle->at(sfLossUnrealized)};
}

// Overwrite the vault totals and share issuance outstanding on the open ledger to reach states a
// real transaction cannot. Returns false if the vault or issuance is missing.
[[nodiscard]] inline bool
updateVaultState(
    jtx::Env& env,
    Keylet const& vaultKeylet,
    Number const& assetsTotal,
    Number const& assetsAvailable,
    std::uint64_t sharesTotal,
    Number const& assetsMaximum = Number{0},
    Number const& lossUnrealized = Number{0})
{
    return env.app().getOpenLedger().modify(  //
        [&](OpenView& view, beast::Journal) -> bool {
            Sandbox sb(&view, TapNone);
            auto v = sb.peek(vaultKeylet);
            if (!v)
                return false;
            auto iss = sb.peek(keylet::mptokenIssuance(v->at(sfShareMPTID)));
            if (!iss)
                return false;
            v->at(sfAssetsTotal) = assetsTotal;
            v->at(sfAssetsAvailable) = assetsAvailable;
            v->at(sfAssetsMaximum) = assetsMaximum;
            v->at(sfLossUnrealized) = lossUnrealized;
            iss->setFieldU64(sfOutstandingAmount, sharesTotal);
            sb.update(v);
            sb.update(iss);
            sb.apply(view);
            return true;
        });
}

// True iff totalA / sharesA >= totalB / sharesB, compared exactly via an int128 cross-multiply
// (a Number multiply would re-round and hide a sub-ULP dilution).
[[nodiscard]] inline bool
priceNotBelow(
    Number const& totalA,
    Number const& sharesA,
    Number const& totalB,
    Number const& sharesB)
{
    __int128 lhs = static_cast<__int128>(totalA.mantissa()) * sharesB.mantissa();
    __int128 rhs = static_cast<__int128>(totalB.mantissa()) * sharesA.mantissa();
    int const eL = totalA.exponent() + sharesB.exponent();
    int const eR = totalB.exponent() + sharesA.exponent();
    int const e = eL < eR ? eL : eR;
    for (int i = e; i < eL; ++i)
        lhs *= 10;
    for (int i = e; i < eR; ++i)
        rhs *= 10;
    return lhs >= rhs;
}

// Build a NAV-drifted IOU vault by real deposits: the holder deposits 899999999.876543 (minting
// 899999999876543 shares at the default scale 6) and the owner donates 123.4567891 (no shares), so
// assetsTotal = 900000123.3333321 and the share price is a non-terminating decimal.
[[nodiscard]] inline Keylet
createDilutionVault(
    jtx::Env& env,
    jtx::Account const& owner,
    jtx::Account const& issuer,
    jtx::Account const& holder,
    jtx::PrettyAsset const& asset,
    Number const& holderExtra = Number{0})
{
    using namespace jtx;
    env.fund(XRP(1'000'000), owner, issuer, holder);
    env.close();
    env(fset(issuer, asfAllowTrustLineClawback));  // for the clawback variant
    env.close();
    env(trust(owner, asset(1'000'000)));
    env(trust(holder, asset(2'000'000'000)));
    env.close();

    Number const seed{899'999'999'876'543LL, -6};
    Number const donation{1'234'567'891LL, -7};
    env(pay(issuer, holder, asset(seed + holderExtra)));
    env(pay(issuer, owner, asset(donation)));
    env.close();

    auto const keylet = createVault(env, owner, asset.raw());
    env(Vault::deposit({.depositor = holder, .id = keylet.key, .amount = asset(seed)}));
    env.close();
    env(Vault::deposit(
        {.depositor = owner, .id = keylet.key, .amount = asset(donation), .flags = tfVaultDonate}));
    env.close();
    return keylet;
}

// A scale-18 vault mints 7e15 shares for a 0.007 deposit, then a 2.993 owner donation lifts
// the total to 3. The share price 3/7e15 puts every round-trip amount off the vault grid.
[[nodiscard]] inline Keylet
createAppliedDeltaVault(
    jtx::Env& env,
    jtx::Account const& owner,
    jtx::Account const& issuer,
    jtx::Account const& holder,
    jtx::PrettyAsset const& asset)
{
    using namespace jtx;
    env.fund(XRP(1'000'000), owner, issuer, holder);
    env.close();
    // Clawback must be enabled while the issuer has no trust line yet.
    env(fset(issuer, asfAllowTrustLineClawback));
    env.close();
    env(trust(owner, asset(10)));
    env(trust(holder, asset(10)));
    env.close();
    env(pay(issuer, owner, asset(Number{2'993, -3})));
    env(pay(issuer, holder, asset(Number{1})));
    env.close();

    Vault vault{env};
    auto [tx, keylet] = vault.create({.owner = owner, .asset = asset.raw()});
    tx[sfScale] = 18;
    env(tx);
    env.close();

    env(Vault::deposit({.depositor = holder, .id = keylet.key, .amount = asset(Number{7, -3})}));
    env.close();
    env(Vault::deposit(
        {.depositor = owner,
         .id = keylet.key,
         .amount = asset(Number{2'993, -3}),
         .flags = tfVaultDonate}));
    env.close();
    return keylet;
}

// The account's IOU balance as a Number.
[[nodiscard]] inline Number
iouBalance(jtx::Env& env, jtx::Account const& account, jtx::PrettyAsset const& asset)
{
    return env.balance(account, asset.raw().get<Issue>()).value();
}

// Replicates the file-static roundToVaultScale from VaultDeposit.cpp: round the amount down
// to the scale the vault total has after adding it.
[[nodiscard]] inline STAmount
roundToVaultScale(jtx::PrettyAsset const& asset, Number const& assetsTotal, Number const& amount)
{
    int const postScale = [&] {
        NumberRoundModeGuard const rg(Number::RoundingMode::ToNearest);
        return scale(assetsTotal + amount, asset.raw());
    }();
    return roundToScale(STAmount{asset.raw(), amount}, postScale, Number::RoundingMode::Downward);
}

}  // namespace xrpl::test::formal_verification
