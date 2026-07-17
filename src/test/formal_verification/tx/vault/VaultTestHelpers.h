#pragma once

#include <test/formal_verification/ffi/vault/VaultStateFFI.h>
#include <test/jtx.h>
#include <test/jtx/vault.h>

#include <xrpl/basics/Number.h>
#include <xrpl/ledger/OpenView.h>
#include <xrpl/ledger/Sandbox.h>
#include <xrpl/protocol/Asset.h>
#include <xrpl/protocol/Indexes.h>
#include <xrpl/protocol/MPTIssue.h>
#include <xrpl/protocol/SField.h>
#include <xrpl/protocol/STLedgerEntry.h>

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
        .numericType = NumericTypeFFI::tagOf(asset),
        .scale = vaultSle->at(sfScale),
        .sharesTotal = Number{static_cast<std::int64_t>(
            env.le(keylet::mptIssuance(shareMptId))->at(sfOutstandingAmount))},
        .interestUnrealized = vaultSle->at(sfInterestUnrealized),
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
    std::uint64_t sharesTotal)
{
    return env.app().getOpenLedger().modify(  //
        [&](OpenView& view, beast::Journal) -> bool {
            Sandbox sb(&view, TapNone);
            auto v = sb.peek(vaultKeylet);
            if (!v)
                return false;
            auto iss = sb.peek(keylet::mptIssuance(v->at(sfShareMPTID)));
            if (!iss)
                return false;
            v->at(sfAssetsTotal) = assetsTotal;
            v->at(sfAssetsAvailable) = assetsAvailable;
            iss->setFieldU64(sfOutstandingAmount, sharesTotal);
            sb.update(v);
            sb.update(iss);
            sb.apply(view);
            return true;
        });
}

}  // namespace xrpl::test::formal_verification
