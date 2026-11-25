import XRPL.Properties.Vault.Common.ReachableDefs
import XRPL.Properties.Vault.Proofs.Reachable
import XRPL.Properties.Vault.Proofs.ReachableTotal
import XRPL.Properties.Vault.Proofs.MaxValueFits
import XRPL.Properties.Vault.Proofs.Support.VaultBalances
import XRPL.Properties.Vault.Proofs.ShareWorth

/-! # Vault reachability

`Vault.Reachable v t` holds when `v` results from `Vault.create` and successful vault transactions, the last at close
time `t`. A reachable vault keeps its cash in the Open zone, so every cash update on it is exact. -/

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol

/-- Every vault reachable by vault transactions is lawful. -/
theorem Vault.Reachable.lawful (v : Vault) (t : UInt32) (_hr : Vault.Reachable v t) :
    v.toRawVault.WF ∧ v.toRawVault.Valid := by
  sorry

/-- Every reachable vault -> AssetsDeployed = AssetsReserved = LossUnrealized = YieldUnrealized = 0, AssetsTotal =
AssetsAvailable ≤ the Open limit (9·10^15 base units), and every share is worth at least one base unit of cash. -/
theorem Vault.Reachable.vault_fields (v : Vault) (t : UInt32) (hr : Vault.Reachable v t) :
    (v.toExact.assetsDeployed = 0 ∧ v.toExact.assetsReserved = 0 ∧ v.toExact.lossUnrealized = 0 ∧
      v.toExact.yieldUnrealized = 0) ∧
    v.assetsTotal = .ok v.assetsAvailable ∧
    v.assetsAvailable.toRat ≤ 9 * (10 : ℚ) ^ (15 + v.baseExponent) ∧
    (v.toExact.sharesTotal : ℚ) * 10 ^ v.baseExponent ≤ v.assetsAvailable.toRat := by
  sorry

/-- On a reachable vault -> a deposit adds exactly its charge and minted shares, a withdrawal or clawback subtracts
exactly its payout and burned shares. A deposit never decreases the cash, withdrawal and clawback never increase it. -/
theorem Vault.vault_updates_exact (v : Vault) (t0 : UInt32) (hr : Vault.Reachable v t0) :
    (∀ (amount : STAmount) (isDonation : Bool) (t : UInt32) (hpos : 0 < amount.toRat),
      amount.Canonical →
      amount.mNumericType = v.numericType →
      ∀ r : VaultWithAmounts, (v.deposit amount isDonation t hpos).run = .ok (.ok r) →
        r.vault'.assetsAvailable.toRat = v.assetsAvailable.toRat + r.assets.toRat ∧
          (r.vault'.toExact.sharesTotal : ℚ) = v.toExact.sharesTotal + r.shares.toRat ∧
          v.assetsAvailable.toRat ≤ r.vault'.assetsAvailable.toRat) ∧
    (∀ (amount : WithdrawAmount) (waive : Bool) (t : UInt32) (hpos : 0 < amount.amount.toRat),
      amount.amount.Canonical →
      amount.InAsset v.numericType →
      ∀ r : VaultWithAmounts, (v.withdraw amount waive t hpos).run = .ok (.ok r) →
        r.vault'.assetsAvailable.toRat = v.assetsAvailable.toRat - r.assets.toRat ∧
          (r.vault'.toExact.sharesTotal : ℚ) = v.toExact.sharesTotal - r.shares.toRat ∧
          r.vault'.assetsAvailable.toRat ≤ v.assetsAvailable.toRat) ∧
    ∀ (assets holderShares : STAmount) (waive : Bool) (hnn : 0 ≤ assets.toRat),
      assets.CanonicalOrZero → -- a clawback amount is canonical, or zero to claw back the holding
      holderShares.ShareBalance →
      ∀ r : VaultWithAmounts, (v.clawback assets holderShares waive hnn).run = .ok (.ok r) →
        r.vault'.assetsAvailable.toRat = v.assetsAvailable.toRat - r.assets.toRat ∧
          (r.vault'.toExact.sharesTotal : ℚ) = v.toExact.sharesTotal - r.shares.toRat ∧
          r.vault'.assetsAvailable.toRat ≤ v.assetsAvailable.toRat := by
  sorry

end XRPL.Model.SingleAssetVault
