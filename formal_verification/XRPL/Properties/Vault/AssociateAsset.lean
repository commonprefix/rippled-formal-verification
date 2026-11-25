import XRPL.Properties.Vault.Proofs.AssociateAssetPreserve
import XRPL.Properties.Vault.Proofs.Reachable
import XRPL.Properties.Vault.Proofs.MaxValueFits

/-! # `associateAsset` is a no-op

Every vault transactor calls `associateAsset`, which rounds each asset amount of the vault to the asset's precision.
The model omits it. On a reachable vault each such amount is stored exactly, so the step changes nothing. -/

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol

/-- `associateAsset` changes nothing on a reachable vault: the asset stores every amount the vault
records exactly, and the total is the cash. -/
theorem Vault.Reachable.associateAsset_noop (v : Vault) (t : UInt32) (hr : Vault.Reachable v t) :
    ¬ v.assetsRounded ∧ v.assetsTotal = .ok v.assetsAvailable := by
  sorry

/-- A deposit stores its new cash exactly and leaves the other amounts `associateAsset` rounds, except AssetsTotal,
as they were. -/
theorem Vault.deposit_associateAsset_noop (v : Vault) (amount : STAmount) (isDonation : Bool) (t : UInt32)
    (hpos : 0 < amount.toRat)
    -- the asset's maximum fits an int64 amount, as C++ caps every MPT maximum
    (hmax : v.numericType.isIntegral = true → v.numericType.maxValue.toNat ≤ maxRep.toNat)
    (r : VaultWithAmounts) (hok : (v.deposit amount isDonation t hpos).run = .ok (.ok r)) :
    STAmount.isRounded v.numericType r.vault'.assetsAvailable = false ∧ r.vault'.assetsDeployed = v.assetsDeployed ∧
      r.vault'.assetsReserved = v.assetsReserved ∧ r.vault'.lossUnrealized = v.lossUnrealized ∧
      r.vault'.yieldUnrealized = v.yieldUnrealized ∧ r.vault'.assetsMaximum = v.assetsMaximum := by
  sorry

/-- A withdrawal stores its new cash exactly and leaves the other amounts `associateAsset` rounds, except
AssetsTotal, as they were. -/
theorem Vault.withdraw_associateAsset_noop (v : Vault) (amount : WithdrawAmount) (waive : Bool) (t : UInt32)
    (hpos : 0 < amount.amount.toRat)
    -- the asset's maximum fits an int64 amount, as C++ caps every MPT maximum
    (hmax : v.numericType.isIntegral = true → v.numericType.maxValue.toNat ≤ maxRep.toNat)
    (r : VaultWithAmounts) (hok : (v.withdraw amount waive t hpos).run = .ok (.ok r)) :
    STAmount.isRounded v.numericType r.vault'.assetsAvailable = false ∧ r.vault'.assetsDeployed = v.assetsDeployed ∧
      r.vault'.assetsReserved = v.assetsReserved ∧ r.vault'.lossUnrealized = v.lossUnrealized ∧
      r.vault'.yieldUnrealized = v.yieldUnrealized ∧ r.vault'.assetsMaximum = v.assetsMaximum := by
  sorry

/-- A clawback stores its new cash exactly and leaves the other amounts `associateAsset` rounds, except AssetsTotal,
as they were. -/
theorem Vault.clawback_associateAsset_noop (v : Vault) (assets holderShares : STAmount) (waive : Bool)
    (hnn : 0 ≤ assets.toRat)
    -- the asset's maximum fits an int64 amount, as C++ caps every MPT maximum
    (hmax : v.numericType.isIntegral = true → v.numericType.maxValue.toNat ≤ maxRep.toNat)
    (r : VaultWithAmounts) (hok : (v.clawback assets holderShares waive hnn).run = .ok (.ok r)) :
    STAmount.isRounded v.numericType r.vault'.assetsAvailable = false ∧ r.vault'.assetsDeployed = v.assetsDeployed ∧
      r.vault'.assetsReserved = v.assetsReserved ∧ r.vault'.lossUnrealized = v.lossUnrealized ∧
      r.vault'.yieldUnrealized = v.yieldUnrealized ∧ r.vault'.assetsMaximum = v.assetsMaximum := by
  sorry

end XRPL.Model.SingleAssetVault
