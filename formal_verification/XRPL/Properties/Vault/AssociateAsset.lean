import XRPL.Properties.Vault.Proofs.AssociateAssetPreserve
import XRPL.Properties.Vault.Proofs.Reachable
import XRPL.Properties.Vault.Proofs.MaxValueFits

/-! # `associateAsset` is a no-op

Every vault transactor calls `associateAsset` on the vault SLE after updating it, which rounds
each `kSmdNeedsAsset` field (`assetsTotal`, `assetsAvailable`, `assetsDeployed`, `assetsReserved`,
`lossUnrealized`, `yieldUnrealized`, `assetsMaximum`) to the asset's precision. The model has no such
step, and on a reachable vault every such amount is stored exactly, so the step changes nothing. -/

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol

/-- `associateAsset` changes nothing on a reachable vault: the asset stores every amount the vault
records exactly, and the total is the cash. -/
theorem Vault.Reachable.associateAsset_noop (v : Vault) (t : UInt32) (hr : Vault.Reachable v t) :
    ¬ v.assetsRounded ∧ v.assetsTotal = .ok v.assetsAvailable :=
  ⟨Vault.Reachable.associateAsset_noop_of_cashExact v t hr (Vault.Reachable.assetsAvailable_exact_proof v t hr),
    Vault.Reachable.asset_parity_proof v t hr⟩

/-- A deposit stores its new cash exactly and leaves the other amounts `associateAsset` rounds, except AssetsTotal,
as they were. -/
theorem Vault.deposit_associateAsset_noop (v : Vault) (amount : STAmount) (isDonation : Bool) (t : UInt32)
    (hpos : 0 < amount.toRat)
    -- the asset's maximum fits an int64 amount, as C++ caps every MPT maximum
    (hmax : v.numericType.isIntegral = true → v.numericType.maxValue.toNat ≤ maxRep.toNat)
    (r : VaultWithAmounts) (hok : (v.deposit amount isDonation t hpos).run = .ok (.ok r)) :
    STAmount.isRounded v.numericType r.vault'.assetsAvailable = false ∧ r.vault'.assetsDeployed = v.assetsDeployed ∧
      r.vault'.assetsReserved = v.assetsReserved ∧ r.vault'.lossUnrealized = v.lossUnrealized ∧
      r.vault'.yieldUnrealized = v.yieldUnrealized ∧ r.vault'.assetsMaximum = v.assetsMaximum :=
  Vault.deposit_associateAsset_noop_proof v amount isDonation t hpos hmax r hok

/-- A withdrawal stores its new cash exactly and leaves the other amounts `associateAsset` rounds, except
AssetsTotal, as they were. -/
theorem Vault.withdraw_associateAsset_noop (v : Vault) (amount : WithdrawAmount) (waive : Bool) (t : UInt32)
    (hpos : 0 < amount.amount.toRat)
    -- the asset's maximum fits an int64 amount, as C++ caps every MPT maximum
    (hmax : v.numericType.isIntegral = true → v.numericType.maxValue.toNat ≤ maxRep.toNat)
    (r : VaultWithAmounts) (hok : (v.withdraw amount waive t hpos).run = .ok (.ok r)) :
    STAmount.isRounded v.numericType r.vault'.assetsAvailable = false ∧ r.vault'.assetsDeployed = v.assetsDeployed ∧
      r.vault'.assetsReserved = v.assetsReserved ∧ r.vault'.lossUnrealized = v.lossUnrealized ∧
      r.vault'.yieldUnrealized = v.yieldUnrealized ∧ r.vault'.assetsMaximum = v.assetsMaximum :=
  Vault.withdraw_associateAsset_noop_proof v amount waive t hpos hmax r hok

/-- A clawback stores its new cash exactly and leaves the other amounts `associateAsset` rounds, except AssetsTotal,
as they were. -/
theorem Vault.clawback_associateAsset_noop (v : Vault) (assets holderShares : STAmount) (waive : Bool)
    (hnn : 0 ≤ assets.toRat)
    -- the asset's maximum fits an int64 amount, as C++ caps every MPT maximum
    (hmax : v.numericType.isIntegral = true → v.numericType.maxValue.toNat ≤ maxRep.toNat)
    (r : VaultWithAmounts) (hok : (v.clawback assets holderShares waive hnn).run = .ok (.ok r)) :
    STAmount.isRounded v.numericType r.vault'.assetsAvailable = false ∧ r.vault'.assetsDeployed = v.assetsDeployed ∧
      r.vault'.assetsReserved = v.assetsReserved ∧ r.vault'.lossUnrealized = v.lossUnrealized ∧
      r.vault'.yieldUnrealized = v.yieldUnrealized ∧ r.vault'.assetsMaximum = v.assetsMaximum :=
  Vault.clawback_associateAsset_noop_proof v assets holderShares waive hnn hmax r hok

/-- A deposit into a vault that stores every amount `associateAsset` rounds, other than AssetsTotal, exactly keeps
them all stored exactly. -/
theorem Vault.deposit_assetsRounded_preserved (v : Vault) (amount : STAmount) (isDonation : Bool) (t : UInt32)
    (hpos : 0 < amount.toRat)
    -- the asset's maximum fits an int64 amount, as C++ caps every MPT maximum
    (hmax : v.numericType.isIntegral = true → v.numericType.maxValue.toNat ≤ maxRep.toNat)
    (r : VaultWithAmounts) (hok : (v.deposit amount isDonation t hpos).run = .ok (.ok r))
    (hv : ¬ v.assetsRounded) : ¬ r.vault'.assetsRounded :=
  Vault.deposit_assetsRounded_preserved_proof v amount isDonation t hpos hmax r hok hv

/-- A withdrawal from a vault that stores every amount `associateAsset` rounds, other than AssetsTotal, exactly
keeps them all stored exactly. -/
theorem Vault.withdraw_assetsRounded_preserved (v : Vault) (amount : WithdrawAmount) (waive : Bool) (t : UInt32)
    (hpos : 0 < amount.amount.toRat)
    -- the asset's maximum fits an int64 amount, as C++ caps every MPT maximum
    (hmax : v.numericType.isIntegral = true → v.numericType.maxValue.toNat ≤ maxRep.toNat)
    (r : VaultWithAmounts) (hok : (v.withdraw amount waive t hpos).run = .ok (.ok r))
    (hv : ¬ v.assetsRounded) : ¬ r.vault'.assetsRounded :=
  Vault.withdraw_assetsRounded_preserved_proof v amount waive t hpos hmax r hok hv

/-- A clawback from a vault that stores every amount `associateAsset` rounds, other than AssetsTotal, exactly
keeps them all stored exactly. -/
theorem Vault.clawback_assetsRounded_preserved (v : Vault) (assets holderShares : STAmount) (waive : Bool)
    (hnn : 0 ≤ assets.toRat)
    -- the asset's maximum fits an int64 amount, as C++ caps every MPT maximum
    (hmax : v.numericType.isIntegral = true → v.numericType.maxValue.toNat ≤ maxRep.toNat)
    (r : VaultWithAmounts) (hok : (v.clawback assets holderShares waive hnn).run = .ok (.ok r))
    (hv : ¬ v.assetsRounded) : ¬ r.vault'.assetsRounded :=
  Vault.clawback_assetsRounded_preserved_proof v assets holderShares waive hnn hmax r hok hv

end XRPL.Model.SingleAssetVault
