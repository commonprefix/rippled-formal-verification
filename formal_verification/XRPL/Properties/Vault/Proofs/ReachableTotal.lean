import XRPL.Properties.Vault.Proofs.Reachable
import XRPL.Properties.Vault.Proofs.TotalStored

/-! # A reachable vault stores its total

C++ `adjustVaultBalances` ends with `syncAssetsTotal`, which stores AssetsAvailable + AssetsDeployed as an amount of
the asset. A new vault holds nothing, and every transaction either runs that update or leaves the two balances. -/

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol

/-- On a reachable vault AssetsAvailable + AssetsDeployed is an amount of the asset. -/
lemma Vault.Reachable.totalStored (v : Vault) (t : UInt32) (hr : Vault.Reachable v t) : v.TotalStored := by
  induction hr with
  | create _ _ _ _ _ _ _ w _ hcr =>
    have hv := Vault.create_ok_toRawVault hcr
    have hAA : w.assetsAvailable = Number.zero := (congrArg RawVault.assetsAvailable hv).trans rfl
    have hAD : w.assetsDeployed = Number.zero := (congrArg RawVault.assetsDeployed hv).trans rfl
    unfold Vault.TotalStored
    rw [hAA, hAD]
    exact TotalStores.of_zero_deployed _ Number.zero Number.zero_isNormalized (by rw [Number.toRat_zero])
      (STAmount.isRounded_zero _)
  | deposit u _ _ _ _ r _ _ _ _ _ hok _ _ => exact Vault.deposit_totalStored u _ _ _ _ r hok
  | withdraw u _ _ _ _ _ r _ _ _ _ _ _ _ hok _ _ => exact Vault.withdraw_totalStored u _ _ _ _ r hok
  | clawback u _ _ _ _ _ r _ _ _ _ _ _ _ hok _ _ => exact Vault.clawback_totalStored u _ _ _ _ r hok
  | burnShares u _ _ _ _ _ v' _ _ _ _ hok ih => exact Vault.burnShares_totalStored u _ v' hok ih
  | update u _ _ _ _ v' _ _ _ hok ih => exact Vault.update_totalStored u _ _ v' hok ih

end XRPL.Model.SingleAssetVault
