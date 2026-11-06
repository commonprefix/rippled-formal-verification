import XRPL.Properties.Vault.Proofs.OpenZone

/-! # Operations keep the vault's amounts stored exactly

`associateAsset` rounds each vault amount to the asset's precision. A deposit, withdrawal or
clawback rounds its new cash to the asset, and touches no other such amount, so the step has
nothing left to round in the amounts the operation writes. -/

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol

/-- The cash update leaves the asset storing every amount `associateAsset` rounds as before: the new
cash exactly, the other amounts unchanged. -/
private lemma Vault.adjustAssetsAndShares_associateAsset (v v' : Vault) (assets shares : STAmount) (raw : RawVault)
    (hmax : v.numericType.isIntegral = true → v.numericType.maxValue.toNat ≤ maxRep.toNat)
    (hadj : (v.adjustAssetsAndShares assets shares).run = .ok (.ok raw)) (hv' : v'.toRawVault = raw) :
    STAmount.isRounded v.numericType v'.assetsAvailable = false ∧ v'.assetsDeployed = v.assetsDeployed ∧
      v'.assetsReserved = v.assetsReserved ∧ v'.lossUnrealized = v.lossUnrealized ∧
      v'.yieldUnrealized = v.yieldUnrealized ∧ v'.assetsMaximum = v.assetsMaximum := by
  obtain ⟨_, _, s, aa', st', -, -, -, -, haa, rfl⟩ := Vault.adjustAssetsAndShares_ok_reduces v _ _ _ hadj
  have hAA : v'.assetsAvailable = aa' := (congrArg RawVault.assetsAvailable hv').trans rfl
  have h0 : 0 ≤ aa'.toRat := hAA ▸ v'.exact.assetsAvailable_nonneg
  exact ⟨by rw [hAA]; exact STAmount.isRounded_eq_false_of_rounded _ s aa' hmax haa h0,
    (congrArg RawVault.assetsDeployed hv').trans rfl, (congrArg RawVault.assetsReserved hv').trans rfl,
    (congrArg RawVault.lossUnrealized hv').trans rfl, (congrArg RawVault.yieldUnrealized hv').trans rfl,
    (congrArg RawVault.assetsMaximum hv').trans rfl⟩

lemma Vault.deposit_associateAsset_noop_proof (v : Vault) (amount : STAmount) (isDonation : Bool) (t : UInt32)
    (hpos : 0 < amount.toRat)
    (hmax : v.numericType.isIntegral = true → v.numericType.maxValue.toNat ≤ maxRep.toNat)
    (r : VaultWithAmounts) (hok : (v.deposit amount isDonation t hpos).run = .ok (.ok r)) :
    STAmount.isRounded v.numericType r.vault'.assetsAvailable = false ∧ r.vault'.assetsDeployed = v.assetsDeployed ∧
      r.vault'.assetsReserved = v.assetsReserved ∧ r.vault'.lossUnrealized = v.lossUnrealized ∧
      r.vault'.yieldUnrealized = v.yieldUnrealized ∧ r.vault'.assetsMaximum = v.assetsMaximum := by
  obtain ⟨_, _, raw, -, -, -, hadj, hraw, -⟩ := Vault.deposit_ok_reduces v amount isDonation t hpos r hok
  exact Vault.adjustAssetsAndShares_associateAsset v r.vault' _ _ raw hmax hadj hraw

lemma Vault.withdraw_associateAsset_noop_proof (v : Vault) (amount : WithdrawAmount) (waive : Bool) (t : UInt32)
    (hpos : 0 < amount.amount.toRat)
    (hmax : v.numericType.isIntegral = true → v.numericType.maxValue.toNat ≤ maxRep.toNat)
    (r : VaultWithAmounts) (hok : (v.withdraw amount waive t hpos).run = .ok (.ok r)) :
    STAmount.isRounded v.numericType r.vault'.assetsAvailable = false ∧ r.vault'.assetsDeployed = v.assetsDeployed ∧
      r.vault'.assetsReserved = v.assetsReserved ∧ r.vault'.lossUnrealized = v.lossUnrealized ∧
      r.vault'.yieldUnrealized = v.yieldUnrealized ∧ r.vault'.assetsMaximum = v.assetsMaximum := by
  obtain ⟨raw, hadj, hraw⟩ := Vault.withdraw_ok_reduces v amount waive t hpos r hok
  exact Vault.adjustAssetsAndShares_associateAsset v r.vault' _ _ raw hmax hadj hraw

lemma Vault.clawback_associateAsset_noop_proof (v : Vault) (assets holderShares : STAmount) (waive : Bool)
    (hnn : 0 ≤ assets.toRat)
    (hmax : v.numericType.isIntegral = true → v.numericType.maxValue.toNat ≤ maxRep.toNat)
    (r : VaultWithAmounts) (hok : (v.clawback assets holderShares waive hnn).run = .ok (.ok r)) :
    STAmount.isRounded v.numericType r.vault'.assetsAvailable = false ∧ r.vault'.assetsDeployed = v.assetsDeployed ∧
      r.vault'.assetsReserved = v.assetsReserved ∧ r.vault'.lossUnrealized = v.lossUnrealized ∧
      r.vault'.yieldUnrealized = v.yieldUnrealized ∧ r.vault'.assetsMaximum = v.assetsMaximum := by
  obtain ⟨_, raw, -, hadj, hraw, -, -⟩ := Vault.clawback_ok_reduces v assets holderShares waive hnn r hok
  exact Vault.adjustAssetsAndShares_associateAsset v r.vault' _ _ raw hmax hadj hraw

end XRPL.Model.SingleAssetVault
