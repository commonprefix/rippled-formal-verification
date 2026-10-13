import XRPL.Properties.Vault.Common.ClawbackDefs
import XRPL.Properties.Vault.VaultValid

/-! # Identities of the ideal exchange formulas

Pure `ℚ` facts about the ideal (exact) conversions; no `Number`, rounding or
clamp is involved. -/

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol

/-- When the exchange rate still equals `10 ^ scale`, `idealSharesDeposit` is the
empty-vault formula. -/
lemma Vault.idealSharesDeposit_initial_rate_proof (v : Vault) (amount : ℚ)
    (hrate : (v.toExact.sharesTotal : ℚ) =
      v.depositNav * (10 : ℚ) ^ v.scale.toNat) :
    v.idealSharesDeposit amount = amount * (10 : ℚ) ^ v.scale.toNat := by
  unfold RawVault.idealSharesDeposit
  by_cases h : v.toExact.assetsTotal = 0
  · rw [if_pos h]
  · rw [if_neg h]
    have hpos : 0 < v.toExact.assetsTotal :=
      lt_of_le_of_ne v.exact.assetsTotal_nonneg (Ne.symm h)
    have hnav : (0 : ℚ) < v.depositNav := by
      unfold RawVault.depositNav; exact hpos
    have hne : v.depositNav ≠ 0 := hnav.ne'
    rw [hrate]; field_simp

/-- **Proof body of `idealAssetsClawback_idealSharesClawback`.** -/
lemma RawVault.idealAssetsClawback_idealSharesClawback_proof (rv : RawVault) (assets : ℚ)
    (hnav : rv.withdrawNav ≠ 0) (hsh : rv.toExact.sharesTotal ≠ 0) :
    rv.idealAssetsClawback (rv.idealSharesClawback assets) = assets := by
  unfold RawVault.idealAssetsClawback RawVault.idealSharesClawback
  have hsh' : ((rv.toExact.sharesTotal : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hsh
  field_simp

end XRPL.Model.SingleAssetVault
