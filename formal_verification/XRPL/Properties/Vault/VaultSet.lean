import XRPL.Properties.Vault.Defs
import XRPL.Properties.Vault.Common.GuardProofs
import XRPL.Model.Vault.VaultSet

/-! # `Vault.canVaultSet` exits -/

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol

variable (v : Vault)

/-! ## `Vault.canVaultSet` -/

/-- A nonzero new maximum below the current assets total: `tecLIMIT_EXCEEDED`. -/
theorem Vault.canVaultSet_below_total (assetsMaximum : Number)
    (hne : assetsMaximum.operator_ne Number.zero = true) -- the new maximum is nonzero
    (hlt : assetsMaximum.operator_lt v.assetsTotal = true) : -- and compares below the assets total
    v.canVaultSet assetsMaximum = .tecLIMIT_EXCEEDED := by
  unfold Vault.canVaultSet
  exact if_pos (by rw [Bool.and_eq_true]; exact ⟨hne, hlt⟩)

/-- A new maximum that compares equal to zero, or does not compare below the
current assets total, passes. Zero requests removing the cap. -/
theorem Vault.canVaultSet_success (assetsMaximum : Number)
    -- the failure guard is off: the maximum is zero or not below the assets total
    (hok : (assetsMaximum.operator_ne Number.zero &&
        assetsMaximum.operator_lt v.assetsTotal) = false) :
    v.canVaultSet assetsMaximum = .tesSUCCESS := by
  unfold Vault.canVaultSet
  exact if_neg (by rw [Bool.not_eq_true]; exact hok)

/-- Every outcome of the check: `tecLIMIT_EXCEEDED` is the only rejection
`canVaultSet` can return. -/
theorem Vault.canVaultSet_error_codes (assetsMaximum : Number) :
    v.canVaultSet assetsMaximum = .tesSUCCESS ∨
    v.canVaultSet assetsMaximum = .tecLIMIT_EXCEEDED := by
  unfold Vault.canVaultSet
  split_ifs <;> first | exact Or.inl rfl | exact Or.inr rfl

/-- On a lawful vault, a normalized new maximum passes exactly when it is zero
or at least the exact assets total. -/
theorem Vault.lawful_canVaultSet_iff
    (hv : v.Lawful) -- the starting vault is lawful
    (assetsMaximum : Number)
    (hnorm : assetsMaximum.isNormalized) : -- the new maximum is normalized
    v.canVaultSet assetsMaximum = .tesSUCCESS ↔
      assetsMaximum.toRat = 0 ∨ v.toExact.assetsTotal ≤ assetsMaximum.toRat := by
  have htotal : v.assetsTotal.isNormalized := hv.wf.assetsTotal_norm
  -- the nonzero guard vanishes exactly at rational zero
  have hb1 : assetsMaximum.operator_ne Number.zero = false ↔ assetsMaximum.toRat = 0 :=
    Number.operator_ne_zero_eq_false_iff assetsMaximum hnorm
  -- the below-total guard vanishes exactly when the maximum is at least the total
  have hb2 : assetsMaximum.operator_lt v.assetsTotal = false ↔
      v.assetsTotal.toRat ≤ assetsMaximum.toRat := by
    rw [Bool.eq_false_iff, ne_eq, operator_lt_iff assetsMaximum v.assetsTotal hnorm htotal, not_lt]
  -- `v.toExact.assetsTotal` is `v.assetsTotal.toRat` by definition of `toExact`
  show v.canVaultSet assetsMaximum = .tesSUCCESS ↔
      assetsMaximum.toRat = 0 ∨ v.assetsTotal.toRat ≤ assetsMaximum.toRat
  unfold Vault.canVaultSet
  by_cases hc : (assetsMaximum.operator_ne Number.zero &&
      assetsMaximum.operator_lt v.assetsTotal) = true
  · rw [if_pos hc]
    rw [Bool.and_eq_true] at hc
    refine iff_of_false (by decide) ?_
    rintro (h0 | hle)
    · rw [hb1.mpr h0] at hc; exact absurd hc.1 (by decide)
    · rw [hb2.mpr hle] at hc; exact absurd hc.2 (by decide)
  · rw [if_neg hc]
    rw [Bool.not_eq_true, Bool.and_eq_false_iff] at hc
    refine iff_of_true rfl ?_
    rcases hc with h1 | h2
    · exact Or.inl (hb1.mp h1)
    · exact Or.inr (hb2.mp h2)

end XRPL.Model.SingleAssetVault
