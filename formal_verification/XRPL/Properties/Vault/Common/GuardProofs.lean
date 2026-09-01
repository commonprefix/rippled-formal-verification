import XRPL.Properties.Vault.Defs
import XRPL.Properties.Vault.LawfulVaultValid
import XRPL.Properties.Protocol.Number.Compare.Compare
import XRPL.Properties.Protocol.Number.Common.ToRatLemmas
import XRPL.Model.Vault.VaultSet
import XRPL.Model.Vault.VaultDelete

/-! # Shared bridges for the pure vault guards

`canVaultSet` and `canVaultDelete` are boolean guards over `Number.operator_ne` /
`Number.operator_lt`. Their exit theorems need two bridges:

* a structural one, `operator_eq`/`operator_ne` decide record equality of the
  three `Number` fields, used where the statement compares against `Number.zero`
  with `=`/`≠`;
* the rational one from `Compare`, `operator_ne`/`operator_lt` agree with the
  order on `toRat` once both sides are normalized.
-/

namespace XRPL.Model.Protocol

/-- `Number.operator_eq` decides structural record equality. -/
theorem Number.operator_eq_iff_eq (x y : Number) :
    x.operator_eq y = true ↔ x = y := by
  unfold Number.operator_eq
  rw [Bool.and_eq_true, Bool.and_eq_true, beq_iff_eq, beq_iff_eq, beq_iff_eq]
  constructor
  · rintro ⟨⟨hn, hm⟩, he⟩
    obtain ⟨xn, xm, xe⟩ := x
    obtain ⟨yn, ym, ye⟩ := y
    simp only at hn hm he
    subst hn; subst hm; subst he; rfl
  · rintro rfl
    exact ⟨⟨rfl, rfl⟩, rfl⟩

/-- `Number.operator_ne` decides structural record inequality. -/
theorem Number.operator_ne_iff_ne (x y : Number) :
    x.operator_ne y = true ↔ x ≠ y := by
  rw [ne_eq, ← Number.operator_eq_iff_eq]
  unfold Number.operator_ne
  cases x.operator_eq y <;> simp

/-- `Number.zero` is normalized. -/
theorem Number.zero_isNormalized : Number.zero.isNormalized := Or.inl rfl

/-- On a normalized number, `operator_ne` against zero is false exactly at
rational zero. -/
theorem Number.operator_ne_zero_eq_false_iff (x : Number) (hx : x.isNormalized) :
    x.operator_ne Number.zero = false ↔ x.toRat = 0 := by
  rw [Bool.eq_false_iff, ne_eq, operator_ne_iff x Number.zero hx Number.zero_isNormalized,
      Number.toRat_zero, not_not]

end XRPL.Model.Protocol

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol

/-! ## `LawfulVault.canVaultSet` proof bodies -/

/-- **Proof body of `canVaultSet_below_total`.** -/
theorem LawfulVault.canVaultSet_below_total_proof (lv : LawfulVault) (assetsMaximum : Number)
    (hne : assetsMaximum.operator_ne Number.zero = true)
    (hlt : assetsMaximum.operator_lt lv.assetsTotal = true) :
    lv.canVaultSet assetsMaximum = .tecLIMIT_EXCEEDED := by
  unfold LawfulVault.canVaultSet
  exact if_pos (by rw [Bool.and_eq_true]; exact ⟨hne, hlt⟩)

/-- **Proof body of `canVaultSet_success`.** -/
theorem LawfulVault.canVaultSet_success_proof (lv : LawfulVault) (assetsMaximum : Number)
    (hok : (assetsMaximum.operator_ne Number.zero &&
        assetsMaximum.operator_lt lv.assetsTotal) = false) :
    lv.canVaultSet assetsMaximum = .tesSUCCESS := by
  unfold LawfulVault.canVaultSet
  exact if_neg (by rw [Bool.not_eq_true]; exact hok)

/-- **Proof body of `canVaultSet_error_codes`.** -/
theorem LawfulVault.canVaultSet_error_codes_proof (lv : LawfulVault) (assetsMaximum : Number) :
    lv.canVaultSet assetsMaximum = .tesSUCCESS ∨
    lv.canVaultSet assetsMaximum = .tecLIMIT_EXCEEDED := by
  unfold LawfulVault.canVaultSet
  split_ifs <;> first | exact Or.inl rfl | exact Or.inr rfl

/-- **Proof body of `lawful_canVaultSet_iff`.** -/
theorem LawfulVault.lawful_canVaultSet_iff_proof (lv : LawfulVault)
    (assetsMaximum : Number)
    (hnorm : assetsMaximum.isNormalized) :
    lv.canVaultSet assetsMaximum = .tesSUCCESS ↔
      assetsMaximum.toRat = 0 ∨ lv.toExact.assetsTotal ≤ assetsMaximum.toRat := by
  have htotal : lv.assetsTotal.isNormalized := lv.wf.assetsTotal_norm
  -- the nonzero guard vanishes exactly at rational zero
  have hb1 : assetsMaximum.operator_ne Number.zero = false ↔ assetsMaximum.toRat = 0 :=
    Number.operator_ne_zero_eq_false_iff assetsMaximum hnorm
  -- the below-total guard vanishes exactly when the maximum is at least the total
  have hb2 : assetsMaximum.operator_lt lv.assetsTotal = false ↔
      lv.assetsTotal.toRat ≤ assetsMaximum.toRat := by
    rw [Bool.eq_false_iff, ne_eq, operator_lt_iff assetsMaximum lv.assetsTotal hnorm htotal, not_lt]
  -- `lv.toExact.assetsTotal` is `lv.assetsTotal.toRat` by definition of `toExact`
  show lv.canVaultSet assetsMaximum = .tesSUCCESS ↔
      assetsMaximum.toRat = 0 ∨ lv.assetsTotal.toRat ≤ assetsMaximum.toRat
  unfold LawfulVault.canVaultSet
  by_cases hc : (assetsMaximum.operator_ne Number.zero &&
      assetsMaximum.operator_lt lv.assetsTotal) = true
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

/-! ## `LawfulVault.canVaultDelete` proof bodies -/

/-- **Proof body of `lawful_canVaultDelete_iff`.** On a lawful vault
`assetsAvailable ≤ assetsTotal` and `0 ≤ assetsAvailable`, so `assetsTotal = 0`
already forces `assetsAvailable = 0`. The redundant middle conjunct is dropped:
the success condition is `assetsTotal = 0 ∧ sharesTotal = 0`, and the
`assetsAvailable` guard (checked first) is discharged from `assetsTotal = 0`. -/
theorem LawfulVault.lawful_canVaultDelete_iff_proof (lv : LawfulVault) :
    lv.canVaultDelete = .tesSUCCESS ↔
      lv.toExact.assetsTotal = 0 ∧ lv.toExact.sharesTotal = 0 := by
  have hav := Number.operator_ne_zero_eq_false_iff lv.assetsAvailable lv.wf.assetsAvailable_norm
  have hat := Number.operator_ne_zero_eq_false_iff lv.assetsTotal lv.wf.assetsTotal_norm
  have hst := Number.operator_ne_zero_eq_false_iff lv.sharesTotal lv.wf.sharesTotal_norm
  have hshares : lv.toExact.sharesTotal = 0 ↔ lv.sharesTotal.toRat = 0 := by
    rw [← RawVault.WF.toExact_sharesTotal lv.toRawVault lv.wf, Nat.cast_eq_zero]
  -- on a lawful vault `assetsTotal = 0` forces `assetsAvailable = 0`
  have hAV0 : lv.assetsTotal.toRat = 0 → lv.assetsAvailable.toRat = 0 := fun h => by
    have hle : lv.assetsAvailable.toRat ≤ lv.assetsTotal.toRat := lv.exact.assetsAvailable_le
    have hnn : 0 ≤ lv.assetsAvailable.toRat := lv.exact.assetsAvailable_nonneg
    rw [h] at hle
    exact le_antisymm hle hnn
  show lv.canVaultDelete = .tesSUCCESS ↔
      lv.assetsTotal.toRat = 0 ∧ lv.toExact.sharesTotal = 0
  rw [← hat, hshares, ← hst]
  unfold LawfulVault.canVaultDelete
  split_ifs with h1 h2 h3
  · refine iff_of_false (by decide) ?_
    rintro ⟨hat', _⟩
    have hAvz : lv.assetsAvailable.operator_ne Number.zero = false := hav.mpr (hAV0 (hat.mp hat'))
    rw [hAvz] at h1; exact absurd h1 (by decide)
  · refine iff_of_false (by decide) ?_
    rintro ⟨hat', _⟩; rw [h2] at hat'; exact absurd hat' (by decide)
  · refine iff_of_false (by decide) ?_
    rintro ⟨_, hst'⟩; rw [h3] at hst'; exact absurd hst' (by decide)
  · exact iff_of_true rfl ⟨Bool.eq_false_iff.mpr h2, Bool.eq_false_iff.mpr h3⟩

/-- **Proof body of `canVaultDelete_error_codes`.** -/
theorem LawfulVault.canVaultDelete_error_codes_proof (lv : LawfulVault) :
    lv.canVaultDelete = .tesSUCCESS ∨
    lv.canVaultDelete = .tecHAS_OBLIGATIONS := by
  unfold LawfulVault.canVaultDelete
  split_ifs <;> first | exact Or.inl rfl | exact Or.inr rfl

/-- **Proof body of `canVaultDelete_has_obligations_iff`.** -/
theorem LawfulVault.canVaultDelete_has_obligations_iff_proof (lv : LawfulVault) :
    lv.canVaultDelete = .tecHAS_OBLIGATIONS ↔
      (lv.assetsAvailable ≠ Number.zero ∨ lv.assetsTotal ≠ Number.zero ∨
        lv.sharesTotal ≠ Number.zero) := by
  unfold LawfulVault.canVaultDelete
  rw [← Number.operator_ne_iff_ne lv.assetsAvailable, ← Number.operator_ne_iff_ne lv.assetsTotal,
      ← Number.operator_ne_iff_ne lv.sharesTotal]
  split_ifs with h1 h2 h3
  · exact iff_of_true rfl (Or.inl h1)
  · exact iff_of_true rfl (Or.inr (Or.inl h2))
  · exact iff_of_true rfl (Or.inr (Or.inr h3))
  · refine iff_of_false (by decide) ?_
    rintro (h | h | h)
    · exact h1 h
    · exact h2 h
    · exact h3 h

end XRPL.Model.SingleAssetVault
