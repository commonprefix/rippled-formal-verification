import XRPL.Properties.Vault.Defs
import XRPL.Properties.Vault.Common.GuardProofs
import XRPL.Properties.Vault.Common.SubDownward
import XRPL.Properties.Vault.Common.WithdrawTotality
import XRPL.Properties.Protocol.Number.Sub.RoundsToRepresentable
import XRPL.Properties.Protocol.Number.Compare.Compare
import XRPL.Properties.Protocol.Number.Common.Closest.Tightness
import XRPL.Properties.Protocol.Number.Common.Defs

/-! # `Vault.Valid` ⟺ `Vault.Exact.Valid`. The Number-operator invariant `Vault.Valid`
is equivalent to the exact-ℚ invariant `Vault.Exact.Valid`.

Only the subtraction clause `lossUnrealized_le` depends on rounding. It uses
**downward** rounding, and that is exactly what makes it match the exact clause:
because `lossUnrealized` is itself a representable number,
`lossUnrealized ≤ round_down(assetsTotal − assetsAvailable)` holds in precisely
the cases where the exact `lossUnrealized ≤ assetsTotal − assetsAvailable` holds. -/

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol

variable {v : Vault}

/-- The downward difference `assetsTotal − assetsAvailable` of a well-formed vault
is normalized and is the correct downward rounding of the exact difference, given
only that `assetsAvailable` is nonnegative and bounded by `assetsTotal`. -/
lemma Vault.assetsSub_rounds (v : Vault) (hwf : v.WF)
    (h_aa_nn : 0 ≤ v.assetsAvailable.toRat)
    (h_le : v.assetsAvailable.toRat ≤ v.assetsTotal.toRat)
    {d : Number}
    (hok : v.assetsTotal.operator_sub v.assetsAvailable .downward = .ok d) :
    d.isNormalized ∧
      Number.RoundsToRepresentable d
        (v.assetsTotal.toRat - v.assetsAvailable.toRat) .downward := by
  have h_at_nn : 0 ≤ v.assetsTotal.toRat := le_trans h_aa_nn h_le
  have htruth_nn : 0 ≤ v.assetsTotal.toRat - v.assetsAvailable.toRat := by linarith
  have hdn : d.isNormalized := by
    by_cases haa0 : v.assetsAvailable.mantissa_ = 0
    · have hsub := Number.operator_sub_of_mantissa_zero v.assetsTotal v.assetsAvailable .downward haa0
      rw [hsub] at hok
      rw [(Except.ok.inj hok).symm]; exact hwf.assetsTotal_norm
    · have haa_neg : v.assetsAvailable.negative_ = false :=
        Number.negative_eq_false_of_nonneg v.assetsAvailable haa0 h_aa_nn
      have hnaa_neg : v.assetsAvailable.operator_neg.negative_ = true := by
        rw [Number.operator_neg_negative_of_ne v.assetsAvailable haa0, haa_neg]; rfl
      have hat_ne : v.assetsTotal.mantissa_ ≠ 0 := by
        intro hz
        have hz0 : v.assetsTotal.toRat = 0 := Number.toRat_eq_zero_iff.mpr hz
        have haaz : v.assetsAvailable.toRat = 0 := le_antisymm (by linarith) h_aa_nn
        exact haa0 (Number.toRat_eq_zero_iff.mp haaz)
      have hat_neg : v.assetsTotal.negative_ = false :=
        Number.negative_eq_false_of_nonneg v.assetsTotal hat_ne h_at_nn
      have h_diff : v.assetsTotal.negative_ ≠ v.assetsAvailable.operator_neg.negative_ := by
        rw [hat_neg, hnaa_neg]; decide
      exact operator_sub_isNormalized_downward v.assetsTotal v.assetsAvailable d
        hwf.assetsTotal_norm hwf.assetsAvailable_norm h_diff hok
  refine ⟨hdn, ?_⟩
  by_cases hd0 : d.mantissa_ = 0
  · refine ⟨Number.zero, ?_, by rw [Number.toRat_eq_zero_iff.mpr hd0, Number.toRat_zero]⟩
    rcases eq_or_lt_of_le htruth_nn with heq | hpos
    · rw [← heq]; simp [Number.lower]
    · have haa0 : v.assetsAvailable.mantissa_ ≠ 0 := by
        intro hz
        have hsub := Number.operator_sub_of_mantissa_zero v.assetsTotal v.assetsAvailable .downward hz
        rw [hsub] at hok
        have hda : d = v.assetsTotal := (Except.ok.inj hok).symm
        have haaz : v.assetsAvailable.toRat = 0 := Number.toRat_eq_zero_iff.mpr hz
        rw [hda] at hd0
        have hatz : v.assetsTotal.toRat = 0 := Number.toRat_eq_zero_iff.mpr hd0
        rw [hatz, haaz] at hpos; simp at hpos
      have hat_ne : v.assetsTotal.mantissa_ ≠ 0 := by
        intro hz
        have hz0 : v.assetsTotal.toRat = 0 := Number.toRat_eq_zero_iff.mpr hz
        rw [hz0] at hpos; linarith
      have haa_neg : v.assetsAvailable.negative_ = false :=
        Number.negative_eq_false_of_nonneg v.assetsAvailable haa0 h_aa_nn
      have hnaa_neg : v.assetsAvailable.operator_neg.negative_ = true := by
        rw [Number.operator_neg_negative_of_ne v.assetsAvailable haa0, haa_neg]; rfl
      have hat_neg : v.assetsTotal.negative_ = false :=
        Number.negative_eq_false_of_nonneg v.assetsTotal hat_ne h_at_nn
      have h_diff : v.assetsTotal.negative_ ≠ v.assetsAvailable.operator_neg.negative_ := by
        rw [hat_neg, hnaa_neg]; decide
      have h_not_cancel : ¬ v.assetsTotal.operator_eq v.assetsAvailable = true := by
        rw [operator_eq_iff v.assetsTotal v.assetsAvailable hwf.assetsTotal_norm
          hwf.assetsAvailable_norm]
        intro heq; rw [heq] at hpos; simp at hpos
      have hsmall := operator_sub_underflow_small_diff v.assetsTotal v.assetsAvailable d
        hwf.assetsTotal_norm hwf.assetsAvailable_norm hat_ne haa0 h_diff h_not_cancel hok hd0
      rw [abs_of_pos hpos] at hsmall
      exact Number.lower_eq_zero_of_pos_small _ hpos hsmall
  · exact operator_sub_rounded_downward v.assetsTotal v.assetsAvailable d
      hwf.assetsTotal_norm hwf.assetsAvailable_norm hok hd0

/-- `assetsTotal − assetsAvailable` can only fail by overflow: `doNormalize128`
errors once the result exponent passes `maxExponent`. It succeeds as soon as
`assetsTotal.exponent_ + 22 ≤ maxExponent`, which rules that out.

The `+ 22` is the renormalization headroom. The 128-bit intermediate is
`< 2^128 < 10^19 · 10^20`, so shrinking it into the 19-digit mantissa range raises
the exponent by ≤ 20 drops, and the cap and round tail add ≤ 2 more, ≤ 22 in all.
Real vaults clear it hugely (asset exponents are STAmount-scale). -/
lemma Vault.assetsSub_ok (v : Vault) (hwf : v.WF)
    (h_aa_nn : 0 ≤ v.assetsAvailable.toRat)
    (h_le : v.assetsAvailable.toRat ≤ v.assetsTotal.toRat)
    (hbound : v.assetsTotal.exponent_ + 22 ≤ maxExponent) :
    ∃ d, v.assetsTotal.operator_sub v.assetsAvailable .downward = .ok d := by
  have h_at_nn : 0 ≤ v.assetsTotal.toRat := le_trans h_aa_nn h_le
  by_cases haa0 : v.assetsAvailable.mantissa_ = 0
  · exact ⟨v.assetsTotal, Number.operator_sub_of_mantissa_zero _ _ _ haa0⟩
  · have hat_ne : v.assetsTotal.mantissa_ ≠ 0 := by
      intro hz
      have haaz : v.assetsAvailable.toRat = 0 :=
        le_antisymm (by rw [Number.toRat_eq_zero_iff.mpr hz] at h_le; linarith) h_aa_nn
      exact haa0 (Number.toRat_eq_zero_iff.mp haaz)
    have hat_neg : v.assetsTotal.negative_ = false :=
      Number.negative_eq_false_of_nonneg v.assetsTotal hat_ne h_at_nn
    have haa_neg : v.assetsAvailable.negative_ = false :=
      Number.negative_eq_false_of_nonneg v.assetsAvailable haa0 h_aa_nn
    have h_at_pos : 0 < v.assetsTotal.toRat :=
      lt_of_le_of_ne h_at_nn (Ne.symm (Number.mantissa_ne_zero_iff.mp hat_ne))
    have haa_ne_zero : v.assetsAvailable ≠ Number.zero := fun h => haa0 (by rw [h]; rfl)
    have haa_exp_le : v.assetsAvailable.exponent_ ≤ v.assetsTotal.exponent_ :=
      le_trans
        (exponent_le_of_toRat_le_pos v.assetsTotal.toRat h_at_pos v.assetsAvailable
          hwf.assetsAvailable_norm haa_neg haa_ne_zero h_le)
        (exponent_ge_of_toRat_ge v.assetsTotal.toRat h_at_pos v.assetsTotal
          hwf.assetsTotal_norm (le_refl _))
    exact Number.operator_sub_ok_of_exp v.assetsTotal v.assetsAvailable .downward
      hat_neg haa_neg hbound (by omega)

/-- The exact invariant implies the Number-operator check. -/
theorem Vault.Valid.of_exact (hwf : v.WF) (h : v.toExact.Valid) : v.Valid := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [operator_le_iff _ _ Number.zero_isNormalized hwf.assetsTotal_norm, Number.toRat_zero]
    exact h.assetsTotal_nonneg
  · rw [operator_le_iff _ _ Number.zero_isNormalized hwf.assetsAvailable_norm, Number.toRat_zero]
    exact h.assetsAvailable_nonneg
  · rw [operator_le_iff _ _ hwf.assetsAvailable_norm hwf.assetsTotal_norm]
    exact h.assetsAvailable_le
  · intro m hm
    rw [operator_lt_iff _ _ Number.zero_isNormalized (hwf.assetsMaximum_norm m hm), Number.toRat_zero]
    exact h.assetsMaximum_pos m.toRat (by simp only [Vault.toExact, Option.mem_map]; exact ⟨m, hm, rfl⟩)
  · intro h0
    have hs0 : v.toExact.sharesTotal = 0 := by
      show v.sharesTotal.toRat.num.toNat = 0
      rw [h0, Number.toRat_zero]; rfl
    obtain ⟨hat, haa⟩ := h.empty_shares hs0
    exact ⟨Number.eq_zero_of_mantissa_zero _ hwf.assetsTotal_norm (Number.toRat_eq_zero_iff.mp hat),
           Number.eq_zero_of_mantissa_zero _ hwf.assetsAvailable_norm (Number.toRat_eq_zero_iff.mp haa)⟩
  · intro m hm
    rw [operator_le_iff _ _ hwf.assetsTotal_norm (hwf.assetsMaximum_norm m hm)]
    exact h.cap m.toRat (by simp only [Vault.toExact, Option.mem_map]; exact ⟨m, hm, rfl⟩)
  · rw [operator_le_iff _ _ Number.zero_isNormalized hwf.lossUnrealized_norm, Number.toRat_zero]
    exact h.lossUnrealized_nonneg
  · intro d hok
    obtain ⟨hdn, n, hlo, hval⟩ :=
      Vault.assetsSub_rounds v hwf h.assetsAvailable_nonneg h.assetsAvailable_le hok
    rw [operator_le_iff _ _ hwf.lossUnrealized_norm hdn, hval]
    exact Number.lower_tight _ n hlo v.lossUnrealized hwf.lossUnrealized_norm h.lossUnrealized_le
  · rw [operator_le_iff _ _ hwf.lossUnrealized_norm hwf.assetsTotal_norm]
    have hw : (0 : ℚ) ≤ v.assetsTotal.toRat - v.lossUnrealized.toRat := h.withdraw_nav_nonneg
    linarith

/-- The Number-operator check implies the exact invariant. -/
theorem Vault.Valid.to_exact (hwf : v.WF)
    (hbound : v.assetsTotal.exponent_ + 22 ≤ maxExponent)
    (h : v.Valid) : v.toExact.Valid := by
  have h_aa_nn : 0 ≤ v.assetsAvailable.toRat := by
    have := (operator_le_iff _ _ Number.zero_isNormalized hwf.assetsAvailable_norm).mp
      h.assetsAvailable_nonneg
    rwa [Number.toRat_zero] at this
  have h_le : v.assetsAvailable.toRat ≤ v.assetsTotal.toRat :=
    (operator_le_iff _ _ hwf.assetsAvailable_norm hwf.assetsTotal_norm).mp h.assetsAvailable_le
  have htot := Vault.assetsSub_ok v hwf h_aa_nn h_le hbound
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have := (operator_le_iff _ _ Number.zero_isNormalized hwf.assetsTotal_norm).mp h.assetsTotal_nonneg
    rwa [Number.toRat_zero] at this
  · exact h_aa_nn
  · exact h_le
  · intro m hm
    obtain ⟨m', hm', rfl⟩ := by simpa only [Vault.toExact, Option.mem_map] using hm
    have := (operator_lt_iff _ _ Number.zero_isNormalized (hwf.assetsMaximum_norm m' hm')).mp
      (h.assetsMaximum_pos m' hm')
    rwa [Number.toRat_zero] at this
  · intro h0
    have hst0 : v.sharesTotal.toRat = 0 := by
      rw [← Vault.WF.toExact_sharesTotal v hwf, h0]; simp
    obtain ⟨hat, haa⟩ := h.empty_shares
      (Number.eq_zero_of_mantissa_zero _ hwf.sharesTotal_norm (Number.toRat_eq_zero_iff.mp hst0))
    exact ⟨by show v.assetsTotal.toRat = 0; rw [hat, Number.toRat_zero],
           by show v.assetsAvailable.toRat = 0; rw [haa, Number.toRat_zero]⟩
  · intro m hm
    obtain ⟨m', hm', rfl⟩ := by simpa only [Vault.toExact, Option.mem_map] using hm
    exact (operator_le_iff _ _ hwf.assetsTotal_norm (hwf.assetsMaximum_norm m' hm')).mp (h.cap m' hm')
  · have := (operator_le_iff _ _ Number.zero_isNormalized hwf.lossUnrealized_norm).mp
      h.lossUnrealized_nonneg
    rwa [Number.toRat_zero] at this
  · obtain ⟨d, hok⟩ := htot
    obtain ⟨hdn, n, hlo, hval⟩ := Vault.assetsSub_rounds v hwf h_aa_nn h_le hok
    have hle : v.lossUnrealized.toRat ≤ d.toRat :=
      (operator_le_iff _ _ hwf.lossUnrealized_norm hdn).mp (h.lossUnrealized_le d hok)
    have hd_le : d.toRat ≤ v.assetsTotal.toRat - v.assetsAvailable.toRat := by
      rw [hval]; exact Number.lower_le _ n hlo
    show v.lossUnrealized.toRat ≤ v.assetsTotal.toRat - v.assetsAvailable.toRat
    linarith
  · have := (operator_le_iff _ _ hwf.lossUnrealized_norm hwf.assetsTotal_norm).mp h.withdraw_nav_nonneg
    show 0 ≤ v.assetsTotal.toRat - v.lossUnrealized.toRat
    linarith

/-- **`Vault.Valid` ⟺ `Vault.Exact.Valid`** under `WF`, with `lossUnrealized_le`
clause in downward rounding. The only side condition is `hbound`
(`assetsTotal.exponent_ + 22 ≤ maxExponent`), which every STAmount-scale vault
satisfies with vast margin (STAmount exponents are ≤ 80, `maxExponent` is 32768). -/
theorem Vault.valid_iff_exact (hwf : v.WF)
    (hbound : v.assetsTotal.exponent_ + 22 ≤ maxExponent) :
    v.Valid ↔ v.toExact.Valid :=
  ⟨fun h => Vault.Valid.to_exact hwf hbound h, fun h => Vault.Valid.of_exact hwf h⟩

end XRPL.Model.SingleAssetVault
