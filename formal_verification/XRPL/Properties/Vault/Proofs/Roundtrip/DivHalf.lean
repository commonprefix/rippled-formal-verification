import XRPL.Properties.Protocol.Number.Div.Common.ToNearest.CuspFacts
import XRPL.Properties.Protocol.Number.Common.Rounding.DoRoundUp.ValueChar

/-! # Half-unit division rounding

Below the cusp a `.to_nearest` quotient is within half a unit of its decade grid
`10 ^ k`, on which the true quotient `v` sits between `zm` and `zm + 1`. -/

namespace XRPL.Model.SingleAssetVault.RtT

open XRPL.Model.Protocol

lemma div_half (x y R : Number) (hx : x.isNormalized) (hy : y.isNormalized)
    (hok : Number.operator_div x y .to_nearest = .ok R) (hR : R.mantissa_ ≠ 0)
    (hv : 0 < x.toRat / y.toRat) :
    ∃ (zm : ℕ) (k : ℤ), 922337203685477580 ≤ zm ∧ zm ≤ 9223372036854775810 ∧
      (zm : ℚ) * 10 ^ k ≤ x.toRat / y.toRat ∧ x.toRat / y.toRat < ((zm : ℚ) + 1) * 10 ^ k ∧
      (zm = 922337203685477580 → ((zm : ℚ) + 4 / 5) * 10 ^ k ≤ x.toRat / y.toRat) ∧
      (zm < 9223372036854775807 →
        (R.toRat = (zm : ℚ) * 10 ^ k ∨ R.toRat = ((zm : ℚ) + 1) * 10 ^ k) ∧
        |R.toRat - x.toRat / y.toRat| ≤ 1 / 2 * 10 ^ k) := by
  obtain ⟨hxm, hym⟩ := operator_div_operands_ne_zero hx hy hok hR
  obtain ⟨zm, ze', f, g, res, hF⟩ :=
    operator_div_algorithmic_facts_to_nearest x y R hx hy hxm hym hok hR
  have hR0 : 0 ≤ R.toRat := hF.result_nonneg hv
  have hRv : R.toRat = (res.mantissa_.toNat : ℚ) * 10 ^ res.exponent_ := by
    rw [← abs_of_nonneg hR0]; exact hF.result_abs
  have hvv : x.toRat / y.toRat = ((zm.toNat : ℚ) + f) * 10 ^ ze' := by
    rw [← abs_of_pos hv]; exact hF.value_eq
  have hu : (0 : ℚ) < 10 ^ ze' := zpow_pos (by norm_num) _
  have hlo : 922337203685477580 ≤ zm.toNat := hF.zm_ge_floor
  have hhi : zm.toNat ≤ 9223372036854775810 := hF.zm_le_maxRepUp
  refine ⟨zm.toNat, ze', hlo, hhi, ?_, ?_, fun h => ?_, fun hlt => ?_⟩
  · rw [hvv]; nlinarith [hF.f_nonneg]
  · rw [hvv]; nlinarith [hF.f_lt_one]
  · rw [hvv]; have := hF.floor_cusp h; nlinarith
  have hmax : maxRep.toNat = 9223372036854775807 := by decide
  by_cases hs : g.shouldRoundUp_to_nearest zm
  · have hv' := doRoundUp_value_to_nearest_roundUp_noCusp g zm ze' hs (by rw [hmax]; omega)
      .normalize2 res hF.rounds hF.res_mant_ne
    have hf : 1 / 2 ≤ f := by
      rcases hs with h1 | ⟨h0, -⟩
      · exact le_of_lt (hF.round_eq_one h1)
      · exact le_of_eq (hF.round_eq_zero h0).symm
    refine ⟨Or.inr (by rw [hRv, hv']), ?_⟩
    rw [hRv, hv', hvv]
    rw [abs_le]; constructor <;> nlinarith [hF.f_lt_one]
  · have hv' := doRoundUp_value_no_roundUp g zm ze' hs (by rw [hmax]; omega)
      .normalize2 res hF.rounds hF.res_mant_ne
    have hf : f ≤ 1 / 2 := by
      by_contra h
      exact hs (Or.inl (hF.f_gt_half (lt_of_not_ge h)))
    refine ⟨Or.inl (by rw [hRv, hv']), ?_⟩
    rw [hRv, hv', hvv]
    rw [abs_le]; constructor <;> nlinarith [hF.f_nonneg]

end XRPL.Model.SingleAssetVault.RtT
