import XRPL.Properties.Vault.Common.RoundMonotoneSat
import XRPL.Properties.Protocol.Number.Div.Common.ToNearest.CuspFacts

/-! # Cusp-aware rounding for `operator_div`

The quotient guard keeps only the top dropped digits, so the division facts carry the round decision directly instead
of `represents`. -/

namespace XRPL.Model.Protocol

/-- A positive `to_nearest` quotient of nonzero normalized operands is a cusp-aware grid image of the exact quotient. -/
lemma operator_div_roundsCuspAware (x y r : Number)
    (hx : x.isNormalized) (hy : y.isNormalized)
    (hxm : x.mantissa_ ≠ 0) (hym : y.mantissa_ ≠ 0)
    (hok : Number.operator_div x y .to_nearest = .ok r) (hrm : r.mantissa_ ≠ 0)
    (hpos : 0 < x.toRat / y.toRat) :
    r.RoundsCuspAware (x.toRat / y.toRat) := by
  obtain ⟨zm, ze', f, g, res_pos, hF⟩ :=
    operator_div_algorithmic_facts_to_nearest x y r hx hy hxm hym hok hrm
  exact roundsCuspAware_of_doRoundUp _ r zm ze' f g res_pos .normalize2 hpos
    (by rw [← abs_of_pos hpos]; exact hF.value_eq)
    (hF.result_nonneg hpos) hF.result_abs hF.rounds hF.res_mant_ne
    hF.f_nonneg hF.f_lt_one hF.zm_ge_floor hF.zm_le_maxRepUp hF.floor_cusp
    hF.round_eq_one hF.round_eq_zero hF.f_gt_half hF.f_eq_half
    (fun hdir => operator_div_rounded_branchA x y r hx hy hxm hym hok hrm hdir
      (operator_div_no_inbetween_below_to_nearest x y r hx hy hxm hym hok hrm hdir))
    (fun hdir => operator_div_rounded_branchB x y r hx hy hxm hym hok hrm hdir
      (operator_div_no_inbetween_above x y r hx hy hxm hym hok hrm hdir))

end XRPL.Model.Protocol
