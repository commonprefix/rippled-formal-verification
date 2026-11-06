import XRPL.Properties.Protocol.Number.Common.Notation
import Mathlib.Tactic

import XRPL.Properties.Approx
import XRPL.Properties.Protocol.Number.Common.Helpers
import XRPL.Properties.Protocol.Number.Div.Common.ToNearest.AlgorithmicFacts


namespace XRPL.Model.Protocol

/-! # Division rounding bound (`.to_nearest`)

`operator_div` ends in `doNormalize128` with an exact sticky flag, so the bound is the general `doNormalize128`
to-nearest bound `6/(2^63 − 3)`, applied to the quotient state from the division facts. -/

theorem operator_div_rounding_bound_to_nearest (x y result : Number)
    (hx : x.isNormalized) (hy : y.isNormalized)
    (hx_mant_ne : x.mantissa_ ≠ 0) (hy_mant_ne : y.mantissa_ ≠ 0)
    (hok : Number.operator_div x y .to_nearest = .ok result)
    (hresult : result.mantissa_ ≠ 0) :
    |result.toRat - x.toRat / y.toRat| ≤ |x.toRat / y.toRat| * (6 / (2 ^ 63 - 3 : ℚ)) := by
  obtain ⟨M, ze', δ, zn, sticky, hδ_low, hδ_le, hsticky_zero, hM_pos, hM_lt, hδM,
      htruth, hok128, hsign, _, _⟩ :=
    operator_div_algorithmic_facts_represents x y result .to_nearest hx hy
      hx_mant_ne hy_mant_ne hok
  obtain ⟨hbound, hneg⟩ :=
    doNormalize128_rounds_to_nearest zn M ze' δ sticky hδ_low hδ_le hsticky_zero
      hM_pos hM_lt hδM result hok128 hresult
  have h_abs_diff_eq : |result.toRat - x.toRat / y.toRat|
      = |(|result.toRat| - |x.toRat / y.toRat|)| :=
    abs_diff_eq_abs_sub_abs_of_sign_aligned result (x.toRat / y.toRat)
      (fun h_neg => hsign.1 (hneg ▸ h_neg))
      (fun h_pos => hsign.2 (hneg ▸ h_pos))
  rw [h_abs_diff_eq, htruth]
  exact hbound

end XRPL.Model.Protocol
