import XRPL.Properties.Protocol.Number.Common.Rounding.SuccessCondition
import XRPL.Properties.Protocol.Number.Div.Common.ToNearest.AlgorithmicFacts

/-! # Exact success condition for `operator_div`

`x / y` succeeds exactly when the exact quotient is below `(maxRepUp + 1) * 10^maxExponent` in size. The staged
quotient drops a residual too small to move the mantissa across that bound, and `doNormalize128` does the rest. -/

namespace XRPL.Model.Protocol

/-- `x / y` succeeds exactly when the exact quotient is below `(maxRepUp + 1) * 10^maxExponent` in size, in every
rounding mode. -/
lemma Number.operator_div_ok_iff_proof (x y : Number) (mode : rounding_mode)
    (hx : x.isNormalized) (hy : y.isNormalized)
    (hx0 : x.mantissa_ ≠ 0) (hy0 : y.mantissa_ ≠ 0) :
    (∃ result, x.operator_div y mode = .ok result) ↔
      |x.toRat / y.toRat| < 9223372036854775811 * (10 : ℚ) ^ (maxExponent : ℤ) := by
  obtain ⟨M, ze', δ, zn, sticky, hδ0, -, hzero, -, -, hδM, hval, heq, -, hδ1, -⟩ :=
    Number.operator_div_eq_normalize128 x y mode hx hy hx0 hy0
  have hsmall : δ * 10 ^ 20 ≤ (M.toNat : ℚ) := by
    cases hs : sticky
    · rw [hzero hs, zero_mul]; exact Nat.cast_nonneg _
    · exact hδM hs
  rw [heq, hval, scaled_lt_top_iff_of_small M.toNat δ ze' hδ0 hδ1 hsmall]
  exact doNormalize128_ok_iff_value zn M ze' mode sticky

/-- Every `operator_div` error on nonzero operands is an overflow error. -/
lemma Number.operator_div_error_isOverflow (x y : Number) (mode : rounding_mode)
    (hx : x.isNormalized) (hy : y.isNormalized)
    (hx0 : x.mantissa_ ≠ 0) (hy0 : y.mantissa_ ≠ 0) {err : Error}
    (h : x.operator_div y mode = .error err) : isOverflow err = true := by
  obtain ⟨M, ze', δ, zn, sticky, -, -, -, -, -, -, -, heq, -, -, -⟩ :=
    Number.operator_div_eq_normalize128 x y mode hx hy hx0 hy0
  rw [heq] at h
  exact doNormalize128_error_isOverflow largeRange_min_toNat_le h

/-- `x / y` fails with an overflow error when the exact quotient is at or above
`(maxRepUp + 1) * 10^maxExponent` in size. -/
lemma Number.operator_div_overflow_proof (x y : Number) (mode : rounding_mode)
    (hx : x.isNormalized) (hy : y.isNormalized)
    (hx0 : x.mantissa_ ≠ 0) (hy0 : y.mantissa_ ≠ 0)
    (h : 9223372036854775811 * (10 : ℚ) ^ (maxExponent : ℤ) ≤ |x.toRat / y.toRat|) :
    ∃ err, x.operator_div y mode = .error err ∧ isOverflow err = true :=
  overflow_of_not_ok
    (fun hok => absurd ((Number.operator_div_ok_iff_proof x y mode hx hy hx0 hy0).mp hok) (not_lt.mpr h))
    (fun _ herr => Number.operator_div_error_isOverflow x y mode hx hy hx0 hy0 herr)

end XRPL.Model.Protocol
