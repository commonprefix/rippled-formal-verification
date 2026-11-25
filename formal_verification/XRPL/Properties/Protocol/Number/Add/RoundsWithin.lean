import XRPL.Properties.Protocol.Number.Add.Common.RoundsWithinProofs
import XRPL.Properties.Approx
import XRPL.Properties.Protocol.Number.Add.Common.Rounded

/-! # Relative error of `operator_add`

`operator_add_rounds_<mode>` holds for any signs and assumes a nonzero result, since a sum too small for a `Number`
becomes zero. `operator_add_rounds_same_sign_<mode>` gives the smaller bound when both operands have the same sign. -/

namespace XRPL.Model.Protocol

theorem Number.operator_add_rounds_same_sign_downward (x y result : Number)
    (hx : x.isNormalized) (hy : y.isNormalized)
    (hx_mant_ne : x.mantissa_ ≠ 0) (hy_mant_ne : y.mantissa_ ≠ 0)
    (h_same_sign : x.negative_ = y.negative_)
    (h_not_zero : ¬ x.operator_eq y.operator_neg)
    (hok : Number.operator_add x y .downward = .ok result) :
    RoundsWithin result (x.toRat + y.toRat) .downward (10 / (2 ^ 63 + 2 : ℚ)) := by
  sorry

theorem Number.operator_add_rounds_downward (x y result : Number)
    (hx : x.isNormalized) (hy : y.isNormalized)
    (hx_mant_ne : x.mantissa_ ≠ 0) (hy_mant_ne : y.mantissa_ ≠ 0)
    (h_not_zero : ¬ x.operator_eq y.operator_neg)
    (hok : Number.operator_add x y .downward = .ok result)
    (hresult : result.mantissa_ ≠ 0) :
    RoundsWithin result (x.toRat + y.toRat) .downward (11 / (2 ^ 63 - 18 : ℚ)) := by
  sorry

theorem Number.operator_add_rounding_bound_same_sign_downward_attained :
    ∃ (x y result : Number),
      x.isNormalized ∧
      y.isNormalized ∧
      x.negative_ = y.negative_ ∧
      Number.operator_add x y .downward = .ok result ∧
      result.mantissa_ ≠ 0 ∧
      RoundsWithinWitness result (x.toRat + y.toRat) (8 / (2 ^ 63 + 2 : ℚ)) := by
  sorry

theorem Number.operator_add_rounds_same_sign_upward (x y result : Number)
    (hx : x.isNormalized) (hy : y.isNormalized)
    (hx_mant_ne : x.mantissa_ ≠ 0) (hy_mant_ne : y.mantissa_ ≠ 0)
    (h_same_sign : x.negative_ = y.negative_)
    (h_not_zero : ¬ x.operator_eq y.operator_neg)
    (hok : Number.operator_add x y .upward = .ok result) :
    RoundsWithin result (x.toRat + y.toRat) .upward (10 / (2 ^ 63 + 2 : ℚ)) := by
  sorry

theorem Number.operator_add_rounds_upward (x y result : Number)
    (hx : x.isNormalized) (hy : y.isNormalized)
    (hx_mant_ne : x.mantissa_ ≠ 0) (hy_mant_ne : y.mantissa_ ≠ 0)
    (h_not_zero : ¬ x.operator_eq y.operator_neg)
    (hok : Number.operator_add x y .upward = .ok result)
    (hresult : result.mantissa_ ≠ 0) :
    RoundsWithin result (x.toRat + y.toRat) .upward (11 / (2 ^ 63 - 18 : ℚ)) := by
  sorry

theorem Number.operator_add_rounding_bound_same_sign_upward_attained :
    ∃ (x y result : Number),
      x.isNormalized ∧
      y.isNormalized ∧
      x.negative_ = y.negative_ ∧
      Number.operator_add x y .upward = .ok result ∧
      result.mantissa_ ≠ 0 ∧
      RoundsWithinWitness result (x.toRat + y.toRat) (9 / (2 ^ 63 + 2 : ℚ)) := by
  sorry

theorem Number.operator_add_rounds_same_sign_towards_zero (x y result : Number)
    (hx : x.isNormalized) (hy : y.isNormalized)
    (hx_mant_ne : x.mantissa_ ≠ 0) (hy_mant_ne : y.mantissa_ ≠ 0)
    (h_same_sign : x.negative_ = y.negative_)
    (h_not_zero : ¬ x.operator_eq y.operator_neg)
    (hok : Number.operator_add x y .towards_zero = .ok result) :
    RoundsWithin result (x.toRat + y.toRat) .towards_zero (10 / (2 ^ 63 + 2 : ℚ)) := by
  sorry

theorem Number.operator_add_rounds_towards_zero (x y result : Number)
    (hx : x.isNormalized) (hy : y.isNormalized)
    (hx_mant_ne : x.mantissa_ ≠ 0) (hy_mant_ne : y.mantissa_ ≠ 0)
    (h_not_zero : ¬ x.operator_eq y.operator_neg)
    (hok : Number.operator_add x y .towards_zero = .ok result)
    (hresult : result.mantissa_ ≠ 0) :
    RoundsWithin result (x.toRat + y.toRat) .towards_zero (11 / (2 ^ 63 - 18 : ℚ)) := by
  sorry

theorem Number.operator_add_rounding_bound_same_sign_towards_zero_attained :
    ∃ (x y result : Number),
      x.isNormalized ∧
      y.isNormalized ∧
      x.negative_ = y.negative_ ∧
      Number.operator_add x y .towards_zero = .ok result ∧
      result.mantissa_ ≠ 0 ∧
      RoundsWithinWitness result (x.toRat + y.toRat) (8 / (2 ^ 63 + 2 : ℚ)) := by
  sorry

theorem Number.operator_add_rounds_same_sign_to_nearest (x y result : Number)
    (hx : x.isNormalized) (hy : y.isNormalized)
    (hx_mant_ne : x.mantissa_ ≠ 0) (hy_mant_ne : y.mantissa_ ≠ 0)
    (h_same_sign : x.negative_ = y.negative_)
    (h_not_zero : ¬ x.operator_eq y.operator_neg)
    (hok : Number.operator_add x y .to_nearest = .ok result) :
    RoundsWithin result (x.toRat + y.toRat) .to_nearest (5 / (2 ^ 63 + 7 : ℚ)) := by
  sorry

theorem Number.operator_add_rounds_to_nearest (x y result : Number)
    (hx : x.isNormalized) (hy : y.isNormalized)
    (hx_mant_ne : x.mantissa_ ≠ 0) (hy_mant_ne : y.mantissa_ ≠ 0)
    (h_not_zero : ¬ x.operator_eq y.operator_neg)
    (hok : Number.operator_add x y .to_nearest = .ok result)
    (hresult : result.mantissa_ ≠ 0) :
    RoundsWithin result (x.toRat + y.toRat) .to_nearest (6 / (2 ^ 63 - 3 : ℚ)) := by
  sorry

theorem Number.operator_add_rounding_bound_same_sign_to_nearest_attained :
    ∃ (x y result : Number),
      x.isNormalized ∧
      y.isNormalized ∧
      x.negative_ = y.negative_ ∧
      Number.operator_add x y .to_nearest = .ok result ∧
      result.mantissa_ ≠ 0 ∧
      |result.toRat - (x.toRat + y.toRat)| = |x.toRat + y.toRat| * (5 / (2 ^ 63 + 7 : ℚ)) := by
  sorry

/-- A zero sum of two nonzero Numbers with different signs, other than `x + (-x)`, means the exact sum is below
the smallest positive `Number`. -/
theorem Number.operator_add_underflow_truth_small (x y result : Number) (mode : rounding_mode)
    (hx : x.isNormalized) (hy : y.isNormalized)
    (hx_mant_ne : x.mantissa_ ≠ 0) (hy_mant_ne : y.mantissa_ ≠ 0)
    (h_diff_sign : x.negative_ ≠ y.negative_)
    (h_not_zero : ¬ x.operator_eq y.operator_neg)
    (hok : Number.operator_add x y mode = .ok result)
    (hres0 : result.mantissa_ = 0) :
    |x.toRat + y.toRat| < (10 : ℚ) ^ (18 : ℕ) * (10 : ℚ) ^ (minExponent : ℤ) := by
  sorry

end XRPL.Model.Protocol
