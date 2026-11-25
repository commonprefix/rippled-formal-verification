import XRPL.Properties.Approx
import XRPL.Properties.Protocol.Number.Div.Common.Downward.BoundProof
import XRPL.Properties.Protocol.Number.Div.Common.Downward.WitnessTrace
import XRPL.Properties.Protocol.Number.Div.Common.Upward.BoundProof
import XRPL.Properties.Protocol.Number.Div.Common.Upward.WitnessTrace
import XRPL.Properties.Protocol.Number.Div.Common.TowardsZero.BoundProof
import XRPL.Properties.Protocol.Number.Div.Common.TowardsZero.WitnessTrace
import XRPL.Properties.Protocol.Number.Div.Common.ToNearest.BoundProof
import XRPL.Properties.Protocol.Number.Div.Common.ToNearest.WitnessTrace
import XRPL.Properties.Protocol.Number.Div.Common.Decompose

/-! # Relative error of `operator_div`

Each bound assumes a nonzero result, since a quotient too small for a `Number` becomes zero. The `_attained`
theorems give operands whose error passes a smaller bound. -/

namespace XRPL.Model.Protocol

theorem Number.operator_div_rounds_downward (x y result : Number)
    (hx : x.isNormalized) (hy : y.isNormalized)
    (hok : Number.operator_div x y .downward = .ok result)
    (hresult : result.mantissa_ ≠ 0) :
    RoundsWithin result (x.toRat / y.toRat) .downward (11 / ((2 : ℚ) ^ 63 - 18)) := by
  sorry

theorem Number.operator_div_rounding_bound_downward_attained :
    ∃ (x y result : Number),
      x.isNormalized ∧
      y.isNormalized ∧
      Number.operator_div x y .downward = .ok result ∧
      result.mantissa_ ≠ 0 ∧
      RoundsWithinWitness result (x.toRat / y.toRat) (9 / (2 ^ 63 - 18 : ℚ)) := by
  sorry

theorem Number.operator_div_rounds_upward (x y result : Number)
    (hx : x.isNormalized) (hy : y.isNormalized)
    (hok : Number.operator_div x y .upward = .ok result)
    (hresult : result.mantissa_ ≠ 0) :
    RoundsWithin result (x.toRat / y.toRat) .upward (11 / ((2 : ℚ) ^ 63 - 18)) := by
  sorry

theorem Number.operator_div_rounding_bound_upward_attained :
    ∃ (x y result : Number),
      x.isNormalized ∧
      y.isNormalized ∧
      Number.operator_div x y .upward = .ok result ∧
      result.mantissa_ ≠ 0 ∧
      RoundsWithinWitness result (x.toRat / y.toRat) (9 / (2 ^ 63 - 18 : ℚ)) := by
  sorry

theorem Number.operator_div_rounds_towards_zero (x y result : Number)
    (hx : x.isNormalized) (hy : y.isNormalized)
    (hok : Number.operator_div x y .towards_zero = .ok result)
    (hresult : result.mantissa_ ≠ 0) :
    RoundsWithin result (x.toRat / y.toRat) .towards_zero (11 / ((2 : ℚ) ^ 63 - 18)) := by
  sorry

theorem Number.operator_div_rounding_bound_towards_zero_attained :
    ∃ (x y result : Number),
      x.isNormalized ∧
      y.isNormalized ∧
      Number.operator_div x y .towards_zero = .ok result ∧
      result.mantissa_ ≠ 0 ∧
      RoundsWithinWitness result (x.toRat / y.toRat) (9 / (2 ^ 63 - 18 : ℚ)) := by
  sorry

theorem Number.operator_div_rounds_to_nearest (x y result : Number)
    (hx : x.isNormalized) (hy : y.isNormalized)
    (hok : Number.operator_div x y .to_nearest = .ok result)
    (hresult : result.mantissa_ ≠ 0) :
    RoundsWithin result (x.toRat / y.toRat) .to_nearest (6 / ((2 : ℚ) ^ 63 - 3)) := by
  sorry

theorem Number.operator_div_rounding_bound_to_nearest_attained :
    ∃ (x y result : Number),
      x.isNormalized ∧
      y.isNormalized ∧
      Number.operator_div x y .to_nearest = .ok result ∧
      result.mantissa_ ≠ 0 ∧
      RoundsWithinWitness result (x.toRat / y.toRat) (4 / (2 ^ 63 - 3 : ℚ)) := by
  sorry

/-- A zero quotient of two nonzero Numbers means the exact quotient is below the smallest positive `Number`. -/
theorem Number.operator_div_underflow_truth_small (x y result : Number) (mode : rounding_mode)
    (hx : x.isNormalized) (hy : y.isNormalized)
    (hx_mant_ne : x.mantissa_ ≠ 0) (hy_mant_ne : y.mantissa_ ≠ 0)
    (hok : Number.operator_div x y mode = .ok result)
    (hres0 : result.mantissa_ = 0) :
    |x.toRat / y.toRat| < (10 : ℚ) ^ (18 : ℕ) * (10 : ℚ) ^ (minExponent : ℤ) := by
  sorry

end XRPL.Model.Protocol
