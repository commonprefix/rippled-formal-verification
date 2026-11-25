import XRPL.Properties.Protocol.Number.Common.Notation
import XRPL.Properties.Approx
import XRPL.Properties.Protocol.Number.Normalize.Common.ResultFacts
import XRPL.Properties.Protocol.Number.Normalize.Common.Downward.BoundProof
import XRPL.Properties.Protocol.Number.Normalize.Common.Downward.WitnessTrace
import XRPL.Properties.Protocol.Number.Normalize.Common.Upward.BoundProof
import XRPL.Properties.Protocol.Number.Normalize.Common.Upward.WitnessTrace
import XRPL.Properties.Protocol.Number.Normalize.Common.TowardsZero.BoundProof
import XRPL.Properties.Protocol.Number.Normalize.Common.TowardsZero.WitnessTrace
import XRPL.Properties.Protocol.Number.Normalize.Common.ToNearest.BoundProof
import XRPL.Properties.Protocol.Number.Normalize.Common.ToNearest.WitnessTrace
import XRPL.Properties.Protocol.Number.Normalize.Common.Underflow

/-! # Relative error of `normalize`

Each bound assumes a nonzero result, since a value too small for a `Number` becomes zero. The `_attained` theorems
reach the `to_nearest` bound exactly and pass a smaller bound in the other modes. -/

namespace XRPL.Model.Protocol

theorem Number.normalize_rounds_downward (n result : Number)
    (hok : n.normalize largeRange.min largeRange.max .downward = .ok result)
    (hresult : result.mantissa_ ≠ 0) :
    RoundsWithin result n.toRat .downward (10 / (2 ^ 63 + 2 : ℚ)) := by
  sorry

theorem Number.normalize_rounding_bound_downward_attained :
    ∃ (n result : Number),
      Number.normalize n largeRange.min largeRange.max .downward = .ok result ∧
      result.mantissa_ ≠ 0 ∧
      RoundsWithinWitness result n.toRat (8 / (2 ^ 63 + 2 : ℚ)) := by
  sorry

theorem Number.normalize_rounds_upward (n result : Number)
    (hok : n.normalize largeRange.min largeRange.max .upward = .ok result)
    (hresult : result.mantissa_ ≠ 0) :
    RoundsWithin result n.toRat .upward (10 / (2 ^ 63 + 2 : ℚ)) := by
  sorry

theorem Number.normalize_rounding_bound_upward_attained :
    ∃ (n result : Number),
      Number.normalize n largeRange.min largeRange.max .upward = .ok result ∧
      result.mantissa_ ≠ 0 ∧
      RoundsWithinWitness result n.toRat (8 / (2 ^ 63 + 2 : ℚ)) := by
  sorry

theorem Number.normalize_rounds_towards_zero (n result : Number)
    (hok : n.normalize largeRange.min largeRange.max .towards_zero = .ok result)
    (hresult : result.mantissa_ ≠ 0) :
    RoundsWithin result n.toRat .towards_zero (10 / (2 ^ 63 + 2 : ℚ)) := by
  sorry

theorem Number.normalize_rounding_bound_towards_zero_attained :
    ∃ (n result : Number),
      Number.normalize n largeRange.min largeRange.max .towards_zero = .ok result ∧
      result.mantissa_ ≠ 0 ∧
      RoundsWithinWitness result n.toRat (8 / (2 ^ 63 + 2 : ℚ)) := by
  sorry

theorem Number.normalize_rounds_to_nearest (n result : Number)
    (hok : n.normalize largeRange.min largeRange.max .to_nearest = .ok result)
    (hresult : result.mantissa_ ≠ 0) :
    RoundsWithin result n.toRat .to_nearest (5 / (2 ^ 63 + 7 : ℚ)) := by
  sorry

theorem Number.normalize_rounding_bound_to_nearest_attained :
    ∃ (n result : Number),
      Number.normalize n largeRange.min largeRange.max .to_nearest = .ok result ∧
      result.mantissa_ ≠ 0 ∧
      |result.toRat - n.toRat| = |n.toRat| * (5 / (2 ^ 63 + 7 : ℚ)) := by
  sorry

/-- A zero `normalize` result of a nonzero input means the value is below the smallest positive `Number`. -/
theorem Number.normalize_underflow_truth_small (n result : Number) (mode : rounding_mode)
    (hn_mant_ne : n.mantissa_ ≠ 0)
    (hok : n.normalize largeRange.min largeRange.max mode = .ok result)
    (hres0 : result.mantissa_ = 0) :
    |n.toRat| < (10 : ℚ) ^ (18 : ℕ) * (10 : ℚ) ^ (minExponent : ℤ) := by
  sorry

end XRPL.Model.Protocol
