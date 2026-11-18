import XRPL.Properties.Protocol.Number.Common.Notation
import XRPL.Properties.Protocol.Number.Common.ProofTactics
import XRPL.Properties.Approx
import XRPL.Properties.Protocol.Number.Mul.Common.Downward.BoundProof
import XRPL.Properties.Protocol.Number.Mul.Common.Downward.WitnessTrace
import XRPL.Properties.Protocol.Number.Mul.Common.Upward.BoundProof
import XRPL.Properties.Protocol.Number.Mul.Common.Upward.WitnessTrace
import XRPL.Properties.Protocol.Number.Mul.Common.TowardsZero.BoundProof
import XRPL.Properties.Protocol.Number.Mul.Common.TowardsZero.WitnessTrace
import XRPL.Properties.Protocol.Number.Mul.Common.ToNearest.BoundProof
import XRPL.Properties.Protocol.Number.Mul.Common.ToNearest.WitnessTrace
import XRPL.Properties.Protocol.Number.Mul.Common.Underflow

/-! # Relative error of `operator_mul`

Each bound assumes a nonzero result, since a product too small for a `Number` becomes zero. The `_attained` theorems
reach the `to_nearest` bound exactly and pass a smaller bound in the other modes. -/

namespace XRPL.Model.Protocol

theorem Number.operator_mul_rounds_downward (x y result : Number)
    (hx : x.isNormalized) (hy : y.isNormalized)
    (hok : Number.operator_mul x y .downward = .ok result)
    (hresult : result.mantissa_ ≠ 0) :
    RoundsWithin result (x.toRat * y.toRat) .downward (10 / (2 ^ 63 + 2 : ℚ)) := by
  obtain ⟨hx_mant_ne, hy_mant_ne⟩ := Number.operator_mul_operands_ne_zero hx hy hok hresult
  obtain ⟨h_dir, h_mag⟩ :=
    Number.operator_mul_rounding_bound_downward x y result hx hy hx_mant_ne hy_mant_ne hok hresult
  exact ⟨h_dir, le_of_lt h_mag⟩

theorem Number.operator_mul_rounding_bound_downward_attained :
    ∃ (x y result : Number),
      x.isNormalized ∧
      y.isNormalized ∧
      Number.operator_mul x y .downward = .ok result ∧
      result.mantissa_ ≠ 0 ∧
      RoundsWithinWitness result (x.toRat * y.toRat) (9 / (2 ^ 63 + 2 : ℚ)) :=
  Number.operator_mul_downward_attained

theorem Number.operator_mul_rounds_upward (x y result : Number)
    (hx : x.isNormalized) (hy : y.isNormalized)
    (hok : Number.operator_mul x y .upward = .ok result)
    (hresult : result.mantissa_ ≠ 0) :
    RoundsWithin result (x.toRat * y.toRat) .upward (10 / (2 ^ 63 + 2 : ℚ)) := by
  obtain ⟨hx_mant_ne, hy_mant_ne⟩ := Number.operator_mul_operands_ne_zero hx hy hok hresult
  obtain ⟨h_dir, h_mag⟩ :=
    Number.operator_mul_rounding_bound_upward x y result hx hy hx_mant_ne hy_mant_ne hok hresult
  exact ⟨h_dir, le_of_lt h_mag⟩

theorem Number.operator_mul_rounding_bound_upward_attained :
    ∃ (x y result : Number),
      x.isNormalized ∧
      y.isNormalized ∧
      Number.operator_mul x y .upward = .ok result ∧
      result.mantissa_ ≠ 0 ∧
      RoundsWithinWitness result (x.toRat * y.toRat) (9 / (2 ^ 63 + 2 : ℚ)) :=
  Number.operator_mul_upward_attained

theorem Number.operator_mul_rounds_towards_zero (x y result : Number)
    (hx : x.isNormalized) (hy : y.isNormalized)
    (hok : Number.operator_mul x y .towards_zero = .ok result)
    (hresult : result.mantissa_ ≠ 0) :
    RoundsWithin result (x.toRat * y.toRat) .towards_zero (10 / (2 ^ 63 + 2 : ℚ)) := by
  obtain ⟨hx_mant_ne, hy_mant_ne⟩ := Number.operator_mul_operands_ne_zero hx hy hok hresult
  obtain ⟨h_dir, h_mag⟩ :=
    Number.operator_mul_rounding_bound_towards_zero x y result hx hy hx_mant_ne hy_mant_ne hok hresult
  exact ⟨h_dir, le_of_lt h_mag⟩

theorem Number.operator_mul_rounding_bound_towards_zero_attained :
    ∃ (x y result : Number),
      x.isNormalized ∧
      y.isNormalized ∧
      Number.operator_mul x y .towards_zero = .ok result ∧
      result.mantissa_ ≠ 0 ∧
      RoundsWithinWitness result (x.toRat * y.toRat) (9 / (2 ^ 63 + 2 : ℚ)) :=
  Number.operator_mul_towards_zero_attained

theorem Number.operator_mul_rounds_to_nearest (x y result : Number)
    (hx : x.isNormalized) (hy : y.isNormalized)
    (hok : Number.operator_mul x y .to_nearest = .ok result)
    (hresult : result.mantissa_ ≠ 0) :
    RoundsWithin result (x.toRat * y.toRat) .to_nearest (5 / (2 ^ 63 + 7 : ℚ)) := by
  obtain ⟨hx_mant_ne, hy_mant_ne⟩ := Number.operator_mul_operands_ne_zero hx hy hok hresult
  exact Number.operator_mul_rounding_bound_to_nearest x y result hx hy hx_mant_ne hy_mant_ne hok hresult

theorem Number.operator_mul_rounding_bound_to_nearest_attained :
    ∃ (x y result : Number),
      x.isNormalized ∧
      y.isNormalized ∧
      Number.operator_mul x y .to_nearest = .ok result ∧
      result.mantissa_ ≠ 0 ∧
      |result.toRat - x.toRat * y.toRat| = |x.toRat * y.toRat| * (5 / (2 ^ 63 + 7 : ℚ)) :=
  Number.operator_mul_to_nearest_attained

/-- A zero product of two nonzero Numbers means the exact product is below the smallest positive `Number`. -/
theorem Number.operator_mul_underflow_truth_small (x y result : Number) (mode : rounding_mode)
    (hx : x.isNormalized) (hy : y.isNormalized)
    (hx_mant_ne : x.mantissa_ ≠ 0) (hy_mant_ne : y.mantissa_ ≠ 0)
    (hok : Number.operator_mul x y mode = .ok result)
    (hres0 : result.mantissa_ = 0) :
    |x.toRat * y.toRat| < (10 : ℚ) ^ (18 : ℕ) * (10 : ℚ) ^ (minExponent : ℤ) :=
  Number.operator_mul_underflow_truth_small_proof x y result mode hx hy hx_mant_ne hy_mant_ne hok hres0

end XRPL.Model.Protocol
