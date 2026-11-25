import XRPL.Properties.Protocol.Number.Common.Notation
import XRPL.Properties.Protocol.Number.Common.ProofTactics
import XRPL.Model.Protocol.Number
import XRPL.Properties.Protocol.Number.Common.Rounding.Normalize
import XRPL.Properties.Protocol.Number.Add.Common.NoWrap


namespace XRPL.Model.Protocol

/-- `operator_add` on the witness inputs, evaluated. -/
lemma Number.operator_add_to_nearest_witness :
    Number.operator_add
        ⟨false, 5000000000000000000, 0⟩
        ⟨false, 4223372036854775815, 0⟩
        .to_nearest =
      .ok ⟨false, 9223372036854775820, 0⟩ := by
  rw [Number.operator_add_eq_spec]
  case hx => decide
  case hy => decide
  decide +kernel

/-- The bound `5/(2^63 + 7)` is attained exactly by `x = 5e18`, `y = 4223372036854775815`, whose sum `2^63 + 7`
ties at an odd mantissa and rounds up by 5. -/
theorem Number.operator_add_to_nearest_attained :
    ∃ (x y result : Number),
      x.isNormalized ∧ y.isNormalized ∧
      x.negative_ = y.negative_ ∧
      Number.operator_add x y .to_nearest = .ok result ∧
      result.mantissa_ ≠ 0 ∧
      |result.toRat - (x.toRat + y.toRat)|
        = |x.toRat + y.toRat| * (5 / (2 ^ 63 + 7 : ℚ)) := by
  refine ⟨⟨false, 5000000000000000000, 0⟩,
          ⟨false, 4223372036854775815, 0⟩,
          ⟨false, 9223372036854775820, 0⟩,
          ?_, ?_, ?_, ?_, ?_, ?_⟩
  · norm_isNormalized
  · norm_isNormalized
  · rfl
  · exact Number.operator_add_to_nearest_witness
  · decide
  · have hx_rat : (⟨false, 5000000000000000000, 0⟩ : Number).toRat = 5000000000000000000 := by
      unfold Number.toRat; rfl
    have hy_rat : (⟨false, 4223372036854775815, 0⟩ : Number).toRat = 4223372036854775815 := by
      unfold Number.toRat; rfl
    have hr_rat : (⟨false, 9223372036854775820, 0⟩ : Number).toRat = 9223372036854775820 := by
      unfold Number.toRat; rfl
    rw [hx_rat, hy_rat, hr_rat]
    change |(9223372036854775820 : ℚ) - (5000000000000000000 + 4223372036854775815)|
       = |(5000000000000000000 : ℚ) + 4223372036854775815| * (5 / (2 ^ 63 + 7 : ℚ))
    rw [show ((2 : ℚ) ^ 63 + 7) = 9223372036854775815 by norm_num]
    rw [show (5000000000000000000 : ℚ) + 4223372036854775815 = 9223372036854775815 by norm_num]
    rw [show (9223372036854775820 : ℚ) - 9223372036854775815 = 5 by norm_num]
    rw [abs_of_pos (by norm_num : (0 : ℚ) < 5)]
    rw [abs_of_pos (by norm_num : (0 : ℚ) < 9223372036854775815)]
    field_simp

end XRPL.Model.Protocol
