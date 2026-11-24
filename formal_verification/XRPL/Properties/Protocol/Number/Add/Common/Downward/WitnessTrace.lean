import XRPL.Properties.Protocol.Number.Common.Notation
import XRPL.Properties.Protocol.Number.Common.ProofTactics
import XRPL.Model.Protocol.Number
import XRPL.Properties.Protocol.Number.Common.Rounding.Normalize
import XRPL.Properties.Protocol.Number.Add.Common.NoWrap


namespace XRPL.Model.Protocol

/-- `operator_add` on the witness inputs, evaluated. -/
lemma Number.operator_add_downward_witness :
    Number.operator_add
        ⟨false, 5000000000000000004, 0⟩
        ⟨false, 5000000000000000005, 0⟩
        .downward =
      .ok ⟨false, 1000000000000000000, 1⟩ := by
  rw [Number.operator_add_eq_spec]
  case hx => decide
  case hy => decide
  decide +kernel

theorem Number.operator_add_downward_attained :
    ∃ (x y result : Number),
      x.isNormalized ∧ y.isNormalized ∧
      x.negative_ = y.negative_ ∧
      Number.operator_add x y .downward = .ok result ∧
      result.mantissa_ ≠ 0 ∧
      |result.toRat - (x.toRat + y.toRat)|
        > |x.toRat + y.toRat| * (8 / (2 ^ 63 + 2 : ℚ)) := by
  refine ⟨⟨false, 5000000000000000004, 0⟩,
          ⟨false, 5000000000000000005, 0⟩,
          ⟨false, 1000000000000000000, 1⟩,
          ?_, ?_, ?_, ?_, ?_, ?_⟩
  · norm_isNormalized
  · norm_isNormalized
  · rfl
  · exact Number.operator_add_downward_witness
  · decide
  · have hx_rat : (⟨false, 5000000000000000004, 0⟩ : Number).toRat = 5000000000000000004 := by
      unfold Number.toRat; rfl
    have hy_rat : (⟨false, 5000000000000000005, 0⟩ : Number).toRat = 5000000000000000005 := by
      unfold Number.toRat; rfl
    have hr_rat : (⟨false, 1000000000000000000, 1⟩ : Number).toRat
        = 1000000000000000000 * (10 : ℚ) ^ (1 : ℕ) := by
      unfold Number.toRat; simp; ring
    rw [hx_rat, hy_rat, hr_rat]
    rw [show ((2 : ℚ) ^ 63 + 2) = maxRepCuspTarget by norm_num]
    rw [show (5000000000000000004 : ℚ) + 5000000000000000005 = 10000000000000000009 by norm_num]
    rw [show (1000000000000000000 : ℚ) * (10 : ℚ) ^ (1 : ℕ) - 10000000000000000009
          = -9 by norm_num]
    rw [abs_neg]
    rw [abs_of_pos (by norm_num : (0 : ℚ) < 9)]
    rw [abs_of_pos (by norm_num : (0 : ℚ) < 10000000000000000009)]
    rw [gt_iff_lt, show (10000000000000000009 : ℚ) * (8 / maxRepCuspTarget)
                       = 8 * 10000000000000000009 / maxRepCuspTarget by ring]
    rw [div_lt_iff₀ (by norm_num : (0 : ℚ) < maxRepCuspTarget)]
    norm_num

end XRPL.Model.Protocol
