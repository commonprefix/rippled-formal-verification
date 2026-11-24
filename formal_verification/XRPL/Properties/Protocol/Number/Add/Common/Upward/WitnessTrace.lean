import XRPL.Properties.Protocol.Number.Common.ProofTactics
import XRPL.Properties.Protocol.Number.Common.Rounding.Normalize
import XRPL.Properties.Protocol.Number.Add.Common.NoWrap


namespace XRPL.Model.Protocol

/-- `operator_add` on the witness inputs, evaluated. -/
lemma Number.operator_add_upward_witness :
    Number.operator_add
        ⟨false, 1000000000000000000, 0⟩
        ⟨false, 1000000000000000000, 20⟩
        .upward =
      .ok ⟨false, 1000000000000000001, 20⟩ := by
  rw [Number.operator_add_eq_spec]
  case hx => decide
  case hy => decide
  decide +kernel

theorem Number.operator_add_upward_attained :
    ∃ (x y result : Number),
      x.isNormalized ∧ y.isNormalized ∧
      x.negative_ = y.negative_ ∧
      Number.operator_add x y .upward = .ok result ∧
      result.mantissa_ ≠ 0 ∧
      |result.toRat - (x.toRat + y.toRat)|
        > |x.toRat + y.toRat| * (9 / (2 ^ 63 + 2 : ℚ)) := by
  refine ⟨⟨false, 1000000000000000000, 0⟩,
          ⟨false, 1000000000000000000, 20⟩,
          ⟨false, 1000000000000000001, 20⟩,
          ?_, ?_, ?_, ?_, ?_, ?_⟩
  · norm_isNormalized
  · norm_isNormalized
  · rfl
  · exact Number.operator_add_upward_witness
  · decide
  · have hx_rat : (⟨false, 1000000000000000000, 0⟩ : Number).toRat = 1000000000000000000 := by
      unfold Number.toRat; rfl
    have hy_rat : (⟨false, 1000000000000000000, 20⟩ : Number).toRat
                = 1000000000000000000 * (10 : ℚ) ^ (20 : ℕ) := by
      unfold Number.toRat; simp; ring
    have hr_rat : (⟨false, 1000000000000000001, 20⟩ : Number).toRat
                = 1000000000000000001 * (10 : ℚ) ^ (20 : ℕ) := by
      unfold Number.toRat; simp; ring
    rw [hx_rat, hy_rat, hr_rat]
    rw [show ((2 : ℚ) ^ 63 + 2) = maxRepCuspTarget by norm_num]
    rw [show (1000000000000000000 : ℚ) + 1000000000000000000 * (10 : ℚ) ^ (20 : ℕ)
          = 100000000000000000001000000000000000000 by norm_num]
    rw [show (1000000000000000001 : ℚ) * (10 : ℚ) ^ (20 : ℕ)
            - 100000000000000000001000000000000000000
          = 99000000000000000000 by norm_num]
    rw [abs_of_pos (by norm_num : (0 : ℚ) < 99000000000000000000)]
    rw [abs_of_pos (by norm_num : (0 : ℚ) < 100000000000000000001000000000000000000)]
    rw [show (100000000000000000001000000000000000000 : ℚ) * (9 / (maxRepCuspTarget : ℚ))
          = 9 * 100000000000000000001000000000000000000 / maxRepCuspTarget by ring]
    rw [gt_iff_lt, div_lt_iff₀ (by norm_num : (0 : ℚ) < maxRepCuspTarget)]
    norm_num

end XRPL.Model.Protocol
