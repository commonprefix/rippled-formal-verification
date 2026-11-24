import XRPL.Properties.Protocol.Number.Common.Notation
import XRPL.Properties.Protocol.Number.Mul.Common.TowardsZero.BoundProof
import XRPL.Properties.Protocol.Number.Common.ProofTactics


namespace XRPL.Model.Protocol

/-! # Witness for `Number.operator_mul_rounding_bound_towards_zero`

One product has a relative error above `9/(2^63+2)`, so the bound `10/(2^63+2)` is tight. -/

local syntax "sd_step" : tactic
local macro_rules | `(tactic| sd_step) => `(tactic|
  (conv_lhs => rw [scaleDown128Spec]; rw [dite_eq_left (by decide)]; rfl))

lemma scaleDown128_towards_zero_witness :
    scaleDown128Spec (toUInt128 (9223372036854775810 : UInt64) * toUInt128 (1000000000000000001 : UInt64))
                 (0 : Int) Guard.new
        = (mantissaFloorSucc, 19,
           { digits_ := 10530320965215537013, xbit_ := true, sbit_ := false }) := by
  have hprod : toUInt128 (9223372036854775810 : UInt64) * toUInt128 (1000000000000000001 : UInt64)
        = (9223372036854775819223372036854775810 : UInt128) := by decide
  rw [hprod]
  sd_step; sd_step; sd_step; sd_step; sd_step
  sd_step; sd_step; sd_step; sd_step; sd_step
  sd_step; sd_step; sd_step; sd_step; sd_step
  sd_step; sd_step; sd_step; sd_step
  conv_lhs => rw [scaleDown128Spec]; rw [dite_eq_right (by decide)]
  rfl

lemma Number.operator_mul_towards_zero_witness :
    Number.operator_mul
        ⟨false, 9223372036854775810, 0⟩
        ⟨false, 1000000000000000001, 0⟩
        .towards_zero =
      .ok ⟨false, 9223372036854775810, 18⟩ := by
  rw [Number.operator_mul_eq_spec]
  unfold Number.operator_mulSpec
  have hx_ne : (⟨false, 9223372036854775810, 0⟩ : Number).operator_eq Number.zero = false := by decide
  have hy_ne : (⟨false, 1000000000000000001, 0⟩ : Number).operator_eq Number.zero = false := by decide
  simp only [hx_ne, hy_ne, Bool.false_eq_true, ite_false, bne_self_eq_false, add_zero]
  rw [scaleDown128_towards_zero_witness]
  have h_rup : ({ digits_ := 10530320965215537013, xbit_ := true, sbit_ := false } : Guard).doRoundUp
      false (mantissaFloorSucc : UInt64) (19 : Int) largeRange.min largeRange.max .towards_zero
      .overflow =
      .ok { negative_ := false, mantissa_ := 9223372036854775810, exponent_ := 18 } := by
    rw_doRoundUp_spec
    unfold Guard.doRoundUpSpec Guard.bringIntoRangeSpec Guard.round Guard.doDropDigit; rfl
  rw [h_rup]
  simp only [RoundResult.toNumber]
  unfold Number.normalize
  rw [show doNormalize false (9223372036854775810 : UInt64) (18 : Int)
        largeRange.min largeRange.max .towards_zero
        = .ok { negative_ := false, mantissa_ := 9223372036854775810, exponent_ := 18 } from by
    rw [doNormalize_eq_spec]
    all_goals try min_fit
    unfold doNormalizeSpec
    rw [show ((9223372036854775810 : UInt64) == 0) = false from rfl]
    simp only [Bool.false_eq_true, ite_false]
    rw [show doNormalize_scaleUpSpec largeRange.min (9223372036854775810 : UInt64) (18 : Int)
          = ((9223372036854775810 : UInt64), (18 : Int)) by
          unfold doNormalize_scaleUpSpec; rw [ite_eq_right (by decide)]]
    rw [show doNormalize_scaleDown largeRange.max (9223372036854775810 : UInt64) (18 : Int) Guard.new
          = .ok ((9223372036854775810 : UInt64), (18 : Int), Guard.new) by
          unfold doNormalize_scaleDown; rw [dite_eq_right (by decide)]]
    simp only []
    rw [show ((18 : Int) < minExponent || (9223372036854775810 : UInt64) < largeRange.min) = false from by decide]
    simp only [Bool.false_eq_true, ite_false]
    rw [show doNormalize_capAtMaxRep (9223372036854775810 : UInt64) (18 : Int) Guard.new
          = .ok ((9223372036854775810 : UInt64), (18 : Int), Guard.new) by
        unfold doNormalize_capAtMaxRep; rw [ite_eq_right (by decide)]]
    simp only []
    have h_rup2 : Guard.new.doRoundUp false (9223372036854775810 : UInt64) (18 : Int)
        largeRange.min largeRange.max .towards_zero .normalize2 =
        .ok { negative_ := false, mantissa_ := 9223372036854775810, exponent_ := 18 } := by
      rw_doRoundUp_spec
      unfold Guard.doRoundUpSpec Guard.bringIntoRangeSpec Guard.round Guard.doDropDigit; rfl
    rw [h_rup2]
    simp only [RoundResult.toNumber]]


theorem Number.operator_mul_towards_zero_attained :
    ∃ (x y result : Number),
      x.isNormalized ∧ y.isNormalized ∧
      Number.operator_mul x y .towards_zero = .ok result ∧
      result.mantissa_ ≠ 0 ∧
      |result.toRat - x.toRat * y.toRat| > |x.toRat * y.toRat| * (9 / (2 ^ 63 + 2 : ℚ)) := by
  refine ⟨⟨false, 9223372036854775810, 0⟩,
          ⟨false, 1000000000000000001, 0⟩,
          ⟨false, 9223372036854775810, 18⟩,
          ?_, ?_, ?_, ?_, ?_⟩
  · norm_isNormalized
  · norm_isNormalized
  · exact Number.operator_mul_towards_zero_witness
  · decide
  · have hx_rat : (⟨false, 9223372036854775810, 0⟩ : Number).toRat = 9223372036854775810 := by
      unfold Number.toRat; rfl
    have hy_rat : (⟨false, 1000000000000000001, 0⟩ : Number).toRat = 1000000000000000001 := by
      unfold Number.toRat; rfl
    have hr_rat : (⟨false, 9223372036854775810, 18⟩ : Number).toRat
                = 9223372036854775810 * (10 : ℚ) ^ (18 : ℕ) := by
      unfold Number.toRat; simp; ring
    rw [hx_rat, hy_rat, hr_rat]
    rw [show (9223372036854775810 : ℚ) * 1000000000000000001
          = 9223372036854775810 * 10 ^ (18 : ℕ) + 9223372036854775810 by norm_num]
    rw [show 9223372036854775810 * (10 : ℚ) ^ (18 : ℕ) -
          (9223372036854775810 * 10 ^ (18 : ℕ) + 9223372036854775810)
          = -(9223372036854775810 : ℚ) by ring]
    rw [show ((2 : ℚ) ^ 63 + 2) = maxRepCuspTarget by norm_num]
    rw [abs_neg]
    rw [abs_of_pos (by positivity : (0 : ℚ) < (9223372036854775810 : ℚ))]
    rw [abs_of_pos (by positivity : (0 : ℚ) < 9223372036854775810 * 10 ^ (18 : ℕ) + 9223372036854775810)]
    rw [show (9223372036854775810 * 10 ^ (18 : ℕ) + 9223372036854775810) *
          (9 / (maxRepCuspTarget : ℚ))
          = 9 * (9223372036854775810 * 10 ^ (18 : ℕ) + 9223372036854775810) / maxRepCuspTarget by ring]
    rw [gt_iff_lt, div_lt_iff₀ (by norm_num : (0 : ℚ) < maxRepCuspTarget)]
    norm_num

end XRPL.Model.Protocol
