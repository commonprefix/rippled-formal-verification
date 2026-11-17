import XRPL.Properties.Protocol.Number.Common.Notation
import XRPL.Properties.Protocol.Number.Common.ProofTactics
import XRPL.Model.Protocol.Number
import XRPL.Properties.Protocol.Number.Common.Rounding.Normalize
import XRPL.Properties.Protocol.Number.Add.Common.NoWrap


namespace XRPL.Model.Protocol

lemma Number.operator_add_to_nearest_witness :
    Number.operator_add
        ⟨false, 5000000000000000000, 0⟩
        ⟨false, 4223372036854775815, 0⟩
        .to_nearest =
      .ok ⟨false, 9223372036854775820, 0⟩ := by
  rw [Number.operator_add_eq_spec]
  case hx => decide
  case hy => decide
  unfold Number.operator_addSpec
  have hy_ne : (⟨false, 4223372036854775815, 0⟩ : Number).operator_eq Number.zero = false := by decide
  have hx_ne : (⟨false, 5000000000000000000, 0⟩ : Number).operator_eq Number.zero = false := by decide
  have hxy_neg_ne : (⟨false, 5000000000000000000, 0⟩ : Number).operator_eq
      (⟨false, 4223372036854775815, 0⟩ : Number).operator_neg = false := by decide
  simp only [hy_ne, hx_ne, hxy_neg_ne, Bool.false_eq_true, if_false]
  rw [if_neg (by decide : ¬ ((0 : Int) < 0))]
  rw [if_neg (by decide : ¬ ((0 : Int) > 0))]
  rw [show ((false : Bool) == (false : Bool)) = true from rfl]
  simp only [if_true]
  have hsum : toUInt128 (5000000000000000000 : UInt64) + toUInt128 (4223372036854775815 : UInt64)
      = (9223372036854775815 : UInt128) := by decide
  rw [hsum]
  rw [show checkSumAtTop (9223372036854775815 : UInt128) 0 = .ok () from by decide, ok_bind]
  rw [show (decide ((9223372036854775815 : UInt128) > toUInt128 largeRange.max) ||
           decide ((9223372036854775815 : UInt128) > toUInt128 maxRepUp)) = true from by decide]
  simp only [if_true]
  have hdrop : Guard.new.doDropDigit128Spec (9223372036854775815 : UInt128) 0
      = ({ digits_ := 5764607523034234880, xbit_ := false, sbit_ := false },
         (mantissaFloorSucc : UInt128), (1 : Int)) := by
    unfold Guard.doDropDigit128Spec Guard.new Guard.push; rfl
  rw [hdrop]
  simp only
  have htoUInt64 : toUInt64 (mantissaFloorSucc : UInt128) = (mantissaFloorSucc : UInt64) := by decide
  rw [htoUInt64]
  have h_rup : ({ digits_ := 5764607523034234880, xbit_ := false, sbit_ := false } : Guard).doRoundUp
      false (mantissaFloorSucc : UInt64) (1 : Int) largeRange.min largeRange.max .to_nearest
      .overflow =
      .ok { negative_ := false, mantissa_ := 9223372036854775820, exponent_ := 0 } := by
    rw [Guard.doRoundUp_eq_spec]
    all_goals try min_fit
    unfold Guard.doRoundUpSpec Guard.bringIntoRangeSpec Guard.round Guard.doDropDigit
    rfl
  rw [h_rup]
  simp only [RoundResult.toNumber]

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
