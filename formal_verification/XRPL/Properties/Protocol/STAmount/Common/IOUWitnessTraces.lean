import XRPL.Properties.Protocol.STAmount.Add.Common.IOU
import XRPL.Properties.Protocol.STAmount.Mul.Common.IOU
import XRPL.Properties.Protocol.Number.Add.Common.NoWrap

/-! # Step-by-step evaluations of the IOU witnesses

The witness results err by more than `|truth|·4/10¹⁶`, so the `to_nearest` IOU bounds of about `½·10⁻¹⁵` are close
to optimal. -/

namespace XRPL.Model.Protocol

/-- Inner `Number` addition of the 19-digit lifts of `5·10¹⁵+3` and `5·10¹⁵+2`: same-sign add, overflow, and a
one-digit scale-down that drops a `0` (no rounding). -/
lemma add_lift_trace :
    Number.operator_add ⟨false, 5000000000000003000, -3⟩ ⟨false, 5000000000000002000, -3⟩ .to_nearest
      = .ok ⟨false, 1000000000000000500, -2⟩ := by
  rw [Number.operator_add_eq_spec]
  case hx => decide
  case hy => decide
  unfold Number.operator_addSpec
  have hy_ne : (⟨false, 5000000000000002000, -3⟩ : Number).operator_eq Number.zero = false := by decide
  have hx_ne : (⟨false, 5000000000000003000, -3⟩ : Number).operator_eq Number.zero = false := by decide
  have hxy : (⟨false, 5000000000000003000, -3⟩ : Number).operator_eq
      (⟨false, 5000000000000002000, -3⟩ : Number).operator_neg = false := by decide
  simp only [hy_ne, hx_ne, hxy, Bool.false_eq_true, if_false]
  rw [if_neg (by decide : ¬ ((-3 : Int) < -3)), if_neg (by decide : ¬ ((-3 : Int) > -3))]
  rw [show ((false : Bool) == (false : Bool)) = true from rfl]
  simp only [if_true]
  have hsum : toUInt128 (5000000000000003000 : UInt64) + toUInt128 (5000000000000002000 : UInt64)
      = (10000000000000005000 : UInt128) := by decide
  rw [hsum]
  rw [show (decide ((10000000000000005000 : UInt128) > toUInt128 largeRange.max) ||
           decide ((10000000000000005000 : UInt128) > toUInt128 maxRepUp)) = true from by decide]
  simp only [if_true]
  have hdrop : Guard.new.doDropDigit128Spec (10000000000000005000 : UInt128) (-3)
      = ({ digits_ := 0, xbit_ := false, sbit_ := false }, (1000000000000000500 : UInt128), (-2 : Int)) := by
    unfold Guard.doDropDigit128Spec Guard.new Guard.push; rfl
  rw [hdrop]
  simp only
  have htoUInt64 : toUInt64 (1000000000000000500 : UInt128) = (1000000000000000500 : UInt64) := by decide
  rw [htoUInt64]
  have h_rup : ({ digits_ := 0, xbit_ := false, sbit_ := false } : Guard).doRoundUp
      false (1000000000000000500 : UInt64) (-2 : Int) largeRange.min largeRange.max .to_nearest
      .overflow =
      .ok { negative_ := false, mantissa_ := 1000000000000000500, exponent_ := -2 } := by
    rw_doRoundUp_spec
    unfold Guard.doRoundUpSpec Guard.bringIntoRangeSpec Guard.round Guard.doDropDigit; rfl
  rw [h_rup]
  simp only [RoundResult.toNumber]
  unfold Number.normalize
  rw [doNormalize_eq_spec]
  all_goals try min_fit
  unfold doNormalizeSpec
  rw [show (((1000000000000000500 : UInt64)) == 0) = false from rfl]
  simp only [Bool.false_eq_true, if_false]
  rw [show doNormalize_scaleUpSpec largeRange.min (1000000000000000500 : UInt64) (-2)
        = ((1000000000000000500 : UInt64), (-2 : Int)) by
        unfold doNormalize_scaleUpSpec; rw [if_neg (by decide)]]
  rw [show doNormalize_scaleDown largeRange.max (1000000000000000500 : UInt64) (-2 : Int) Guard.new
        = .ok ((1000000000000000500 : UInt64), (-2 : Int), Guard.new) by
        unfold doNormalize_scaleDown; rw [dif_neg (by decide)]]
  simp only []
  rw [show ((-2 : Int) < minExponent || (1000000000000000500 : UInt64) < largeRange.min) = false from by decide]
  simp only [Bool.false_eq_true, if_false]
  rw [show doNormalize_capAtMaxRep (1000000000000000500 : UInt64) (-2 : Int) Guard.new
        = .ok ((1000000000000000500 : UInt64), (-2 : Int), Guard.new) from by
      unfold doNormalize_capAtMaxRep; rw [if_neg (by decide)]]
  simp only []
  have h_rup2 : Guard.new.doRoundUp false (1000000000000000500 : UInt64) (-2 : Int)
      largeRange.min largeRange.max .to_nearest .normalize2 =
      .ok { negative_ := false, mantissa_ := 1000000000000000500, exponent_ := -2 } := by
    rw_doRoundUp_spec
    unfold Guard.doRoundUpSpec Guard.bringIntoRangeSpec Guard.round Guard.doDropDigit; rfl
  rw [h_rup2]
  simp only [RoundResult.toNumber]

/-- The 16-digit canonical re-round of `10¹⁶+5` (`= 1000000000000000500·10⁻²`):
scale down three digits (dropping `500`), `to_nearest` ties to even → `10¹⁶`. -/
lemma reround_trace :
    (⟨false, 1000000000000000500, -2⟩ : Number).normalizeToRange cMinValue cMaxValue .to_nearest
      = .ok (1000000000000000, 1) := by
  unfold Number.normalizeToRange
  rw [doNormalize_eq_spec]
  all_goals try min_fit
  unfold doNormalizeSpec
  rw [show (((1000000000000000500 : UInt64)) == 0) = false from rfl]
  simp only [Bool.false_eq_true, if_false]
  rw [show doNormalize_scaleUpSpec cMinValue (1000000000000000500 : UInt64) (-2)
        = ((1000000000000000500 : UInt64), (-2 : Int)) by
        unfold doNormalize_scaleUpSpec; rw [if_neg (by decide)]]
  rw [show doNormalize_scaleDown cMaxValue (1000000000000000500 : UInt64) (-2 : Int) Guard.new
        = .ok ((1000000000000000 : UInt64), (1 : Int), (Guard.new.push 0 |>.push 0 |>.push 5)) by
        unfold doNormalize_scaleDown
        rw [dif_pos (by decide), if_neg (by decide)]
        rw [show (1000000000000000500 : UInt64) / 10 = 100000000000000050 from by decide,
            show (1000000000000000500 : UInt64) % 10 = 0 from by decide, show (-2 : Int) + 1 = -1 from by decide]
        unfold doNormalize_scaleDown
        rw [dif_pos (by decide), if_neg (by decide)]
        rw [show (100000000000000050 : UInt64) / 10 = 10000000000000005 from by decide,
            show (100000000000000050 : UInt64) % 10 = 0 from by decide, show (-1 : Int) + 1 = 0 from by decide]
        unfold doNormalize_scaleDown
        rw [dif_pos (by decide), if_neg (by decide)]
        rw [show (10000000000000005 : UInt64) / 10 = 1000000000000000 from by decide,
            show (10000000000000005 : UInt64) % 10 = 5 from by decide, show (0 : Int) + 1 = 1 from by decide]
        unfold doNormalize_scaleDown
        rw [dif_neg (by decide)]]
  simp only []
  rw [show ((1 : Int) < minExponent || (1000000000000000 : UInt64) < cMinValue) = false from by decide]
  simp only [Bool.false_eq_true, if_false]
  rw [show doNormalize_capAtMaxRep (1000000000000000 : UInt64) (1 : Int) (Guard.new.push 0 |>.push 0 |>.push 5)
        = .ok ((1000000000000000 : UInt64), (1 : Int), (Guard.new.push 0 |>.push 0 |>.push 5)) from by
      unfold doNormalize_capAtMaxRep; rw [if_neg (by decide)]]
  simp only []
  rw [show (Guard.new.push 0 |>.push 0 |>.push 5 : Guard).doRoundUp false (1000000000000000 : UInt64) (1 : Int)
        cMinValue cMaxValue .to_nearest .normalize2
        = .ok { negative_ := false, mantissa_ := 1000000000000000, exponent_ := 1 } from by
      rw_doRoundUp_spec
      unfold Guard.doRoundUpSpec Guard.bringIntoRangeSpec Guard.round Guard.doDropDigit Guard.push Guard.new; rfl]
  simp only [RoundResult.toNumber]
  rfl

/-- `IOUAmount.ofNumber` re-round of the add result. -/
lemma ofnum_trace :
    IOUAmount.ofNumber ⟨false, 1000000000000000500, -2⟩ .to_nearest = .ok ⟨1000000000000000, 1⟩ := by
  unfold IOUAmount.ofNumber IOUAmount.fromNumber
  rw [reround_trace]
  simp only []
  rw [if_neg (by decide : ¬ ((1 : Int) > cMaxOffset)), if_neg (by decide : ¬ ((1 : Int) < cMinOffset))]

/-- Full `STAmount.operator_add` evaluation on the add/sub witness operands. -/
theorem STAmount.operator_add_iou_witness_eq :
    STAmount.operator_add ⟨.fractional, 5000000000000003, 0, false⟩
        ⟨.fractional, 5000000000000002, 0, false⟩ .to_nearest
      = .ok ⟨.fractional, 1000000000000000, 1, false⟩ := by
  have hc1 : (⟨.fractional, 5000000000000003, 0, false⟩ : STAmount).IOUCanonical :=
    ⟨by decide, by decide, by decide, by decide, by decide⟩
  have hc2 : (⟨.fractional, 5000000000000002, 0, false⟩ : STAmount).IOUCanonical :=
    ⟨by decide, by decide, by decide, by decide, by decide⟩
  have hiou1 := STAmount.iou_canonical_id ⟨.fractional, 5000000000000003, 0, false⟩ .to_nearest hc1
  have hiou2 := STAmount.iou_canonical_id ⟨.fractional, 5000000000000002, 0, false⟩ .to_nearest hc2
  have htn1 : (⟨(⟨.fractional, 5000000000000003, 0, false⟩ : STAmount).signedDrops.toInt64,
      (⟨.fractional, 5000000000000003, 0, false⟩ : STAmount).mOffset⟩ : IOUAmount).toNumber .to_nearest
      = .ok ⟨false, 5000000000000003000, -3⟩ :=
    STAmount.iou_toNumber_canonical ⟨.fractional, 5000000000000003, 0, false⟩ .to_nearest hc1
  have htn2 : (⟨(⟨.fractional, 5000000000000002, 0, false⟩ : STAmount).signedDrops.toInt64,
      (⟨.fractional, 5000000000000002, 0, false⟩ : STAmount).mOffset⟩ : IOUAmount).toNumber .to_nearest
      = .ok ⟨false, 5000000000000002000, -3⟩ :=
    STAmount.iou_toNumber_canonical ⟨.fractional, 5000000000000002, 0, false⟩ .to_nearest hc2
  have hsumI_range : (⟨1000000000000000, 1⟩ : IOUAmount).InRange16 :=
    ⟨by decide, by decide, by decide, by decide⟩
  have hofiou := STAmount.ofIOU_canonical ⟨1000000000000000, 1⟩ .to_nearest hsumI_range
  have hadd_inner : IOUAmount.operator_add
      ⟨(⟨.fractional, 5000000000000003, 0, false⟩ : STAmount).signedDrops.toInt64,
        (⟨.fractional, 5000000000000003, 0, false⟩ : STAmount).mOffset⟩
      ⟨(⟨.fractional, 5000000000000002, 0, false⟩ : STAmount).signedDrops.toInt64,
        (⟨.fractional, 5000000000000002, 0, false⟩ : STAmount).mOffset⟩ .to_nearest
      = .ok ⟨1000000000000000, 1⟩ := by
    unfold IOUAmount.operator_add
    rw [if_neg (by decide : ¬ (((⟨(⟨.fractional, 5000000000000002, 0, false⟩ : STAmount).signedDrops.toInt64,
          (⟨.fractional, 5000000000000002, 0, false⟩ : STAmount).mOffset⟩ : IOUAmount).mantissa_ == 0) = true)),
        if_neg (by decide : ¬ (((⟨(⟨.fractional, 5000000000000003, 0, false⟩ : STAmount).signedDrops.toInt64,
          (⟨.fractional, 5000000000000003, 0, false⟩ : STAmount).mOffset⟩ : IOUAmount).mantissa_ == 0) = true))]
    rw [htn1]; simp only []
    rw [htn2]; simp only []
    rw [add_lift_trace]; simp only []
    rw [ofnum_trace]
  unfold STAmount.operator_add
  rw [if_neg (by decide : ¬ ((!STAmount.areComparable ⟨.fractional, 5000000000000003, 0, false⟩
        ⟨.fractional, 5000000000000002, 0, false⟩) = true)),
      if_neg (by decide : ¬ (((⟨.fractional, 5000000000000002, 0, false⟩ : STAmount).mValue == 0) = true)),
      if_neg (by decide : ¬ (((⟨.fractional, 5000000000000003, 0, false⟩ : STAmount).mValue == 0) = true)),
      if_neg (by decide : ¬ (((⟨.fractional, 5000000000000003, 0, false⟩ : STAmount).integral) = true))]
  rw [hiou1]; simp only []
  rw [hiou2]; simp only []
  rw [hadd_inner]; simp only []
  rw [hofiou]; rfl

end XRPL.Model.Protocol
