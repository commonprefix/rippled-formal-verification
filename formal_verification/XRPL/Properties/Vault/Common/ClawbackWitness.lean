import XRPL.Properties.Vault.Common.WitnessSupport
import XRPL.Properties.Vault.Common.DepositReduction
import XRPL.Properties.Vault.Common.ClawbackDefs
import XRPL.Properties.Vault.Common.WithdrawDefs
import XRPL.Model.Vault.VaultClawback

/-! # Witness data for the `Vault.clawback` sharpness theorems

Two lawful IOU vaults back the four clawback `*_attained` witnesses.

* `cwv` (3 assets, 3 available, 7·10¹⁵ shares): clawing `1` prices
  `7000000000000000 / 3 = 2333333333333333.33…` shares, rounded to
  `2333333333333333`; the half-share rounding error `1/3` exceeds the relative
  budget. The recovery prices those shares at
  `3 · 2333333333333333 / 7000000000000000 = 0.99999999999999985714…`,
  rounded downward at 16 digits to `0.9999999999999998`, short of the exact
  worth by `4/(7·10¹⁶)`, beyond the relative budget.
* `cwvB` (same vault with only `0.0001` available): clawing `1` first computes
  the same `0.9999999999999998` recovery, which exceeds `assetsAvailable`, so
  the run reprices from `0.0001`: `700000000000/3 = 233333333333.33…` shares
  truncate to `233333333333` (error `1/3`, beyond the relative budget), worth
  `0.000099999999999857142857…`, stored as `0.000099999999999857140`. The
  final total `3 - 0.00009999999999985714` needs 21 significant digits, so the
  19-digit stored total `2.999900000000000143` is not the exact difference.

Every pipeline stage is stepped by hand through the well-founded decimal
recursion, in the style of the deposit witness traces in `VaultDeposit.lean`. -/

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol

/-- The shared witness vault: 3 assets, 3 available, 7·10¹⁵ shares. -/
def cwv : Vault :=
  { assetsTotal := ⟨false, 3000000000000000000, -18⟩
  , assetsAvailable := ⟨false, 3000000000000000000, -18⟩
  , assetsMaximum := none, numericType := .fractional, scale := 0
  , sharesTotal := ⟨false, 7000000000000000000, -3⟩
  , interestUnrealized := Number.zero, lossUnrealized := Number.zero }

/-- The clamped-run vault: the same vault with only `0.0001` available. -/
def cwvB : Vault :=
  { cwv with assetsAvailable := ⟨false, 1000000000000000000, -22⟩ }

/-- The clawed amount, `1` of the IOU. -/
def cwa1 : STAmount := STAmount.unchecked .fractional 1000000000000000 (-15) false

/-- The destroyed shares of the `cwv` run, `2333333333333333`. -/
def cwsh1 : STAmount := STAmount.unchecked .int64 2333333333333333 0 false

/-- The recovered assets of the `cwv` run, `0.9999999999999998`. -/
def cwar1 : STAmount := STAmount.unchecked .fractional 9999999999999998 (-16) false

/-- The clamped recovery amount of the `cwvB` run, `0.0001`. -/
def cwclamp : STAmount := STAmount.unchecked .fractional 1000000000000000 (-19) false

/-- The destroyed shares of the `cwvB` run, `233333333333`. -/
def cwsh2 : STAmount := STAmount.unchecked .int64 233333333333 0 false

/-- The recovered assets of the `cwvB` run, `0.000099999999999857140`. -/
def cwar2 : STAmount := STAmount.unchecked .fractional 9999999999985714 (-20) false

section
set_option maxRecDepth 10000

local syntax "csd128_step" : tactic
local macro_rules | `(tactic| csd128_step) => `(tactic|
  (conv_lhs => rw [scaleDown128]; rw [dif_pos (by decide)]; rfl))

local syntax "cdsd128_step" : tactic
local macro_rules | `(tactic| cdsd128_step) => `(tactic|
  (conv_lhs => rw [doNormalize_scaleDown128]; rw [dif_pos (by decide), if_neg (by decide)]; rfl))

local syntax "csu_step" : tactic
local macro_rules | `(tactic| csu_step) => `(tactic|
  (conv_lhs => rw [doNormalize_scaleUp]; rw [if_pos (by decide)]))

local syntax "csu128_step" : tactic
local macro_rules | `(tactic| csu128_step) => `(tactic|
  (conv_lhs => rw [doNormalize128.scaleUp.eq_def]; rw [if_pos (by decide)]))

/-! ## The `cwv` run: claw `1`, shares `2333333333333333`, recovery
`0.9999999999999998` -/

private theorem cwa1_canonical : cwa1.IOUCanonical :=
  ⟨rfl, by decide, by decide, by decide, by decide⟩

private theorem cwa1_toNumber :
    cwa1.toNumber .to_nearest = .ok ⟨false, 1000000000000000000, -18⟩ := by
  rw [STAmount.toNumber_iou_canonical cwa1 .to_nearest cwa1_canonical]
  rfl

/-- `sharesTotal * amount = 7e15 * 1` at 19 digits, exact. -/
private theorem cw_shares1_mul :
    Number.operator_mul ⟨false, 7000000000000000000, -3⟩ ⟨false, 1000000000000000000, -18⟩
      .to_nearest = .ok ⟨false, 7000000000000000000, -3⟩ := by
  unfold Number.operator_mul
  simp only [show (⟨false, 7000000000000000000, -3⟩ : Number).operator_eq Number.zero = false from by decide,
    show (⟨false, 1000000000000000000, -18⟩ : Number).operator_eq Number.zero = false from by decide,
    Bool.false_eq_true, if_false, bne_self_eq_false]
  rw [show toUInt128 (7000000000000000000 : UInt64) * toUInt128 (1000000000000000000 : UInt64)
      = (7000000000000000000000000000000000000 : UInt128) from by decide,
    show (-3 : Int) + (-18) = -21 from by decide]
  rw [show scaleDown128 (7000000000000000000000000000000000000 : UInt128) (-21) Guard.new
      = ((7000000000000000000 : UInt64), (-3 : Int), Guard.new) from by
    csd128_step; csd128_step; csd128_step; csd128_step; csd128_step; csd128_step
    csd128_step; csd128_step; csd128_step; csd128_step; csd128_step; csd128_step
    csd128_step; csd128_step; csd128_step; csd128_step; csd128_step; csd128_step
    conv_lhs => rw [scaleDown128]; rw [dif_neg (by decide)]
    rfl]
  simp only []
  rw [show Guard.new.doRoundUp false (7000000000000000000 : UInt64) (-3)
      largeRange.min largeRange.max .to_nearest "Number::multiplication overflow"
      = .ok { negative_ := false, mantissa_ := 7000000000000000000, exponent_ := -3 } from by
    unfold Guard.doRoundUp Guard.bringIntoRange Guard.round Guard.doDropDigit; rfl]
  simp only [RoundResult.toNumber]
  unfold Number.normalize
  exact doNormalize_id .to_nearest false 7000000000000000000 (-3) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)

/-- `7e15 / 3` at 19 digits to nearest: `2333333333333333.333`. -/
private theorem cw_shares1_div :
    Number.operator_div ⟨false, 7000000000000000000, -3⟩ ⟨false, 3000000000000000000, -18⟩
      .to_nearest = .ok ⟨false, 2333333333333333333, -3⟩ := by
  unfold Number.operator_div
  rw [if_neg (by decide), if_neg (by decide)]
  change (match divQuotient128 (7000000000000000000 : UInt64) (3000000000000000000 : UInt64) (-3) (-18) with
      | (zm128, ze, dropped) => doNormalize128 false zm128 ze largeRange.min largeRange.max .to_nearest dropped)
    = Except.ok ⟨false, 2333333333333333333, -3⟩
  rw [show divQuotient128 (7000000000000000000 : UInt64) (3000000000000000000 : UInt64) (-3) (-18)
      = (23333333333333333333333, -7, true) from by decide]
  change doNormalize128 false (23333333333333333333333 : UInt128) (-7)
      largeRange.min largeRange.max .to_nearest true = Except.ok ⟨false, 2333333333333333333, -3⟩
  unfold doNormalize128
  rw [show ((23333333333333333333333 : UInt128) == 0) = false from by decide]
  simp only [Bool.false_eq_true, if_false]
  rw [show doNormalize128.scaleUp largeRange.min (23333333333333333333333 : UInt128) (-7)
        = ((23333333333333333333333 : UInt128), (-7 : Int)) from by
      rw [doNormalize128.scaleUp.eq_def]; rw [if_neg (by decide)]]
  simp only [if_true]
  rw [show (Guard.new.set_sticky : Guard)
        = { digits_ := 0, xbit_ := true, sbit_ := false } from rfl]
  rw [show doNormalize_scaleDown128 largeRange.max (23333333333333333333333 : UInt128) (-7)
        { digits_ := 0, xbit_ := true, sbit_ := false }
      = .ok (2333333333333333333, -3,
             { digits_ := 0x3333000000000000, xbit_ := true, sbit_ := false }) from by
    cdsd128_step; cdsd128_step; cdsd128_step; cdsd128_step
    conv_lhs => rw [doNormalize_scaleDown128]; rw [dif_neg (by decide)]
    rfl]
  simp only []
  rw [show (decide ((-3 : Int) < minExponent)
        || decide ((2333333333333333333 : UInt128) < toUInt128 largeRange.min)) = false from by decide]
  simp only [Bool.false_eq_true, if_false]
  rw [show doNormalize_capAtMaxRep (toUInt64 (2333333333333333333 : UInt128)) (-3)
        { digits_ := 0x3333000000000000, xbit_ := true, sbit_ := false }
      = .ok ((2333333333333333333 : UInt64), (-3 : Int),
             { digits_ := 0x3333000000000000, xbit_ := true, sbit_ := false }) from by
    unfold doNormalize_capAtMaxRep; rw [if_neg (by decide)]; rfl]
  simp only []
  rw [show ({ digits_ := 0x3333000000000000, xbit_ := true, sbit_ := false } : Guard).doRoundUp
      false (2333333333333333333 : UInt64) (-3) largeRange.min largeRange.max .to_nearest
      "Number::normalize 2"
      = .ok { negative_ := false, mantissa_ := 2333333333333333333, exponent_ := -3 } from by
    unfold Guard.doRoundUp Guard.bringIntoRange Guard.round Guard.doDropDigit; rfl]
  simp only [RoundResult.toNumber]

/-- `to_rep` of the untruncated shares `Number`: three digits `333` drop into
the guard, below the rounding midpoint. -/
private theorem cw_shares1_to_rep :
    (⟨false, 2333333333333333333, -3⟩ : Number).to_rep .to_nearest
      = .ok (2333333333333333 : Int64) := by
  unfold Number.to_rep
  rw [show (⟨false, 2333333333333333333, -3⟩ : Number).mantissa = (2333333333333333333 : Int64) from by decide,
      show (⟨false, 2333333333333333333, -3⟩ : Number).exponent = (-3 : Int) from by decide]
  simp only [show ((2333333333333333333 : Int64) == 0) = false from by decide,
    Bool.false_eq_true, if_false]
  rw [if_pos (show (-3 : Int) < 0 from by decide)]
  rw [show Number.to_rep.shift 2333333333333333333 (-3) Guard.new
      = ((2333333333333333 : Int64),
         ({ digits_ := 0x3330000000000000, xbit_ := false, sbit_ := false } : Guard)) from by
    rw [to_rep_shift_step _ _ _ (by decide)]
    show Number.to_rep.shift 233333333333333333 (-2)
        { digits_ := 0x3000000000000000, xbit_ := false, sbit_ := false } = _
    rw [to_rep_shift_step _ _ _ (by decide)]
    show Number.to_rep.shift 23333333333333333 (-1)
        { digits_ := 0x3300000000000000, xbit_ := false, sbit_ := false } = _
    rw [to_rep_shift_step _ _ _ (by decide)]
    show Number.to_rep.shift 2333333333333333 0
        { digits_ := 0x3330000000000000, xbit_ := false, sbit_ := false } = _
    exact to_rep_shift_stop _ _]
  simp only []
  rw [if_neg (show ¬ ((-3 : Int) ≥ 0) from by decide)]
  rfl

/-- `to_rep` at offset `0` is the identity on the mantissa. -/
private theorem cw_shares1_to_rep0 :
    (⟨false, 2333333333333333, 0⟩ : Number).to_rep .to_nearest
      = .ok (2333333333333333 : Int64) := by
  unfold Number.to_rep
  rw [show (⟨false, 2333333333333333, 0⟩ : Number).mantissa = (2333333333333333 : Int64) from by decide,
      show (⟨false, 2333333333333333, 0⟩ : Number).exponent = (0 : Int) from by decide]
  simp only [show ((2333333333333333 : Int64) == 0) = false from by decide,
    Bool.false_eq_true, if_false]
  rw [if_neg (show ¬ ((0 : Int) < 0) from by decide)]
  simp only []
  rw [if_pos (show (0 : Int) ≥ 0 from by decide), to_rep_grow_zero]
  rfl

/-- Packing the rounded shares `Number` into the int64 `STAmount`. -/
private theorem cw_shares1_ofNumber :
    STAmount.ofNumber .int64 ⟨false, 2333333333333333333, -3⟩ .to_nearest = .ok cwsh1 := by
  unfold STAmount.ofNumber
  simp only [show (decide ((⟨false, 2333333333333333333, -3⟩ : Number).signum < 0)) = false from by decide,
    Bool.false_eq_true, if_false,
    show NumericType.int64.isIntegral = true from rfl, if_true]
  rw [cw_shares1_to_rep]
  simp only []
  rw [show ((2333333333333333 : Int64)).toUInt64 = (2333333333333333 : UInt64) from by decide]
  unfold STAmount.checked STAmount.canonicalize
  simp only [STAmount.unchecked]
  rw [if_pos (by decide)]
  rw [if_neg (by decide)]
  rw [if_neg (by decide)]
  rw [show IntAmount.ofNumber (Number.unchecked false 2333333333333333 0) .to_nearest
      = .ok { value := 2333333333333333 } from by
    unfold IntAmount.ofNumber Number.unchecked
    rw [cw_shares1_to_rep0]]
  simp only []
  rw [if_neg (by decide)]
  rfl

/-- The `cwv` first-pass shares computation: `assetsToSharesWithdraw` on the
witness fields issues `2333333333333333` share drops (no truncation). -/
private theorem cw_assetsToShares1 (v : Vault)
    (hAT : v.assetsTotal = ⟨false, 3000000000000000000, -18⟩)
    (hIU : v.interestUnrealized = Number.zero)
    (hLU : v.lossUnrealized = Number.zero)
    (hST : v.sharesTotal = ⟨false, 7000000000000000000, -3⟩) :
    assetsToSharesWithdraw v cwa1 false false = .ok cwsh1 := by
  unfold assetsToSharesWithdraw
  rw [hAT, hIU, hLU, hST]
  simp only [operator_sub_zero_right, ok_bind]
  rw [if_neg (show ¬ (((⟨false, 3000000000000000000, -18⟩ : Number).mantissa_ == 0) = true) from by decide)]
  simp only [cwa1_toNumber, ok_bind, cw_shares1_mul, cw_shares1_div, pure_bind,
    cw_shares1_ofNumber]

/-- The issued shares convert back to the 19-digit `Number` lift. -/
private theorem cwsh1_toNumber :
    cwsh1.toNumber .to_nearest = .ok ⟨false, 2333333333333333000, -3⟩ := by
  unfold STAmount.toNumber
  rw [if_pos (show cwsh1.integral = true from rfl),
    show cwsh1.intAmount = .ok { value := 2333333333333333 } from by
      unfold STAmount.intAmount STAmount.signedDrops
      rw [if_pos (show cwsh1.integral = true from rfl)]
      rfl]
  show IntAmount.toNumber { value := 2333333333333333 } .to_nearest = _
  unfold IntAmount.toNumber Number.from_rep Number.normalized Number.normalize
  show doNormalize false 2333333333333333 0 largeRange.min largeRange.max .to_nearest = _
  rw [doNormalize_large_16digit false 2333333333333333 0 .to_nearest
    (by decide) (by decide) (by decide) (by decide)]
  rfl

/-- `nav * shares = 3 * 2333333333333333` at 19 digits, exact. -/
private theorem cw_recovered1_mul :
    Number.operator_mul ⟨false, 3000000000000000000, -18⟩ ⟨false, 2333333333333333000, -3⟩
      .to_nearest = .ok ⟨false, 6999999999999999000, -3⟩ := by
  unfold Number.operator_mul
  simp only [show (⟨false, 3000000000000000000, -18⟩ : Number).operator_eq Number.zero = false from by decide,
    show (⟨false, 2333333333333333000, -3⟩ : Number).operator_eq Number.zero = false from by decide,
    Bool.false_eq_true, if_false, bne_self_eq_false]
  rw [show toUInt128 (3000000000000000000 : UInt64) * toUInt128 (2333333333333333000 : UInt64)
      = (6999999999999999000000000000000000000 : UInt128) from by decide,
    show (-18 : Int) + (-3) = -21 from by decide]
  rw [show scaleDown128 (6999999999999999000000000000000000000 : UInt128) (-21) Guard.new
      = ((6999999999999999000 : UInt64), (-3 : Int), Guard.new) from by
    csd128_step; csd128_step; csd128_step; csd128_step; csd128_step; csd128_step
    csd128_step; csd128_step; csd128_step; csd128_step; csd128_step; csd128_step
    csd128_step; csd128_step; csd128_step; csd128_step; csd128_step; csd128_step
    conv_lhs => rw [scaleDown128]; rw [dif_neg (by decide)]
    rfl]
  simp only []
  rw [show Guard.new.doRoundUp false (6999999999999999000 : UInt64) (-3)
      largeRange.min largeRange.max .to_nearest "Number::multiplication overflow"
      = .ok { negative_ := false, mantissa_ := 6999999999999999000, exponent_ := -3 } from by
    unfold Guard.doRoundUp Guard.bringIntoRange Guard.round Guard.doDropDigit; rfl]
  simp only [RoundResult.toNumber]
  unfold Number.normalize
  exact doNormalize_id .to_nearest false 6999999999999999000 (-3) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)

/-- `6999999999999999 / 7e15` at 19 digits to nearest: `0.999999999999999857`. -/
private theorem cw_recovered1_div :
    Number.operator_div ⟨false, 6999999999999999000, -3⟩ ⟨false, 7000000000000000000, -3⟩
      .to_nearest = .ok ⟨false, 9999999999999998570, -19⟩ := by
  unfold Number.operator_div
  rw [if_neg (by decide), if_neg (by decide)]
  change (match divQuotient128 (6999999999999999000 : UInt64) (7000000000000000000 : UInt64) (-3) (-3) with
      | (zm128, ze, dropped) => doNormalize128 false zm128 ze largeRange.min largeRange.max .to_nearest dropped)
    = Except.ok ⟨false, 9999999999999998570, -19⟩
  rw [show divQuotient128 (6999999999999999000 : UInt64) (7000000000000000000 : UInt64) (-3) (-3)
      = (9999999999999998571428, -22, true) from by decide]
  change doNormalize128 false (9999999999999998571428 : UInt128) (-22)
      largeRange.min largeRange.max .to_nearest true = Except.ok ⟨false, 9999999999999998570, -19⟩
  unfold doNormalize128
  rw [show ((9999999999999998571428 : UInt128) == 0) = false from by decide]
  simp only [Bool.false_eq_true, if_false]
  rw [show doNormalize128.scaleUp largeRange.min (9999999999999998571428 : UInt128) (-22)
        = ((9999999999999998571428 : UInt128), (-22 : Int)) from by
      rw [doNormalize128.scaleUp.eq_def]; rw [if_neg (by decide)]]
  simp only [if_true]
  rw [show (Guard.new.set_sticky : Guard)
        = { digits_ := 0, xbit_ := true, sbit_ := false } from rfl]
  rw [show doNormalize_scaleDown128 largeRange.max (9999999999999998571428 : UInt128) (-22)
        { digits_ := 0, xbit_ := true, sbit_ := false }
      = .ok (9999999999999998571, -19,
             { digits_ := 0x4280000000000000, xbit_ := true, sbit_ := false }) from by
    cdsd128_step; cdsd128_step; cdsd128_step
    conv_lhs => rw [doNormalize_scaleDown128]; rw [dif_neg (by decide)]
    rfl]
  simp only []
  rw [show (decide ((-19 : Int) < minExponent)
        || decide ((9999999999999998571 : UInt128) < toUInt128 largeRange.min)) = false from by decide]
  simp only [Bool.false_eq_true, if_false]
  rw [show doNormalize_capAtMaxRep (toUInt64 (9999999999999998571 : UInt128)) (-19)
        { digits_ := 0x4280000000000000, xbit_ := true, sbit_ := false }
      = .ok ((999999999999999857 : UInt64), (-18 : Int),
             { digits_ := 0x1428000000000000, xbit_ := true, sbit_ := false }) from by
    unfold doNormalize_capAtMaxRep
    rw [if_pos (by decide), if_neg (by decide)]
    rfl]
  simp only []
  rw [show ({ digits_ := 0x1428000000000000, xbit_ := true, sbit_ := false } : Guard).doRoundUp
      false (999999999999999857 : UInt64) (-18) largeRange.min largeRange.max .to_nearest
      "Number::normalize 2"
      = .ok { negative_ := false, mantissa_ := 9999999999999998570, exponent_ := -19 } from by
    unfold Guard.doRoundUp Guard.bringIntoRange Guard.round Guard.doDropDigit; rfl]
  simp only [RoundResult.toNumber]

/-- The recovery `Number` truncates downward onto the 16-digit grid:
`0.9999999999999998`. -/
private theorem cw_recovered1_ofNumber :
    STAmount.ofNumber .fractional ⟨false, 9999999999999998570, -19⟩ .downward = .ok cwar1 := by
  unfold STAmount.ofNumber
  simp only [show (decide ((⟨false, 9999999999999998570, -19⟩ : Number).signum < 0)) = false from by decide,
    Bool.false_eq_true, if_false,
    show NumericType.fractional.isIntegral = false from rfl]
  rw [show kMinValue = cMinValue from rfl, show kMaxValue = cMaxValue from rfl]
  rw [show (⟨false, 9999999999999998570, -19⟩ : Number).normalizeToRange cMinValue cMaxValue .downward
      = .ok ((9999999999999998 : Int64), (-16 : Int)) from by
    unfold Number.normalizeToRange
    simp only []
    rw [show doNormalize false 9999999999999998570 (-19) cMinValue cMaxValue .downward
        = .ok { negative_ := false, mantissa_ := 9999999999999998, exponent_ := -16 } from by
      unfold doNormalize
      rw [show ((9999999999999998570 : UInt64) == 0) = false from rfl]
      simp only [Bool.false_eq_true, if_false]
      rw [doNormalize_scaleUp_id cMinValue 9999999999999998570 (-19) (by decide)]
      rw [show doNormalize_scaleDown cMaxValue (9999999999999998570 : UInt64) (-19) Guard.new
          = .ok ((9999999999999998 : UInt64), (-16 : Int),
                 { digits_ := 0x5700000000000000, xbit_ := false, sbit_ := false }) from by
        rw [doNormalize_scaleDown_step (by decide) (by decide)]
        show doNormalize_scaleDown cMaxValue 999999999999999857 (-18) (Guard.new.push 0) = _
        rw [doNormalize_scaleDown_step (by decide) (by decide)]
        show doNormalize_scaleDown cMaxValue 99999999999999985 (-17) ((Guard.new.push 0).push 7) = _
        rw [doNormalize_scaleDown_step (by decide) (by decide)]
        show doNormalize_scaleDown cMaxValue 9999999999999998 (-16)
            (((Guard.new.push 0).push 7).push 5) = _
        rw [doNormalize_scaleDown_id _ _ _ _ (by decide)]
        rfl]
      simp only []
      rw [show (decide ((-16 : Int) < minExponent)
            || decide ((9999999999999998 : UInt64) < cMinValue)) = false from by decide]
      simp only [Bool.false_eq_true, if_false]
      rw [show doNormalize_capAtMaxRep (9999999999999998 : UInt64) (-16)
            { digits_ := 0x5700000000000000, xbit_ := false, sbit_ := false }
          = .ok ((9999999999999998 : UInt64), (-16 : Int),
                 { digits_ := 0x5700000000000000, xbit_ := false, sbit_ := false }) from by
        unfold doNormalize_capAtMaxRep; rw [if_neg (by decide)]]
      simp only []
      rw [show ({ digits_ := 0x5700000000000000, xbit_ := false, sbit_ := false } : Guard).doRoundUp
          false (9999999999999998 : UInt64) (-16) cMinValue cMaxValue .downward
          "Number::normalize 2"
          = .ok { negative_ := false, mantissa_ := 9999999999999998, exponent_ := -16 } from by
        unfold Guard.doRoundUp Guard.bringIntoRange Guard.round Guard.doDropDigit; rfl]
      simp only [RoundResult.toNumber]]
    rfl]
  simp only []
  show STAmount.checked .fractional 9999999999999998 (-16) false .downward = _
  unfold STAmount.checked STAmount.unchecked
  exact STAmount.canonicalize_canonical_id _ .downward ⟨rfl, by decide, by decide, by decide, by decide⟩

/-- The `cwv` recovery computation: `sharesToAssetsWithdraw` on the witness
fields pays `0.9999999999999998`. -/
private theorem cw_sharesToAssets1 (v : Vault)
    (hAT : v.assetsTotal = ⟨false, 3000000000000000000, -18⟩)
    (hIU : v.interestUnrealized = Number.zero)
    (hLU : v.lossUnrealized = Number.zero)
    (hST : v.sharesTotal = ⟨false, 7000000000000000000, -3⟩)
    (hNT : v.numericType = NumericType.fractional) :
    Vault.sharesToAssetsWithdraw v cwsh1 false = .ok cwar1 := by
  unfold Vault.sharesToAssetsWithdraw
  rw [hAT, hIU, hLU, hST, hNT]
  simp only [operator_sub_zero_right, ok_bind]
  rw [if_neg (show ¬ (((⟨false, 3000000000000000000, -18⟩ : Number).mantissa_ == 0) = true) from by decide)]
  simp only [cwsh1_toNumber, ok_bind, cw_recovered1_mul, cw_recovered1_div,
    cw_recovered1_ofNumber, pure_bind]
  rfl

/-- The recovered amount as a `Number` (19-digit lift). -/
private theorem cwar1_toNumber :
    cwar1.toNumber .to_nearest = .ok ⟨false, 9999999999999998000, -19⟩ := by
  rw [STAmount.toNumber_iou_canonical cwar1 .to_nearest ⟨rfl, by decide, by decide, by decide, by decide⟩]
  rfl

/-! ## The `cwvB` clamped run: reprice from `0.0001`, shares `233333333333`,
recovery `0.000099999999999857140` -/

/-- `assetsAvailable = 0.0001` snaps onto the 16-digit grid exactly. -/
private theorem cw_clamp_ofNumber :
    STAmount.ofNumber .fractional ⟨false, 1000000000000000000, -22⟩ .to_nearest = .ok cwclamp := by
  unfold STAmount.ofNumber
  simp only [show (decide ((⟨false, 1000000000000000000, -22⟩ : Number).signum < 0)) = false from by decide,
    Bool.false_eq_true, if_false,
    show NumericType.fractional.isIntegral = false from rfl]
  rw [show kMinValue = cMinValue from rfl, show kMaxValue = cMaxValue from rfl]
  rw [normalizeToRange_16_exact _ .to_nearest (by decide) (by decide) (by decide) (by decide) (by decide)]
  simp only [Bool.false_eq_true, if_false]
  rw [show (((1000000000000000000 : UInt64) / 10 / 10 / 10).toInt64).toUInt64
      = (1000000000000000 : UInt64) from by decide,
    show (⟨false, 1000000000000000000, -22⟩ : Number).exponent_ + 3 = -19 from by decide]
  show STAmount.checked .fractional 1000000000000000 (-19) false .to_nearest = _
  unfold STAmount.checked STAmount.unchecked
  exact STAmount.canonicalize_canonical_id _ .to_nearest ⟨rfl, by decide, by decide, by decide, by decide⟩

private theorem cwclamp_toNumber :
    cwclamp.toNumber .to_nearest = .ok ⟨false, 1000000000000000000, -22⟩ := by
  rw [STAmount.toNumber_iou_canonical cwclamp .to_nearest ⟨rfl, by decide, by decide, by decide, by decide⟩]
  rfl

/-- `sharesTotal * clamped = 7e15 * 0.0001` at 19 digits, exact. -/
private theorem cw_shares2_mul :
    Number.operator_mul ⟨false, 7000000000000000000, -3⟩ ⟨false, 1000000000000000000, -22⟩
      .to_nearest = .ok ⟨false, 7000000000000000000, -7⟩ := by
  unfold Number.operator_mul
  simp only [show (⟨false, 7000000000000000000, -3⟩ : Number).operator_eq Number.zero = false from by decide,
    show (⟨false, 1000000000000000000, -22⟩ : Number).operator_eq Number.zero = false from by decide,
    Bool.false_eq_true, if_false, bne_self_eq_false]
  rw [show toUInt128 (7000000000000000000 : UInt64) * toUInt128 (1000000000000000000 : UInt64)
      = (7000000000000000000000000000000000000 : UInt128) from by decide,
    show (-3 : Int) + (-22) = -25 from by decide]
  rw [show scaleDown128 (7000000000000000000000000000000000000 : UInt128) (-25) Guard.new
      = ((7000000000000000000 : UInt64), (-7 : Int), Guard.new) from by
    csd128_step; csd128_step; csd128_step; csd128_step; csd128_step; csd128_step
    csd128_step; csd128_step; csd128_step; csd128_step; csd128_step; csd128_step
    csd128_step; csd128_step; csd128_step; csd128_step; csd128_step; csd128_step
    conv_lhs => rw [scaleDown128]; rw [dif_neg (by decide)]
    rfl]
  simp only []
  rw [show Guard.new.doRoundUp false (7000000000000000000 : UInt64) (-7)
      largeRange.min largeRange.max .to_nearest "Number::multiplication overflow"
      = .ok { negative_ := false, mantissa_ := 7000000000000000000, exponent_ := -7 } from by
    unfold Guard.doRoundUp Guard.bringIntoRange Guard.round Guard.doDropDigit; rfl]
  simp only [RoundResult.toNumber]
  unfold Number.normalize
  exact doNormalize_id .to_nearest false 7000000000000000000 (-7) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)

/-- `7e11 / 3` at 19 digits to nearest: `233333333333.3333`. -/
private theorem cw_shares2_div :
    Number.operator_div ⟨false, 7000000000000000000, -7⟩ ⟨false, 3000000000000000000, -18⟩
      .to_nearest = .ok ⟨false, 2333333333333333333, -7⟩ := by
  unfold Number.operator_div
  rw [if_neg (by decide), if_neg (by decide)]
  change (match divQuotient128 (7000000000000000000 : UInt64) (3000000000000000000 : UInt64) (-7) (-18) with
      | (zm128, ze, dropped) => doNormalize128 false zm128 ze largeRange.min largeRange.max .to_nearest dropped)
    = Except.ok ⟨false, 2333333333333333333, -7⟩
  rw [show divQuotient128 (7000000000000000000 : UInt64) (3000000000000000000 : UInt64) (-7) (-18)
      = (23333333333333333333333, -11, true) from by decide]
  change doNormalize128 false (23333333333333333333333 : UInt128) (-11)
      largeRange.min largeRange.max .to_nearest true = Except.ok ⟨false, 2333333333333333333, -7⟩
  unfold doNormalize128
  rw [show ((23333333333333333333333 : UInt128) == 0) = false from by decide]
  simp only [Bool.false_eq_true, if_false]
  rw [show doNormalize128.scaleUp largeRange.min (23333333333333333333333 : UInt128) (-11)
        = ((23333333333333333333333 : UInt128), (-11 : Int)) from by
      rw [doNormalize128.scaleUp.eq_def]; rw [if_neg (by decide)]]
  simp only [if_true]
  rw [show (Guard.new.set_sticky : Guard)
        = { digits_ := 0, xbit_ := true, sbit_ := false } from rfl]
  rw [show doNormalize_scaleDown128 largeRange.max (23333333333333333333333 : UInt128) (-11)
        { digits_ := 0, xbit_ := true, sbit_ := false }
      = .ok (2333333333333333333, -7,
             { digits_ := 0x3333000000000000, xbit_ := true, sbit_ := false }) from by
    cdsd128_step; cdsd128_step; cdsd128_step; cdsd128_step
    conv_lhs => rw [doNormalize_scaleDown128]; rw [dif_neg (by decide)]
    rfl]
  simp only []
  rw [show (decide ((-7 : Int) < minExponent)
        || decide ((2333333333333333333 : UInt128) < toUInt128 largeRange.min)) = false from by decide]
  simp only [Bool.false_eq_true, if_false]
  rw [show doNormalize_capAtMaxRep (toUInt64 (2333333333333333333 : UInt128)) (-7)
        { digits_ := 0x3333000000000000, xbit_ := true, sbit_ := false }
      = .ok ((2333333333333333333 : UInt64), (-7 : Int),
             { digits_ := 0x3333000000000000, xbit_ := true, sbit_ := false }) from by
    unfold doNormalize_capAtMaxRep; rw [if_neg (by decide)]; rfl]
  simp only []
  rw [show ({ digits_ := 0x3333000000000000, xbit_ := true, sbit_ := false } : Guard).doRoundUp
      false (2333333333333333333 : UInt64) (-7) largeRange.min largeRange.max .to_nearest
      "Number::normalize 2"
      = .ok { negative_ := false, mantissa_ := 2333333333333333333, exponent_ := -7 } from by
    unfold Guard.doRoundUp Guard.bringIntoRange Guard.round Guard.doDropDigit; rfl]
  simp only [RoundResult.toNumber]

/-- Normalizing the integer `233333333333`: seven scale-up shifts, exact. -/
private theorem cw_norm233 :
    doNormalize false 233333333333 0 largeRange.min largeRange.max .to_nearest
      = .ok ⟨false, 2333333333330000000, -7⟩ := by
  unfold doNormalize
  rw [show ((233333333333 : UInt64) == 0) = false from rfl]
  simp only [Bool.false_eq_true, if_false]
  rw [show doNormalize_scaleUp largeRange.min 233333333333 0
      = ((2333333333330000000 : UInt64), (-7 : Int)) from by
    csu_step; csu_step; csu_step; csu_step; csu_step; csu_step; csu_step
    rw [doNormalize_scaleUp]; rw [if_neg (by decide)]
    rfl]
  simp only []
  rw [doNormalize_scaleDown_id _ _ _ _ (by decide)]
  simp only []
  rw [show (decide ((-7 : Int) < minExponent)
        || decide ((2333333333330000000 : UInt64) < largeRange.min)) = false from by decide]
  simp only [Bool.false_eq_true, if_false]
  rw [show doNormalize_capAtMaxRep (2333333333330000000 : UInt64) (-7) Guard.new
      = .ok ((2333333333330000000 : UInt64), (-7 : Int), Guard.new) from by
    unfold doNormalize_capAtMaxRep; rw [if_neg (by decide)]]
  simp only []
  rw [show Guard.new.doRoundUp false (2333333333330000000 : UInt64) (-7)
      largeRange.min largeRange.max .to_nearest "Number::normalize 2"
      = .ok { negative_ := false, mantissa_ := 2333333333330000000, exponent_ := -7 } from by
    unfold Guard.doRoundUp Guard.bringIntoRange Guard.round Guard.doDropDigit; rfl]
  simp only [RoundResult.toNumber]

/-- Truncating `233333333333.3333` to the integer `233333333333`. -/
private theorem cw_shares2_truncate :
    Number.truncate ⟨false, 2333333333333333333, -7⟩ = .ok ⟨false, 2333333333330000000, -7⟩ := by
  unfold Number.truncate
  rw [if_neg (show ¬ ((⟨false, 2333333333333333333, -7⟩ : Number).exponent_ ≥ 0
      ∨ (⟨false, 2333333333333333333, -7⟩ : Number).mantissa_ = 0) from by decide)]
  rw [show Number.truncateAux (⟨false, 2333333333333333333, -7⟩ : Number).mantissa_
        (⟨false, 2333333333333333333, -7⟩ : Number).exponent_
      = ((233333333333 : UInt64), (0 : Int)) from by
    show Number.truncateAux 2333333333333333333 (-7) = _
    rw [truncateAux_step _ _ (by decide) (by decide)]
    show Number.truncateAux 233333333333333333 (-6) = _
    rw [truncateAux_step _ _ (by decide) (by decide)]
    show Number.truncateAux 23333333333333333 (-5) = _
    rw [truncateAux_step _ _ (by decide) (by decide)]
    show Number.truncateAux 2333333333333333 (-4) = _
    rw [truncateAux_step _ _ (by decide) (by decide)]
    show Number.truncateAux 233333333333333 (-3) = _
    rw [truncateAux_step _ _ (by decide) (by decide)]
    show Number.truncateAux 23333333333333 (-2) = _
    rw [truncateAux_step _ _ (by decide) (by decide)]
    show Number.truncateAux 2333333333333 (-1) = _
    rw [truncateAux_step _ _ (by decide) (by decide)]
    show Number.truncateAux 233333333333 0 = _
    exact truncateAux_stop _]
  simp only []
  show Number.normalized false 233333333333 0 largeRange.min largeRange.max .to_nearest = _
  unfold Number.normalized Number.normalize Number.unchecked
  show doNormalize false 233333333333 0 largeRange.min largeRange.max .to_nearest = _
  exact cw_norm233

/-- `to_rep` of the truncated shares `Number`: seven exact shifts. -/
private theorem cw_shares2_to_rep :
    (⟨false, 2333333333330000000, -7⟩ : Number).to_rep .to_nearest
      = .ok (233333333333 : Int64) := by
  unfold Number.to_rep
  rw [show (⟨false, 2333333333330000000, -7⟩ : Number).mantissa = (2333333333330000000 : Int64) from by decide,
      show (⟨false, 2333333333330000000, -7⟩ : Number).exponent = (-7 : Int) from by decide]
  simp only [show ((2333333333330000000 : Int64) == 0) = false from by decide,
    Bool.false_eq_true, if_false]
  rw [if_pos (show (-7 : Int) < 0 from by decide)]
  rw [show Number.to_rep.shift 2333333333330000000 (-7) Guard.new
      = ((233333333333 : Int64), Guard.new) from by
    rw [to_rep_shift_step _ _ _ (by decide)]
    show Number.to_rep.shift 233333333333000000 (-6) Guard.new = _
    rw [to_rep_shift_step _ _ _ (by decide)]
    show Number.to_rep.shift 23333333333300000 (-5) Guard.new = _
    rw [to_rep_shift_step _ _ _ (by decide)]
    show Number.to_rep.shift 2333333333330000 (-4) Guard.new = _
    rw [to_rep_shift_step _ _ _ (by decide)]
    show Number.to_rep.shift 233333333333000 (-3) Guard.new = _
    rw [to_rep_shift_step _ _ _ (by decide)]
    show Number.to_rep.shift 23333333333300 (-2) Guard.new = _
    rw [to_rep_shift_step _ _ _ (by decide)]
    show Number.to_rep.shift 2333333333330 (-1) Guard.new = _
    rw [to_rep_shift_step _ _ _ (by decide)]
    show Number.to_rep.shift 233333333333 0 Guard.new = _
    exact to_rep_shift_stop _ _]
  simp only []
  rw [if_neg (show ¬ ((-7 : Int) ≥ 0) from by decide)]
  rfl

/-- `to_rep` at offset `0` is the identity on the mantissa. -/
private theorem cw_shares2_to_rep0 :
    (⟨false, 233333333333, 0⟩ : Number).to_rep .to_nearest
      = .ok (233333333333 : Int64) := by
  unfold Number.to_rep
  rw [show (⟨false, 233333333333, 0⟩ : Number).mantissa = (233333333333 : Int64) from by decide,
      show (⟨false, 233333333333, 0⟩ : Number).exponent = (0 : Int) from by decide]
  simp only [show ((233333333333 : Int64) == 0) = false from by decide,
    Bool.false_eq_true, if_false]
  rw [if_neg (show ¬ ((0 : Int) < 0) from by decide)]
  simp only []
  rw [if_pos (show (0 : Int) ≥ 0 from by decide), to_rep_grow_zero]
  rfl

/-- Packing the truncated shares `Number` into the int64 `STAmount`. -/
private theorem cw_shares2_ofNumber :
    STAmount.ofNumber .int64 ⟨false, 2333333333330000000, -7⟩ .to_nearest = .ok cwsh2 := by
  unfold STAmount.ofNumber
  simp only [show (decide ((⟨false, 2333333333330000000, -7⟩ : Number).signum < 0)) = false from by decide,
    Bool.false_eq_true, if_false,
    show NumericType.int64.isIntegral = true from rfl, if_true]
  rw [cw_shares2_to_rep]
  simp only []
  rw [show ((233333333333 : Int64)).toUInt64 = (233333333333 : UInt64) from by decide]
  unfold STAmount.checked STAmount.canonicalize
  simp only [STAmount.unchecked]
  rw [if_pos (by decide)]
  rw [if_neg (by decide)]
  rw [if_neg (by decide)]
  rw [show IntAmount.ofNumber (Number.unchecked false 233333333333 0) .to_nearest
      = .ok { value := 233333333333 } from by
    unfold IntAmount.ofNumber Number.unchecked
    rw [cw_shares2_to_rep0]]
  simp only []
  rw [if_neg (by decide)]
  rfl

/-- The clamped shares computation: `assetsToSharesWithdraw` with truncation
destroys `233333333333` share drops. -/
private theorem cw_assetsToShares2 (v : Vault)
    (hAT : v.assetsTotal = ⟨false, 3000000000000000000, -18⟩)
    (hIU : v.interestUnrealized = Number.zero)
    (hLU : v.lossUnrealized = Number.zero)
    (hST : v.sharesTotal = ⟨false, 7000000000000000000, -3⟩) :
    assetsToSharesWithdraw v cwclamp true false = .ok cwsh2 := by
  unfold assetsToSharesWithdraw
  rw [hAT, hIU, hLU, hST]
  simp only [operator_sub_zero_right, ok_bind]
  rw [if_neg (show ¬ (((⟨false, 3000000000000000000, -18⟩ : Number).mantissa_ == 0) = true) from by decide)]
  simp only [cwclamp_toNumber, ok_bind, cw_shares2_mul, cw_shares2_div,
    cw_shares2_truncate, cw_shares2_ofNumber]
  rfl

/-- The clamped shares convert back to the 19-digit `Number` lift. -/
private theorem cwsh2_toNumber :
    cwsh2.toNumber .to_nearest = .ok ⟨false, 2333333333330000000, -7⟩ := by
  unfold STAmount.toNumber
  rw [if_pos (show cwsh2.integral = true from rfl),
    show cwsh2.intAmount = .ok { value := 233333333333 } from by
      unfold STAmount.intAmount STAmount.signedDrops
      rw [if_pos (show cwsh2.integral = true from rfl)]
      rfl]
  show IntAmount.toNumber { value := 233333333333 } .to_nearest = _
  unfold IntAmount.toNumber Number.from_rep Number.normalized Number.normalize
  show doNormalize false 233333333333 0 largeRange.min largeRange.max .to_nearest = _
  exact cw_norm233

/-- `nav * shares = 3 * 233333333333` at 19 digits, exact. -/
private theorem cw_recovered2_mul :
    Number.operator_mul ⟨false, 3000000000000000000, -18⟩ ⟨false, 2333333333330000000, -7⟩
      .to_nearest = .ok ⟨false, 6999999999990000000, -7⟩ := by
  unfold Number.operator_mul
  simp only [show (⟨false, 3000000000000000000, -18⟩ : Number).operator_eq Number.zero = false from by decide,
    show (⟨false, 2333333333330000000, -7⟩ : Number).operator_eq Number.zero = false from by decide,
    Bool.false_eq_true, if_false, bne_self_eq_false]
  rw [show toUInt128 (3000000000000000000 : UInt64) * toUInt128 (2333333333330000000 : UInt64)
      = (6999999999990000000000000000000000000 : UInt128) from by decide,
    show (-18 : Int) + (-7) = -25 from by decide]
  rw [show scaleDown128 (6999999999990000000000000000000000000 : UInt128) (-25) Guard.new
      = ((6999999999990000000 : UInt64), (-7 : Int), Guard.new) from by
    csd128_step; csd128_step; csd128_step; csd128_step; csd128_step; csd128_step
    csd128_step; csd128_step; csd128_step; csd128_step; csd128_step; csd128_step
    csd128_step; csd128_step; csd128_step; csd128_step; csd128_step; csd128_step
    conv_lhs => rw [scaleDown128]; rw [dif_neg (by decide)]
    rfl]
  simp only []
  rw [show Guard.new.doRoundUp false (6999999999990000000 : UInt64) (-7)
      largeRange.min largeRange.max .to_nearest "Number::multiplication overflow"
      = .ok { negative_ := false, mantissa_ := 6999999999990000000, exponent_ := -7 } from by
    unfold Guard.doRoundUp Guard.bringIntoRange Guard.round Guard.doDropDigit; rfl]
  simp only [RoundResult.toNumber]
  unfold Number.normalize
  exact doNormalize_id .to_nearest false 6999999999990000000 (-7) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)

/-- `699999999999 / 7e15` at 19 digits to nearest: the quotient crosses the
`maxRepUp` cusp, so the stored mantissa keeps a trailing zero:
`0.0000999999999998571429`. -/
private theorem cw_recovered2_div :
    Number.operator_div ⟨false, 6999999999990000000, -7⟩ ⟨false, 7000000000000000000, -3⟩
      .to_nearest = .ok ⟨false, 9999999999985714290, -23⟩ := by
  unfold Number.operator_div
  rw [if_neg (by decide), if_neg (by decide)]
  change (match divQuotient128 (6999999999990000000 : UInt64) (7000000000000000000 : UInt64) (-7) (-3) with
      | (zm128, ze, dropped) => doNormalize128 false zm128 ze largeRange.min largeRange.max .to_nearest dropped)
    = Except.ok ⟨false, 9999999999985714290, -23⟩
  rw [show divQuotient128 (6999999999990000000 : UInt64) (7000000000000000000 : UInt64) (-7) (-3)
      = (9999999999985714285714, -26, true) from by decide]
  change doNormalize128 false (9999999999985714285714 : UInt128) (-26)
      largeRange.min largeRange.max .to_nearest true = Except.ok ⟨false, 9999999999985714290, -23⟩
  unfold doNormalize128
  rw [show ((9999999999985714285714 : UInt128) == 0) = false from by decide]
  simp only [Bool.false_eq_true, if_false]
  rw [show doNormalize128.scaleUp largeRange.min (9999999999985714285714 : UInt128) (-26)
        = ((9999999999985714285714 : UInt128), (-26 : Int)) from by
      rw [doNormalize128.scaleUp.eq_def]; rw [if_neg (by decide)]]
  simp only [if_true]
  rw [show (Guard.new.set_sticky : Guard)
        = { digits_ := 0, xbit_ := true, sbit_ := false } from rfl]
  rw [show doNormalize_scaleDown128 largeRange.max (9999999999985714285714 : UInt128) (-26)
        { digits_ := 0, xbit_ := true, sbit_ := false }
      = .ok (9999999999985714285, -23,
             { digits_ := 0x7140000000000000, xbit_ := true, sbit_ := false }) from by
    cdsd128_step; cdsd128_step; cdsd128_step
    conv_lhs => rw [doNormalize_scaleDown128]; rw [dif_neg (by decide)]
    rfl]
  simp only []
  rw [show (decide ((-23 : Int) < minExponent)
        || decide ((9999999999985714285 : UInt128) < toUInt128 largeRange.min)) = false from by decide]
  simp only [Bool.false_eq_true, if_false]
  rw [show doNormalize_capAtMaxRep (toUInt64 (9999999999985714285 : UInt128)) (-23)
        { digits_ := 0x7140000000000000, xbit_ := true, sbit_ := false }
      = .ok ((999999999998571428 : UInt64), (-22 : Int),
             { digits_ := 0x5714000000000000, xbit_ := true, sbit_ := false }) from by
    unfold doNormalize_capAtMaxRep
    rw [if_pos (by decide), if_neg (by decide)]
    rfl]
  simp only []
  rw [show ({ digits_ := 0x5714000000000000, xbit_ := true, sbit_ := false } : Guard).doRoundUp
      false (999999999998571428 : UInt64) (-22) largeRange.min largeRange.max .to_nearest
      "Number::normalize 2"
      = .ok { negative_ := false, mantissa_ := 9999999999985714290, exponent_ := -23 } from by
    unfold Guard.doRoundUp Guard.bringIntoRange Guard.round Guard.doDropDigit; rfl]
  simp only [RoundResult.toNumber]

/-- The clamped recovery `Number` truncates downward onto the 16-digit grid:
`0.000099999999999857140`. -/
private theorem cw_recovered2_ofNumber :
    STAmount.ofNumber .fractional ⟨false, 9999999999985714290, -23⟩ .downward = .ok cwar2 := by
  unfold STAmount.ofNumber
  simp only [show (decide ((⟨false, 9999999999985714290, -23⟩ : Number).signum < 0)) = false from by decide,
    Bool.false_eq_true, if_false,
    show NumericType.fractional.isIntegral = false from rfl]
  rw [show kMinValue = cMinValue from rfl, show kMaxValue = cMaxValue from rfl]
  rw [show (⟨false, 9999999999985714290, -23⟩ : Number).normalizeToRange cMinValue cMaxValue .downward
      = .ok ((9999999999985714 : Int64), (-20 : Int)) from by
    unfold Number.normalizeToRange
    simp only []
    rw [show doNormalize false 9999999999985714290 (-23) cMinValue cMaxValue .downward
        = .ok { negative_ := false, mantissa_ := 9999999999985714, exponent_ := -20 } from by
      unfold doNormalize
      rw [show ((9999999999985714290 : UInt64) == 0) = false from rfl]
      simp only [Bool.false_eq_true, if_false]
      rw [doNormalize_scaleUp_id cMinValue 9999999999985714290 (-23) (by decide)]
      rw [show doNormalize_scaleDown cMaxValue (9999999999985714290 : UInt64) (-23) Guard.new
          = .ok ((9999999999985714 : UInt64), (-20 : Int),
                 { digits_ := 0x2900000000000000, xbit_ := false, sbit_ := false }) from by
        rw [doNormalize_scaleDown_step (by decide) (by decide)]
        show doNormalize_scaleDown cMaxValue 999999999998571429 (-22) (Guard.new.push 0) = _
        rw [doNormalize_scaleDown_step (by decide) (by decide)]
        show doNormalize_scaleDown cMaxValue 99999999999857142 (-21) ((Guard.new.push 0).push 9) = _
        rw [doNormalize_scaleDown_step (by decide) (by decide)]
        show doNormalize_scaleDown cMaxValue 9999999999985714 (-20)
            (((Guard.new.push 0).push 9).push 2) = _
        rw [doNormalize_scaleDown_id _ _ _ _ (by decide)]
        rfl]
      simp only []
      rw [show (decide ((-20 : Int) < minExponent)
            || decide ((9999999999985714 : UInt64) < cMinValue)) = false from by decide]
      simp only [Bool.false_eq_true, if_false]
      rw [show doNormalize_capAtMaxRep (9999999999985714 : UInt64) (-20)
            { digits_ := 0x2900000000000000, xbit_ := false, sbit_ := false }
          = .ok ((9999999999985714 : UInt64), (-20 : Int),
                 { digits_ := 0x2900000000000000, xbit_ := false, sbit_ := false }) from by
        unfold doNormalize_capAtMaxRep; rw [if_neg (by decide)]]
      simp only []
      rw [show ({ digits_ := 0x2900000000000000, xbit_ := false, sbit_ := false } : Guard).doRoundUp
          false (9999999999985714 : UInt64) (-20) cMinValue cMaxValue .downward
          "Number::normalize 2"
          = .ok { negative_ := false, mantissa_ := 9999999999985714, exponent_ := -20 } from by
        unfold Guard.doRoundUp Guard.bringIntoRange Guard.round Guard.doDropDigit; rfl]
      simp only [RoundResult.toNumber]]
    rfl]
  simp only []
  show STAmount.checked .fractional 9999999999985714 (-20) false .downward = _
  unfold STAmount.checked STAmount.unchecked
  exact STAmount.canonicalize_canonical_id _ .downward ⟨rfl, by decide, by decide, by decide, by decide⟩

/-- The clamped recovery computation pays `0.000099999999999857140`. -/
private theorem cw_sharesToAssets2 (v : Vault)
    (hAT : v.assetsTotal = ⟨false, 3000000000000000000, -18⟩)
    (hIU : v.interestUnrealized = Number.zero)
    (hLU : v.lossUnrealized = Number.zero)
    (hST : v.sharesTotal = ⟨false, 7000000000000000000, -3⟩)
    (hNT : v.numericType = NumericType.fractional) :
    Vault.sharesToAssetsWithdraw v cwsh2 false = .ok cwar2 := by
  unfold Vault.sharesToAssetsWithdraw
  rw [hAT, hIU, hLU, hST, hNT]
  simp only [operator_sub_zero_right, ok_bind]
  rw [if_neg (show ¬ (((⟨false, 3000000000000000000, -18⟩ : Number).mantissa_ == 0) = true) from by decide)]
  simp only [cwsh2_toNumber, ok_bind, cw_recovered2_mul, cw_recovered2_div,
    cw_recovered2_ofNumber, pure_bind]
  rfl

/-- The clamped recovery as a `Number` (19-digit lift). -/
private theorem cwar2_toNumber :
    cwar2.toNumber .to_nearest = .ok ⟨false, 9999999999985714000, -23⟩ := by
  rw [STAmount.toNumber_iou_canonical cwar2 .to_nearest ⟨rfl, by decide, by decide, by decide, by decide⟩]
  rfl

/-! ## Stored-field subtractions -/

/-- `3 - 0.9999999999999998` at 19 digits: one alignment shift, exact. -/
private theorem cw_sub_total1 :
    Number.operator_sub ⟨false, 3000000000000000000, -18⟩ ⟨false, 9999999999999998000, -19⟩
      .to_nearest = .ok ⟨false, 2000000000000000200, -18⟩ := by
  unfold Number.operator_sub
  rw [show (⟨false, 9999999999999998000, -19⟩ : Number).operator_neg
      = ⟨true, 9999999999999998000, -19⟩ from by decide]
  unfold Number.operator_add
  rw [if_neg (show ¬ ((⟨true, 9999999999999998000, -19⟩ : Number).operator_eq Number.zero = true) from by decide),
      if_neg (show ¬ ((⟨false, 3000000000000000000, -18⟩ : Number).operator_eq Number.zero = true) from by decide),
      if_neg (show ¬ ((⟨false, 3000000000000000000, -18⟩ : Number).operator_eq
        (⟨true, 9999999999999998000, -19⟩ : Number).operator_neg = true) from by decide)]
  simp -iota only [Bool.false_eq_true, if_false]
  rw [if_neg (by decide : ¬ ((-18 : Int) < (-19 : Int))), if_pos (by decide : (-18 : Int) > (-19 : Int))]
  rw [if_pos trivial]
  rw [show Number.operator_add.alignDown 9999999999999998000 (-19) Guard.new.set_negative (-18)
      = ((999999999999999800 : UInt64), (-18 : Int), Guard.new.set_negative) from by
    rw [Number.operator_add.alignDown, if_pos (by decide : (-19 : Int) < (-18 : Int))]
    show Number.operator_add.alignDown 999999999999999800 (-18) (Guard.new.set_negative.push 0) (-18) = _
    rw [Number.operator_add.alignDown, if_neg (by decide : ¬ ((-18 : Int) < (-18 : Int)))]
    rfl]
  simp only []
  rw [show ((false : Bool) == (true : Bool)) = false from rfl]
  simp only [Bool.false_eq_true, if_false]
  rw [if_pos (by decide : (3000000000000000000 : UInt64) > (999999999999999800 : UInt64))]
  rw [show toUInt128 (3000000000000000000 : UInt64) - toUInt128 (999999999999999800 : UInt64)
      = (2000000000000000200 : UInt128) from by decide]
  simp only []
  rw [show Number.operator_add.recover (toUInt128 largeRange.min * 1000)
        (2000000000000000200 : UInt128) (-18) Guard.new.set_negative 40
      = ((2000000000000000200 : UInt128), (-18 : Int), Guard.new.set_negative) from rfl]
  simp only [show (Guard.new.set_negative.empty : Bool) = true from rfl, Bool.not_true, if_true]
  show doNormalize128 false (2000000000000000200 : UInt128) (-18)
      largeRange.min largeRange.max .to_nearest false = _
  unfold doNormalize128
  rw [show ((2000000000000000200 : UInt128) == 0) = false from by decide]
  simp only [Bool.false_eq_true, if_false]
  rw [show doNormalize128.scaleUp largeRange.min (2000000000000000200 : UInt128) (-18)
        = ((2000000000000000200 : UInt128), (-18 : Int)) from by
      rw [doNormalize128.scaleUp.eq_def]; rw [if_neg (by decide)]]
  simp only []
  rw [show doNormalize_scaleDown128 largeRange.max (2000000000000000200 : UInt128) (-18) Guard.new
      = .ok (2000000000000000200, -18, Guard.new) from by
    conv_lhs => rw [doNormalize_scaleDown128]; rw [dif_neg (by decide)]]
  simp only []
  rw [show (decide ((-18 : Int) < minExponent)
        || decide ((2000000000000000200 : UInt128) < toUInt128 largeRange.min)) = false from by decide]
  simp only [Bool.false_eq_true, if_false]
  rw [show doNormalize_capAtMaxRep (toUInt64 (2000000000000000200 : UInt128)) (-18) Guard.new
      = .ok ((2000000000000000200 : UInt64), (-18 : Int), Guard.new) from by
    unfold doNormalize_capAtMaxRep; rw [if_neg (by decide)]; rfl]
  simp only []
  rw [show Guard.new.doRoundUp false (2000000000000000200 : UInt64) (-18)
      largeRange.min largeRange.max .to_nearest "Number::normalize 2"
      = .ok { negative_ := false, mantissa_ := 2000000000000000200, exponent_ := -18 } from by
    unfold Guard.doRoundUp Guard.bringIntoRange Guard.round Guard.doDropDigit; rfl]
  simp only [RoundResult.toNumber]

/-- `7e15 - 2333333333333333` at 19 digits: same exponent, exact. -/
private theorem cw_sub_shares1 :
    Number.operator_sub ⟨false, 7000000000000000000, -3⟩ ⟨false, 2333333333333333000, -3⟩
      .to_nearest = .ok ⟨false, 4666666666666667000, -3⟩ := by
  unfold Number.operator_sub
  rw [show (⟨false, 2333333333333333000, -3⟩ : Number).operator_neg
      = ⟨true, 2333333333333333000, -3⟩ from by decide]
  unfold Number.operator_add
  rw [if_neg (show ¬ ((⟨true, 2333333333333333000, -3⟩ : Number).operator_eq Number.zero = true) from by decide),
      if_neg (show ¬ ((⟨false, 7000000000000000000, -3⟩ : Number).operator_eq Number.zero = true) from by decide),
      if_neg (show ¬ ((⟨false, 7000000000000000000, -3⟩ : Number).operator_eq
        (⟨true, 2333333333333333000, -3⟩ : Number).operator_neg = true) from by decide)]
  simp -iota only [Bool.false_eq_true, if_false]
  rw [if_neg (by decide : ¬ ((-3 : Int) < (-3 : Int))), if_neg (by decide : ¬ ((-3 : Int) > (-3 : Int)))]
  simp only []
  rw [show ((false : Bool) == (true : Bool)) = false from rfl]
  simp only [Bool.false_eq_true, if_false]
  rw [if_pos (by decide : (7000000000000000000 : UInt64) > (2333333333333333000 : UInt64))]
  rw [show toUInt128 (7000000000000000000 : UInt64) - toUInt128 (2333333333333333000 : UInt64)
      = (4666666666666667000 : UInt128) from by decide]
  simp only []
  rw [show Number.operator_add.recover (toUInt128 largeRange.min * 1000)
        (4666666666666667000 : UInt128) (-3) Guard.new 40
      = ((4666666666666667000 : UInt128), (-3 : Int), Guard.new) from rfl]
  simp only [show (Guard.new.empty : Bool) = true from rfl, Bool.not_true, if_true]
  show doNormalize128 false (4666666666666667000 : UInt128) (-3)
      largeRange.min largeRange.max .to_nearest false = _
  unfold doNormalize128
  rw [show ((4666666666666667000 : UInt128) == 0) = false from by decide]
  simp only [Bool.false_eq_true, if_false]
  rw [show doNormalize128.scaleUp largeRange.min (4666666666666667000 : UInt128) (-3)
        = ((4666666666666667000 : UInt128), (-3 : Int)) from by
      rw [doNormalize128.scaleUp.eq_def]; rw [if_neg (by decide)]]
  simp only []
  rw [show doNormalize_scaleDown128 largeRange.max (4666666666666667000 : UInt128) (-3) Guard.new
      = .ok (4666666666666667000, -3, Guard.new) from by
    conv_lhs => rw [doNormalize_scaleDown128]; rw [dif_neg (by decide)]]
  simp only []
  rw [show (decide ((-3 : Int) < minExponent)
        || decide ((4666666666666667000 : UInt128) < toUInt128 largeRange.min)) = false from by decide]
  simp only [Bool.false_eq_true, if_false]
  rw [show doNormalize_capAtMaxRep (toUInt64 (4666666666666667000 : UInt128)) (-3) Guard.new
      = .ok ((4666666666666667000 : UInt64), (-3 : Int), Guard.new) from by
    unfold doNormalize_capAtMaxRep; rw [if_neg (by decide)]; rfl]
  simp only []
  rw [show Guard.new.doRoundUp false (4666666666666667000 : UInt64) (-3)
      largeRange.min largeRange.max .to_nearest "Number::normalize 2"
      = .ok { negative_ := false, mantissa_ := 4666666666666667000, exponent_ := -3 } from by
    unfold Guard.doRoundUp Guard.bringIntoRange Guard.round Guard.doDropDigit; rfl]
  simp only [RoundResult.toNumber]

/-- `3 - 0.000099999999999857140` at 19 digits: the exact difference needs 21
digits, the recover loop replays two guard digits and the result rounds up to
`2.999900000000000143`. -/
private theorem cw_sub_total2 :
    Number.operator_sub ⟨false, 3000000000000000000, -18⟩ ⟨false, 9999999999985714000, -23⟩
      .to_nearest = .ok ⟨false, 2999900000000000143, -18⟩ := by
  unfold Number.operator_sub
  rw [show (⟨false, 9999999999985714000, -23⟩ : Number).operator_neg
      = ⟨true, 9999999999985714000, -23⟩ from by decide]
  unfold Number.operator_add
  rw [if_neg (show ¬ ((⟨true, 9999999999985714000, -23⟩ : Number).operator_eq Number.zero = true) from by decide),
      if_neg (show ¬ ((⟨false, 3000000000000000000, -18⟩ : Number).operator_eq Number.zero = true) from by decide),
      if_neg (show ¬ ((⟨false, 3000000000000000000, -18⟩ : Number).operator_eq
        (⟨true, 9999999999985714000, -23⟩ : Number).operator_neg = true) from by decide)]
  simp -iota only [Bool.false_eq_true, if_false]
  rw [if_neg (by decide : ¬ ((-18 : Int) < (-23 : Int))), if_pos (by decide : (-18 : Int) > (-23 : Int))]
  rw [if_pos trivial]
  rw [show Number.operator_add.alignDown 9999999999985714000 (-23) Guard.new.set_negative (-18)
      = ((99999999999857 : UInt64), (-18 : Int),
         ({ digits_ := 0x1400000000000000, xbit_ := false, sbit_ := true } : Guard)) from by
    rw [Number.operator_add.alignDown, if_pos (by decide : (-23 : Int) < (-18 : Int))]
    show Number.operator_add.alignDown 999999999998571400 (-22) Guard.new.set_negative (-18) = _
    rw [Number.operator_add.alignDown, if_pos (by decide : (-22 : Int) < (-18 : Int))]
    show Number.operator_add.alignDown 99999999999857140 (-21) Guard.new.set_negative (-18) = _
    rw [Number.operator_add.alignDown, if_pos (by decide : (-21 : Int) < (-18 : Int))]
    show Number.operator_add.alignDown 9999999999985714 (-20) Guard.new.set_negative (-18) = _
    rw [Number.operator_add.alignDown, if_pos (by decide : (-20 : Int) < (-18 : Int))]
    show Number.operator_add.alignDown 999999999998571 (-19)
        { digits_ := 0x4000000000000000, xbit_ := false, sbit_ := true } (-18) = _
    rw [Number.operator_add.alignDown, if_pos (by decide : (-19 : Int) < (-18 : Int))]
    show Number.operator_add.alignDown 99999999999857 (-18)
        { digits_ := 0x1400000000000000, xbit_ := false, sbit_ := true } (-18) = _
    rw [Number.operator_add.alignDown, if_neg (by decide : ¬ ((-18 : Int) < (-18 : Int)))]]
  simp only []
  rw [show ((false : Bool) == (true : Bool)) = false from rfl]
  simp only [Bool.false_eq_true, if_false]
  rw [if_pos (by decide : (3000000000000000000 : UInt64) > (99999999999857 : UInt64))]
  rw [show toUInt128 (3000000000000000000 : UInt64) - toUInt128 (99999999999857 : UInt64)
      = (2999900000000000143 : UInt128) from by decide]
  simp only []
  rw [show Number.operator_add.recover (toUInt128 largeRange.min * 1000)
        (2999900000000000143 : UInt128) (-18)
        ({ digits_ := 0x1400000000000000, xbit_ := false, sbit_ := true } : Guard) 40
      = ((299990000000000014286 : UInt128), (-20 : Int),
         ({ digits_ := 0, xbit_ := false, sbit_ := true } : Guard)) from rfl]
  simp only [show (({ digits_ := 0, xbit_ := false, sbit_ := true } : Guard).empty : Bool) = true from rfl,
    Bool.not_true, if_true]
  show doNormalize128 false (299990000000000014286 : UInt128) (-20)
      largeRange.min largeRange.max .to_nearest false = _
  unfold doNormalize128
  rw [show ((299990000000000014286 : UInt128) == 0) = false from by decide]
  simp only [Bool.false_eq_true, if_false]
  rw [show doNormalize128.scaleUp largeRange.min (299990000000000014286 : UInt128) (-20)
        = ((299990000000000014286 : UInt128), (-20 : Int)) from by
      rw [doNormalize128.scaleUp.eq_def]; rw [if_neg (by decide)]]
  simp only []
  rw [show doNormalize_scaleDown128 largeRange.max (299990000000000014286 : UInt128) (-20) Guard.new
      = .ok (2999900000000000142, -18,
             { digits_ := 0x8600000000000000, xbit_ := false, sbit_ := false }) from by
    cdsd128_step; cdsd128_step
    conv_lhs => rw [doNormalize_scaleDown128]; rw [dif_neg (by decide)]
    rfl]
  simp only []
  rw [show (decide ((-18 : Int) < minExponent)
        || decide ((2999900000000000142 : UInt128) < toUInt128 largeRange.min)) = false from by decide]
  simp only [Bool.false_eq_true, if_false]
  rw [show doNormalize_capAtMaxRep (toUInt64 (2999900000000000142 : UInt128)) (-18)
        { digits_ := 0x8600000000000000, xbit_ := false, sbit_ := false }
      = .ok ((2999900000000000142 : UInt64), (-18 : Int),
             { digits_ := 0x8600000000000000, xbit_ := false, sbit_ := false }) from by
    unfold doNormalize_capAtMaxRep; rw [if_neg (by decide)]; rfl]
  simp only []
  rw [show ({ digits_ := 0x8600000000000000, xbit_ := false, sbit_ := false } : Guard).doRoundUp
      false (2999900000000000142 : UInt64) (-18) largeRange.min largeRange.max .to_nearest
      "Number::normalize 2"
      = .ok { negative_ := false, mantissa_ := 2999900000000000143, exponent_ := -18 } from by
    unfold Guard.doRoundUp Guard.bringIntoRange Guard.round Guard.doDropDigit; rfl]
  simp only [RoundResult.toNumber]

/-- `7e15 - 233333333333` at 19 digits: four alignment shifts, exact. -/
private theorem cw_sub_shares2 :
    Number.operator_sub ⟨false, 7000000000000000000, -3⟩ ⟨false, 2333333333330000000, -7⟩
      .to_nearest = .ok ⟨false, 6999766666666667000, -3⟩ := by
  unfold Number.operator_sub
  rw [show (⟨false, 2333333333330000000, -7⟩ : Number).operator_neg
      = ⟨true, 2333333333330000000, -7⟩ from by decide]
  unfold Number.operator_add
  rw [if_neg (show ¬ ((⟨true, 2333333333330000000, -7⟩ : Number).operator_eq Number.zero = true) from by decide),
      if_neg (show ¬ ((⟨false, 7000000000000000000, -3⟩ : Number).operator_eq Number.zero = true) from by decide),
      if_neg (show ¬ ((⟨false, 7000000000000000000, -3⟩ : Number).operator_eq
        (⟨true, 2333333333330000000, -7⟩ : Number).operator_neg = true) from by decide)]
  simp -iota only [Bool.false_eq_true, if_false]
  rw [if_neg (by decide : ¬ ((-3 : Int) < (-7 : Int))), if_pos (by decide : (-3 : Int) > (-7 : Int))]
  rw [if_pos trivial]
  rw [show Number.operator_add.alignDown 2333333333330000000 (-7) Guard.new.set_negative (-3)
      = ((233333333333000 : UInt64), (-3 : Int), Guard.new.set_negative) from by
    rw [Number.operator_add.alignDown, if_pos (by decide : (-7 : Int) < (-3 : Int))]
    show Number.operator_add.alignDown 233333333333000000 (-6) Guard.new.set_negative (-3) = _
    rw [Number.operator_add.alignDown, if_pos (by decide : (-6 : Int) < (-3 : Int))]
    show Number.operator_add.alignDown 23333333333300000 (-5) Guard.new.set_negative (-3) = _
    rw [Number.operator_add.alignDown, if_pos (by decide : (-5 : Int) < (-3 : Int))]
    show Number.operator_add.alignDown 2333333333330000 (-4) Guard.new.set_negative (-3) = _
    rw [Number.operator_add.alignDown, if_pos (by decide : (-4 : Int) < (-3 : Int))]
    show Number.operator_add.alignDown 233333333333000 (-3) Guard.new.set_negative (-3) = _
    rw [Number.operator_add.alignDown, if_neg (by decide : ¬ ((-3 : Int) < (-3 : Int)))]]
  simp only []
  rw [show ((false : Bool) == (true : Bool)) = false from rfl]
  simp only [Bool.false_eq_true, if_false]
  rw [if_pos (by decide : (7000000000000000000 : UInt64) > (233333333333000 : UInt64))]
  rw [show toUInt128 (7000000000000000000 : UInt64) - toUInt128 (233333333333000 : UInt64)
      = (6999766666666667000 : UInt128) from by decide]
  simp only []
  rw [show Number.operator_add.recover (toUInt128 largeRange.min * 1000)
        (6999766666666667000 : UInt128) (-3) Guard.new.set_negative 40
      = ((6999766666666667000 : UInt128), (-3 : Int), Guard.new.set_negative) from rfl]
  simp only [show (Guard.new.set_negative.empty : Bool) = true from rfl, Bool.not_true, if_true]
  show doNormalize128 false (6999766666666667000 : UInt128) (-3)
      largeRange.min largeRange.max .to_nearest false = _
  unfold doNormalize128
  rw [show ((6999766666666667000 : UInt128) == 0) = false from by decide]
  simp only [Bool.false_eq_true, if_false]
  rw [show doNormalize128.scaleUp largeRange.min (6999766666666667000 : UInt128) (-3)
        = ((6999766666666667000 : UInt128), (-3 : Int)) from by
      rw [doNormalize128.scaleUp.eq_def]; rw [if_neg (by decide)]]
  simp only []
  rw [show doNormalize_scaleDown128 largeRange.max (6999766666666667000 : UInt128) (-3) Guard.new
      = .ok (6999766666666667000, -3, Guard.new) from by
    conv_lhs => rw [doNormalize_scaleDown128]; rw [dif_neg (by decide)]]
  simp only []
  rw [show (decide ((-3 : Int) < minExponent)
        || decide ((6999766666666667000 : UInt128) < toUInt128 largeRange.min)) = false from by decide]
  simp only [Bool.false_eq_true, if_false]
  rw [show doNormalize_capAtMaxRep (toUInt64 (6999766666666667000 : UInt128)) (-3) Guard.new
      = .ok ((6999766666666667000 : UInt64), (-3 : Int), Guard.new) from by
    unfold doNormalize_capAtMaxRep; rw [if_neg (by decide)]; rfl]
  simp only []
  rw [show Guard.new.doRoundUp false (6999766666666667000 : UInt64) (-3)
      largeRange.min largeRange.max .to_nearest "Number::normalize 2"
      = .ok { negative_ := false, mantissa_ := 6999766666666667000, exponent_ := -3 } from by
    unfold Guard.doRoundUp Guard.bringIntoRange Guard.round Guard.doDropDigit; rfl]
  simp only [RoundResult.toNumber]

/-- `0.0001 - 0.000099999999999857140` at 19 digits: the tiny difference
`1.4286e-16` scales up twelve digits, exact. -/
private theorem cw_sub_avail2 :
    Number.operator_sub ⟨false, 1000000000000000000, -22⟩ ⟨false, 9999999999985714000, -23⟩
      .to_nearest = .ok ⟨false, 1428600000000000000, -34⟩ := by
  unfold Number.operator_sub
  rw [show (⟨false, 9999999999985714000, -23⟩ : Number).operator_neg
      = ⟨true, 9999999999985714000, -23⟩ from by decide]
  unfold Number.operator_add
  rw [if_neg (show ¬ ((⟨true, 9999999999985714000, -23⟩ : Number).operator_eq Number.zero = true) from by decide),
      if_neg (show ¬ ((⟨false, 1000000000000000000, -22⟩ : Number).operator_eq Number.zero = true) from by decide),
      if_neg (show ¬ ((⟨false, 1000000000000000000, -22⟩ : Number).operator_eq
        (⟨true, 9999999999985714000, -23⟩ : Number).operator_neg = true) from by decide)]
  simp -iota only [Bool.false_eq_true, if_false]
  rw [if_neg (by decide : ¬ ((-22 : Int) < (-23 : Int))), if_pos (by decide : (-22 : Int) > (-23 : Int))]
  rw [if_pos trivial]
  rw [show Number.operator_add.alignDown 9999999999985714000 (-23) Guard.new.set_negative (-22)
      = ((999999999998571400 : UInt64), (-22 : Int), Guard.new.set_negative) from by
    rw [Number.operator_add.alignDown, if_pos (by decide : (-23 : Int) < (-22 : Int))]
    show Number.operator_add.alignDown 999999999998571400 (-22) Guard.new.set_negative (-22) = _
    rw [Number.operator_add.alignDown, if_neg (by decide : ¬ ((-22 : Int) < (-22 : Int)))]]
  simp only []
  rw [show ((false : Bool) == (true : Bool)) = false from rfl]
  simp only [Bool.false_eq_true, if_false]
  rw [if_pos (by decide : (1000000000000000000 : UInt64) > (999999999998571400 : UInt64))]
  rw [show toUInt128 (1000000000000000000 : UInt64) - toUInt128 (999999999998571400 : UInt64)
      = (1428600 : UInt128) from by decide]
  simp only []
  rw [show Number.operator_add.recover (toUInt128 largeRange.min * 1000)
        (1428600 : UInt128) (-22) Guard.new.set_negative 40
      = ((1428600 : UInt128), (-22 : Int), Guard.new.set_negative) from rfl]
  simp only [show (Guard.new.set_negative.empty : Bool) = true from rfl, Bool.not_true, if_true]
  show doNormalize128 false (1428600 : UInt128) (-22)
      largeRange.min largeRange.max .to_nearest false = _
  unfold doNormalize128
  rw [show ((1428600 : UInt128) == 0) = false from by decide]
  simp only [Bool.false_eq_true, if_false]
  rw [show doNormalize128.scaleUp largeRange.min (1428600 : UInt128) (-22)
        = ((1428600000000000000 : UInt128), (-34 : Int)) from by
      csu128_step; csu128_step; csu128_step; csu128_step; csu128_step; csu128_step
      csu128_step; csu128_step; csu128_step; csu128_step; csu128_step; csu128_step
      rw [doNormalize128.scaleUp.eq_def]; rw [if_neg (by decide)]
      rfl]
  simp only []
  rw [show doNormalize_scaleDown128 largeRange.max (1428600000000000000 : UInt128) (-34) Guard.new
      = .ok (1428600000000000000, -34, Guard.new) from by
    conv_lhs => rw [doNormalize_scaleDown128]; rw [dif_neg (by decide)]]
  simp only []
  rw [show (decide ((-34 : Int) < minExponent)
        || decide ((1428600000000000000 : UInt128) < toUInt128 largeRange.min)) = false from by decide]
  simp only [Bool.false_eq_true, if_false]
  rw [show doNormalize_capAtMaxRep (toUInt64 (1428600000000000000 : UInt128)) (-34) Guard.new
      = .ok ((1428600000000000000 : UInt64), (-34 : Int), Guard.new) from by
    unfold doNormalize_capAtMaxRep; rw [if_neg (by decide)]; rfl]
  simp only []
  rw [show Guard.new.doRoundUp false (1428600000000000000 : UInt64) (-34)
      largeRange.min largeRange.max .to_nearest "Number::normalize 2"
      = .ok { negative_ := false, mantissa_ := 1428600000000000000, exponent_ := -34 } from by
    unfold Guard.doRoundUp Guard.bringIntoRange Guard.round Guard.doDropDigit; rfl]
  simp only [RoundResult.toNumber]

/-! ## 16-digit views of the stored totals (the too-small guard) -/

/-- The 16-digit view of the old total `3`: exact. -/
private theorem cw_round_3 :
    STAmount.ofNumber .fractional ⟨false, 3000000000000000000, -18⟩ .to_nearest
      = .ok (STAmount.unchecked .fractional 3000000000000000 (-15) false) := by
  unfold STAmount.ofNumber
  simp only [show (decide ((⟨false, 3000000000000000000, -18⟩ : Number).signum < 0)) = false from by decide,
    Bool.false_eq_true, if_false,
    show NumericType.fractional.isIntegral = false from rfl]
  rw [show kMinValue = cMinValue from rfl, show kMaxValue = cMaxValue from rfl]
  rw [normalizeToRange_16_exact _ .to_nearest (by decide) (by decide) (by decide) (by decide) (by decide)]
  simp only [Bool.false_eq_true, if_false]
  rw [show (((3000000000000000000 : UInt64) / 10 / 10 / 10).toInt64).toUInt64
      = (3000000000000000 : UInt64) from by decide,
    show (⟨false, 3000000000000000000, -18⟩ : Number).exponent_ + 3 = -15 from by decide]
  show STAmount.checked .fractional 3000000000000000 (-15) false .to_nearest = _
  unfold STAmount.checked STAmount.unchecked
  exact STAmount.canonicalize_canonical_id _ .to_nearest ⟨rfl, by decide, by decide, by decide, by decide⟩

/-- The 16-digit view of the new total `2.0000000000000002`: the tail rounds
away. -/
private theorem cw_round_total1 :
    STAmount.ofNumber .fractional ⟨false, 2000000000000000200, -18⟩ .to_nearest
      = .ok (STAmount.unchecked .fractional 2000000000000000 (-15) false) := by
  unfold STAmount.ofNumber
  simp only [show (decide ((⟨false, 2000000000000000200, -18⟩ : Number).signum < 0)) = false from by decide,
    Bool.false_eq_true, if_false,
    show NumericType.fractional.isIntegral = false from rfl]
  rw [show kMinValue = cMinValue from rfl, show kMaxValue = cMaxValue from rfl]
  rw [show (⟨false, 2000000000000000200, -18⟩ : Number).normalizeToRange cMinValue cMaxValue .to_nearest
      = .ok ((2000000000000000 : Int64), (-15 : Int)) from by
    unfold Number.normalizeToRange
    simp only []
    rw [show doNormalize false 2000000000000000200 (-18) cMinValue cMaxValue .to_nearest
        = .ok { negative_ := false, mantissa_ := 2000000000000000, exponent_ := -15 } from by
      unfold doNormalize
      rw [show ((2000000000000000200 : UInt64) == 0) = false from rfl]
      simp only [Bool.false_eq_true, if_false]
      rw [doNormalize_scaleUp_id cMinValue 2000000000000000200 (-18) (by decide)]
      rw [show doNormalize_scaleDown cMaxValue (2000000000000000200 : UInt64) (-18) Guard.new
          = .ok ((2000000000000000 : UInt64), (-15 : Int),
                 { digits_ := 0x2000000000000000, xbit_ := false, sbit_ := false }) from by
        rw [doNormalize_scaleDown_step (by decide) (by decide)]
        show doNormalize_scaleDown cMaxValue 200000000000000020 (-17) (Guard.new.push 0) = _
        rw [doNormalize_scaleDown_step (by decide) (by decide)]
        show doNormalize_scaleDown cMaxValue 20000000000000002 (-16) ((Guard.new.push 0).push 0) = _
        rw [doNormalize_scaleDown_step (by decide) (by decide)]
        show doNormalize_scaleDown cMaxValue 2000000000000000 (-15)
            (((Guard.new.push 0).push 0).push 2) = _
        rw [doNormalize_scaleDown_id _ _ _ _ (by decide)]
        rfl]
      simp only []
      rw [show (decide ((-15 : Int) < minExponent)
            || decide ((2000000000000000 : UInt64) < cMinValue)) = false from by decide]
      simp only [Bool.false_eq_true, if_false]
      rw [show doNormalize_capAtMaxRep (2000000000000000 : UInt64) (-15)
            { digits_ := 0x2000000000000000, xbit_ := false, sbit_ := false }
          = .ok ((2000000000000000 : UInt64), (-15 : Int),
                 { digits_ := 0x2000000000000000, xbit_ := false, sbit_ := false }) from by
        unfold doNormalize_capAtMaxRep; rw [if_neg (by decide)]]
      simp only []
      rw [show ({ digits_ := 0x2000000000000000, xbit_ := false, sbit_ := false } : Guard).doRoundUp
          false (2000000000000000 : UInt64) (-15) cMinValue cMaxValue .to_nearest
          "Number::normalize 2"
          = .ok { negative_ := false, mantissa_ := 2000000000000000, exponent_ := -15 } from by
        unfold Guard.doRoundUp Guard.bringIntoRange Guard.round Guard.doDropDigit; rfl]
      simp only [RoundResult.toNumber]]
    rfl]
  simp only []
  show STAmount.checked .fractional 2000000000000000 (-15) false .to_nearest = _
  unfold STAmount.checked STAmount.unchecked
  exact STAmount.canonicalize_canonical_id _ .to_nearest ⟨rfl, by decide, by decide, by decide, by decide⟩

/-- The 16-digit view of the new total `2.999900000000000143`: the tail rounds
away. -/
private theorem cw_round_total2 :
    STAmount.ofNumber .fractional ⟨false, 2999900000000000143, -18⟩ .to_nearest
      = .ok (STAmount.unchecked .fractional 2999900000000000 (-15) false) := by
  unfold STAmount.ofNumber
  simp only [show (decide ((⟨false, 2999900000000000143, -18⟩ : Number).signum < 0)) = false from by decide,
    Bool.false_eq_true, if_false,
    show NumericType.fractional.isIntegral = false from rfl]
  rw [show kMinValue = cMinValue from rfl, show kMaxValue = cMaxValue from rfl]
  rw [show (⟨false, 2999900000000000143, -18⟩ : Number).normalizeToRange cMinValue cMaxValue .to_nearest
      = .ok ((2999900000000000 : Int64), (-15 : Int)) from by
    unfold Number.normalizeToRange
    simp only []
    rw [show doNormalize false 2999900000000000143 (-18) cMinValue cMaxValue .to_nearest
        = .ok { negative_ := false, mantissa_ := 2999900000000000, exponent_ := -15 } from by
      unfold doNormalize
      rw [show ((2999900000000000143 : UInt64) == 0) = false from rfl]
      simp only [Bool.false_eq_true, if_false]
      rw [doNormalize_scaleUp_id cMinValue 2999900000000000143 (-18) (by decide)]
      rw [show doNormalize_scaleDown cMaxValue (2999900000000000143 : UInt64) (-18) Guard.new
          = .ok ((2999900000000000 : UInt64), (-15 : Int),
                 { digits_ := 0x1430000000000000, xbit_ := false, sbit_ := false }) from by
        rw [doNormalize_scaleDown_step (by decide) (by decide)]
        show doNormalize_scaleDown cMaxValue 299990000000000014 (-17) (Guard.new.push 3) = _
        rw [doNormalize_scaleDown_step (by decide) (by decide)]
        show doNormalize_scaleDown cMaxValue 29999000000000001 (-16) ((Guard.new.push 3).push 4) = _
        rw [doNormalize_scaleDown_step (by decide) (by decide)]
        show doNormalize_scaleDown cMaxValue 2999900000000000 (-15)
            (((Guard.new.push 3).push 4).push 1) = _
        rw [doNormalize_scaleDown_id _ _ _ _ (by decide)]
        rfl]
      simp only []
      rw [show (decide ((-15 : Int) < minExponent)
            || decide ((2999900000000000 : UInt64) < cMinValue)) = false from by decide]
      simp only [Bool.false_eq_true, if_false]
      rw [show doNormalize_capAtMaxRep (2999900000000000 : UInt64) (-15)
            { digits_ := 0x1430000000000000, xbit_ := false, sbit_ := false }
          = .ok ((2999900000000000 : UInt64), (-15 : Int),
                 { digits_ := 0x1430000000000000, xbit_ := false, sbit_ := false }) from by
        unfold doNormalize_capAtMaxRep; rw [if_neg (by decide)]]
      simp only []
      rw [show ({ digits_ := 0x1430000000000000, xbit_ := false, sbit_ := false } : Guard).doRoundUp
          false (2999900000000000 : UInt64) (-15) cMinValue cMaxValue .to_nearest
          "Number::normalize 2"
          = .ok { negative_ := false, mantissa_ := 2999900000000000, exponent_ := -15 } from by
        unfold Guard.doRoundUp Guard.bringIntoRange Guard.round Guard.doDropDigit; rfl]
      simp only [RoundResult.toNumber]]
    rfl]
  simp only []
  show STAmount.checked .fractional 2999900000000000 (-15) false .to_nearest = _
  unfold STAmount.checked STAmount.unchecked
  exact STAmount.canonicalize_canonical_id _ .to_nearest ⟨rfl, by decide, by decide, by decide, by decide⟩

/-! ## The two clawback runs -/

/-- The `cwv` post-clawback vault. -/
def cwv1' : Vault :=
  { assetsTotal := ⟨false, 2000000000000000200, -18⟩
  , assetsAvailable := ⟨false, 2000000000000000200, -18⟩
  , assetsMaximum := none, numericType := .fractional, scale := 0
  , sharesTotal := ⟨false, 4666666666666667000, -3⟩
  , interestUnrealized := Number.zero, lossUnrealized := Number.zero }

/-- The `cwv` clawback result. -/
def cwr1 : ClawbackResult := ⟨none, cwv1', cwar1, cwsh1⟩

/-- The `cwvB` post-clawback vault. -/
def cwvB' : Vault :=
  { assetsTotal := ⟨false, 2999900000000000143, -18⟩
  , assetsAvailable := ⟨false, 1428600000000000000, -34⟩
  , assetsMaximum := none, numericType := .fractional, scale := 0
  , sharesTotal := ⟨false, 6999766666666667000, -3⟩
  , interestUnrealized := Number.zero, lossUnrealized := Number.zero }

/-- The `cwvB` clawback result. -/
def cwr2 : ClawbackResult := ⟨none, cwvB', cwar2, cwsh2⟩

/-- The first computed `cwv` recovery does not exceed `assetsAvailable`. -/
private theorem cw_gt1 :
    (⟨false, 9999999999999998000, -19⟩ : Number).operator_gt cwv.assetsAvailable = false := by
  decide

/-- The first computed `cwvB` recovery exceeds `assetsAvailable`. -/
private theorem cw_gt2 :
    (⟨false, 9999999999999998000, -19⟩ : Number).operator_gt cwvB.assetsAvailable = true := by
  decide

/-- The `cwv` exchange passes the availability check on the first pass. -/
private theorem cw_computeClawback1 :
    computeClawback cwv cwa1 = .ok ⟨none, cwar1, cwsh1⟩ := by
  unfold computeClawback
  simp only [show cwa1.negative = false from rfl, Bool.false_eq_true, if_false,
    cw_assetsToShares1 cwv rfl rfl rfl rfl, ok_bind,
    cw_sharesToAssets1 cwv rfl rfl rfl rfl rfl, cwar1_toNumber, cw_gt1]
  rfl

/-- The `cwvB` exchange reprices from `assetsAvailable` and succeeds. -/
private theorem cw_computeClawback2 :
    computeClawback cwvB cwa1 = .ok ⟨none, cwar2, cwsh2⟩ := by
  unfold computeClawback
  simp only [show cwa1.negative = false from rfl, Bool.false_eq_true, if_false,
    cw_assetsToShares1 cwvB rfl rfl rfl rfl, ok_bind,
    cw_sharesToAssets1 cwvB rfl rfl rfl rfl rfl, cwar1_toNumber,
    show cwvB.numericType = NumericType.fractional from rfl,
    show cwvB.assetsAvailable = (⟨false, 1000000000000000000, -22⟩ : Number) from rfl,
    cw_clamp_ofNumber,
    cw_assetsToShares2 cwvB rfl rfl rfl rfl,
    cw_sharesToAssets2 cwvB rfl rfl rfl rfl rfl,
    cwar2_toNumber,
    show (⟨false, 9999999999985714000, -23⟩ : Number).operator_gt
      (⟨false, 1000000000000000000, -22⟩ : Number) = false from by decide]
  rfl

/-- The `cwv` witness clawback runs to `cwr1`. -/
private theorem cwv_run : cwv.clawback cwa1 = .ok cwr1 := by
  unfold Vault.clawback
  simp only [cw_computeClawback1, ok_bind, Option.isSome_none, Bool.false_eq_true, if_false,
    show cwsh1.isZero = false from rfl,
    cwsh1_toNumber, cwar1_toNumber,
    show cwv.assetsTotal = (⟨false, 3000000000000000000, -18⟩ : Number) from rfl,
    show cwv.assetsAvailable = (⟨false, 3000000000000000000, -18⟩ : Number) from rfl,
    show cwv.sharesTotal = (⟨false, 7000000000000000000, -3⟩ : Number) from rfl,
    show cwv.numericType = NumericType.fractional from rfl,
    cw_sub_total1, cw_round_3, cw_round_total1,
    show ((⟨false, 9999999999999998000, -19⟩ : Number).mantissa_ != 0 &&
      (STAmount.unchecked .fractional 3000000000000000 (-15) false).operator_eq
        (STAmount.unchecked .fractional 2000000000000000 (-15) false)) = false from by decide,
    cw_sub_shares1, pure_bind]
  rfl

/-- The `cwvB` witness clawback runs to `cwr2`. -/
private theorem cwvB_run : cwvB.clawback cwa1 = .ok cwr2 := by
  unfold Vault.clawback
  simp only [cw_computeClawback2, ok_bind, Option.isSome_none, Bool.false_eq_true, if_false,
    show cwsh2.isZero = false from rfl,
    cwsh2_toNumber, cwar2_toNumber,
    show cwvB.assetsTotal = (⟨false, 3000000000000000000, -18⟩ : Number) from rfl,
    show cwvB.assetsAvailable = (⟨false, 1000000000000000000, -22⟩ : Number) from rfl,
    show cwvB.sharesTotal = (⟨false, 7000000000000000000, -3⟩ : Number) from rfl,
    show cwvB.numericType = NumericType.fractional from rfl,
    cw_sub_total2, cw_round_3, cw_round_total2,
    show ((⟨false, 9999999999985714000, -23⟩ : Number).mantissa_ != 0 &&
      (STAmount.unchecked .fractional 3000000000000000 (-15) false).operator_eq
        (STAmount.unchecked .fractional 2999900000000000 (-15) false)) = false from by decide,
    cw_sub_shares2, cw_sub_avail2, pure_bind]
  rfl

/-! ## Exact values of the witness data -/

/-- Value of the stored total `3`. -/
private theorem cw_3num_toRat : (⟨false, 3000000000000000000, -18⟩ : Number).toRat = 3 := by
  rw [Number.toRat_of_nonneg _ rfl,
      show ((3000000000000000000 : UInt64).toNat) = 3000000000000000000 from by decide]
  norm_num

/-- Value of the stored available amount of `cwvB`. -/
private theorem cw_1e4_toRat :
    (⟨false, 1000000000000000000, -22⟩ : Number).toRat = 1 / 10 ^ 4 := by
  rw [Number.toRat_of_nonneg _ rfl,
      show ((1000000000000000000 : UInt64).toNat) = 1000000000000000000 from by decide]
  norm_num

/-- Value of the stored share total. -/
private theorem cw_7e15_toRat :
    (⟨false, 7000000000000000000, -3⟩ : Number).toRat = ((7000000000000000 : ℕ) : ℚ) := by
  rw [Number.toRat_of_nonneg _ rfl,
      show ((7000000000000000000 : UInt64).toNat) = 7000000000000000000 from by decide]
  norm_num

/-- Value of the clawed amount. -/
private theorem cwa1_toRat : cwa1.toRat = 1 := by
  rw [STAmount.toRat_of_nonneg cwa1 rfl]
  show ((1000000000000000 : UInt64).toNat : ℚ) * 10 ^ (-15 : ℤ) = 1
  rw [show ((1000000000000000 : UInt64).toNat) = 1000000000000000 from by decide]
  norm_num

/-- Value of the `cwv` destroyed shares. -/
private theorem cwsh1_toRat : cwsh1.toRat = 2333333333333333 := by
  rw [STAmount.toRat_of_nonneg cwsh1 rfl]
  show ((2333333333333333 : UInt64).toNat : ℚ) * 10 ^ (0 : ℤ) = 2333333333333333
  rw [show ((2333333333333333 : UInt64).toNat) = 2333333333333333 from by decide]
  norm_num

/-- Value of the `cwvB` destroyed shares. -/
private theorem cwsh2_toRat : cwsh2.toRat = 233333333333 := by
  rw [STAmount.toRat_of_nonneg cwsh2 rfl]
  show ((233333333333 : UInt64).toNat : ℚ) * 10 ^ (0 : ℤ) = 233333333333
  rw [show ((233333333333 : UInt64).toNat) = 233333333333 from by decide]
  norm_num

/-- Value of the `cwv` recovered assets. -/
private theorem cwar1_toRat : cwar1.toRat = 9999999999999998 / 10 ^ 16 := by
  rw [STAmount.toRat_of_nonneg cwar1 rfl]
  show ((9999999999999998 : UInt64).toNat : ℚ) * 10 ^ (-16 : ℤ) = 9999999999999998 / 10 ^ 16
  rw [show ((9999999999999998 : UInt64).toNat) = 9999999999999998 from by decide]
  norm_num

/-- Value of the `cwvB` recovered assets. -/
private theorem cwar2_toRat : cwar2.toRat = 9999999999985714 / 10 ^ 20 := by
  rw [STAmount.toRat_of_nonneg cwar2 rfl]
  show ((9999999999985714 : UInt64).toNat : ℚ) * 10 ^ (-20 : ℤ) = 9999999999985714 / 10 ^ 20
  rw [show ((9999999999985714 : UInt64).toNat) = 9999999999985714 from by decide]
  norm_num

/-- Value of the clamped recovery amount. -/
private theorem cwclamp_toRat : cwclamp.toRat = 1 / 10 ^ 4 := by
  rw [STAmount.toRat_of_nonneg cwclamp rfl]
  show ((1000000000000000 : UInt64).toNat : ℚ) * 10 ^ (-19 : ℤ) = 1 / 10 ^ 4
  rw [show ((1000000000000000 : UInt64).toNat) = 1000000000000000 from by decide]
  norm_num

/-- Value of the `cwvB` post-clawback stored total. -/
private theorem cwvB'_total_toRat :
    cwvB'.assetsTotal.toRat = 2999900000000000143 / 10 ^ 18 := by
  show (⟨false, 2999900000000000143, -18⟩ : Number).toRat = _
  rw [Number.toRat_of_nonneg _ rfl,
      show ((2999900000000000143 : UInt64).toNat) = 2999900000000000143 from by decide]
  norm_num

/-- Exact share total of both witness vaults. -/
private theorem cw_exact_sharesTotal (v : Vault)
    (hST : v.sharesTotal = ⟨false, 7000000000000000000, -3⟩) :
    v.toExact.sharesTotal = 7000000000000000 := by
  show v.sharesTotal.toRat.num.toNat = _
  rw [hST, cw_7e15_toRat]
  norm_num
  rfl

/-- Withdrawal pricing value of both witness vaults. -/
private theorem cw_withdrawNav (v : Vault)
    (hAT : v.assetsTotal = ⟨false, 3000000000000000000, -18⟩)
    (hIU : v.interestUnrealized = Number.zero)
    (hLU : v.lossUnrealized = Number.zero) : v.withdrawNav = 3 := by
  unfold Vault.withdrawNav
  show v.assetsTotal.toRat - v.interestUnrealized.toRat - v.lossUnrealized.toRat = 3
  rw [hAT, hIU, hLU, cw_3num_toRat,
      Number.toRat_eq_zero_of_mantissa_zero Number.zero rfl]
  norm_num

/-- The two pricing subtractions are exact on both witness vaults. -/
private theorem cw_navExact (v : Vault)
    (hAT : v.assetsTotal = ⟨false, 3000000000000000000, -18⟩)
    (hIU : v.interestUnrealized = Number.zero)
    (hLU : v.lossUnrealized = Number.zero) :
    v.WithdrawNavExact false := by
  refine ⟨⟨false, 3000000000000000000, -18⟩, ⟨false, 3000000000000000000, -18⟩, ?_, ?_, ?_⟩
  · rw [hAT, hIU]
    exact operator_sub_zero_right _ _
  · show (⟨false, 3000000000000000000, -18⟩ : Number).operator_sub v.lossUnrealized
        .to_nearest = .ok ⟨false, 3000000000000000000, -18⟩
    rw [hLU]
    exact operator_sub_zero_right _ _
  · show (⟨false, 3000000000000000000, -18⟩ : Number).toRat = v.withdrawNav
    rw [cw_withdrawNav v hAT hIU hLU]
    exact cw_3num_toRat

/-- The shared witness vault is lawful. -/
private theorem cwv_lawful : cwv.Lawful := by
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · show (⟨false, 3000000000000000000, -18⟩ : Number).isNormalized
    norm_isNormalized
  · show (⟨false, 3000000000000000000, -18⟩ : Number).isNormalized
    norm_isNormalized
  · intro m hm
    rw [show cwv.assetsMaximum = none from rfl] at hm
    exact absurd hm (by simp)
  · show (⟨false, 7000000000000000000, -3⟩ : Number).isNormalized
    norm_isNormalized
  · exact Or.inl rfl
  · exact Or.inl rfl
  · show (0 : ℚ) ≤ (⟨false, 7000000000000000000, -3⟩ : Number).toRat
    rw [cw_7e15_toRat]
    positivity
  · show (⟨false, 7000000000000000000, -3⟩ : Number).toRat.den = 1
    rw [cw_7e15_toRat]
    exact Rat.den_natCast _
  · intro _
    rfl
  · decide
  · have hAT : cwv.toExact.assetsTotal = 3 := by
      show (⟨false, 3000000000000000000, -18⟩ : Number).toRat = _
      exact cw_3num_toRat
    have hAA : cwv.toExact.assetsAvailable = 3 := by
      show (⟨false, 3000000000000000000, -18⟩ : Number).toRat = _
      exact cw_3num_toRat
    have hST := cw_exact_sharesTotal cwv rfl
    have hI : cwv.toExact.interestUnrealized = 0 := by
      simp only [Vault.toExact]
      exact Number.toRat_eq_zero_of_mantissa_zero _ rfl
    have hL : cwv.toExact.lossUnrealized = 0 := by
      simp only [Vault.toExact]
      exact Number.toRat_eq_zero_of_mantissa_zero _ rfl
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hAT]
      norm_num
    · rw [hAA]
      norm_num
    · rw [hAT, hAA]
    · intro m hm
      rw [show cwv.toExact.assetsMaximum = none from rfl] at hm
      exact absurd hm (by simp)
    · intro h
      rw [hST] at h
      exact absurd h (by norm_num)
    · intro m hm
      rw [show cwv.toExact.assetsMaximum = none from rfl] at hm
      exact absurd hm (by simp)
    · rw [hL]
    · rw [hL, hAT, hAA]
      norm_num
    · rw [hI]
    · rw [hI, hAT, hAA]
      norm_num
    · intro _
      rw [hI, hAT]
      norm_num
    · rw [hAT, hI, hL]
      norm_num
    · intro h
      rw [hI] at h
      exact absurd h (by norm_num)

/-- The clamped-run vault is lawful. -/
private theorem cwvB_lawful : cwvB.Lawful := by
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · show (⟨false, 3000000000000000000, -18⟩ : Number).isNormalized
    norm_isNormalized
  · show (⟨false, 1000000000000000000, -22⟩ : Number).isNormalized
    norm_isNormalized
  · intro m hm
    rw [show cwvB.assetsMaximum = none from rfl] at hm
    exact absurd hm (by simp)
  · show (⟨false, 7000000000000000000, -3⟩ : Number).isNormalized
    norm_isNormalized
  · exact Or.inl rfl
  · exact Or.inl rfl
  · show (0 : ℚ) ≤ (⟨false, 7000000000000000000, -3⟩ : Number).toRat
    rw [cw_7e15_toRat]
    positivity
  · show (⟨false, 7000000000000000000, -3⟩ : Number).toRat.den = 1
    rw [cw_7e15_toRat]
    exact Rat.den_natCast _
  · intro _
    rfl
  · decide
  · have hAT : cwvB.toExact.assetsTotal = 3 := by
      show (⟨false, 3000000000000000000, -18⟩ : Number).toRat = _
      exact cw_3num_toRat
    have hAA : cwvB.toExact.assetsAvailable = 1 / 10 ^ 4 := by
      show (⟨false, 1000000000000000000, -22⟩ : Number).toRat = _
      exact cw_1e4_toRat
    have hST := cw_exact_sharesTotal cwvB rfl
    have hI : cwvB.toExact.interestUnrealized = 0 := by
      simp only [Vault.toExact]
      exact Number.toRat_eq_zero_of_mantissa_zero _ rfl
    have hL : cwvB.toExact.lossUnrealized = 0 := by
      simp only [Vault.toExact]
      exact Number.toRat_eq_zero_of_mantissa_zero _ rfl
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hAT]
      norm_num
    · rw [hAA]
      norm_num
    · rw [hAT, hAA]
      norm_num
    · intro m hm
      rw [show cwvB.toExact.assetsMaximum = none from rfl] at hm
      exact absurd hm (by simp)
    · intro h
      rw [hST] at h
      exact absurd h (by norm_num)
    · intro m hm
      rw [show cwvB.toExact.assetsMaximum = none from rfl] at hm
      exact absurd hm (by simp)
    · rw [hL]
    · rw [hL, hAT, hAA]
      norm_num
    · rw [hI]
    · rw [hI, hAT, hAA]
      norm_num
    · intro _
      rw [hI, hAT]
      norm_num
    · rw [hAT, hI, hL]
      norm_num
    · intro h
      rw [hI] at h
      exact absurd h (by norm_num)

/-! ## The witness error margins -/

/-- The `cwv` destroyed shares miss the ideal by `1/3`, beyond the relative
budget. -/
private theorem cwsh1_witness :
    RoundsWithinWitness cwr1.sharesDestroyed (cwv.idealSharesClawback cwa1.toRat) depositε := by
  unfold RoundsWithinWitness Vault.idealSharesClawback depositε
  rw [show RatValued.toRat cwr1.sharesDestroyed = cwsh1.toRat from rfl, cwsh1_toRat, cwa1_toRat,
      cw_exact_sharesTotal cwv rfl, cw_withdrawNav cwv rfl rfl rfl]
  rw [show ((7000000000000000 : ℕ) : ℚ) * 1 / 3 = 7000000000000000 / 3 from by norm_num]
  rw [show (2333333333333333 : ℚ) - 7000000000000000 / 3 = -(1 / 3) from by norm_num]
  rw [abs_neg, abs_of_pos (by norm_num : (0 : ℚ) < 1 / 3),
      abs_of_pos (by norm_num : (0 : ℚ) < (7000000000000000 : ℚ) / 3)]
  norm_num

/-- The `cwvB` destroyed shares miss the clamped ideal by `1/3`, beyond the
relative budget. -/
private theorem cwsh2_witness :
    RoundsWithinWitness cwr2.sharesDestroyed (cwvB.idealSharesClawback cwclamp.toRat)
      depositε := by
  unfold RoundsWithinWitness Vault.idealSharesClawback depositε
  rw [show RatValued.toRat cwr2.sharesDestroyed = cwsh2.toRat from rfl, cwsh2_toRat, cwclamp_toRat,
      cw_exact_sharesTotal cwvB rfl, cw_withdrawNav cwvB rfl rfl rfl]
  rw [show ((7000000000000000 : ℕ) : ℚ) * (1 / 10 ^ 4) / 3 = 700000000000 / 3 from by norm_num]
  rw [show (233333333333 : ℚ) - 700000000000 / 3 = -(1 / 3) from by norm_num]
  rw [abs_neg, abs_of_pos (by norm_num : (0 : ℚ) < 1 / 3),
      abs_of_pos (by norm_num : (0 : ℚ) < (700000000000 : ℚ) / 3)]
  norm_num

/-- The `cwv` recovered assets fall short of the destroyed shares' worth by
`4/(7*10^16)`, beyond the relative budget. -/
private theorem cwar1_witness :
    RoundsWithinWitness cwr1.assetsRecovered
      (cwv.idealAssetsClawback cwr1.sharesDestroyed.toRat) depositε := by
  unfold RoundsWithinWitness Vault.idealAssetsClawback depositε
  rw [show RatValued.toRat cwr1.assetsRecovered = cwar1.toRat from rfl,
      show cwr1.sharesDestroyed = cwsh1 from rfl, cwar1_toRat, cwsh1_toRat,
      cw_exact_sharesTotal cwv rfl, cw_withdrawNav cwv rfl rfl rfl]
  rw [show (3 : ℚ) * 2333333333333333 / ((7000000000000000 : ℕ) : ℚ)
      = 6999999999999999 / 7000000000000000 from by norm_num]
  rw [show (9999999999999998 : ℚ) / 10 ^ 16 - 6999999999999999 / 7000000000000000
      = -(4 / 70000000000000000) from by norm_num]
  rw [abs_neg, abs_of_pos (by norm_num : (0 : ℚ) < 4 / 70000000000000000),
      abs_of_pos (by norm_num : (0 : ℚ) < (6999999999999999 : ℚ) / 7000000000000000)]
  norm_num

/-- The `cwvB` stored total is not the exact difference: the exact new total
needs 21 significant digits. -/
private theorem cwvB_update_witness :
    cwr2.vault'.assetsTotal.toRat ≠ cwvB.toExact.assetsTotal - cwr2.assetsRecovered.toRat := by
  have hAT : cwvB.toExact.assetsTotal = 3 := by
    show (⟨false, 3000000000000000000, -18⟩ : Number).toRat = _
    exact cw_3num_toRat
  rw [show cwr2.vault' = cwvB' from rfl, show cwr2.assetsRecovered = cwar2 from rfl,
      cwvB'_total_toRat, cwar2_toRat, hAT]
  norm_num

/-! ## The four `*_attained` witnesses -/

/-- Witness for `Vault.clawback_sharesDestroyed_attained`: the `cwv` run's
half-share rounding error `1/3` exceeds the relative budget alone. -/
theorem Vault.clawback_sharesDestroyed_witness :
    ∃ (v : Vault) (assets sharesDestroyed assetsRecovered : STAmount)
      (assetsRecoveredNumber : Number) (r : ClawbackResult),
      v.Lawful ∧ v.WithdrawNavExact false ∧
      assetsToSharesWithdraw v assets false false = .ok sharesDestroyed ∧
      v.sharesToAssetsWithdraw sharesDestroyed false = .ok assetsRecovered ∧
      assetsRecovered.toNumber .to_nearest = .ok assetsRecoveredNumber ∧
      assetsRecoveredNumber.operator_gt v.assetsAvailable = false ∧
      v.clawback assets = .ok r ∧ r.error = none ∧
      RoundsWithinWitness r.sharesDestroyed
        (v.idealSharesClawback assets.toRat) depositε :=
  ⟨cwv, cwa1, cwsh1, cwar1, ⟨false, 9999999999999998000, -19⟩, cwr1,
    cwv_lawful, cw_navExact cwv rfl rfl rfl,
    cw_assetsToShares1 cwv rfl rfl rfl rfl,
    cw_sharesToAssets1 cwv rfl rfl rfl rfl rfl,
    cwar1_toNumber, cw_gt1, cwv_run, rfl, cwsh1_witness⟩

/-- Witness for `Vault.clawback_sharesDestroyed_clamped_attained`: the `cwvB`
run reprices from `assetsAvailable` and its truncation error `1/3` exceeds the
relative budget alone. -/
theorem Vault.clawback_sharesDestroyed_clamped_witness :
    ∃ (v : Vault) (assets sharesDestroyed assetsRecovered assetsRecovered' : STAmount)
      (assetsRecoveredNumber : Number) (r : ClawbackResult),
      v.Lawful ∧ v.WithdrawNavExact false ∧
      assetsToSharesWithdraw v assets false false = .ok sharesDestroyed ∧
      v.sharesToAssetsWithdraw sharesDestroyed false = .ok assetsRecovered ∧
      assetsRecovered.toNumber .to_nearest = .ok assetsRecoveredNumber ∧
      assetsRecoveredNumber.operator_gt v.assetsAvailable = true ∧
      STAmount.ofNumber v.numericType v.assetsAvailable .to_nearest = .ok assetsRecovered' ∧
      v.clawback assets = .ok r ∧ r.error = none ∧
      RoundsWithinWitness r.sharesDestroyed
        (v.idealSharesClawback assetsRecovered'.toRat) depositε :=
  ⟨cwvB, cwa1, cwsh1, cwar1, cwclamp, ⟨false, 9999999999999998000, -19⟩, cwr2,
    cwvB_lawful, cw_navExact cwvB rfl rfl rfl,
    cw_assetsToShares1 cwvB rfl rfl rfl rfl,
    cw_sharesToAssets1 cwvB rfl rfl rfl rfl rfl,
    cwar1_toNumber, cw_gt2, cw_clamp_ofNumber, cwvB_run, rfl, cwsh2_witness⟩

/-- Witness for `Vault.clawback_assetsRecovered_attained`: the `cwv` run's
recovery misses the destroyed shares' exact worth by more than the relative
budget. -/
theorem Vault.clawback_assetsRecovered_witness :
    ∃ (v : Vault) (assets : STAmount) (r : ClawbackResult),
      v.Lawful ∧ v.WithdrawNavExact false ∧ v.clawback assets = .ok r ∧ r.error = none ∧
      RoundsWithinWitness r.assetsRecovered
        (v.idealAssetsClawback r.sharesDestroyed.toRat) depositε :=
  ⟨cwv, cwa1, cwr1, cwv_lawful, cw_navExact cwv rfl rfl rfl, cwv_run, rfl, cwar1_witness⟩

/-- Witness for `Vault.clawback_vault_updates_attained`: the `cwvB` run's
stored total is not the exact difference. -/
theorem Vault.clawback_vault_updates_witness :
    ∃ (v : Vault) (assets : STAmount) (r : ClawbackResult),
      v.Lawful ∧ v.clawback assets = .ok r ∧ r.error = none ∧
      r.vault'.assetsTotal.toRat ≠ v.toExact.assetsTotal - r.assetsRecovered.toRat :=
  ⟨cwvB, cwa1, cwr2, cwvB_lawful, cwvB_run, rfl, cwvB_update_witness⟩

end

end XRPL.Model.SingleAssetVault
