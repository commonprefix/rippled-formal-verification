import XRPL.Properties.Vault.Defs
import XRPL.Model.Vault.VaultDeposit
import XRPL.Properties.Approx
import XRPL.Properties.Protocol.STAmount.Common.DiscreteDefs
import XRPL.Properties.Vault.Common.DepositDefs
import XRPL.Properties.Vault.Common.DepositAccuracy
import XRPL.Properties.Vault.Common.WitnessSupport
import XRPL.Properties.Vault.Common.DepositWiring
import XRPL.Properties.Vault.Common.DepositChargeFrac

/-! # Witnesses for the `Vault.deposit` `*_attained` theorems

The concrete vault records and their hand-traced pipeline runs backing the
deposit sharpness witnesses. Each `*_witness` lemma packages one witness tuple,
and the matching `*_attained` headline in `VaultDeposit.lean` delegates to it.
The decimal pipeline is a well-founded recursion the kernel cannot reduce by
`decide`, so every run is stepped by hand through its equation lemmas. -/

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol

/-! ### Witness data for the fractional sharpness theorems

One lawful IOU vault backs all three fractional witnesses:
`assetsTotal = assetsAvailable = 3`, `sharesTotal = 7000000000000000`, nothing
unrealized.

* Truncation: depositing `0.4444444444444445` puts the new total at
  `3.4444444444444445`, whose 16-digit STAmount exponent is `-15`, so the
  amount is floored on the `10^(-15)` grid to `0.444444444444444`, strictly
  below the deposit.
* Shares: depositing `1` prices `7000000000000000 / 3 = 2333333333333333.33…`
  shares, truncated to `2333333333333333`. The truncation error `1/3` exceeds
  the relative budget `ideal · depositε = 7/300`.
* Charge: the same run charges for the issued shares' worth
  `3 · 2333333333333333 / 7000000000000000 = 0.9999999999999998571428…`,
  converted upward at 16 digits to `0.9999999999999999`. The overshoot
  `3/(7·10^16)` exceeds `ideal · depositε < 10^(-17)`.

Every pipeline stage is stepped by hand through the well-founded decimal
recursion, in the style of the `wvDVU` trace below. -/

/-- The shared fractional witness vault: 3 assets, 7·10¹⁵ shares. -/
def wvF : Vault :=
  { assetsTotal := ⟨false, 3000000000000000000, -18⟩
  , assetsAvailable := ⟨false, 3000000000000000000, -18⟩
  , assetsMaximum := none, numericType := .fractional, scale := 0
  , sharesTotal := ⟨false, 7000000000000000000, -3⟩
  , interestUnrealized := Number.zero, lossUnrealized := Number.zero }

/-- The witness deposit amount, `1` of the IOU. -/
def waF : STAmount := STAmount.unchecked .fractional 1000000000000000 (-15) false

/-- The issued shares, `⌊7·10¹⁵/3⌋ = 2333333333333333`. -/
def wsF : STAmount := STAmount.unchecked .int64 2333333333333333 0 false

/-- The taken amount: `3 · 2333333333333333 / 7·10¹⁵` rounded upward at 16
digits, `0.9999999999999999`. -/
def wcF : STAmount := STAmount.unchecked .fractional 9999999999999999 (-16) false

section
set_option maxRecDepth 10000

local syntax "sd128_step" : tactic
local macro_rules | `(tactic| sd128_step) => `(tactic|
  (conv_lhs => rw [scaleDown128]; rw [dif_pos (by decide)]; rfl))

local syntax "dsd128_step" : tactic
local macro_rules | `(tactic| dsd128_step) => `(tactic|
  (conv_lhs => rw [doNormalize_scaleDown128]; rw [dif_pos (by decide), if_neg (by decide)]; rfl))

private theorem waF_canonical : waF.IOUCanonical :=
  ⟨rfl, by decide, by decide, by decide, by decide⟩

private theorem waF_toNumber : waF.toNumber .to_nearest = .ok ⟨false, 1000000000000000000, -18⟩ := by
  rw [STAmount.toNumber_iou_canonical waF .to_nearest waF_canonical]
  rfl

/-- `3 + 1` at 19 digits, exact. -/
private theorem wvF_add_amount :
    Number.operator_add ⟨false, 3000000000000000000, -18⟩ ⟨false, 1000000000000000000, -18⟩
      .to_nearest = .ok ⟨false, 4000000000000000000, -18⟩ := by
  unfold Number.operator_add
  simp only [show (⟨false, 1000000000000000000, -18⟩ : Number).operator_eq Number.zero = false from by decide,
    show (⟨false, 3000000000000000000, -18⟩ : Number).operator_eq Number.zero = false from by decide,
    show (⟨false, 3000000000000000000, -18⟩ : Number).operator_eq
      (⟨false, 1000000000000000000, -18⟩ : Number).operator_neg = false from by decide,
    Bool.false_eq_true, if_false]
  rw [if_neg (by decide : ¬ ((-18 : Int) < -18)), if_neg (by decide : ¬ ((-18 : Int) > -18)),
    show ((false : Bool) == (false : Bool)) = true from rfl]
  simp only [if_true]
  rw [show toUInt128 (3000000000000000000 : UInt64) + toUInt128 (1000000000000000000 : UInt64)
      = (4000000000000000000 : UInt128) from by decide]
  rw [show (decide ((4000000000000000000 : UInt128) > toUInt128 largeRange.max) ||
           decide ((4000000000000000000 : UInt128) > toUInt128 maxRepUp)) = false from by decide]
  simp only [Bool.false_eq_true, if_false]
  rw [show toUInt64 (4000000000000000000 : UInt128) = (4000000000000000000 : UInt64) from by decide]
  rw [show Guard.new.doRoundUp false (4000000000000000000 : UInt64) (-18)
      largeRange.min largeRange.max .to_nearest "Number::addition overflow"
      = .ok { negative_ := false, mantissa_ := 4000000000000000000, exponent_ := -18 } from by
    unfold Guard.doRoundUp Guard.bringIntoRange Guard.round Guard.doDropDigit; rfl]
  simp only [RoundResult.toNumber]
  unfold Number.normalize
  exact doNormalize_id .to_nearest false 4000000000000000000 (-18) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)

/-- `STAmount.ofNumber` of the new total `4`: 16-digit conversion, exact. -/
private theorem wvF_postScale_ofNumber :
    STAmount.ofNumber .fractional ⟨false, 4000000000000000000, -18⟩ .to_nearest
      = .ok (STAmount.unchecked .fractional 4000000000000000 (-15) false) := by
  unfold STAmount.ofNumber
  simp only [show (decide ((⟨false, 4000000000000000000, -18⟩ : Number).signum < 0)) = false from by decide,
    Bool.false_eq_true, if_false,
    show NumericType.fractional.isIntegral = false from rfl]
  rw [show kMinValue = cMinValue from rfl, show kMaxValue = cMaxValue from rfl]
  rw [normalizeToRange_16_exact _ .to_nearest (by decide) (by decide) (by decide) (by decide) (by decide)]
  simp only [Bool.false_eq_true, if_false]
  rw [show (((4000000000000000000 : UInt64) / 10 / 10 / 10).toInt64).toUInt64
      = (4000000000000000 : UInt64) from by decide,
    show (⟨false, 4000000000000000000, -18⟩ : Number).exponent_ + 3 = -15 from by decide]
  show STAmount.checked .fractional 4000000000000000 (-15) false .to_nearest = _
  unfold STAmount.checked STAmount.unchecked
  exact STAmount.canonicalize_canonical_id _ .to_nearest ⟨rfl, by decide, by decide, by decide, by decide⟩

/-- The vault exponent after the deposit lands at `-15`. -/
private theorem wvF_postScale :
    exponent ⟨false, 4000000000000000000, -18⟩ .fractional = .ok (-15 : Int) := by
  unfold exponent
  rw [wvF_postScale_ofNumber, ok_bind]
  rfl

/-- `roundToExponent` of the amount `1` at scale `-15` is the identity (fast path). -/
private theorem waF_roundToExponent :
    STAmount.roundToExponent waF (-15) .downward = .ok waF := by
  unfold STAmount.roundToExponent
  rw [if_neg (show ¬ (waF.integral = true) from by decide),
      if_neg (show ¬ (waF.isZero = true) from by decide),
      if_pos (show waF.exponent ≥ (-15 : Int) from by decide)]

/-- The whole `roundToVaultExponent` is the identity on the amount `1`. -/
private theorem waF_roundToVault :
    roundToVaultExponent waF wvF.assetsTotal = .ok waF := by
  unfold roundToVaultExponent
  rw [if_neg (show ¬ (waF.integral = true) from by decide)]
  rw [show wvF.assetsTotal = (⟨false, 3000000000000000000, -18⟩ : Number) from rfl]
  simp only [waF_toNumber, ok_bind, wvF_add_amount,
    show waF.numericType = NumericType.fractional from rfl, wvF_postScale, waF_roundToExponent]
  rfl

/-- `sharesTotal * amount = 7e15 * 1` at 19 digits, exact. -/
private theorem wvF_shares_mul :
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
    sd128_step; sd128_step; sd128_step; sd128_step; sd128_step; sd128_step
    sd128_step; sd128_step; sd128_step; sd128_step; sd128_step; sd128_step
    sd128_step; sd128_step; sd128_step; sd128_step; sd128_step; sd128_step
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
private theorem wvF_shares_div :
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
    dsd128_step; dsd128_step; dsd128_step; dsd128_step
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

/-- Truncating `2333333333333333.333` to the integer `2333333333333333`. -/
private theorem wvF_shares_truncate :
    Number.truncate ⟨false, 2333333333333333333, -3⟩ = .ok ⟨false, 2333333333333333000, -3⟩ := by
  unfold Number.truncate
  rw [if_neg (show ¬ ((⟨false, 2333333333333333333, -3⟩ : Number).exponent_ ≥ 0
      ∨ (⟨false, 2333333333333333333, -3⟩ : Number).mantissa_ = 0) from by decide)]
  rw [show Number.truncateAux (⟨false, 2333333333333333333, -3⟩ : Number).mantissa_
        (⟨false, 2333333333333333333, -3⟩ : Number).exponent_
      = ((2333333333333333 : UInt64), (0 : Int)) from by
    show Number.truncateAux 2333333333333333333 (-3) = _
    rw [truncateAux_step _ _ (by decide) (by decide)]
    show Number.truncateAux 233333333333333333 (-2) = _
    rw [truncateAux_step _ _ (by decide) (by decide)]
    show Number.truncateAux 23333333333333333 (-1) = _
    rw [truncateAux_step _ _ (by decide) (by decide)]
    show Number.truncateAux 2333333333333333 0 = _
    exact truncateAux_stop _]
  simp only []
  show Number.normalized false 2333333333333333 0 largeRange.min largeRange.max .to_nearest = _
  unfold Number.normalized Number.normalize Number.unchecked
  show doNormalize false 2333333333333333 0 largeRange.min largeRange.max .to_nearest = _
  rw [doNormalize_large_16digit false 2333333333333333 0 .to_nearest
    (by decide) (by decide) (by decide) (by decide)]
  rfl

/-- `to_rep` of the truncated shares `Number`: three exact shifts. -/
private theorem wvF_shares_to_rep :
    (⟨false, 2333333333333333000, -3⟩ : Number).to_rep .to_nearest
      = .ok (2333333333333333 : Int64) := by
  unfold Number.to_rep
  rw [show (⟨false, 2333333333333333000, -3⟩ : Number).mantissa = (2333333333333333000 : Int64) from by decide,
      show (⟨false, 2333333333333333000, -3⟩ : Number).exponent = (-3 : Int) from by decide]
  simp only [show ((2333333333333333000 : Int64) == 0) = false from by decide,
    Bool.false_eq_true, if_false]
  rw [if_pos (show (-3 : Int) < 0 from by decide)]
  rw [show Number.to_rep.shift 2333333333333333000 (-3) Guard.new
      = ((2333333333333333 : Int64), Guard.new) from by
    rw [to_rep_shift_step _ _ _ (by decide)]
    show Number.to_rep.shift 233333333333333300 (-2) Guard.new = _
    rw [to_rep_shift_step _ _ _ (by decide)]
    show Number.to_rep.shift 23333333333333330 (-1) Guard.new = _
    rw [to_rep_shift_step _ _ _ (by decide)]
    show Number.to_rep.shift 2333333333333333 0 Guard.new = _
    exact to_rep_shift_stop _ _]
  simp only []
  rw [if_neg (show ¬ ((-3 : Int) ≥ 0) from by decide)]
  rfl

/-- `to_rep` at offset `0` is the identity on the mantissa. -/
private theorem wvF_shares_to_rep0 :
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

/-- Packing the integer shares `Number` into the int64 `STAmount`. -/
private theorem wvF_shares_ofNumber :
    STAmount.ofNumber .int64 ⟨false, 2333333333333333000, -3⟩ .to_nearest = .ok wsF := by
  unfold STAmount.ofNumber
  simp only [show (decide ((⟨false, 2333333333333333000, -3⟩ : Number).signum < 0)) = false from by decide,
    Bool.false_eq_true, if_false,
    show NumericType.int64.isIntegral = true from rfl, if_true]
  rw [wvF_shares_to_rep]
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
    rw [wvF_shares_to_rep0]]
  simp only []
  rw [if_neg (by decide)]
  rfl

/-- The shares computation issues exactly `2333333333333333` share drops. -/
private theorem wvF_assetsToShares : assetsToSharesDeposit wvF waF = .ok wsF := by
  unfold assetsToSharesDeposit
  rw [if_neg (show ¬ (wvF.assetsTotal.mantissa_ = 0) from by decide)]
  rw [show wvF.assetsTotal = (⟨false, 3000000000000000000, -18⟩ : Number) from rfl,
      show wvF.interestUnrealized = Number.zero from rfl,
      show wvF.sharesTotal = (⟨false, 7000000000000000000, -3⟩ : Number) from rfl]
  simp only [waF_toNumber, ok_bind, operator_sub_zero_right, wvF_shares_mul, wvF_shares_div,
    wvF_shares_truncate, wvF_shares_ofNumber]
  rfl

/-- The issued shares convert back to the same `Number` (16-digit lift). -/
private theorem wsF_toNumber : wsF.toNumber .to_nearest = .ok ⟨false, 2333333333333333000, -3⟩ := by
  unfold STAmount.toNumber
  rw [if_pos (show wsF.integral = true from rfl),
    show wsF.intAmount = .ok { value := 2333333333333333 } from by
      unfold STAmount.intAmount STAmount.signedDrops
      rw [if_pos (show wsF.integral = true from rfl)]
      rfl]
  show IntAmount.toNumber { value := 2333333333333333 } .to_nearest = _
  unfold IntAmount.toNumber Number.from_rep Number.normalized Number.normalize
  show doNormalize false 2333333333333333 0 largeRange.min largeRange.max .to_nearest = _
  rw [doNormalize_large_16digit false 2333333333333333 0 .to_nearest
    (by decide) (by decide) (by decide) (by decide)]
  rfl

/-- `nav * shares = 3 * 2333333333333333` at 19 digits, exact. -/
private theorem wvF_charge_mul :
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
    sd128_step; sd128_step; sd128_step; sd128_step; sd128_step; sd128_step
    sd128_step; sd128_step; sd128_step; sd128_step; sd128_step; sd128_step
    sd128_step; sd128_step; sd128_step; sd128_step; sd128_step; sd128_step
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

/-- `6999999999999999 / 7e15` at 19 digits to nearest: the quotient rides the
`maxRepUp` cusp, so the stored mantissa keeps a trailing zero:
`0.999999999999999857`. -/
private theorem wvF_charge_div :
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
    dsd128_step; dsd128_step; dsd128_step
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

/-- The charge `Number` snaps upward onto the 16-digit grid: `0.9999999999999999`. -/
private theorem wcF_ofNumber :
    STAmount.ofNumber .fractional ⟨false, 9999999999999998570, -19⟩ .upward = .ok wcF := by
  unfold STAmount.ofNumber
  simp only [show (decide ((⟨false, 9999999999999998570, -19⟩ : Number).signum < 0)) = false from by decide,
    Bool.false_eq_true, if_false,
    show NumericType.fractional.isIntegral = false from rfl]
  rw [show kMinValue = cMinValue from rfl, show kMaxValue = cMaxValue from rfl]
  rw [show (⟨false, 9999999999999998570, -19⟩ : Number).normalizeToRange cMinValue cMaxValue .upward
      = .ok ((9999999999999999 : Int64), (-16 : Int)) from by
    unfold Number.normalizeToRange
    simp only []
    rw [show doNormalize false 9999999999999998570 (-19) cMinValue cMaxValue .upward
        = .ok { negative_ := false, mantissa_ := 9999999999999999, exponent_ := -16 } from by
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
          false (9999999999999998 : UInt64) (-16) cMinValue cMaxValue .upward
          "Number::normalize 2"
          = .ok { negative_ := false, mantissa_ := 9999999999999999, exponent_ := -16 } from by
        unfold Guard.doRoundUp Guard.bringIntoRange Guard.round Guard.doDropDigit; rfl]
      simp only [RoundResult.toNumber]]
    rfl]
  simp only []
  show STAmount.checked .fractional 9999999999999999 (-16) false .upward = _
  unfold STAmount.checked STAmount.unchecked
  exact STAmount.canonicalize_canonical_id _ .upward ⟨rfl, by decide, by decide, by decide, by decide⟩

/-- The charge computation takes `0.9999999999999999`. -/
private theorem wvF_sharesToAssets : sharesToAssetsDeposit wvF wsF = .ok wcF := by
  unfold sharesToAssetsDeposit
  rw [if_neg (show ¬ (wvF.assetsTotal.mantissa_ = 0) from by decide)]
  rw [show wvF.assetsTotal = (⟨false, 3000000000000000000, -18⟩ : Number) from rfl,
      show wvF.interestUnrealized = Number.zero from rfl,
      show wvF.sharesTotal = (⟨false, 7000000000000000000, -3⟩ : Number) from rfl,
      show wvF.numericType = NumericType.fractional from rfl]
  simp only [wsF_toNumber, ok_bind, operator_sub_zero_right, wvF_charge_mul, wvF_charge_div,
    wcF_ofNumber]
  rfl

/-- The exchange step: shares issued, charge computed, guard passes. -/
private theorem wvF_computeDeposit : computeDeposit wvF waF = .ok (.success wcF wsF) := by
  unfold computeDeposit
  simp only [wvF_assetsToShares, ok_bind, pure_bind,
    show wsF.isZero = false from rfl, Bool.false_eq_true, if_false,
    wvF_sharesToAssets,
    show wcF.operator_gt waF = .ok false from rfl]
  rfl

/-- The charge amount as a `Number` (16-digit lift). -/
private theorem wcF_toNumber : wcF.toNumber .to_nearest = .ok ⟨false, 9999999999999999000, -19⟩ := by
  rw [STAmount.toNumber_iou_canonical wcF .to_nearest ⟨rfl, by decide, by decide, by decide, by decide⟩]
  rfl

/-- `3 + 0.9999999999999999` at 19 digits: one alignment shift, exact. -/
private theorem wvF_total_add :
    Number.operator_add ⟨false, 3000000000000000000, -18⟩ ⟨false, 9999999999999999000, -19⟩
      .to_nearest = .ok ⟨false, 3999999999999999900, -18⟩ := by
  unfold Number.operator_add
  simp only [show (⟨false, 9999999999999999000, -19⟩ : Number).operator_eq Number.zero = false from by decide,
    show (⟨false, 3000000000000000000, -18⟩ : Number).operator_eq Number.zero = false from by decide,
    show (⟨false, 3000000000000000000, -18⟩ : Number).operator_eq
      (⟨false, 9999999999999999000, -19⟩ : Number).operator_neg = false from by decide,
    Bool.false_eq_true, if_false]
  rw [if_neg (by decide : ¬ ((-18 : Int) < -19)), if_pos (by decide : (-18 : Int) > -19)]
  rw [show Number.operator_add.alignDown 9999999999999999000 (-19) Guard.new (-18)
      = ((999999999999999900 : UInt64), (-18 : Int), Guard.new) from by
    rw [Number.operator_add.alignDown, if_pos (by decide : (-19 : Int) < (-18 : Int))]
    show Number.operator_add.alignDown 999999999999999900 (-18) (Guard.new.push 0) (-18) = _
    rw [Number.operator_add.alignDown, if_neg (by decide : ¬ ((-18 : Int) < (-18 : Int)))]
    rfl]
  simp only []
  rw [show ((false : Bool) == (false : Bool)) = true from rfl]
  simp only [if_true]
  rw [show toUInt128 (3000000000000000000 : UInt64) + toUInt128 (999999999999999900 : UInt64)
      = (3999999999999999900 : UInt128) from by decide]
  rw [show (decide ((3999999999999999900 : UInt128) > toUInt128 largeRange.max) ||
           decide ((3999999999999999900 : UInt128) > toUInt128 maxRepUp)) = false from by decide]
  simp only [Bool.false_eq_true, if_false]
  rw [show toUInt64 (3999999999999999900 : UInt128) = (3999999999999999900 : UInt64) from by decide]
  rw [show Guard.new.doRoundUp false (3999999999999999900 : UInt64) (-18)
      largeRange.min largeRange.max .to_nearest "Number::addition overflow"
      = .ok { negative_ := false, mantissa_ := 3999999999999999900, exponent_ := -18 } from by
    unfold Guard.doRoundUp Guard.bringIntoRange Guard.round Guard.doDropDigit; rfl]
  simp only [RoundResult.toNumber]
  unfold Number.normalize
  exact doNormalize_id .to_nearest false 3999999999999999900 (-18) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)

/-- `7e15 + 2333333333333333` at 19 digits: the sum crosses `maxRepUp`, one
digit (a zero) is dropped, exact. -/
private theorem wvF_sharesTotal_add :
    Number.operator_add ⟨false, 7000000000000000000, -3⟩ ⟨false, 2333333333333333000, -3⟩
      .to_nearest = .ok ⟨false, 9333333333333333000, -3⟩ := by
  unfold Number.operator_add
  simp only [show (⟨false, 2333333333333333000, -3⟩ : Number).operator_eq Number.zero = false from by decide,
    show (⟨false, 7000000000000000000, -3⟩ : Number).operator_eq Number.zero = false from by decide,
    show (⟨false, 7000000000000000000, -3⟩ : Number).operator_eq
      (⟨false, 2333333333333333000, -3⟩ : Number).operator_neg = false from by decide,
    Bool.false_eq_true, if_false]
  rw [if_neg (by decide : ¬ ((-3 : Int) < -3)), if_neg (by decide : ¬ ((-3 : Int) > -3)),
    show ((false : Bool) == (false : Bool)) = true from rfl]
  simp only [if_true]
  rw [show toUInt128 (7000000000000000000 : UInt64) + toUInt128 (2333333333333333000 : UInt64)
      = (9333333333333333000 : UInt128) from by decide]
  rw [show (decide ((9333333333333333000 : UInt128) > toUInt128 largeRange.max) ||
           decide ((9333333333333333000 : UInt128) > toUInt128 maxRepUp)) = true from by decide]
  simp only [if_true]
  rw [show Guard.new.doDropDigit128 (9333333333333333000 : UInt128) (-3)
      = (Guard.new, (933333333333333300 : UInt128), (-2 : Int)) from by
    unfold Guard.doDropDigit128 Guard.new Guard.push; rfl]
  simp only
  rw [show toUInt64 (933333333333333300 : UInt128) = (933333333333333300 : UInt64) from by decide]
  rw [show Guard.new.doRoundUp false (933333333333333300 : UInt64) (-2)
      largeRange.min largeRange.max .to_nearest "Number::addition overflow"
      = .ok { negative_ := false, mantissa_ := 9333333333333333000, exponent_ := -3 } from by
    unfold Guard.doRoundUp Guard.bringIntoRange Guard.round Guard.doDropDigit; rfl]
  simp only [RoundResult.toNumber]
  unfold Number.normalize
  exact doNormalize_id .to_nearest false 9333333333333333000 (-3) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)

/-- The post-deposit vault. -/
def wvF' : Vault :=
  { assetsTotal := ⟨false, 3999999999999999900, -18⟩
  , assetsAvailable := ⟨false, 3999999999999999900, -18⟩
  , assetsMaximum := none, numericType := .fractional, scale := 0
  , sharesTotal := ⟨false, 9333333333333333000, -3⟩
  , interestUnrealized := Number.zero, lossUnrealized := Number.zero }

/-- The witness deposit result. -/
def wrF : DepositResult := ⟨none, wvF', wcF, wsF⟩

/-- The witness deposit runs to `wrF`. -/
private theorem wvF_run : wvF.deposit waF false = .ok wrF := by
  unfold Vault.deposit
  rw [waF_roundToVault]
  simp only [ok_bind]
  rw [if_neg (show ¬ (waF.isZero = true) from by decide),
    if_neg (show ¬ ((false && wvF.sharesTotal.mantissa_ == 0) = true) from by decide),
    if_neg (show ¬ ((wvF.isInsolvent && !false) = true) from by decide)]
  simp only [Bool.false_eq_true, if_false, wvF_computeDeposit, ok_bind, pure_bind]
  simp only [show wvF.assetsTotal = (⟨false, 3000000000000000000, -18⟩ : Number) from rfl,
             show wvF.assetsAvailable = (⟨false, 3000000000000000000, -18⟩ : Number) from rfl,
             show wvF.sharesTotal = (⟨false, 7000000000000000000, -3⟩ : Number) from rfl,
             wcF_toNumber, wsF_toNumber, wvF_total_add, wvF_sharesTotal_add, ok_bind]
  rw [show wvF.assetsMaximum = (none : Option Number) from rfl]
  simp only [Option.any_none, Bool.false_eq_true, if_false]
  show pure _ = Except.ok wrF
  rfl

/-- Value of the stored share total. -/
private theorem wvF_shares_toRat :
    (⟨false, 7000000000000000000, -3⟩ : Number).toRat = ((7000000000000000 : ℕ) : ℚ) := by
  rw [Number.toRat_of_nonneg _ rfl,
      show ((7000000000000000000 : UInt64).toNat) = 7000000000000000000 from by decide]
  norm_num

/-- Exact asset total of the witness vault. -/
private theorem wvF_exact_assetsTotal : wvF.toExact.assetsTotal = 3 := by
  show (⟨false, 3000000000000000000, -18⟩ : Number).toRat = _
  rw [Number.toRat_of_nonneg _ rfl,
      show ((3000000000000000000 : UInt64).toNat) = 3000000000000000000 from by decide]
  norm_num

/-- Exact share total of the witness vault. -/
private theorem wvF_exact_sharesTotal : wvF.toExact.sharesTotal = 7000000000000000 := by
  show wvF.sharesTotal.toRat.num.toNat = _
  rw [show wvF.sharesTotal = (⟨false, 7000000000000000000, -3⟩ : Number) from rfl, wvF_shares_toRat]
  norm_num
  rfl

/-- Exact unrealized interest of the witness vault (zero). -/
private theorem wvF_exact_interest : wvF.toExact.interestUnrealized = 0 := by
  simp only [Vault.toExact]
  exact Number.toRat_eq_zero_of_mantissa_zero _ rfl

/-- The witness vault is lawful. -/
private theorem wvF_lawful : wvF.Lawful := by
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · show (⟨false, 3000000000000000000, -18⟩ : Number).isNormalized; norm_isNormalized
  · show (⟨false, 3000000000000000000, -18⟩ : Number).isNormalized; norm_isNormalized
  · intro m hm; rw [show wvF.assetsMaximum = none from rfl] at hm; exact absurd hm (by simp)
  · show (⟨false, 7000000000000000000, -3⟩ : Number).isNormalized; norm_isNormalized
  · exact Or.inl rfl
  · exact Or.inl rfl
  · show (0 : ℚ) ≤ (⟨false, 7000000000000000000, -3⟩ : Number).toRat
    rw [wvF_shares_toRat]; positivity
  · show (⟨false, 7000000000000000000, -3⟩ : Number).toRat.den = 1
    rw [wvF_shares_toRat]; exact Rat.den_natCast _
  · intro _; rfl
  · decide
  · have hAT := wvF_exact_assetsTotal
    have hAA : wvF.toExact.assetsAvailable = 3 := by
      show (⟨false, 3000000000000000000, -18⟩ : Number).toRat = _
      rw [Number.toRat_of_nonneg _ rfl,
          show ((3000000000000000000 : UInt64).toNat) = 3000000000000000000 from by decide]
      norm_num
    have hST := wvF_exact_sharesTotal
    have hI := wvF_exact_interest
    have hL : wvF.toExact.lossUnrealized = 0 := by
      simp only [Vault.toExact]
      exact Number.toRat_eq_zero_of_mantissa_zero _ rfl
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hAT]; norm_num
    · rw [hAA]; norm_num
    · rw [hAT, hAA]
    · intro m hm; rw [show wvF.toExact.assetsMaximum = none from rfl] at hm
      exact absurd hm (by simp)
    · intro h; rw [hST] at h; exact absurd h (by norm_num)
    · intro m hm; rw [show wvF.toExact.assetsMaximum = none from rfl] at hm
      exact absurd hm (by simp)
    · rw [hL]
    · rw [hL, hAT, hAA]; norm_num
    · rw [hI]
    · rw [hI, hAT, hAA]; norm_num
    · intro _; rw [hI, hAT]; norm_num
    · rw [hAT, hI, hL]; norm_num
    · intro h; rw [hI] at h; exact absurd h (by norm_num)

/-- The deposit amount `1` survives `roundedDepositAmount` unchanged. -/
private theorem waF_rounded : wvF.roundedDepositAmount waF = .ok (.rounded waF) := by
  rw [roundedDepositAmount_ok wvF waF waF waF_roundToVault]
  rw [if_neg (show ¬ (waF.isZero = true) from by decide)]

/-- Value of the deposit amount. -/
private theorem waF_toRat : waF.toRat = 1 := by
  rw [STAmount.toRat_of_nonneg waF rfl]
  show ((1000000000000000 : UInt64).toNat : ℚ) * 10 ^ (-15 : ℤ) = 1
  rw [show ((1000000000000000 : UInt64).toNat) = 1000000000000000 from by decide]
  norm_num

/-- Value of the issued shares. -/
private theorem wsF_toRat : wsF.toRat = 2333333333333333 := by
  rw [STAmount.toRat_of_nonneg wsF rfl]
  show ((2333333333333333 : UInt64).toNat : ℚ) * 10 ^ (0 : ℤ) = 2333333333333333
  rw [show ((2333333333333333 : UInt64).toNat) = 2333333333333333 from by decide]
  norm_num

/-- Value of the taken amount. -/
private theorem wcF_toRat : wcF.toRat = 9999999999999999 / 10 ^ 16 := by
  rw [STAmount.toRat_of_nonneg wcF rfl]
  show ((9999999999999999 : UInt64).toNat : ℚ) * 10 ^ (-16 : ℤ) = 9999999999999999 / 10 ^ 16
  rw [show ((9999999999999999 : UInt64).toNat) = 9999999999999999 from by decide]
  norm_num

/-- The amount `1` is positive. -/
private theorem waF_pos : 0 < waF.toRat := by rw [waF_toRat]; norm_num

/-- The issued shares miss the ideal by `1/3`, far beyond the relative budget. -/
private theorem wsF_witness :
    RoundsWithinWitness wrF.sharesIssued (wvF.idealSharesDeposit waF.toRat) depositε := by
  unfold RoundsWithinWitness Vault.idealSharesDeposit Vault.depositNav depositε
  rw [if_neg (show ¬ (wvF.toExact.assetsTotal = 0) from by
    rw [wvF_exact_assetsTotal]; norm_num)]
  rw [show RatValued.toRat wrF.sharesIssued = wsF.toRat from rfl, wsF_toRat, waF_toRat,
      wvF_exact_sharesTotal, wvF_exact_interest, wvF_exact_assetsTotal]
  rw [show ((7000000000000000 : ℕ) : ℚ) * 1 / (3 - 0) = 7000000000000000 / 3 from by norm_num]
  rw [show (2333333333333333 : ℚ) - 7000000000000000 / 3 = -(1 / 3) from by norm_num]
  rw [abs_neg, abs_of_pos (by norm_num : (0 : ℚ) < 1 / 3),
      abs_of_pos (by norm_num : (0 : ℚ) < (7000000000000000 : ℚ) / 3)]
  norm_num

/-- The taken amount overshoots the issued shares' exact worth by `3/(7·10¹⁶)`,
beyond the relative budget. -/
private theorem wcF_witness :
    RoundsWithinWitness wrF.amountDeposit' (wvF.idealChargeDeposit wrF.sharesIssued.toRat)
      depositε := by
  unfold RoundsWithinWitness Vault.idealChargeDeposit Vault.depositNav depositε
  rw [if_neg (show ¬ (wvF.toExact.assetsTotal = 0) from by
    rw [wvF_exact_assetsTotal]; norm_num)]
  rw [show RatValued.toRat wrF.amountDeposit' = wcF.toRat from rfl,
      show wrF.sharesIssued = wsF from rfl, wcF_toRat, wsF_toRat,
      wvF_exact_sharesTotal, wvF_exact_interest, wvF_exact_assetsTotal]
  rw [show (3 - 0 : ℚ) * 2333333333333333 / ((7000000000000000 : ℕ) : ℚ)
      = 6999999999999999 / 7000000000000000 from by norm_num]
  rw [show (9999999999999999 : ℚ) / 10 ^ 16 - 6999999999999999 / 7000000000000000
      = 3 / 70000000000000000 from by norm_num]
  rw [abs_of_pos (by norm_num : (0 : ℚ) < 3 / 70000000000000000),
      abs_of_pos (by norm_num : (0 : ℚ) < (6999999999999999 : ℚ) / 7000000000000000)]
  norm_num

/-! Witness 1: truncation. -/

def wtF : STAmount := STAmount.unchecked .fractional 4444444444444445 (-16) false
def wtrF : STAmount := STAmount.unchecked .fractional 4444444444444440 (-16) false
def refF : STAmount := STAmount.unchecked .fractional 1000000000000000 (-15) false
def sumF : STAmount := STAmount.unchecked .fractional 1444444444444444 (-15) false

private theorem wtF_canonical : wtF.IOUCanonical :=
  ⟨rfl, by decide, by decide, by decide, by decide⟩

private theorem wtF_toNumber : wtF.toNumber .to_nearest = .ok ⟨false, 4444444444444445000, -19⟩ := by
  rw [STAmount.toNumber_iou_canonical wtF .to_nearest wtF_canonical]
  rfl

/-- `3 + 0.4444444444444445` at 19 digits: one alignment shift, exact. -/
private theorem wtF_add :
    Number.operator_add ⟨false, 3000000000000000000, -18⟩ ⟨false, 4444444444444445000, -19⟩
      .to_nearest = .ok ⟨false, 3444444444444444500, -18⟩ := by
  unfold Number.operator_add
  simp only [show (⟨false, 4444444444444445000, -19⟩ : Number).operator_eq Number.zero = false from by decide,
    show (⟨false, 3000000000000000000, -18⟩ : Number).operator_eq Number.zero = false from by decide,
    show (⟨false, 3000000000000000000, -18⟩ : Number).operator_eq
      (⟨false, 4444444444444445000, -19⟩ : Number).operator_neg = false from by decide,
    Bool.false_eq_true, if_false]
  rw [if_neg (by decide : ¬ ((-18 : Int) < -19)), if_pos (by decide : (-18 : Int) > -19)]
  rw [show Number.operator_add.alignDown 4444444444444445000 (-19) Guard.new (-18)
      = ((444444444444444500 : UInt64), (-18 : Int), Guard.new) from by
    rw [Number.operator_add.alignDown, if_pos (by decide : (-19 : Int) < (-18 : Int))]
    show Number.operator_add.alignDown 444444444444444500 (-18) (Guard.new.push 0) (-18) = _
    rw [Number.operator_add.alignDown, if_neg (by decide : ¬ ((-18 : Int) < (-18 : Int)))]
    rfl]
  simp only []
  rw [show ((false : Bool) == (false : Bool)) = true from rfl]
  simp only [if_true]
  rw [show toUInt128 (3000000000000000000 : UInt64) + toUInt128 (444444444444444500 : UInt64)
      = (3444444444444444500 : UInt128) from by decide]
  rw [show (decide ((3444444444444444500 : UInt128) > toUInt128 largeRange.max) ||
           decide ((3444444444444444500 : UInt128) > toUInt128 maxRepUp)) = false from by decide]
  simp only [Bool.false_eq_true, if_false]
  rw [show toUInt64 (3444444444444444500 : UInt128) = (3444444444444444500 : UInt64) from by decide]
  rw [show Guard.new.doRoundUp false (3444444444444444500 : UInt64) (-18)
      largeRange.min largeRange.max .to_nearest "Number::addition overflow"
      = .ok { negative_ := false, mantissa_ := 3444444444444444500, exponent_ := -18 } from by
    unfold Guard.doRoundUp Guard.bringIntoRange Guard.round Guard.doDropDigit; rfl]
  simp only [RoundResult.toNumber]
  unfold Number.normalize
  exact doNormalize_id .to_nearest false 3444444444444444500 (-18) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)

/-- The 16-digit view of the new total `3.4444444444444445`: the dropped `500`
tail is an exact tie and the kept mantissa is even, so it truncates. -/
private theorem wtF_postScale_ofNumber :
    STAmount.ofNumber .fractional ⟨false, 3444444444444444500, -18⟩ .to_nearest
      = .ok (STAmount.unchecked .fractional 3444444444444444 (-15) false) := by
  unfold STAmount.ofNumber
  simp only [show (decide ((⟨false, 3444444444444444500, -18⟩ : Number).signum < 0)) = false from by decide,
    Bool.false_eq_true, if_false,
    show NumericType.fractional.isIntegral = false from rfl]
  rw [show kMinValue = cMinValue from rfl, show kMaxValue = cMaxValue from rfl]
  rw [show (⟨false, 3444444444444444500, -18⟩ : Number).normalizeToRange cMinValue cMaxValue .to_nearest
      = .ok ((3444444444444444 : Int64), (-15 : Int)) from by
    unfold Number.normalizeToRange
    simp only []
    rw [show doNormalize false 3444444444444444500 (-18) cMinValue cMaxValue .to_nearest
        = .ok { negative_ := false, mantissa_ := 3444444444444444, exponent_ := -15 } from by
      unfold doNormalize
      rw [show ((3444444444444444500 : UInt64) == 0) = false from rfl]
      simp only [Bool.false_eq_true, if_false]
      rw [doNormalize_scaleUp_id cMinValue 3444444444444444500 (-18) (by decide)]
      rw [show doNormalize_scaleDown cMaxValue (3444444444444444500 : UInt64) (-18) Guard.new
          = .ok ((3444444444444444 : UInt64), (-15 : Int),
                 { digits_ := 0x5000000000000000, xbit_ := false, sbit_ := false }) from by
        rw [doNormalize_scaleDown_step (by decide) (by decide)]
        show doNormalize_scaleDown cMaxValue 344444444444444450 (-17) (Guard.new.push 0) = _
        rw [doNormalize_scaleDown_step (by decide) (by decide)]
        show doNormalize_scaleDown cMaxValue 34444444444444445 (-16) ((Guard.new.push 0).push 0) = _
        rw [doNormalize_scaleDown_step (by decide) (by decide)]
        show doNormalize_scaleDown cMaxValue 3444444444444444 (-15)
            (((Guard.new.push 0).push 0).push 5) = _
        rw [doNormalize_scaleDown_id _ _ _ _ (by decide)]
        rfl]
      simp only []
      rw [show (decide ((-15 : Int) < minExponent)
            || decide ((3444444444444444 : UInt64) < cMinValue)) = false from by decide]
      simp only [Bool.false_eq_true, if_false]
      rw [show doNormalize_capAtMaxRep (3444444444444444 : UInt64) (-15)
            { digits_ := 0x5000000000000000, xbit_ := false, sbit_ := false }
          = .ok ((3444444444444444 : UInt64), (-15 : Int),
                 { digits_ := 0x5000000000000000, xbit_ := false, sbit_ := false }) from by
        unfold doNormalize_capAtMaxRep; rw [if_neg (by decide)]]
      simp only []
      rw [show ({ digits_ := 0x5000000000000000, xbit_ := false, sbit_ := false } : Guard).doRoundUp
          false (3444444444444444 : UInt64) (-15) cMinValue cMaxValue .to_nearest
          "Number::normalize 2"
          = .ok { negative_ := false, mantissa_ := 3444444444444444, exponent_ := -15 } from by
        unfold Guard.doRoundUp Guard.bringIntoRange Guard.round Guard.doDropDigit; rfl]
      simp only [RoundResult.toNumber]]
    rfl]
  simp only []
  show STAmount.checked .fractional 3444444444444444 (-15) false .to_nearest = _
  unfold STAmount.checked STAmount.unchecked
  exact STAmount.canonicalize_canonical_id _ .to_nearest ⟨rfl, by decide, by decide, by decide, by decide⟩

private theorem wtF_postScale :
    exponent ⟨false, 3444444444444444500, -18⟩ .fractional = .ok (-15 : Int) := by
  unfold exponent
  rw [wtF_postScale_ofNumber, ok_bind]
  rfl

/-- `0.4444444444444445 + 1` at 19 digits, downward: one alignment shift, exact. -/
private theorem wtF_sum_number :
    Number.operator_add ⟨false, 4444444444444445000, -19⟩ ⟨false, 1000000000000000000, -18⟩
      .downward = .ok ⟨false, 1444444444444444500, -18⟩ := by
  unfold Number.operator_add
  rw [if_neg (show ¬ ((⟨false, 1000000000000000000, -18⟩ : Number).operator_eq Number.zero = true) from by decide),
      if_neg (show ¬ ((⟨false, 4444444444444445000, -19⟩ : Number).operator_eq Number.zero = true) from by decide),
      if_neg (show ¬ ((⟨false, 4444444444444445000, -19⟩ : Number).operator_eq
        (⟨false, 1000000000000000000, -18⟩ : Number).operator_neg = true) from by decide)]
  simp -iota only [Bool.false_eq_true, if_false]
  rw [show Number.operator_add.alignDown 4444444444444445000 (-19) Guard.new (-18)
      = ((444444444444444500 : UInt64), (-18 : Int), Guard.new) from by
    rw [Number.operator_add.alignDown, if_pos (by decide : (-19 : Int) < (-18 : Int))]
    show Number.operator_add.alignDown 444444444444444500 (-18) (Guard.new.push 0) (-18) = _
    rw [Number.operator_add.alignDown, if_neg (by decide : ¬ ((-18 : Int) < (-18 : Int)))]
    rfl]
  rw [if_pos (by decide : (-19 : Int) < (-18 : Int))]
  simp only []
  rw [show ((false : Bool) == (false : Bool)) = true from rfl]
  simp only [if_true]
  rw [show toUInt128 (444444444444444500 : UInt64) + toUInt128 (1000000000000000000 : UInt64)
      = (1444444444444444500 : UInt128) from by decide]
  rw [show (decide ((1444444444444444500 : UInt128) > toUInt128 largeRange.max) ||
           decide ((1444444444444444500 : UInt128) > toUInt128 maxRepUp)) = false from by decide]
  simp only [Bool.false_eq_true, if_false]
  rw [show toUInt64 (1444444444444444500 : UInt128) = (1444444444444444500 : UInt64) from by decide]
  rw [show Guard.new.doRoundUp false (1444444444444444500 : UInt64) (-18)
      largeRange.min largeRange.max .downward "Number::addition overflow"
      = .ok { negative_ := false, mantissa_ := 1444444444444444500, exponent_ := -18 } from by
    unfold Guard.doRoundUp Guard.bringIntoRange Guard.round Guard.doDropDigit; rfl]
  simp only [RoundResult.toNumber]
  unfold Number.normalize
  exact doNormalize_id .downward false 1444444444444444500 (-18) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)

/-- The 16-digit view of the sum `1.4444444444444445`, downward: the `500` tail
is dropped. -/
private theorem wtF_sum_ofNumber :
    IOUAmount.ofNumber ⟨false, 1444444444444444500, -18⟩ .downward
      = .ok ⟨1444444444444444, -15⟩ := by
  unfold IOUAmount.ofNumber IOUAmount.fromNumber
  rw [show (⟨false, 1444444444444444500, -18⟩ : Number).normalizeToRange cMinValue cMaxValue .downward
      = .ok ((1444444444444444 : Int64), (-15 : Int)) from by
    unfold Number.normalizeToRange
    simp only []
    rw [show doNormalize false 1444444444444444500 (-18) cMinValue cMaxValue .downward
        = .ok { negative_ := false, mantissa_ := 1444444444444444, exponent_ := -15 } from by
      unfold doNormalize
      rw [show ((1444444444444444500 : UInt64) == 0) = false from rfl]
      simp only [Bool.false_eq_true, if_false]
      rw [doNormalize_scaleUp_id cMinValue 1444444444444444500 (-18) (by decide)]
      rw [show doNormalize_scaleDown cMaxValue (1444444444444444500 : UInt64) (-18) Guard.new
          = .ok ((1444444444444444 : UInt64), (-15 : Int),
                 { digits_ := 0x5000000000000000, xbit_ := false, sbit_ := false }) from by
        rw [doNormalize_scaleDown_step (by decide) (by decide)]
        show doNormalize_scaleDown cMaxValue 144444444444444450 (-17) (Guard.new.push 0) = _
        rw [doNormalize_scaleDown_step (by decide) (by decide)]
        show doNormalize_scaleDown cMaxValue 14444444444444445 (-16) ((Guard.new.push 0).push 0) = _
        rw [doNormalize_scaleDown_step (by decide) (by decide)]
        show doNormalize_scaleDown cMaxValue 1444444444444444 (-15)
            (((Guard.new.push 0).push 0).push 5) = _
        rw [doNormalize_scaleDown_id _ _ _ _ (by decide)]
        rfl]
      simp only []
      rw [show (decide ((-15 : Int) < minExponent)
            || decide ((1444444444444444 : UInt64) < cMinValue)) = false from by decide]
      simp only [Bool.false_eq_true, if_false]
      rw [show doNormalize_capAtMaxRep (1444444444444444 : UInt64) (-15)
            { digits_ := 0x5000000000000000, xbit_ := false, sbit_ := false }
          = .ok ((1444444444444444 : UInt64), (-15 : Int),
                 { digits_ := 0x5000000000000000, xbit_ := false, sbit_ := false }) from by
        unfold doNormalize_capAtMaxRep; rw [if_neg (by decide)]]
      simp only []
      rw [show ({ digits_ := 0x5000000000000000, xbit_ := false, sbit_ := false } : Guard).doRoundUp
          false (1444444444444444 : UInt64) (-15) cMinValue cMaxValue .downward
          "Number::normalize 2"
          = .ok { negative_ := false, mantissa_ := 1444444444444444, exponent_ := -15 } from by
        unfold Guard.doRoundUp Guard.bringIntoRange Guard.round Guard.doDropDigit; rfl]
      simp only [RoundResult.toNumber]]
    rfl]
  simp only []
  rw [if_neg (by decide : ¬ ((-15 : Int) > cMaxOffset)),
      if_neg (by decide : ¬ ((-15 : Int) < cMinOffset))]

/-- `wtF + 1` as STAmounts, downward: `1.444444444444444`, the tail digit gone. -/
private theorem wtF_sum :
    STAmount.operator_add wtF refF .downward = .ok sumF := by
  rw [STAmount.operator_add_iou_unfold wtF refF .downward wtF_canonical
    ⟨rfl, by decide, by decide, by decide, by decide⟩]
  rw [show (⟨wtF.mIsNegative, wtF.mValue * 10 * 10 * 10, wtF.mOffset - 3⟩ : Number)
      = ⟨false, 4444444444444445000, -19⟩ from by decide,
    show (⟨refF.mIsNegative, refF.mValue * 10 * 10 * 10, refF.mOffset - 3⟩ : Number)
      = ⟨false, 1000000000000000000, -18⟩ from by decide]
  rw [wtF_sum_number]
  simp only [wtF_sum_ofNumber]
  rw [STAmount.ofIOU_canonical ⟨1444444444444444, -15⟩ .downward
    ⟨by decide, by decide, by decide, by decide⟩]
  rfl

/-- `1.444444444444444 - 1` at 19 digits, downward: exact difference, scaled up. -/
private theorem wtF_sub_number :
    Number.operator_add ⟨false, 1444444444444444000, -18⟩ ⟨true, 1000000000000000000, -18⟩
      .downward = .ok ⟨false, 4444444444444440000, -19⟩ := by
  unfold Number.operator_add
  rw [if_neg (show ¬ ((⟨true, 1000000000000000000, -18⟩ : Number).operator_eq Number.zero = true) from by decide),
      if_neg (show ¬ ((⟨false, 1444444444444444000, -18⟩ : Number).operator_eq Number.zero = true) from by decide),
      if_neg (show ¬ ((⟨false, 1444444444444444000, -18⟩ : Number).operator_eq
        (⟨true, 1000000000000000000, -18⟩ : Number).operator_neg = true) from by decide)]
  simp -iota only [Bool.false_eq_true, if_false]
  rw [if_neg (by decide : ¬ ((-18 : Int) < (-18 : Int))),
      if_neg (by decide : ¬ ((-18 : Int) > (-18 : Int)))]
  simp only []
  rw [show ((false : Bool) == (true : Bool)) = false from rfl]
  simp only [Bool.false_eq_true, if_false]
  rw [if_pos (by decide : (1444444444444444000 : UInt64) > (1000000000000000000 : UInt64))]
  rw [show toUInt128 (1444444444444444000 : UInt64) - toUInt128 (1000000000000000000 : UInt64)
      = (444444444444444000 : UInt128) from by decide]
  simp only []
  rw [show Number.operator_add.recover (toUInt128 largeRange.min * 1000)
        (444444444444444000 : UInt128) (-18) Guard.new 40
      = ((444444444444444000 : UInt128), (-18 : Int), Guard.new) from rfl]
  simp only [show (Guard.new.empty : Bool) = true from rfl, Bool.not_true, if_true]
  show doNormalize128 false (444444444444444000 : UInt128) (-18)
      largeRange.min largeRange.max .downward false = _
  unfold doNormalize128
  rw [show ((444444444444444000 : UInt128) == 0) = false from by decide]
  simp only [Bool.false_eq_true, if_false]
  rw [show doNormalize128.scaleUp largeRange.min (444444444444444000 : UInt128) (-18)
        = ((4444444444444440000 : UInt128), (-19 : Int)) from by
      rw [doNormalize128.scaleUp.eq_def]; rw [if_pos (by decide)]
      show doNormalize128.scaleUp largeRange.min (4444444444444440000 : UInt128) (-19) = _
      rw [doNormalize128.scaleUp.eq_def]; rw [if_neg (by decide)]]
  simp only []
  rw [show doNormalize_scaleDown128 largeRange.max (4444444444444440000 : UInt128) (-19) Guard.new
      = .ok (4444444444444440000, -19, Guard.new) from by
    conv_lhs => rw [doNormalize_scaleDown128]; rw [dif_neg (by decide)]]
  simp only []
  rw [show (decide ((-19 : Int) < minExponent)
        || decide ((4444444444444440000 : UInt128) < toUInt128 largeRange.min)) = false from by decide]
  simp only [Bool.false_eq_true, if_false]
  rw [show doNormalize_capAtMaxRep (toUInt64 (4444444444444440000 : UInt128)) (-19) Guard.new
      = .ok ((4444444444444440000 : UInt64), (-19 : Int), Guard.new) from by
    unfold doNormalize_capAtMaxRep; rw [if_neg (by decide)]; rfl]
  simp only []
  rw [show Guard.new.doRoundUp false (4444444444444440000 : UInt64) (-19)
      largeRange.min largeRange.max .downward "Number::normalize 2"
      = .ok { negative_ := false, mantissa_ := 4444444444444440000, exponent_ := -19 } from by
    unfold Guard.doRoundUp Guard.bringIntoRange Guard.round Guard.doDropDigit; rfl]
  simp only [RoundResult.toNumber]

/-- The 16-digit view of the difference `0.444444444444444`: exact. -/
private theorem wtF_sub_ofNumber :
    IOUAmount.ofNumber ⟨false, 4444444444444440000, -19⟩ .downward
      = .ok ⟨4444444444444440, -16⟩ := by
  unfold IOUAmount.ofNumber IOUAmount.fromNumber
  rw [normalizeToRange_16_exact _ .downward (by decide) (by decide) (by decide)
    (by decide) (by decide)]
  simp only [Bool.false_eq_true, if_false]
  rw [show ((4444444444444440000 : UInt64) / 10 / 10 / 10).toInt64
      = (4444444444444440 : Int64) from by decide,
    show (⟨false, 4444444444444440000, -19⟩ : Number).exponent_ + 3 = -16 from by decide]
  rw [if_neg (by decide : ¬ ((-16 : Int) > cMaxOffset)),
      if_neg (by decide : ¬ ((-16 : Int) < cMinOffset))]

/-- `sumF - 1` as STAmounts, downward: the truncated amount `0.444444444444444`. -/
private theorem wtF_sub :
    STAmount.operator_sub sumF refF .downward = .ok wtrF := by
  unfold STAmount.operator_sub
  rw [show refF.operator_neg = STAmount.unchecked .fractional 1000000000000000 (-15) true from rfl]
  rw [STAmount.operator_add_iou_unfold sumF
    (STAmount.unchecked .fractional 1000000000000000 (-15) true) .downward
    ⟨rfl, by decide, by decide, by decide, by decide⟩
    ⟨rfl, by decide, by decide, by decide, by decide⟩]
  rw [show (⟨sumF.mIsNegative, sumF.mValue * 10 * 10 * 10, sumF.mOffset - 3⟩ : Number)
      = ⟨false, 1444444444444444000, -18⟩ from by decide,
    show (⟨(STAmount.unchecked .fractional 1000000000000000 (-15) true).mIsNegative,
        (STAmount.unchecked .fractional 1000000000000000 (-15) true).mValue * 10 * 10 * 10,
        (STAmount.unchecked .fractional 1000000000000000 (-15) true).mOffset - 3⟩ : Number)
      = ⟨true, 1000000000000000000, -18⟩ from by decide]
  rw [wtF_sub_number]
  simp only [wtF_sub_ofNumber]
  rw [STAmount.ofIOU_canonical ⟨4444444444444440, -16⟩ .downward
    ⟨by decide, by decide, by decide, by decide⟩]
  rfl

/-- `roundToExponent` of the amount at scale `-15`, downward: digits drop. -/
private theorem wtF_roundToExponent :
    STAmount.roundToExponent wtF (-15) .downward = .ok wtrF := by
  unfold STAmount.roundToExponent
  rw [if_neg (show ¬ (wtF.integral = true) from by decide),
      if_neg (show ¬ (wtF.isZero = true) from by decide),
      if_neg (show ¬ (wtF.exponent ≥ (-15 : Int)) from by decide)]
  rw [show wtF.mNumericType = NumericType.fractional from rfl,
      show wtF.negative = false from rfl]
  rw [STAmount.checked_reference (-15) false .downward (by norm_num) (by norm_num)]
  simp only [show (⟨.fractional, kMinValue, -15, false⟩ : STAmount) = refF from by decide,
    wtF_sum]
  exact wtF_sub

/-- `roundToVaultExponent` truncates the witness amount. -/
private theorem wtF_roundToVault :
    roundToVaultExponent wtF wvF.assetsTotal = .ok wtrF := by
  unfold roundToVaultExponent
  rw [if_neg (show ¬ (wtF.integral = true) from by decide)]
  rw [show wvF.assetsTotal = (⟨false, 3000000000000000000, -18⟩ : Number) from rfl]
  simp only [wtF_toNumber, ok_bind, wtF_add,
    show wtF.numericType = NumericType.fractional from rfl, wtF_postScale, wtF_roundToExponent]
  rfl

private theorem wtF_rounded : wvF.roundedDepositAmount wtF = .ok (.rounded wtrF) := by
  rw [roundedDepositAmount_ok wvF wtF wtrF wtF_roundToVault]
  rw [if_neg (show ¬ (wtrF.isZero = true) from by decide)]

/-- The grid rounding strictly shrinks the witness amount. -/
private theorem wtrF_lt : wtrF.toRat < wtF.toRat := by
  rw [STAmount.toRat_of_nonneg wtrF rfl, STAmount.toRat_of_nonneg wtF rfl]
  show ((4444444444444440 : UInt64).toNat : ℚ) * 10 ^ (-16 : ℤ)
      < ((4444444444444445 : UInt64).toNat : ℚ) * 10 ^ (-16 : ℤ)
  rw [show ((4444444444444440 : UInt64).toNat) = 4444444444444440 from by decide,
      show ((4444444444444445 : UInt64).toNat) = 4444444444444445 from by decide]
  have hp : (0 : ℚ) < 10 ^ (-16 : ℤ) := by positivity
  have hlt : (4444444444444440 : ℚ) < 4444444444444445 := by norm_num
  exact mul_lt_mul_of_pos_right hlt hp

end

/-! ### Witness data for `deposit_vault_updates_attained`

An int64 vault holding `9000000000000000007` (a canonical 19-digit balance) with
`1e18` shares outstanding, nothing lent. A donation of the integral amount
`9000000000000000006` makes the exact new total `18000000000000000013`, which is
20 digits and rounds to nearest at 19 significant digits, storing
`18000000000000000010`. That stored value differs from the exact sum, so the
`depositε` error term in `deposit_vault_updates` cannot be dropped. -/

/-- The witness vault. -/
def wvDVU : Vault :=
  { assetsTotal := ⟨false, 9000000000000000007, 0⟩
  , assetsAvailable := ⟨false, 9000000000000000007, 0⟩
  , assetsMaximum := none, numericType := .int64, scale := 0
  , sharesTotal := ⟨false, 1000000000000000000, 0⟩
  , interestUnrealized := Number.zero, lossUnrealized := Number.zero }

/-- The witness donation amount, `9000000000000000006` int64. -/
def waDVU : STAmount := STAmount.unchecked .int64 9000000000000000006 0 false

/-- The post-donation vault: both asset fields store `18000000000000000010`, the
exact sum `18000000000000000013` rounded to 19 significant digits. -/
def wvDVU' : Vault :=
  { assetsTotal := ⟨false, 1800000000000000001, 1⟩
  , assetsAvailable := ⟨false, 1800000000000000001, 1⟩
  , assetsMaximum := none, numericType := .int64, scale := 0
  , sharesTotal := ⟨false, 1000000000000000000, 0⟩
  , interestUnrealized := Number.zero, lossUnrealized := Number.zero }

/-- The witness deposit result. -/
def wrDVU : DepositResult := ⟨none, wvDVU', waDVU, STAmount.zero .int64⟩

section
set_option maxRecDepth 10000

/-- Hand trace of the `Number` addition `9000000000000000007 + 9000000000000000006`
to nearest: the exact 20-digit sum drops one digit (rounded down) to
`18000000000000000010`. Stepped through the WF pipeline because the kernel does
not reduce it. -/
private theorem wvDVU_add :
    Number.operator_add ⟨false, 9000000000000000007, 0⟩ ⟨false, 9000000000000000006, 0⟩ .to_nearest
      = .ok ⟨false, 1800000000000000001, 1⟩ := by
  unfold Number.operator_add
  simp only [show (⟨false, 9000000000000000006, 0⟩ : Number).operator_eq Number.zero = false from by decide,
    show (⟨false, 9000000000000000007, 0⟩ : Number).operator_eq Number.zero = false from by decide,
    show (⟨false, 9000000000000000007, 0⟩ : Number).operator_eq
      (⟨false, 9000000000000000006, 0⟩ : Number).operator_neg = false from by decide,
    Bool.false_eq_true, if_false]
  rw [if_neg (by decide : ¬ ((0 : Int) < 0)), if_neg (by decide : ¬ ((0 : Int) > 0)),
    show ((false : Bool) == (false : Bool)) = true from rfl]
  simp only [if_true]
  rw [show toUInt128 (9000000000000000007 : UInt64) + toUInt128 (9000000000000000006 : UInt64)
      = (18000000000000000013 : UInt128) from by decide]
  rw [show (decide ((18000000000000000013 : UInt128) > toUInt128 largeRange.max) ||
           decide ((18000000000000000013 : UInt128) > toUInt128 maxRepUp)) = true from by decide]
  simp only [if_true]
  rw [show Guard.new.doDropDigit128 (18000000000000000013 : UInt128) 0
      = ({ digits_ := 3458764513820540928, xbit_ := false, sbit_ := false },
         (1800000000000000001 : UInt128), (1 : Int)) from by
    unfold Guard.doDropDigit128 Guard.new Guard.push; rfl]
  simp only
  rw [show toUInt64 (1800000000000000001 : UInt128) = (1800000000000000001 : UInt64) from by decide]
  rw [show ({ digits_ := 3458764513820540928, xbit_ := false, sbit_ := false } : Guard).doRoundUp
      false (1800000000000000001 : UInt64) (1 : Int) largeRange.min largeRange.max .to_nearest
      "Number::addition overflow"
      = .ok { negative_ := false, mantissa_ := 1800000000000000001, exponent_ := 1 } from by
    unfold Guard.doRoundUp Guard.bringIntoRange Guard.round Guard.doDropDigit; rfl]
  simp only [RoundResult.toNumber]
  unfold Number.normalize doNormalize
  rw [show (((1800000000000000001 : UInt64)) == 0) = false from rfl]
  simp only [Bool.false_eq_true, if_false]
  rw [show doNormalize_scaleUp largeRange.min (1800000000000000001 : UInt64) 1
        = ((1800000000000000001 : UInt64), (1 : Int)) by unfold doNormalize_scaleUp; rw [if_neg (by decide)],
     show doNormalize_scaleDown largeRange.max (1800000000000000001 : UInt64) (1 : Int) Guard.new
        = .ok ((1800000000000000001 : UInt64), (1 : Int), Guard.new) by
        unfold doNormalize_scaleDown; rw [dif_neg (by decide)]]
  simp only []
  rw [show ((1 : Int) < minExponent || (1800000000000000001 : UInt64) < largeRange.min) = false from by decide]
  simp only [Bool.false_eq_true, if_false]
  rw [show doNormalize_capAtMaxRep (1800000000000000001 : UInt64) (1 : Int) Guard.new
        = .ok ((1800000000000000001 : UInt64), (1 : Int), Guard.new) from by
      unfold doNormalize_capAtMaxRep; rw [if_neg (by decide)]]
  simp only []
  rw [show Guard.new.doRoundUp false (1800000000000000001 : UInt64) (1 : Int)
      largeRange.min largeRange.max .to_nearest "Number::normalize 2"
      = .ok { negative_ := false, mantissa_ := 1800000000000000001, exponent_ := 1 } from by
    unfold Guard.doRoundUp Guard.bringIntoRange Guard.round Guard.doDropDigit; rfl]
  simp only [RoundResult.toNumber]

/-- `waDVU` converts to the `Number` `9000000000000000006` (normalize identity). -/
private theorem wvDVU_amt_toNumber : waDVU.toNumber .to_nearest = .ok ⟨false, 9000000000000000006, 0⟩ := by
  unfold STAmount.toNumber waDVU
  rw [if_pos (show (STAmount.unchecked .int64 9000000000000000006 0 false).integral = true from rfl),
    show (STAmount.unchecked .int64 9000000000000000006 0 false).intAmount
        = .ok { value := 9000000000000000006 } from by
      unfold STAmount.intAmount STAmount.signedDrops
      rw [if_pos (show (STAmount.unchecked .int64 9000000000000000006 0 false).integral = true from rfl)]
      rfl]
  show IntAmount.toNumber { value := 9000000000000000006 } .to_nearest = _
  unfold IntAmount.toNumber Number.from_rep Number.normalized Number.normalize
  show doNormalize false 9000000000000000006 0 largeRange.min largeRange.max .to_nearest = _
  rw [doNormalize_id .to_nearest false 9000000000000000006 0 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)]

/-- `roundToVaultExponent` returns an integral amount unchanged. -/
private theorem wvDVU_round : roundToVaultExponent waDVU wvDVU.assetsTotal = .ok waDVU := by
  unfold roundToVaultExponent; rw [if_pos (show waDVU.integral = true from rfl)]; rfl

/-- The witness donation runs to `wrDVU`. -/
private theorem wvDVU_run : wvDVU.deposit waDVU true = .ok wrDVU := by
  show wvDVU.deposit waDVU true = .ok ⟨none, wvDVU', waDVU, STAmount.zero .int64⟩
  unfold Vault.deposit
  rw [wvDVU_round]
  simp only [ok_bind]
  rw [if_neg (show ¬ (waDVU.isZero = true) from by decide),
    if_neg (show ¬ ((true && wvDVU.sharesTotal.mantissa_ == 0) = true) from by decide),
    if_neg (show ¬ ((wvDVU.isInsolvent && !true) = true) from by simp)]
  simp only [if_true, pure_bind, wvDVU_amt_toNumber, zero_int64_toNumber, ok_bind]
  simp only [show wvDVU.assetsTotal = (⟨false, 9000000000000000007, 0⟩ : Number) from rfl,
             show wvDVU.assetsAvailable = (⟨false, 9000000000000000007, 0⟩ : Number) from rfl,
             show wvDVU.sharesTotal = (⟨false, 1000000000000000000, 0⟩ : Number) from rfl,
             wvDVU_add, operator_add_zero_right, ok_bind]
  rw [show wvDVU.assetsMaximum = (none : Option Number) from rfl]
  simp only [Option.any_none, Bool.false_eq_true, if_false]
  show pure _ = Except.ok wrDVU
  rfl

/-- The witness vault is lawful. -/
private theorem wvDVU_lawful : wvDVU.Lawful := by
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · show (⟨false, 9000000000000000007, 0⟩ : Number).isNormalized; norm_isNormalized
  · show (⟨false, 9000000000000000007, 0⟩ : Number).isNormalized; norm_isNormalized
  · intro m hm; rw [show wvDVU.assetsMaximum = none from rfl] at hm; exact absurd hm (by simp)
  · show (⟨false, 1000000000000000000, 0⟩ : Number).isNormalized; norm_isNormalized
  · exact Or.inl rfl
  · exact Or.inl rfl
  · show (0 : ℚ) ≤ (⟨false, 1000000000000000000, 0⟩ : Number).toRat; rw [toRat_nat_exp0]; norm_num
  · show (⟨false, 1000000000000000000, 0⟩ : Number).toRat.den = 1
    rw [toRat_nat_exp0]; decide
  · intro _; rfl
  · decide
  · have hAT : wvDVU.toExact.assetsTotal = 9000000000000000007 := by
      show (⟨false, 9000000000000000007, 0⟩ : Number).toRat = _
      rw [toRat_nat_exp0, show (9000000000000000007 : UInt64).toNat = 9000000000000000007 from by decide]
      norm_num
    have hAA : wvDVU.toExact.assetsAvailable = 9000000000000000007 := by
      show (⟨false, 9000000000000000007, 0⟩ : Number).toRat = _
      rw [toRat_nat_exp0, show (9000000000000000007 : UInt64).toNat = 9000000000000000007 from by decide]
      norm_num
    have hI : wvDVU.toExact.interestUnrealized = 0 := by
      simp only [Vault.toExact]; exact Number.toRat_eq_zero_of_mantissa_zero _ rfl
    have hL : wvDVU.toExact.lossUnrealized = 0 := by
      simp only [Vault.toExact]; exact Number.toRat_eq_zero_of_mantissa_zero _ rfl
    have hST : wvDVU.toExact.sharesTotal = 1000000000000000000 := by
      simp only [Vault.toExact]
      rw [show wvDVU.sharesTotal = (⟨false, 1000000000000000000, 0⟩ : Number) from rfl, toRat_nat_exp0]
      rfl
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hAT]; norm_num
    · rw [hAA]; norm_num
    · rw [hAT, hAA]
    · intro m hm; rw [show wvDVU.toExact.assetsMaximum = none from rfl] at hm; exact absurd hm (by simp)
    · intro h; rw [hST] at h; norm_num at h
    · intro m hm; rw [show wvDVU.toExact.assetsMaximum = none from rfl] at hm; exact absurd hm (by simp)
    · rw [hL]
    · rw [hL, hAT, hAA]; norm_num
    · rw [hI]
    · rw [hI, hAT, hAA]; norm_num
    · intro _; rw [hI, hAT]; norm_num
    · rw [hAT, hI, hL]; norm_num
    · intro h; rw [hI] at h; norm_num at h

end

/-- Witness backing `Vault.roundedDepositAmount_truncation_attained`. -/
theorem Vault.roundedDepositAmount_truncation_witness :
    ∃ (v : Vault) (amountDeposit roundedAmount : STAmount),
      v.Lawful ∧
      v.roundedDepositAmount amountDeposit = .ok (.rounded roundedAmount) ∧
      roundedAmount.toRat < amountDeposit.toRat :=
  ⟨wvF, wtF, wtrF, wvF_lawful, wtF_rounded, wtrF_lt⟩

/-- Witness backing `Vault.deposit_sharesIssued_attained`. -/
theorem Vault.deposit_sharesIssued_witness :
    ∃ (v : Vault) (amountDeposit roundedAmount : STAmount) (r : DepositResult),
      v.Lawful ∧ 0 < amountDeposit.toRat ∧
      v.roundedDepositAmount amountDeposit = .ok (.rounded roundedAmount) ∧
      v.deposit amountDeposit false = .ok r ∧ r.error = none ∧
      RoundsWithinWitness r.sharesIssued
        (v.idealSharesDeposit roundedAmount.toRat) depositε :=
  ⟨wvF, waF, waF, wrF, wvF_lawful, waF_pos, waF_rounded, wvF_run, rfl, wsF_witness⟩

/-- Witness backing `Vault.deposit_charge_attained`. -/
theorem Vault.deposit_charge_witness :
    ∃ (v : Vault) (amountDeposit : STAmount) (r : DepositResult),
      v.Lawful ∧ 0 < amountDeposit.toRat ∧
      v.deposit amountDeposit false = .ok r ∧ r.error = none ∧
      RoundsWithinWitness r.amountDeposit'
        (v.idealChargeDeposit r.sharesIssued.toRat) depositε :=
  ⟨wvF, waF, wrF, wvF_lawful, waF_pos, wvF_run, rfl, wcF_witness⟩

/-- Witness backing `Vault.deposit_vault_updates_attained`. -/
theorem Vault.deposit_vault_updates_witness :
    ∃ (v : Vault) (amountDeposit : STAmount) (isDonation : Bool) (r : DepositResult),
      v.Lawful ∧ v.deposit amountDeposit isDonation = .ok r ∧ r.error = none ∧
      r.vault'.assetsTotal.toRat ≠ v.toExact.assetsTotal + r.amountDeposit'.toRat := by
  refine ⟨wvDVU, waDVU, true, wrDVU, wvDVU_lawful, wvDVU_run, rfl, ?_⟩
  show (⟨false, 1800000000000000001, 1⟩ : Number).toRat ≠ wvDVU.toExact.assetsTotal + waDVU.toRat
  rw [Number.toRat_of_nonneg _ rfl,
    show (⟨false, 1800000000000000001, 1⟩ : Number).mantissa_.toNat = 1800000000000000001 from by decide,
    show (⟨false, 1800000000000000001, 1⟩ : Number).exponent_ = 1 from rfl,
    show wvDVU.toExact.assetsTotal = 9000000000000000007 from by
      show (⟨false, 9000000000000000007, 0⟩ : Number).toRat = _
      rw [toRat_nat_exp0, show (9000000000000000007 : UInt64).toNat = 9000000000000000007 from by decide]
      norm_num,
    show waDVU.toRat = 9000000000000000006 from by
      unfold STAmount.toRat waDVU STAmount.unchecked
      rw [show ((STAmount.mk .int64 9000000000000000006 0 false).mValue).toNat = 9000000000000000006 from by decide]
      norm_num [Rat.mkRat_one]]
  norm_num

end XRPL.Model.SingleAssetVault
