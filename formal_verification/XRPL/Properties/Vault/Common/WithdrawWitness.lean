import XRPL.Model.Vault.VaultWithdraw
import XRPL.Properties.Approx
import XRPL.Properties.Vault.Common.WithdrawDefs
import XRPL.Properties.Vault.Common.DepositReduction
import XRPL.Properties.Vault.Common.WitnessSupport

/-! # Witness data for the `Vault.withdraw` sharpness theorems

Concrete lawful runs backing the four `*_attained` headlines in
`Properties/Vault/VaultWithdraw.lean`. One fractional vault holding `3` assets
against `7·10¹⁵` shares backs every witness.

* Witnesses for `sharesToAssetsWithdraw`, `withdraw_sharesBurned` and
  `withdraw_payout`: withdrawing the amount `1` prices
  `7·10¹⁵ / 3 = 2333333333333333.33…` shares, rounded to `2333333333333333`
  whole shares. The share error `1/3` exceeds the relative budget
  `ideal · depositε`. Those shares are worth
  `3 · 2333333333333333 / 7·10¹⁵ = 0.99999999999999985714…`, converted downward
  at 16 digits to `0.9999999999999998`. The shortfall `4/(7·10¹⁶)` exceeds
  `ideal · depositε < 10^(-17)`.
* Witness for `withdraw_vault_updates`: redeeming `2333333333333` shares pays
  `0.0009999999999998571`, whose lowest digit sits below the 19-digit window of
  the stored total `3`. The stored difference `2.999000000000000143` is the
  exact difference `2.9990000000000001429` rounded to nearest, so the stored
  total is not the exact difference.

Every pipeline stage is stepped by hand through the well-founded decimal
recursion, in the style of the deposit witness traces in
`Properties/Vault/VaultDeposit.lean`. -/

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol

/-- The shared withdraw witness vault: 3 assets, 7·10¹⁵ shares. -/
def wvW : Vault :=
  { assetsTotal := ⟨false, 3000000000000000000, -18⟩
  , assetsAvailable := ⟨false, 3000000000000000000, -18⟩
  , assetsMaximum := none, numericType := .fractional, scale := 0
  , sharesTotal := ⟨false, 7000000000000000000, -3⟩
  , interestUnrealized := Number.zero, lossUnrealized := Number.zero }

/-- The asset-denominated witness amount, `1` of the IOU. -/
def waW : STAmount := STAmount.unchecked .fractional 1000000000000000 (-15) false

/-- The redeemed shares, `7·10¹⁵/3` rounded to nearest: `2333333333333333`. -/
def wshW : STAmount := STAmount.unchecked .int64 2333333333333333 0 false

/-- The payout: `3 · 2333333333333333 / 7·10¹⁵` rounded downward at 16 digits,
`0.9999999999999998`. -/
def wpW : STAmount := STAmount.unchecked .fractional 9999999999999998 (-16) false

/-- The stored share total as an int64 amount, `7000000000000000`. -/
def wstW : STAmount := STAmount.unchecked .int64 7000000000000000 0 false

/-- The post-withdrawal vault of the asset-denominated run. -/
def wvW' : Vault :=
  { assetsTotal := ⟨false, 2000000000000000200, -18⟩
  , assetsAvailable := ⟨false, 2000000000000000200, -18⟩
  , assetsMaximum := none, numericType := .fractional, scale := 0
  , sharesTotal := ⟨false, 4666666666666667000, -3⟩
  , interestUnrealized := Number.zero, lossUnrealized := Number.zero }

/-- The witness result of the asset-denominated run. -/
def wrW : WithdrawResult := ⟨none, wvW', wpW, wshW⟩

/-- The share-denominated witness shares of the vault-updates run,
`2333333333333`. -/
def wsh4W : STAmount := STAmount.unchecked .int64 2333333333333 0 false

/-- The payout of the vault-updates run: `3 · 2333333333333 / 7·10¹⁵` rounded
downward at 16 digits, `0.0009999999999998571`. -/
def wp4W : STAmount := STAmount.unchecked .fractional 9999999999998571 (-19) false

/-- The post-withdrawal vault of the vault-updates run. Its stored
`assetsTotal` is the 19-digit rounding of the exact difference. -/
def wv4W' : Vault :=
  { assetsTotal := ⟨false, 2999000000000000143, -18⟩
  , assetsAvailable := ⟨false, 2999000000000000143, -18⟩
  , assetsMaximum := none, numericType := .fractional, scale := 0
  , sharesTotal := ⟨false, 6997666666666667000, -3⟩
  , interestUnrealized := Number.zero, lossUnrealized := Number.zero }

/-- The witness result of the vault-updates run. -/
def wr4W : WithdrawResult := ⟨none, wv4W', wp4W, wsh4W⟩

section
set_option maxRecDepth 10000

local syntax "sd128_step" : tactic
local macro_rules | `(tactic| sd128_step) => `(tactic|
  (conv_lhs => rw [scaleDown128]; rw [dif_pos (by decide)]; rfl))

local syntax "dsd128_step" : tactic
local macro_rules | `(tactic| dsd128_step) => `(tactic|
  (conv_lhs => rw [doNormalize_scaleDown128]; rw [dif_pos (by decide), if_neg (by decide)]; rfl))

private theorem waW_canonical : waW.IOUCanonical :=
  ⟨rfl, by decide, by decide, by decide, by decide⟩

private theorem waW_toNumber : waW.toNumber .to_nearest = .ok ⟨false, 1000000000000000000, -18⟩ := by
  rw [STAmount.toNumber_iou_canonical waW .to_nearest waW_canonical]
  rfl

/-- `sharesTotal * amount = 7e15 * 1` at 19 digits, exact. -/
private theorem wvW_shares_mul :
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
private theorem wvW_shares_div :
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

/-- `to_rep` of the share quotient to nearest: the dropped `.333` tail rounds
down to the whole share count. -/
private theorem wvW_shares_to_rep :
    (⟨false, 2333333333333333333, -3⟩ : Number).to_rep .to_nearest
      = .ok (2333333333333333 : Int64) := by
  unfold Number.to_rep
  rw [show (⟨false, 2333333333333333333, -3⟩ : Number).mantissa = (2333333333333333333 : Int64) from by decide,
      show (⟨false, 2333333333333333333, -3⟩ : Number).exponent = (-3 : Int) from by decide]
  simp only [show ((2333333333333333333 : Int64) == 0) = false from by decide,
    Bool.false_eq_true, if_false]
  rw [if_pos (show (-3 : Int) < 0 from by decide)]
  rw [show Number.to_rep.shift 2333333333333333333 (-3) Guard.new
      = ((2333333333333333 : Int64), ((Guard.new.push 3).push 3).push 3) from by
    rw [to_rep_shift_step _ _ _ (by decide)]
    show Number.to_rep.shift 233333333333333333 (-2) (Guard.new.push 3) = _
    rw [to_rep_shift_step _ _ _ (by decide)]
    show Number.to_rep.shift 23333333333333333 (-1) ((Guard.new.push 3).push 3) = _
    rw [to_rep_shift_step _ _ _ (by decide)]
    show Number.to_rep.shift 2333333333333333 0 (((Guard.new.push 3).push 3).push 3) = _
    exact to_rep_shift_stop _ _]
  simp only []
  rw [if_neg (show ¬ ((-3 : Int) ≥ 0) from by decide)]
  rfl

/-- `to_rep` at offset `0` is the identity on the share mantissa. -/
private theorem wvW_shares_to_rep0 :
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

/-- Packing the rounded share count into the int64 `STAmount`. -/
private theorem wvW_shares_ofNumber :
    STAmount.ofNumber .int64 ⟨false, 2333333333333333333, -3⟩ .to_nearest = .ok wshW := by
  unfold STAmount.ofNumber
  simp only [show (decide ((⟨false, 2333333333333333333, -3⟩ : Number).signum < 0)) = false from by decide,
    Bool.false_eq_true, if_false,
    show NumericType.int64.isIntegral = true from rfl, if_true]
  rw [wvW_shares_to_rep]
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
    rw [wvW_shares_to_rep0]]
  simp only []
  rw [if_neg (by decide)]
  rfl

/-- The share computation of the asset-denominated run: `2333333333333333`. -/
private theorem wvW_assetsToShares : assetsToSharesWithdraw wvW waW false false = .ok wshW := by
  unfold assetsToSharesWithdraw
  rw [show wvW.assetsTotal = (⟨false, 3000000000000000000, -18⟩ : Number) from rfl,
      show wvW.interestUnrealized = Number.zero from rfl,
      show wvW.lossUnrealized = Number.zero from rfl,
      show wvW.sharesTotal = (⟨false, 7000000000000000000, -3⟩ : Number) from rfl]
  simp only [operator_sub_zero_right, ok_bind,
    show ((⟨false, 3000000000000000000, -18⟩ : Number).mantissa_ == 0) = false from by decide,
    Bool.false_eq_true, if_false,
    waW_toNumber, wvW_shares_mul, wvW_shares_div, pure_bind, wvW_shares_ofNumber]

/-- The redeemed shares convert back to the same `Number` (16-digit lift). -/
private theorem wshW_toNumber : wshW.toNumber .to_nearest = .ok ⟨false, 2333333333333333000, -3⟩ := by
  unfold STAmount.toNumber
  rw [if_pos (show wshW.integral = true from rfl),
    show wshW.intAmount = .ok { value := 2333333333333333 } from by
      unfold STAmount.intAmount STAmount.signedDrops
      rw [if_pos (show wshW.integral = true from rfl)]
      rfl]
  show IntAmount.toNumber { value := 2333333333333333 } .to_nearest = _
  unfold IntAmount.toNumber Number.from_rep Number.normalized Number.normalize
  show doNormalize false 2333333333333333 0 largeRange.min largeRange.max .to_nearest = _
  rw [doNormalize_large_16digit false 2333333333333333 0 .to_nearest
    (by decide) (by decide) (by decide) (by decide)]
  rfl

/-- `nav * shares = 3 * 2333333333333333` at 19 digits, exact. -/
private theorem wvW_pay_mul :
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
private theorem wvW_pay_div :
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

/-- The payout `Number` truncates downward onto the 16-digit grid:
`0.9999999999999998`. -/
private theorem wpW_ofNumber :
    STAmount.ofNumber .fractional ⟨false, 9999999999999998570, -19⟩ .downward = .ok wpW := by
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

/-- The payout computation of the redeemed shares: `0.9999999999999998`. -/
private theorem wvW_sharesToAssets : Vault.sharesToAssetsWithdraw wvW wshW false = .ok wpW := by
  unfold Vault.sharesToAssetsWithdraw
  rw [show wvW.assetsTotal = (⟨false, 3000000000000000000, -18⟩ : Number) from rfl,
      show wvW.interestUnrealized = Number.zero from rfl,
      show wvW.lossUnrealized = Number.zero from rfl,
      show wvW.sharesTotal = (⟨false, 7000000000000000000, -3⟩ : Number) from rfl,
      show wvW.numericType = NumericType.fractional from rfl]
  simp only [operator_sub_zero_right, ok_bind,
    show ((⟨false, 3000000000000000000, -18⟩ : Number).mantissa_ == 0) = false from by decide,
    Bool.false_eq_true, if_false,
    wshW_toNumber, wvW_pay_mul, wvW_pay_div, wpW_ofNumber, pure_bind]
  rfl

/-- The asset-denominated exchange: shares redeemed, payout computed. -/
private theorem wvW_computeByAssets :
    computeWithdrawByAssets wvW waW false = .ok ⟨none, wpW, wshW⟩ := by
  unfold computeWithdrawByAssets
  simp only [wvW_assetsToShares, ok_bind, epure,
    show wshW.isZero = false from rfl, Bool.false_eq_true, if_false,
    wvW_sharesToAssets, tryCatch_ok]

/-- `3 - 0.9999999999999998` at 19 digits: one alignment shift, exact. -/
private theorem wvW_total_sub :
    Number.operator_sub ⟨false, 3000000000000000000, -18⟩ ⟨false, 9999999999999998000, -19⟩
      .to_nearest = .ok ⟨false, 2000000000000000200, -18⟩ := by
  unfold Number.operator_sub
  rw [show (⟨false, 9999999999999998000, -19⟩ : Number).operator_neg
      = ⟨true, 9999999999999998000, -19⟩ from rfl]
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

/-- `7e15 - 2333333333333333` at 19 digits, exact. -/
private theorem wvW_sharesTotal_sub :
    Number.operator_sub ⟨false, 7000000000000000000, -3⟩ ⟨false, 2333333333333333000, -3⟩
      .to_nearest = .ok ⟨false, 4666666666666667000, -3⟩ := by
  unfold Number.operator_sub
  rw [show (⟨false, 2333333333333333000, -3⟩ : Number).operator_neg
      = ⟨true, 2333333333333333000, -3⟩ from rfl]
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

/-- The payout amount as a `Number` (16-digit lift). -/
private theorem wpW_toNumber : wpW.toNumber .to_nearest = .ok ⟨false, 9999999999999998000, -19⟩ := by
  rw [STAmount.toNumber_iou_canonical wpW .to_nearest ⟨rfl, by decide, by decide, by decide, by decide⟩]
  rfl

/-- The stored total `3` on the 16-digit grid: exact. -/
private theorem wvW_rounded3 :
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

/-- The new total `2.0000000000000002` on the 16-digit grid: the dropped `200`
tail rounds down. -/
private theorem wvW_rounded2 :
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

/-- `to_rep` of the stored share total: three exact shifts. -/
private theorem wstW_to_rep :
    (⟨false, 7000000000000000000, -3⟩ : Number).to_rep .to_nearest
      = .ok (7000000000000000 : Int64) := by
  unfold Number.to_rep
  rw [show (⟨false, 7000000000000000000, -3⟩ : Number).mantissa = (7000000000000000000 : Int64) from by decide,
      show (⟨false, 7000000000000000000, -3⟩ : Number).exponent = (-3 : Int) from by decide]
  simp only [show ((7000000000000000000 : Int64) == 0) = false from by decide,
    Bool.false_eq_true, if_false]
  rw [if_pos (show (-3 : Int) < 0 from by decide)]
  rw [show Number.to_rep.shift 7000000000000000000 (-3) Guard.new
      = ((7000000000000000 : Int64), Guard.new) from by
    rw [to_rep_shift_step _ _ _ (by decide)]
    show Number.to_rep.shift 700000000000000000 (-2) Guard.new = _
    rw [to_rep_shift_step _ _ _ (by decide)]
    show Number.to_rep.shift 70000000000000000 (-1) Guard.new = _
    rw [to_rep_shift_step _ _ _ (by decide)]
    show Number.to_rep.shift 7000000000000000 0 Guard.new = _
    exact to_rep_shift_stop _ _]
  simp only []
  rw [if_neg (show ¬ ((-3 : Int) ≥ 0) from by decide)]
  rfl

/-- `to_rep` at offset `0` is the identity on the share total mantissa. -/
private theorem wstW_to_rep0 :
    (⟨false, 7000000000000000, 0⟩ : Number).to_rep .to_nearest
      = .ok (7000000000000000 : Int64) := by
  unfold Number.to_rep
  rw [show (⟨false, 7000000000000000, 0⟩ : Number).mantissa = (7000000000000000 : Int64) from by decide,
      show (⟨false, 7000000000000000, 0⟩ : Number).exponent = (0 : Int) from by decide]
  simp only [show ((7000000000000000 : Int64) == 0) = false from by decide,
    Bool.false_eq_true, if_false]
  rw [if_neg (show ¬ ((0 : Int) < 0) from by decide)]
  simp only []
  rw [if_pos (show (0 : Int) ≥ 0 from by decide), to_rep_grow_zero]
  rfl

/-- Packing the stored share total into the int64 `STAmount`. -/
private theorem wstW_ofNumber_lit :
    STAmount.ofNumber .int64 ⟨false, 7000000000000000000, -3⟩ .to_nearest = .ok wstW := by
  unfold STAmount.ofNumber
  simp only [show (decide ((⟨false, 7000000000000000000, -3⟩ : Number).signum < 0)) = false from by decide,
    Bool.false_eq_true, if_false,
    show NumericType.int64.isIntegral = true from rfl, if_true]
  rw [wstW_to_rep]
  simp only []
  rw [show ((7000000000000000 : Int64)).toUInt64 = (7000000000000000 : UInt64) from by decide]
  unfold STAmount.checked STAmount.canonicalize
  simp only [STAmount.unchecked]
  rw [if_pos (by decide)]
  rw [if_neg (by decide)]
  rw [if_neg (by decide)]
  rw [show IntAmount.ofNumber (Number.unchecked false 7000000000000000 0) .to_nearest
      = .ok { value := 7000000000000000 } from by
    unfold IntAmount.ofNumber Number.unchecked
    rw [wstW_to_rep0]]
  simp only []
  rw [if_neg (by decide)]
  rfl

/-- The stored share total converts to `wstW`, the headline `hst` form. -/
private theorem wvW_sharesTotalAmount :
    STAmount.ofNumber .int64 wvW.sharesTotal .to_nearest = .ok wstW := by
  rw [show wvW.sharesTotal = (⟨false, 7000000000000000000, -3⟩ : Number) from rfl]
  exact wstW_ofNumber_lit

/-- The asset-denominated witness run. -/
private theorem wvW_run : wvW.withdraw (.vaultAssets waW) false = .ok wrW := by
  show wvW.withdraw (.vaultAssets waW) false = .ok ⟨none, wvW', wpW, wshW⟩
  unfold Vault.withdraw
  simp only [wvW_computeByAssets, ok_bind]
  rw [show ((⟨none, wpW, wshW⟩ : ComputeWithdrawResult).error.isSome) = false from rfl]
  simp only [Bool.false_eq_true, if_false, pure_bind, wpW_toNumber, ok_bind]
  rw [show wvW.assetsAvailable = (⟨false, 3000000000000000000, -18⟩ : Number) from rfl,
      show wvW.assetsTotal = (⟨false, 3000000000000000000, -18⟩ : Number) from rfl,
      show wvW.numericType = NumericType.fractional from rfl]
  rw [show Number.operator_lt ⟨false, 3000000000000000000, -18⟩ ⟨false, 9999999999999998000, -19⟩
      = false from by decide]
  simp only [Bool.false_eq_true, if_false, wvW_sharesTotalAmount, ok_bind]
  rw [show wshW.operator_eq wstW = false from by decide]
  simp only [Bool.false_eq_true, if_false, wshW_toNumber, ok_bind,
    wvW_total_sub, wvW_rounded3, wvW_rounded2]
  rw [show ((⟨false, 9999999999999998000, -19⟩ : Number).mantissa_ != 0 &&
      (STAmount.unchecked .fractional 3000000000000000 (-15) false).operator_eq
        (STAmount.unchecked .fractional 2000000000000000 (-15) false)) = false from by decide]
  simp only [Bool.false_eq_true, if_false]
  rw [show wvW.sharesTotal = (⟨false, 7000000000000000000, -3⟩ : Number) from rfl]
  simp only [wvW_sharesTotal_sub, ok_bind]
  show pure _ = Except.ok wrW
  rfl

/-- The vault-updates witness shares convert to a `Number` by six scale-up
shifts. -/
private theorem wsh4W_toNumber : wsh4W.toNumber .to_nearest = .ok ⟨false, 2333333333333000000, -6⟩ := by
  unfold STAmount.toNumber
  rw [if_pos (show wsh4W.integral = true from rfl),
    show wsh4W.intAmount = .ok { value := 2333333333333 } from by
      unfold STAmount.intAmount STAmount.signedDrops
      rw [if_pos (show wsh4W.integral = true from rfl)]
      rfl]
  show IntAmount.toNumber { value := 2333333333333 } .to_nearest = _
  unfold IntAmount.toNumber Number.from_rep Number.normalized Number.normalize
  show doNormalize false 2333333333333 0 largeRange.min largeRange.max .to_nearest = _
  unfold doNormalize
  rw [show ((2333333333333 : UInt64) == 0) = false from rfl]
  simp only [Bool.false_eq_true, if_false]
  rw [show doNormalize_scaleUp largeRange.min 2333333333333 0
      = ((2333333333333000000 : UInt64), (-6 : Int)) from by
    rw [doNormalize_scaleUp_step (by decide) (by decide)]
    show doNormalize_scaleUp largeRange.min 23333333333330 (-1) = _
    rw [doNormalize_scaleUp_step (by decide) (by decide)]
    show doNormalize_scaleUp largeRange.min 233333333333300 (-2) = _
    rw [doNormalize_scaleUp_step (by decide) (by decide)]
    show doNormalize_scaleUp largeRange.min 2333333333333000 (-3) = _
    rw [doNormalize_scaleUp_step (by decide) (by decide)]
    show doNormalize_scaleUp largeRange.min 23333333333330000 (-4) = _
    rw [doNormalize_scaleUp_step (by decide) (by decide)]
    show doNormalize_scaleUp largeRange.min 233333333333300000 (-5) = _
    rw [doNormalize_scaleUp_step (by decide) (by decide)]
    show doNormalize_scaleUp largeRange.min 2333333333333000000 (-6) = _
    exact doNormalize_scaleUp_id _ _ _ (by decide)]
  simp only []
  rw [doNormalize_scaleDown_id _ _ _ _ (by decide)]
  simp only []
  rw [show ((-6 : Int) < minExponent || (2333333333333000000 : UInt64) < largeRange.min) = false from by decide]
  simp only [Bool.false_eq_true, if_false]
  rw [show doNormalize_capAtMaxRep (2333333333333000000 : UInt64) (-6) Guard.new
      = .ok ((2333333333333000000 : UInt64), (-6 : Int), Guard.new) from by
    unfold doNormalize_capAtMaxRep; rw [if_neg (by decide)]]
  simp only []
  rw [show Guard.new.doRoundUp false (2333333333333000000 : UInt64) (-6)
      largeRange.min largeRange.max .to_nearest "Number::normalize 2"
      = .ok { negative_ := false, mantissa_ := 2333333333333000000, exponent_ := -6 } from by
    unfold Guard.doRoundUp Guard.bringIntoRange Guard.round Guard.doDropDigit; rfl]
  simp only [RoundResult.toNumber]

/-- `nav * shares = 3 * 2333333333333` at 19 digits, exact. -/
private theorem ww4_mul :
    Number.operator_mul ⟨false, 3000000000000000000, -18⟩ ⟨false, 2333333333333000000, -6⟩
      .to_nearest = .ok ⟨false, 6999999999999000000, -6⟩ := by
  unfold Number.operator_mul
  simp only [show (⟨false, 3000000000000000000, -18⟩ : Number).operator_eq Number.zero = false from by decide,
    show (⟨false, 2333333333333000000, -6⟩ : Number).operator_eq Number.zero = false from by decide,
    Bool.false_eq_true, if_false, bne_self_eq_false]
  rw [show toUInt128 (3000000000000000000 : UInt64) * toUInt128 (2333333333333000000 : UInt64)
      = (6999999999999000000000000000000000000 : UInt128) from by decide,
    show (-18 : Int) + (-6) = -24 from by decide]
  rw [show scaleDown128 (6999999999999000000000000000000000000 : UInt128) (-24) Guard.new
      = ((6999999999999000000 : UInt64), (-6 : Int), Guard.new) from by
    sd128_step; sd128_step; sd128_step; sd128_step; sd128_step; sd128_step
    sd128_step; sd128_step; sd128_step; sd128_step; sd128_step; sd128_step
    sd128_step; sd128_step; sd128_step; sd128_step; sd128_step; sd128_step
    conv_lhs => rw [scaleDown128]; rw [dif_neg (by decide)]
    rfl]
  simp only []
  rw [show Guard.new.doRoundUp false (6999999999999000000 : UInt64) (-6)
      largeRange.min largeRange.max .to_nearest "Number::multiplication overflow"
      = .ok { negative_ := false, mantissa_ := 6999999999999000000, exponent_ := -6 } from by
    unfold Guard.doRoundUp Guard.bringIntoRange Guard.round Guard.doDropDigit; rfl]
  simp only [RoundResult.toNumber]
  unfold Number.normalize
  exact doNormalize_id .to_nearest false 6999999999999000000 (-6) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)

/-- `6999999999999 / 7e15` at 19 digits to nearest: the quotient rides the
`maxRepUp` cusp, so the stored mantissa keeps a trailing zero:
`0.000999999999999857143`. -/
private theorem ww4_div :
    Number.operator_div ⟨false, 6999999999999000000, -6⟩ ⟨false, 7000000000000000000, -3⟩
      .to_nearest = .ok ⟨false, 9999999999998571430, -22⟩ := by
  unfold Number.operator_div
  rw [if_neg (by decide), if_neg (by decide)]
  change (match divQuotient128 (6999999999999000000 : UInt64) (7000000000000000000 : UInt64) (-6) (-3) with
      | (zm128, ze, dropped) => doNormalize128 false zm128 ze largeRange.min largeRange.max .to_nearest dropped)
    = Except.ok ⟨false, 9999999999998571430, -22⟩
  rw [show divQuotient128 (6999999999999000000 : UInt64) (7000000000000000000 : UInt64) (-6) (-3)
      = (9999999999998571428571, -25, true) from by decide]
  change doNormalize128 false (9999999999998571428571 : UInt128) (-25)
      largeRange.min largeRange.max .to_nearest true = Except.ok ⟨false, 9999999999998571430, -22⟩
  unfold doNormalize128
  rw [show ((9999999999998571428571 : UInt128) == 0) = false from by decide]
  simp only [Bool.false_eq_true, if_false]
  rw [show doNormalize128.scaleUp largeRange.min (9999999999998571428571 : UInt128) (-25)
        = ((9999999999998571428571 : UInt128), (-25 : Int)) from by
      rw [doNormalize128.scaleUp.eq_def]; rw [if_neg (by decide)]]
  simp only [if_true]
  rw [show (Guard.new.set_sticky : Guard)
        = { digits_ := 0, xbit_ := true, sbit_ := false } from rfl]
  rw [show doNormalize_scaleDown128 largeRange.max (9999999999998571428571 : UInt128) (-25)
        { digits_ := 0, xbit_ := true, sbit_ := false }
      = .ok (9999999999998571428, -22,
             { digits_ := 0x5710000000000000, xbit_ := true, sbit_ := false }) from by
    dsd128_step; dsd128_step; dsd128_step
    conv_lhs => rw [doNormalize_scaleDown128]; rw [dif_neg (by decide)]
    rfl]
  simp only []
  rw [show (decide ((-22 : Int) < minExponent)
        || decide ((9999999999998571428 : UInt128) < toUInt128 largeRange.min)) = false from by decide]
  simp only [Bool.false_eq_true, if_false]
  rw [show doNormalize_capAtMaxRep (toUInt64 (9999999999998571428 : UInt128)) (-22)
        { digits_ := 0x5710000000000000, xbit_ := true, sbit_ := false }
      = .ok ((999999999999857142 : UInt64), (-21 : Int),
             { digits_ := 0x8571000000000000, xbit_ := true, sbit_ := false }) from by
    unfold doNormalize_capAtMaxRep
    rw [if_pos (by decide), if_neg (by decide)]
    rfl]
  simp only []
  rw [show ({ digits_ := 0x8571000000000000, xbit_ := true, sbit_ := false } : Guard).doRoundUp
      false (999999999999857142 : UInt64) (-21) largeRange.min largeRange.max .to_nearest
      "Number::normalize 2"
      = .ok { negative_ := false, mantissa_ := 9999999999998571430, exponent_ := -22 } from by
    unfold Guard.doRoundUp Guard.bringIntoRange Guard.round Guard.doDropDigit; rfl]
  simp only [RoundResult.toNumber]

/-- The vault-updates payout `Number` truncates downward onto the 16-digit
grid: `0.0009999999999998571`. -/
private theorem wp4W_ofNumber :
    STAmount.ofNumber .fractional ⟨false, 9999999999998571430, -22⟩ .downward = .ok wp4W := by
  unfold STAmount.ofNumber
  simp only [show (decide ((⟨false, 9999999999998571430, -22⟩ : Number).signum < 0)) = false from by decide,
    Bool.false_eq_true, if_false,
    show NumericType.fractional.isIntegral = false from rfl]
  rw [show kMinValue = cMinValue from rfl, show kMaxValue = cMaxValue from rfl]
  rw [show (⟨false, 9999999999998571430, -22⟩ : Number).normalizeToRange cMinValue cMaxValue .downward
      = .ok ((9999999999998571 : Int64), (-19 : Int)) from by
    unfold Number.normalizeToRange
    simp only []
    rw [show doNormalize false 9999999999998571430 (-22) cMinValue cMaxValue .downward
        = .ok { negative_ := false, mantissa_ := 9999999999998571, exponent_ := -19 } from by
      unfold doNormalize
      rw [show ((9999999999998571430 : UInt64) == 0) = false from rfl]
      simp only [Bool.false_eq_true, if_false]
      rw [doNormalize_scaleUp_id cMinValue 9999999999998571430 (-22) (by decide)]
      rw [show doNormalize_scaleDown cMaxValue (9999999999998571430 : UInt64) (-22) Guard.new
          = .ok ((9999999999998571 : UInt64), (-19 : Int),
                 { digits_ := 0x4300000000000000, xbit_ := false, sbit_ := false }) from by
        rw [doNormalize_scaleDown_step (by decide) (by decide)]
        show doNormalize_scaleDown cMaxValue 999999999999857143 (-21) (Guard.new.push 0) = _
        rw [doNormalize_scaleDown_step (by decide) (by decide)]
        show doNormalize_scaleDown cMaxValue 99999999999985714 (-20) ((Guard.new.push 0).push 3) = _
        rw [doNormalize_scaleDown_step (by decide) (by decide)]
        show doNormalize_scaleDown cMaxValue 9999999999998571 (-19)
            (((Guard.new.push 0).push 3).push 4) = _
        rw [doNormalize_scaleDown_id _ _ _ _ (by decide)]
        rfl]
      simp only []
      rw [show (decide ((-19 : Int) < minExponent)
            || decide ((9999999999998571 : UInt64) < cMinValue)) = false from by decide]
      simp only [Bool.false_eq_true, if_false]
      rw [show doNormalize_capAtMaxRep (9999999999998571 : UInt64) (-19)
            { digits_ := 0x4300000000000000, xbit_ := false, sbit_ := false }
          = .ok ((9999999999998571 : UInt64), (-19 : Int),
                 { digits_ := 0x4300000000000000, xbit_ := false, sbit_ := false }) from by
        unfold doNormalize_capAtMaxRep; rw [if_neg (by decide)]]
      simp only []
      rw [show ({ digits_ := 0x4300000000000000, xbit_ := false, sbit_ := false } : Guard).doRoundUp
          false (9999999999998571 : UInt64) (-19) cMinValue cMaxValue .downward
          "Number::normalize 2"
          = .ok { negative_ := false, mantissa_ := 9999999999998571, exponent_ := -19 } from by
        unfold Guard.doRoundUp Guard.bringIntoRange Guard.round Guard.doDropDigit; rfl]
      simp only [RoundResult.toNumber]]
    rfl]
  simp only []
  show STAmount.checked .fractional 9999999999998571 (-19) false .downward = _
  unfold STAmount.checked STAmount.unchecked
  exact STAmount.canonicalize_canonical_id _ .downward ⟨rfl, by decide, by decide, by decide, by decide⟩

/-- The payout computation of the vault-updates run: `0.0009999999999998571`. -/
private theorem ww4_sharesToAssets : Vault.sharesToAssetsWithdraw wvW wsh4W false = .ok wp4W := by
  unfold Vault.sharesToAssetsWithdraw
  rw [show wvW.assetsTotal = (⟨false, 3000000000000000000, -18⟩ : Number) from rfl,
      show wvW.interestUnrealized = Number.zero from rfl,
      show wvW.lossUnrealized = Number.zero from rfl,
      show wvW.sharesTotal = (⟨false, 7000000000000000000, -3⟩ : Number) from rfl,
      show wvW.numericType = NumericType.fractional from rfl]
  simp only [operator_sub_zero_right, ok_bind,
    show ((⟨false, 3000000000000000000, -18⟩ : Number).mantissa_ == 0) = false from by decide,
    Bool.false_eq_true, if_false,
    wsh4W_toNumber, ww4_mul, ww4_div, wp4W_ofNumber, pure_bind]
  rfl

/-- The share-denominated exchange of the vault-updates run. -/
private theorem ww4_computeByShares :
    computeWithdrawByShares wvW wsh4W false = .ok ⟨none, wp4W, wsh4W⟩ := by
  unfold computeWithdrawByShares
  simp only [ww4_sharesToAssets, ok_bind, epure, tryCatch_ok]

/-- The vault-updates payout as a `Number` (16-digit lift). -/
private theorem wp4W_toNumber : wp4W.toNumber .to_nearest = .ok ⟨false, 9999999999998571000, -22⟩ := by
  rw [STAmount.toNumber_iou_canonical wp4W .to_nearest ⟨rfl, by decide, by decide, by decide, by decide⟩]
  rfl

/-- `3 - 0.0009999999999998571` at 19 digits to nearest: the payout tail sits
below the window, the guard recovers one digit and the dropped `9` rounds the
stored difference up. -/
private theorem ww4_total_sub :
    Number.operator_sub ⟨false, 3000000000000000000, -18⟩ ⟨false, 9999999999998571000, -22⟩
      .to_nearest = .ok ⟨false, 2999000000000000143, -18⟩ := by
  unfold Number.operator_sub
  rw [show (⟨false, 9999999999998571000, -22⟩ : Number).operator_neg
      = ⟨true, 9999999999998571000, -22⟩ from rfl]
  unfold Number.operator_add
  rw [if_neg (show ¬ ((⟨true, 9999999999998571000, -22⟩ : Number).operator_eq Number.zero = true) from by decide),
      if_neg (show ¬ ((⟨false, 3000000000000000000, -18⟩ : Number).operator_eq Number.zero = true) from by decide),
      if_neg (show ¬ ((⟨false, 3000000000000000000, -18⟩ : Number).operator_eq
        (⟨true, 9999999999998571000, -22⟩ : Number).operator_neg = true) from by decide)]
  simp -iota only [Bool.false_eq_true, if_false]
  rw [if_neg (by decide : ¬ ((-18 : Int) < (-22 : Int))), if_pos (by decide : (-18 : Int) > (-22 : Int))]
  rw [if_pos trivial]
  rw [show Number.operator_add.alignDown 9999999999998571000 (-22) Guard.new.set_negative (-18)
      = ((999999999999857 : UInt64), (-18 : Int),
         ({ digits_ := 0x1000000000000000, xbit_ := false, sbit_ := true } : Guard)) from by
    rw [Number.operator_add.alignDown, if_pos (by decide : (-22 : Int) < (-18 : Int))]
    show Number.operator_add.alignDown 999999999999857100 (-21) (Guard.new.set_negative.push 0) (-18) = _
    rw [Number.operator_add.alignDown, if_pos (by decide : (-21 : Int) < (-18 : Int))]
    show Number.operator_add.alignDown 99999999999985710 (-20)
        ((Guard.new.set_negative.push 0).push 0) (-18) = _
    rw [Number.operator_add.alignDown, if_pos (by decide : (-20 : Int) < (-18 : Int))]
    show Number.operator_add.alignDown 9999999999998571 (-19)
        (((Guard.new.set_negative.push 0).push 0).push 0) (-18) = _
    rw [Number.operator_add.alignDown, if_pos (by decide : (-19 : Int) < (-18 : Int))]
    show Number.operator_add.alignDown 999999999999857 (-18)
        ((((Guard.new.set_negative.push 0).push 0).push 0).push 1) (-18) = _
    rw [Number.operator_add.alignDown, if_neg (by decide : ¬ ((-18 : Int) < (-18 : Int)))]
    rfl]
  simp only []
  rw [show ((false : Bool) == (true : Bool)) = false from rfl]
  simp only [Bool.false_eq_true, if_false]
  rw [if_pos (by decide : (3000000000000000000 : UInt64) > (999999999999857 : UInt64))]
  rw [show toUInt128 (3000000000000000000 : UInt64) - toUInt128 (999999999999857 : UInt64)
      = (2999000000000000143 : UInt128) from by decide]
  simp only []
  rw [show Number.operator_add.recover (toUInt128 largeRange.min * 1000)
        (2999000000000000143 : UInt128) (-18)
        ({ digits_ := 0x1000000000000000, xbit_ := false, sbit_ := true } : Guard) 40
      = ((29990000000000001429 : UInt128), (-19 : Int),
         ({ digits_ := 0, xbit_ := false, sbit_ := true } : Guard)) from rfl]
  simp only [show (({ digits_ := 0, xbit_ := false, sbit_ := true } : Guard).empty : Bool) = true from rfl,
    Bool.not_true, if_true]
  show doNormalize128 false (29990000000000001429 : UInt128) (-19)
      largeRange.min largeRange.max .to_nearest false = _
  unfold doNormalize128
  rw [show ((29990000000000001429 : UInt128) == 0) = false from by decide]
  simp only [Bool.false_eq_true, if_false]
  rw [show doNormalize128.scaleUp largeRange.min (29990000000000001429 : UInt128) (-19)
        = ((29990000000000001429 : UInt128), (-19 : Int)) from by
      rw [doNormalize128.scaleUp.eq_def]; rw [if_neg (by decide)]]
  simp only []
  rw [show doNormalize_scaleDown128 largeRange.max (29990000000000001429 : UInt128) (-19) Guard.new
      = .ok (2999000000000000142, -18,
             { digits_ := 0x9000000000000000, xbit_ := false, sbit_ := false }) from by
    dsd128_step
    conv_lhs => rw [doNormalize_scaleDown128]; rw [dif_neg (by decide)]
    rfl]
  simp only []
  rw [show (decide ((-18 : Int) < minExponent)
        || decide ((2999000000000000142 : UInt128) < toUInt128 largeRange.min)) = false from by decide]
  simp only [Bool.false_eq_true, if_false]
  rw [show doNormalize_capAtMaxRep (toUInt64 (2999000000000000142 : UInt128)) (-18)
        { digits_ := 0x9000000000000000, xbit_ := false, sbit_ := false }
      = .ok ((2999000000000000142 : UInt64), (-18 : Int),
             { digits_ := 0x9000000000000000, xbit_ := false, sbit_ := false }) from by
    unfold doNormalize_capAtMaxRep; rw [if_neg (by decide)]; rfl]
  simp only []
  rw [show ({ digits_ := 0x9000000000000000, xbit_ := false, sbit_ := false } : Guard).doRoundUp
      false (2999000000000000142 : UInt64) (-18) largeRange.min largeRange.max .to_nearest
      "Number::normalize 2"
      = .ok { negative_ := false, mantissa_ := 2999000000000000143, exponent_ := -18 } from by
    unfold Guard.doRoundUp Guard.bringIntoRange Guard.round Guard.doDropDigit; rfl]
  simp only [RoundResult.toNumber]

/-- The new total `2.999000000000000143` on the 16-digit grid: the dropped
`143` tail rounds down. -/
private theorem ww4_rounded2 :
    STAmount.ofNumber .fractional ⟨false, 2999000000000000143, -18⟩ .to_nearest
      = .ok (STAmount.unchecked .fractional 2999000000000000 (-15) false) := by
  unfold STAmount.ofNumber
  simp only [show (decide ((⟨false, 2999000000000000143, -18⟩ : Number).signum < 0)) = false from by decide,
    Bool.false_eq_true, if_false,
    show NumericType.fractional.isIntegral = false from rfl]
  rw [show kMinValue = cMinValue from rfl, show kMaxValue = cMaxValue from rfl]
  rw [show (⟨false, 2999000000000000143, -18⟩ : Number).normalizeToRange cMinValue cMaxValue .to_nearest
      = .ok ((2999000000000000 : Int64), (-15 : Int)) from by
    unfold Number.normalizeToRange
    simp only []
    rw [show doNormalize false 2999000000000000143 (-18) cMinValue cMaxValue .to_nearest
        = .ok { negative_ := false, mantissa_ := 2999000000000000, exponent_ := -15 } from by
      unfold doNormalize
      rw [show ((2999000000000000143 : UInt64) == 0) = false from rfl]
      simp only [Bool.false_eq_true, if_false]
      rw [doNormalize_scaleUp_id cMinValue 2999000000000000143 (-18) (by decide)]
      rw [show doNormalize_scaleDown cMaxValue (2999000000000000143 : UInt64) (-18) Guard.new
          = .ok ((2999000000000000 : UInt64), (-15 : Int),
                 { digits_ := 0x1430000000000000, xbit_ := false, sbit_ := false }) from by
        rw [doNormalize_scaleDown_step (by decide) (by decide)]
        show doNormalize_scaleDown cMaxValue 299900000000000014 (-17) (Guard.new.push 3) = _
        rw [doNormalize_scaleDown_step (by decide) (by decide)]
        show doNormalize_scaleDown cMaxValue 29990000000000001 (-16) ((Guard.new.push 3).push 4) = _
        rw [doNormalize_scaleDown_step (by decide) (by decide)]
        show doNormalize_scaleDown cMaxValue 2999000000000000 (-15)
            (((Guard.new.push 3).push 4).push 1) = _
        rw [doNormalize_scaleDown_id _ _ _ _ (by decide)]
        rfl]
      simp only []
      rw [show (decide ((-15 : Int) < minExponent)
            || decide ((2999000000000000 : UInt64) < cMinValue)) = false from by decide]
      simp only [Bool.false_eq_true, if_false]
      rw [show doNormalize_capAtMaxRep (2999000000000000 : UInt64) (-15)
            { digits_ := 0x1430000000000000, xbit_ := false, sbit_ := false }
          = .ok ((2999000000000000 : UInt64), (-15 : Int),
                 { digits_ := 0x1430000000000000, xbit_ := false, sbit_ := false }) from by
        unfold doNormalize_capAtMaxRep; rw [if_neg (by decide)]]
      simp only []
      rw [show ({ digits_ := 0x1430000000000000, xbit_ := false, sbit_ := false } : Guard).doRoundUp
          false (2999000000000000 : UInt64) (-15) cMinValue cMaxValue .to_nearest
          "Number::normalize 2"
          = .ok { negative_ := false, mantissa_ := 2999000000000000, exponent_ := -15 } from by
        unfold Guard.doRoundUp Guard.bringIntoRange Guard.round Guard.doDropDigit; rfl]
      simp only [RoundResult.toNumber]]
    rfl]
  simp only []
  show STAmount.checked .fractional 2999000000000000 (-15) false .to_nearest = _
  unfold STAmount.checked STAmount.unchecked
  exact STAmount.canonicalize_canonical_id _ .to_nearest ⟨rfl, by decide, by decide, by decide, by decide⟩

/-- `7e15 - 2333333333333` at 19 digits: three exact alignment shifts. -/
private theorem ww4_sharesTotal_sub :
    Number.operator_sub ⟨false, 7000000000000000000, -3⟩ ⟨false, 2333333333333000000, -6⟩
      .to_nearest = .ok ⟨false, 6997666666666667000, -3⟩ := by
  unfold Number.operator_sub
  rw [show (⟨false, 2333333333333000000, -6⟩ : Number).operator_neg
      = ⟨true, 2333333333333000000, -6⟩ from rfl]
  unfold Number.operator_add
  rw [if_neg (show ¬ ((⟨true, 2333333333333000000, -6⟩ : Number).operator_eq Number.zero = true) from by decide),
      if_neg (show ¬ ((⟨false, 7000000000000000000, -3⟩ : Number).operator_eq Number.zero = true) from by decide),
      if_neg (show ¬ ((⟨false, 7000000000000000000, -3⟩ : Number).operator_eq
        (⟨true, 2333333333333000000, -6⟩ : Number).operator_neg = true) from by decide)]
  simp -iota only [Bool.false_eq_true, if_false]
  rw [if_neg (by decide : ¬ ((-3 : Int) < (-6 : Int))), if_pos (by decide : (-3 : Int) > (-6 : Int))]
  rw [if_pos trivial]
  rw [show Number.operator_add.alignDown 2333333333333000000 (-6) Guard.new.set_negative (-3)
      = ((2333333333333000 : UInt64), (-3 : Int), Guard.new.set_negative) from by
    rw [Number.operator_add.alignDown, if_pos (by decide : (-6 : Int) < (-3 : Int))]
    show Number.operator_add.alignDown 233333333333300000 (-5) (Guard.new.set_negative.push 0) (-3) = _
    rw [Number.operator_add.alignDown, if_pos (by decide : (-5 : Int) < (-3 : Int))]
    show Number.operator_add.alignDown 23333333333330000 (-4)
        ((Guard.new.set_negative.push 0).push 0) (-3) = _
    rw [Number.operator_add.alignDown, if_pos (by decide : (-4 : Int) < (-3 : Int))]
    show Number.operator_add.alignDown 2333333333333000 (-3)
        (((Guard.new.set_negative.push 0).push 0).push 0) (-3) = _
    rw [Number.operator_add.alignDown, if_neg (by decide : ¬ ((-3 : Int) < (-3 : Int)))]
    rfl]
  simp only []
  rw [show ((false : Bool) == (true : Bool)) = false from rfl]
  simp only [Bool.false_eq_true, if_false]
  rw [if_pos (by decide : (7000000000000000000 : UInt64) > (2333333333333000 : UInt64))]
  rw [show toUInt128 (7000000000000000000 : UInt64) - toUInt128 (2333333333333000 : UInt64)
      = (6997666666666667000 : UInt128) from by decide]
  simp only []
  rw [show Number.operator_add.recover (toUInt128 largeRange.min * 1000)
        (6997666666666667000 : UInt128) (-3) Guard.new.set_negative 40
      = ((6997666666666667000 : UInt128), (-3 : Int), Guard.new.set_negative) from rfl]
  simp only [show (Guard.new.set_negative.empty : Bool) = true from rfl, Bool.not_true, if_true]
  show doNormalize128 false (6997666666666667000 : UInt128) (-3)
      largeRange.min largeRange.max .to_nearest false = _
  unfold doNormalize128
  rw [show ((6997666666666667000 : UInt128) == 0) = false from by decide]
  simp only [Bool.false_eq_true, if_false]
  rw [show doNormalize128.scaleUp largeRange.min (6997666666666667000 : UInt128) (-3)
        = ((6997666666666667000 : UInt128), (-3 : Int)) from by
      rw [doNormalize128.scaleUp.eq_def]; rw [if_neg (by decide)]]
  simp only []
  rw [show doNormalize_scaleDown128 largeRange.max (6997666666666667000 : UInt128) (-3) Guard.new
      = .ok (6997666666666667000, -3, Guard.new) from by
    conv_lhs => rw [doNormalize_scaleDown128]; rw [dif_neg (by decide)]]
  simp only []
  rw [show (decide ((-3 : Int) < minExponent)
        || decide ((6997666666666667000 : UInt128) < toUInt128 largeRange.min)) = false from by decide]
  simp only [Bool.false_eq_true, if_false]
  rw [show doNormalize_capAtMaxRep (toUInt64 (6997666666666667000 : UInt128)) (-3) Guard.new
      = .ok ((6997666666666667000 : UInt64), (-3 : Int), Guard.new) from by
    unfold doNormalize_capAtMaxRep; rw [if_neg (by decide)]; rfl]
  simp only []
  rw [show Guard.new.doRoundUp false (6997666666666667000 : UInt64) (-3)
      largeRange.min largeRange.max .to_nearest "Number::normalize 2"
      = .ok { negative_ := false, mantissa_ := 6997666666666667000, exponent_ := -3 } from by
    unfold Guard.doRoundUp Guard.bringIntoRange Guard.round Guard.doDropDigit; rfl]
  simp only [RoundResult.toNumber]

/-- The vault-updates witness run. -/
private theorem ww4_run : wvW.withdraw (.vaultShares wsh4W) false = .ok wr4W := by
  show wvW.withdraw (.vaultShares wsh4W) false = .ok ⟨none, wv4W', wp4W, wsh4W⟩
  unfold Vault.withdraw
  simp only [ww4_computeByShares, ok_bind]
  rw [show ((⟨none, wp4W, wsh4W⟩ : ComputeWithdrawResult).error.isSome) = false from rfl]
  simp only [Bool.false_eq_true, if_false, pure_bind, wp4W_toNumber, ok_bind]
  rw [show wvW.assetsAvailable = (⟨false, 3000000000000000000, -18⟩ : Number) from rfl,
      show wvW.assetsTotal = (⟨false, 3000000000000000000, -18⟩ : Number) from rfl,
      show wvW.numericType = NumericType.fractional from rfl]
  rw [show Number.operator_lt ⟨false, 3000000000000000000, -18⟩ ⟨false, 9999999999998571000, -22⟩
      = false from by decide]
  simp only [Bool.false_eq_true, if_false, wvW_sharesTotalAmount, ok_bind]
  rw [show wsh4W.operator_eq wstW = false from by decide]
  simp only [Bool.false_eq_true, if_false, wsh4W_toNumber, ok_bind,
    ww4_total_sub, wvW_rounded3, ww4_rounded2]
  rw [show ((⟨false, 9999999999998571000, -22⟩ : Number).mantissa_ != 0 &&
      (STAmount.unchecked .fractional 3000000000000000 (-15) false).operator_eq
        (STAmount.unchecked .fractional 2999000000000000 (-15) false)) = false from by decide]
  simp only [Bool.false_eq_true, if_false]
  rw [show wvW.sharesTotal = (⟨false, 7000000000000000000, -3⟩ : Number) from rfl]
  simp only [ww4_sharesTotal_sub, ok_bind]
  show pure _ = Except.ok wr4W
  rfl

/-- Value of the stored share total. -/
private theorem wvW_shares_toRat :
    (⟨false, 7000000000000000000, -3⟩ : Number).toRat = ((7000000000000000 : ℕ) : ℚ) := by
  rw [Number.toRat_of_nonneg _ rfl,
      show ((7000000000000000000 : UInt64).toNat) = 7000000000000000000 from by decide]
  norm_num

/-- Exact asset total of the witness vault. -/
private theorem wvW_exact_assetsTotal : wvW.toExact.assetsTotal = 3 := by
  show (⟨false, 3000000000000000000, -18⟩ : Number).toRat = _
  rw [Number.toRat_of_nonneg _ rfl,
      show ((3000000000000000000 : UInt64).toNat) = 3000000000000000000 from by decide]
  norm_num

/-- Exact share total of the witness vault. -/
private theorem wvW_exact_sharesTotal : wvW.toExact.sharesTotal = 7000000000000000 := by
  show wvW.sharesTotal.toRat.num.toNat = _
  rw [show wvW.sharesTotal = (⟨false, 7000000000000000000, -3⟩ : Number) from rfl, wvW_shares_toRat]
  norm_num
  rfl

/-- Exact unrealized interest of the witness vault (zero). -/
private theorem wvW_exact_interest : wvW.toExact.interestUnrealized = 0 := by
  simp only [Vault.toExact]
  exact Number.toRat_eq_zero_of_mantissa_zero _ rfl

/-- Exact unrealized loss of the witness vault (zero). -/
private theorem wvW_exact_loss : wvW.toExact.lossUnrealized = 0 := by
  simp only [Vault.toExact]
  exact Number.toRat_eq_zero_of_mantissa_zero _ rfl

/-- The witness vault is lawful. -/
private theorem wvW_lawful : wvW.Lawful := by
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · show (⟨false, 3000000000000000000, -18⟩ : Number).isNormalized; norm_isNormalized
  · show (⟨false, 3000000000000000000, -18⟩ : Number).isNormalized; norm_isNormalized
  · intro m hm; rw [show wvW.assetsMaximum = none from rfl] at hm; exact absurd hm (by simp)
  · show (⟨false, 7000000000000000000, -3⟩ : Number).isNormalized; norm_isNormalized
  · exact Or.inl rfl
  · exact Or.inl rfl
  · show (0 : ℚ) ≤ (⟨false, 7000000000000000000, -3⟩ : Number).toRat
    rw [wvW_shares_toRat]; positivity
  · show (⟨false, 7000000000000000000, -3⟩ : Number).toRat.den = 1
    rw [wvW_shares_toRat]; exact Rat.den_natCast _
  · intro _; rfl
  · decide
  · have hAT := wvW_exact_assetsTotal
    have hAA : wvW.toExact.assetsAvailable = 3 := by
      show (⟨false, 3000000000000000000, -18⟩ : Number).toRat = _
      rw [Number.toRat_of_nonneg _ rfl,
          show ((3000000000000000000 : UInt64).toNat) = 3000000000000000000 from by decide]
      norm_num
    have hST := wvW_exact_sharesTotal
    have hI := wvW_exact_interest
    have hL := wvW_exact_loss
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hAT]; norm_num
    · rw [hAA]; norm_num
    · rw [hAT, hAA]
    · intro m hm; rw [show wvW.toExact.assetsMaximum = none from rfl] at hm
      exact absurd hm (by simp)
    · intro h; rw [hST] at h; exact absurd h (by norm_num)
    · intro m hm; rw [show wvW.toExact.assetsMaximum = none from rfl] at hm
      exact absurd hm (by simp)
    · rw [hL]
    · rw [hL, hAT, hAA]; norm_num
    · rw [hI]
    · rw [hI, hAT, hAA]; norm_num
    · intro _; rw [hI, hAT]; norm_num
    · rw [hAT, hI, hL]; norm_num
    · intro h; rw [hI] at h; exact absurd h (by norm_num)

/-- The witness vault prices withdrawals exactly: both `Number` subtractions
are no-ops on the zero unrealized fields. -/
private theorem wvW_navExact : wvW.WithdrawNavExact false := by
  refine ⟨⟨false, 3000000000000000000, -18⟩, ⟨false, 3000000000000000000, -18⟩, ?_, ?_, ?_⟩
  · rw [show wvW.assetsTotal = (⟨false, 3000000000000000000, -18⟩ : Number) from rfl,
        show wvW.interestUnrealized = Number.zero from rfl]
    exact operator_sub_zero_right _ _
  · show Number.operator_sub _ wvW.lossUnrealized .to_nearest = _
    rw [show wvW.lossUnrealized = Number.zero from rfl]
    exact operator_sub_zero_right _ _
  · simp only [Bool.false_eq_true, if_false]
    unfold Vault.withdrawNav
    rw [wvW_exact_assetsTotal, wvW_exact_interest, wvW_exact_loss,
        Number.toRat_of_nonneg _ rfl,
        show ((3000000000000000000 : UInt64).toNat) = 3000000000000000000 from by decide]
    norm_num

/-- Value of the asset-denominated amount. -/
private theorem waW_toRat : waW.toRat = 1 := by
  rw [STAmount.toRat_of_nonneg waW rfl]
  show ((1000000000000000 : UInt64).toNat : ℚ) * 10 ^ (-15 : ℤ) = 1
  rw [show ((1000000000000000 : UInt64).toNat) = 1000000000000000 from by decide]
  norm_num

/-- The amount `1` is positive. -/
private theorem waW_pos : 0 < waW.toRat := by rw [waW_toRat]; norm_num

/-- Value of the redeemed shares. -/
private theorem wshW_toRat : wshW.toRat = 2333333333333333 := by
  rw [STAmount.toRat_of_nonneg wshW rfl]
  show ((2333333333333333 : UInt64).toNat : ℚ) * 10 ^ (0 : ℤ) = 2333333333333333
  rw [show ((2333333333333333 : UInt64).toNat) = 2333333333333333 from by decide]
  norm_num

/-- The redeemed shares are positive. -/
private theorem wshW_pos : 0 < wshW.toRat := by rw [wshW_toRat]; norm_num

/-- Value of the payout. -/
private theorem wpW_toRat : wpW.toRat = 9999999999999998 / 10 ^ 16 := by
  rw [STAmount.toRat_of_nonneg wpW rfl]
  show ((9999999999999998 : UInt64).toNat : ℚ) * 10 ^ (-16 : ℤ) = 9999999999999998 / 10 ^ 16
  rw [show ((9999999999999998 : UInt64).toNat) = 9999999999999998 from by decide]
  norm_num

/-- Value of the vault-updates payout. -/
private theorem wp4W_toRat : wp4W.toRat = 9999999999998571 / 10 ^ 19 := by
  rw [STAmount.toRat_of_nonneg wp4W rfl]
  show ((9999999999998571 : UInt64).toNat : ℚ) * 10 ^ (-19 : ℤ) = 9999999999998571 / 10 ^ 19
  rw [show ((9999999999998571 : UInt64).toNat) = 9999999999998571 from by decide]
  norm_num

/-- The redeemed shares miss the ideal by `1/3`, far beyond the relative
budget. -/
private theorem wshW_witness :
    RoundsWithinWitness wrW.sharesBurned (wvW.idealSharesWithdraw false waW.toRat) depositε := by
  unfold RoundsWithinWitness Vault.idealSharesWithdraw Vault.withdrawNav depositε
  simp only [Bool.false_eq_true, if_false]
  rw [show RatValued.toRat wrW.sharesBurned = wshW.toRat from rfl, wshW_toRat, waW_toRat,
      wvW_exact_sharesTotal, wvW_exact_interest, wvW_exact_loss, wvW_exact_assetsTotal]
  rw [show ((7000000000000000 : ℕ) : ℚ) * 1 / (3 - 0 - 0) = 7000000000000000 / 3 from by norm_num]
  rw [show (2333333333333333 : ℚ) - 7000000000000000 / 3 = -(1 / 3) from by norm_num]
  rw [abs_neg, abs_of_pos (by norm_num : (0 : ℚ) < 1 / 3),
      abs_of_pos (by norm_num : (0 : ℚ) < (7000000000000000 : ℚ) / 3)]
  norm_num

/-- The payout undershoots the redeemed shares' exact worth by `4/(7·10¹⁶)`,
beyond the relative budget. -/
private theorem wpW_witness :
    RoundsWithinWitness wrW.assets'
      (wvW.idealAssetsWithdraw false wrW.sharesBurned.toRat) depositε := by
  unfold RoundsWithinWitness Vault.idealAssetsWithdraw Vault.withdrawNav depositε
  simp only [Bool.false_eq_true, if_false]
  rw [show RatValued.toRat wrW.assets' = wpW.toRat from rfl,
      show wrW.sharesBurned = wshW from rfl, wpW_toRat, wshW_toRat,
      wvW_exact_sharesTotal, wvW_exact_interest, wvW_exact_loss, wvW_exact_assetsTotal]
  rw [show (3 - 0 - 0 : ℚ) * 2333333333333333 / ((7000000000000000 : ℕ) : ℚ)
      = 6999999999999999 / 7000000000000000 from by norm_num]
  rw [show (9999999999999998 : ℚ) / 10 ^ 16 - 6999999999999999 / 7000000000000000
      = -(4 / 70000000000000000) from by norm_num]
  rw [abs_neg, abs_of_pos (by norm_num : (0 : ℚ) < 4 / 70000000000000000),
      abs_of_pos (by norm_num : (0 : ℚ) < (6999999999999999 : ℚ) / 7000000000000000)]
  norm_num

/-- The stored total of the vault-updates run is not the exact difference. -/
private theorem wr4W_updates_ne :
    wr4W.vault'.assetsTotal.toRat ≠ wvW.toExact.assetsTotal - wr4W.assets'.toRat := by
  show (⟨false, 2999000000000000143, -18⟩ : Number).toRat ≠ wvW.toExact.assetsTotal - wp4W.toRat
  rw [Number.toRat_of_nonneg _ rfl,
      show ((2999000000000000143 : UInt64).toNat) = 2999000000000000143 from by decide,
      wvW_exact_assetsTotal, wp4W_toRat]
  norm_num

end

/-- Witness data for `Vault.sharesToAssetsWithdraw_attained`. -/
theorem Vault.sharesToAssetsWithdraw_witness :
    ∃ (v : Vault) (shares assets : STAmount) (waiveUnrealizedLoss : Bool),
      v.Lawful ∧ 0 < shares.toRat ∧
      v.WithdrawNavExact waiveUnrealizedLoss ∧
      v.sharesToAssetsWithdraw shares waiveUnrealizedLoss = .ok assets ∧
      RoundsWithinWitness assets
        (v.idealAssetsWithdraw waiveUnrealizedLoss shares.toRat) depositε :=
  ⟨wvW, wshW, wpW, false, wvW_lawful, wshW_pos, wvW_navExact, wvW_sharesToAssets, wpW_witness⟩

/-- Witness data for `Vault.withdraw_sharesBurned_attained`. -/
theorem Vault.withdraw_sharesBurned_witness :
    ∃ (v : Vault) (assets : STAmount) (waiveUnrealizedLoss : Bool) (r : WithdrawResult),
      v.Lawful ∧ 0 < assets.toRat ∧
      v.WithdrawNavExact waiveUnrealizedLoss ∧
      v.withdraw (.vaultAssets assets) waiveUnrealizedLoss = .ok r ∧ r.error = none ∧
      RoundsWithinWitness r.sharesBurned
        (v.idealSharesWithdraw waiveUnrealizedLoss assets.toRat) depositε :=
  ⟨wvW, waW, false, wrW, wvW_lawful, waW_pos, wvW_navExact, wvW_run, rfl, wshW_witness⟩

/-- Witness data for `Vault.withdraw_payout_attained`. -/
theorem Vault.withdraw_payout_witness :
    ∃ (v : Vault) (amount : WithdrawAmount) (waiveUnrealizedLoss : Bool)
      (sharesTotalAmount : STAmount) (r : WithdrawResult),
      v.Lawful ∧ v.WithdrawNavExact waiveUnrealizedLoss ∧
      v.withdraw amount waiveUnrealizedLoss = .ok r ∧ r.error = none ∧
      STAmount.ofNumber .int64 v.sharesTotal .to_nearest = .ok sharesTotalAmount ∧
      r.sharesBurned.operator_eq sharesTotalAmount = false ∧
      RoundsWithinWitness r.assets'
        (v.idealAssetsWithdraw waiveUnrealizedLoss r.sharesBurned.toRat) depositε :=
  ⟨wvW, .vaultAssets waW, false, wstW, wrW, wvW_lawful, wvW_navExact, wvW_run, rfl,
    wvW_sharesTotalAmount, by decide, wpW_witness⟩

/-- Witness data for `Vault.withdraw_vault_updates_attained`. -/
theorem Vault.withdraw_vault_updates_witness :
    ∃ (v : Vault) (amount : WithdrawAmount) (waiveUnrealizedLoss : Bool)
      (sharesTotalAmount : STAmount) (r : WithdrawResult),
      v.Lawful ∧ v.withdraw amount waiveUnrealizedLoss = .ok r ∧ r.error = none ∧
      STAmount.ofNumber .int64 v.sharesTotal .to_nearest = .ok sharesTotalAmount ∧
      r.sharesBurned.operator_eq sharesTotalAmount = false ∧
      r.vault'.assetsTotal.toRat ≠ v.toExact.assetsTotal - r.assets'.toRat :=
  ⟨wvW, .vaultShares wsh4W, false, wstW, wr4W, wvW_lawful, ww4_run, rfl,
    wvW_sharesTotalAmount, by decide, wr4W_updates_ne⟩

end XRPL.Model.SingleAssetVault
