import XRPL.Properties.Protocol.Number.Common.ToRatLemmas
import XRPL.Properties.Protocol.Number.Common.Rounding.BitVec
import XRPL.Properties.Protocol.Number.Common.Rounding.DivQuotient
import XRPL.Properties.Protocol.Number.Common.NumberBridge
import XRPL.Properties.Protocol.Number.Compare.Compare
import XRPL.Properties.Protocol.Number.Add.Common.NoWrap
import XRPL.Properties.Protocol.Number.Add.Common.SuccessCondition
import XRPL.Properties.Protocol.Number.Mul.Common.SuccessCondition
import XRPL.Properties.Protocol.Number.Div.Common.SuccessCondition
import XRPL.Properties.Protocol.Number.Common.Rounding.TopGap

/-! # When the `Number` operations succeed

Success conditions of the four operations in each rounding mode, and the overflow error outside them. Add, subtract
and divide check for overflow before rounding (FV_M1_19), so their theorems carry `hrange` and a witness. -/

namespace XRPL.Model.Protocol

/-- `operator_neg` of a mantissa-zero `Number` is the canonical zero. -/
theorem Number.operator_neg_of_mantissa_zero (n : Number) (h : n.mantissa_ = 0) :
    n.operator_neg = Number.zero := by
  sorry

/-- Adding the canonical zero on the right is the identity and never errors. -/
theorem Number.operator_add_zero_right (x : Number) (mode : rounding_mode) :
    x.operator_add Number.zero mode = .ok x := by
  sorry

/-- Adding the canonical zero on the left returns the other operand and never errors. -/
theorem Number.operator_add_zero_left (y : Number) (mode : rounding_mode) :
    Number.zero.operator_add y mode = .ok y := by
  sorry

/-- Subtracting a mantissa-zero `Number` returns the first operand unchanged, in every mode. -/
theorem Number.operator_sub_of_mantissa_zero (x y : Number) (mode : rounding_mode)
    (h : y.mantissa_ = 0) :
    x.operator_sub y mode = .ok x := by
  sorry

/-- `operator_eq Number.zero` detects a zero mantissa, so a nonzero mantissa is not
equal to the canonical zero. -/
theorem Number.operator_eq_zero_false_of_mantissa_ne (n : Number) (h : n.mantissa_ ≠ 0) :
    n.operator_eq Number.zero = false := by
  sorry

/-- With a nonzero divisor, `operator_div` passes the divide-by-zero check and reduces to the
`doNormalize128` pipeline. -/
theorem Number.operator_div_of_divisor_ne (x y : Number) (mode : rounding_mode)
    (hy : y.mantissa_ ≠ 0) :
    x.operator_div y mode =
      (if x.operator_eq Number.zero then pure x
       else do
         let zn := x.negative_ != y.negative_
         let (zm128, ze, dropped) ←
           divQuotient128 x.mantissa_ y.mantissa_ x.exponent_ y.exponent_
         doNormalize128 zn zm128 ze largeRange.min largeRange.max mode dropped) := by
  sorry

/-- `doRoundUp` succeeds when the source exponent is at most `maxExponent - 1`, since the rounding step cannot
overflow. -/
theorem Guard.doRoundUp_ok_of_exp_le (g : Guard) (neg : Bool) (m : UInt64) (e : Int)
    (minM maxM : UInt64) (mode : rounding_mode) (loc : Error) (hmin : minM.toNat ≤ 10 ^ 18)
    (he : e + 1 ≤ maxExponent) :
    ∃ res, g.doRoundUp neg m e minM maxM mode loc = .ok res := by
  sorry

/-- From a source exponent `e ≥ minExponent`, a successful `doRoundUp` never raises the exponent above `e + 1`.
Only the carry drop-digit leg raises it, by one. -/
theorem Guard.doRoundUp_ok_output_exp_le (g : Guard) (neg : Bool) (m : UInt64) (e : Int)
    (minM maxM : UInt64) (mode : rounding_mode) (loc : Error) (res : RoundResult)
    (he_lo : minExponent ≤ e)
    (hok : g.doRoundUp neg m e minM maxM mode loc = .ok res) :
    res.exponent_ ≤ e + 1 := by
  sorry

/-- `capAtMaxRep` succeeds below `maxExponent`. It either keeps the mantissa or drops one digit, raising the
exponent by one. -/
theorem doNormalize_capAtMaxRep_ok_of_exp (m : UInt64) (e : Int) (g : Guard)
    (he : e < maxExponent) :
    ∃ (m' : UInt64) (e' : Int) (g' : Guard),
      doNormalize_capAtMaxRep m e g = .ok (m', e', g') ∧ e' ≤ e + 1 := by
  sorry

/-- `scaleDown128Spec` runs some `k` steps: the output exponent is `e + k`, the output mantissa is `≤ maxRepUp`, and
`k ≥ 1` forces the input mantissa to be at least `9223372036854775811 * 10^(k - 1)`. -/
theorem scaleDown128_forward_exp_bound (M : UInt128) (e : Int) (g0 : Guard) :
    ∃ k : ℕ,
      (scaleDown128Spec M e g0).2.1 = e + (k : Int) ∧
      (scaleDown128Spec M e g0).1.toNat ≤ maxRepUp.toNat ∧
      (1 ≤ k → 9223372036854775811 * 10 ^ (k - 1) ≤ M.toNat) := by
  sorry

/-- `scaleDown128Spec` returns a mantissa `≤ maxRepUp` and an exponent in `[e, e + 20]`, since a `UInt128` input
needs at most twenty digit drops. -/
theorem scaleDown128_output_bound (M : UInt128) (e : Int) (g0 : Guard) :
    (scaleDown128Spec M e g0).1.toNat ≤ maxRepUp.toNat ∧
    e ≤ (scaleDown128Spec M e g0).2.1 ∧
    (scaleDown128Spec M e g0).2.1 ≤ e + 20 := by
  sorry

/-- `operator_mul` succeeds in every mode when both mantissas are at least `largeRange.min` and the exponent
sum `x.exponent_ + y.exponent_` lies in `[minExponent, maxExponent - 22]`. -/
theorem Number.operator_mul_ok_of_large_operands
    (x y : Number) (mode : rounding_mode)
    (hxm : largeRange.min ≤ x.mantissa_) (hym : largeRange.min ≤ y.mantissa_)
    (he_lo : minExponent ≤ x.exponent_ + y.exponent_)
    (he_hi : x.exponent_ + y.exponent_ ≤ maxExponent - 22) :
    ∃ result, x.operator_mul y mode = .ok result := by
  sorry

/-- `operator_mul` succeeds in every mode on two normalized nonzero operands whose exponent sum lies in
`[minExponent, maxExponent - 22]`. -/
lemma Number.operator_mul_ok_of_normalized
    (x y : Number) (mode : rounding_mode)
    (hx : x.isNormalized) (hy : y.isNormalized)
    (hx0 : x.mantissa_ ≠ 0) (hy0 : y.mantissa_ ≠ 0)
    (he_lo : minExponent ≤ x.exponent_ + y.exponent_)
    (he_hi : x.exponent_ + y.exponent_ ≤ maxExponent - 22) :
    ∃ result, x.operator_mul y mode = .ok result := by
  sorry

/-- `doNormalize128_scaleUpSpec` never raises the exponent, since it only multiplies the mantissa by 10 and
decrements the exponent. -/
theorem doNormalize128_scaleUp_exp_le (minMant : UInt64) (m : UInt128) (e : Int) :
    (doNormalize128_scaleUpSpec minMant m e).2 ≤ e := by
  sorry

/-- If the mantissa is below `(maxMantissa + 1) · 10^d` and `e + d ≤ maxExponent`, `doNormalize_scaleDown128Spec`
succeeds with an output exponent at most `e + d`. -/
theorem doNormalize_scaleDown128_ok_aux (d : ℕ) :
    ∀ (m : UInt128) (e : Int) (g : Guard),
      m.toNat < (largeRange.max.toNat + 1) * 10 ^ d →
      e + (d : Int) ≤ maxExponent →
      ∃ (m' : UInt128) (e' : Int) (g' : Guard),
        doNormalize_scaleDown128Spec largeRange.max m e g = .ok (m', e', g') ∧
        e' ≤ e + (d : Int) := by
  sorry

/-- `doNormalize128` succeeds whenever the source exponent is at most `maxExponent - 22`, with no mantissa
bound and no lower exponent bound. -/
theorem doNormalize128_ok_of_exp (zn : Bool) (M : UInt128) (e : Int)
    (mode : rounding_mode) (sticky : Bool) (he : e + 22 ≤ maxExponent) :
    ∃ result, doNormalize128 zn M e largeRange.min largeRange.max mode sticky = .ok result := by
  sorry

/-- `operator_div` succeeds in every mode on two normalized nonzero operands with
`x.exponent_ - y.exponent_ ≤ maxExponent - 5`, which leaves `doNormalize128` the headroom it needs. -/
lemma Number.operator_div_ok_of_normalized
    (x y : Number) (mode : rounding_mode)
    (hx : x.isNormalized) (hy : y.isNormalized)
    (hx0 : x.mantissa_ ≠ 0) (hy0 : y.mantissa_ ≠ 0)
    (he : x.exponent_ - y.exponent_ ≤ maxExponent - 5) :
    ∃ result, x.operator_div y mode = .ok result := by
  sorry

/-- The `Number` exponent of a nonzero normalized source sits at or above `minExponent`. -/
lemma Number.exponent_ge_min (n : Number) (hn : n.isNormalized) (hn0 : n.mantissa_ ≠ 0) :
    minExponent ≤ n.exponent_ := by
  sorry

/-- A normalized Number whose exponent is at least 3 below `maxExponent` is at most `10^16 · 10^maxExponent` in size. -/
private lemma Number.abs_toRat_le_of_exp (x : Number) (hx : x.isNormalized) (hxe : x.exponent_ + 3 ≤ maxExponent) :
    |x.toRat| ≤ 10 ^ 16 * (10 : ℚ) ^ (maxExponent : ℤ) := by
  sorry

/-- `operator_add` succeeds on two normalized operands with exponent headroom. Either operand may be zero, and the
signs may differ. -/
lemma Number.operator_add_ok_of_exp (x y : Number) (mode : rounding_mode)
    (hx : x.isNormalized) (hy : y.isNormalized)
    (hxe : x.exponent_ + 22 ≤ maxExponent) (hye : y.exponent_ + 22 ≤ maxExponent) :
    ∃ result, x.operator_add y mode = .ok result := by
  sorry

/-- `operator_sub` succeeds on two normalized operands with exponent headroom. Either operand may be zero, and the
signs may differ. -/
lemma Number.operator_sub_ok_of_exp (x y : Number) (mode : rounding_mode)
    (hx : x.isNormalized) (hy : y.isNormalized)
    (hxe : x.exponent_ + 22 ≤ maxExponent) (hye : y.exponent_ + 22 ≤ maxExponent) :
    ∃ result, x.operator_sub y mode = .ok result := by
  sorry

/-- `to_nearest` `x + y` succeeds exactly when the exact sum is below `Number.top_plus_five` in size. `hrange` leaves
out the sums where the early overflow check differs (FV_M1_19). -/
theorem Number.operator_add_ok_iff_to_nearest (x y : Number)
    (hx : x.isNormalized) (hy : y.isNormalized) (hx0 : x.mantissa_ ≠ 0) (hy0 : y.mantissa_ ≠ 0)
    (hrange : |x.toRat + y.toRat| < Number.top_plus_one ∨ Number.top_plus_five ≤ |x.toRat + y.toRat|) :
    (∃ result, x.operator_add y .to_nearest = .ok result) ↔
      |x.toRat + y.toRat| < Number.top_plus_five := by
  sorry

/-- A sum left out by `hrange`: it is below `Number.top_plus_five` in size, and `to_nearest` `x + y` fails with an
overflow error. -/
theorem Number.operator_add_ok_iff_to_nearest_attained :
    ∃ x y : Number,
      x.isNormalized ∧
      y.isNormalized ∧
      x.mantissa_ ≠ 0 ∧
      y.mantissa_ ≠ 0 ∧
      |x.toRat + y.toRat| < Number.top_plus_five ∧
      ∃ err,
        x.operator_add y .to_nearest = .error err ∧
        isOverflow err = true := by
  sorry

/-- `towards_zero` `x + y` succeeds exactly when the exact sum is below `Number.top_plus_ten` in size. `hrange` leaves
out the sums where the early overflow check differs (FV_M1_19). -/
theorem Number.operator_add_ok_iff_towards_zero (x y : Number)
    (hx : x.isNormalized) (hy : y.isNormalized) (hx0 : x.mantissa_ ≠ 0) (hy0 : y.mantissa_ ≠ 0)
    (hrange : |x.toRat + y.toRat| < Number.top_plus_one ∨ Number.top_plus_ten ≤ |x.toRat + y.toRat|) :
    (∃ result, x.operator_add y .towards_zero = .ok result) ↔
      |x.toRat + y.toRat| < Number.top_plus_ten := by
  sorry

/-- A sum left out by `hrange`: it is below `Number.top_plus_ten` in size, and `towards_zero` `x + y` fails with an
overflow error. -/
theorem Number.operator_add_ok_iff_towards_zero_attained :
    ∃ x y : Number,
      x.isNormalized ∧
      y.isNormalized ∧
      x.mantissa_ ≠ 0 ∧
      y.mantissa_ ≠ 0 ∧
      |x.toRat + y.toRat| < Number.top_plus_ten ∧
      ∃ err,
        x.operator_add y .towards_zero = .error err ∧
        isOverflow err = true := by
  sorry

/-- `downward` `x + y` succeeds exactly when the exact sum is at least `-Number.top` and below `Number.top_plus_ten`.
`hrange` leaves out the sums where the early overflow check differs (FV_M1_19). -/
theorem Number.operator_add_ok_iff_downward (x y : Number)
    (hx : x.isNormalized) (hy : y.isNormalized) (hx0 : x.mantissa_ ≠ 0) (hy0 : y.mantissa_ ≠ 0)
    (hrange : (x.toRat + y.toRat ≤ -Number.top_plus_one ∨ -Number.top ≤ x.toRat + y.toRat) ∧
      (x.toRat + y.toRat < Number.top_plus_one ∨ Number.top_plus_ten ≤ x.toRat + y.toRat)) :
    (∃ result, x.operator_add y .downward = .ok result) ↔
      -Number.top ≤ x.toRat + y.toRat ∧ x.toRat + y.toRat < Number.top_plus_ten := by
  sorry

/-- A sum left out by `hrange`: it is at least `-Number.top` and below `Number.top_plus_ten`, and `downward` `x + y`
fails with an overflow error. -/
theorem Number.operator_add_ok_iff_downward_attained :
    ∃ x y : Number,
      x.isNormalized ∧
      y.isNormalized ∧
      x.mantissa_ ≠ 0 ∧
      y.mantissa_ ≠ 0 ∧
      (-Number.top ≤ x.toRat + y.toRat ∧ x.toRat + y.toRat < Number.top_plus_ten) ∧
      ∃ err,
        x.operator_add y .downward = .error err ∧
        isOverflow err = true := by
  sorry

/-- `upward` `x + y` succeeds exactly when the exact sum is above `-Number.top_plus_ten` and at most `Number.top`.
`hrange` leaves out the sums where the early overflow check differs (FV_M1_19). -/
theorem Number.operator_add_ok_iff_upward (x y : Number)
    (hx : x.isNormalized) (hy : y.isNormalized) (hx0 : x.mantissa_ ≠ 0) (hy0 : y.mantissa_ ≠ 0)
    (hrange : (x.toRat + y.toRat ≤ -Number.top_plus_ten ∨ -Number.top_plus_one < x.toRat + y.toRat) ∧
      (x.toRat + y.toRat ≤ Number.top ∨ Number.top_plus_one ≤ x.toRat + y.toRat)) :
    (∃ result, x.operator_add y .upward = .ok result) ↔
      -Number.top_plus_ten < x.toRat + y.toRat ∧ x.toRat + y.toRat ≤ Number.top := by
  sorry

/-- A sum left out by `hrange`: it is above `-Number.top_plus_ten` and at most `Number.top`, and `upward` `x + y` fails
with an overflow error. -/
theorem Number.operator_add_ok_iff_upward_attained :
    ∃ x y : Number,
      x.isNormalized ∧
      y.isNormalized ∧
      x.mantissa_ ≠ 0 ∧
      y.mantissa_ ≠ 0 ∧
      (-Number.top_plus_ten < x.toRat + y.toRat ∧ x.toRat + y.toRat ≤ Number.top) ∧
      ∃ err,
        x.operator_add y .upward = .error err ∧
        isOverflow err = true := by
  sorry

/-- `to_nearest` `x - y` succeeds exactly when the exact difference is below `Number.top_plus_five` in size. `hrange`
leaves out the differences where the early overflow check differs (FV_M1_19). -/
theorem Number.operator_sub_ok_iff_to_nearest (x y : Number)
    (hx : x.isNormalized) (hy : y.isNormalized) (hx0 : x.mantissa_ ≠ 0) (hy0 : y.mantissa_ ≠ 0)
    (hrange : |x.toRat - y.toRat| < Number.top_plus_one ∨ Number.top_plus_five ≤ |x.toRat - y.toRat|) :
    (∃ result, x.operator_sub y .to_nearest = .ok result) ↔
      |x.toRat - y.toRat| < Number.top_plus_five := by
  sorry

/-- A difference left out by `hrange`: it is below `Number.top_plus_five` in size, and `to_nearest` `x - y` fails with
an overflow error. -/
theorem Number.operator_sub_ok_iff_to_nearest_attained :
    ∃ x y : Number,
      x.isNormalized ∧
      y.isNormalized ∧
      x.mantissa_ ≠ 0 ∧
      y.mantissa_ ≠ 0 ∧
      |x.toRat - y.toRat| < Number.top_plus_five ∧
      ∃ err,
        x.operator_sub y .to_nearest = .error err ∧
        isOverflow err = true := by
  sorry

/-- `towards_zero` `x - y` succeeds exactly when the exact difference is below `Number.top_plus_ten` in size. `hrange`
leaves out the differences where the early overflow check differs (FV_M1_19). -/
theorem Number.operator_sub_ok_iff_towards_zero (x y : Number)
    (hx : x.isNormalized) (hy : y.isNormalized) (hx0 : x.mantissa_ ≠ 0) (hy0 : y.mantissa_ ≠ 0)
    (hrange : |x.toRat - y.toRat| < Number.top_plus_one ∨ Number.top_plus_ten ≤ |x.toRat - y.toRat|) :
    (∃ result, x.operator_sub y .towards_zero = .ok result) ↔
      |x.toRat - y.toRat| < Number.top_plus_ten := by
  sorry

/-- A difference left out by `hrange`: it is below `Number.top_plus_ten` in size, and `towards_zero` `x - y` fails with
an overflow error. -/
theorem Number.operator_sub_ok_iff_towards_zero_attained :
    ∃ x y : Number,
      x.isNormalized ∧
      y.isNormalized ∧
      x.mantissa_ ≠ 0 ∧
      y.mantissa_ ≠ 0 ∧
      |x.toRat - y.toRat| < Number.top_plus_ten ∧
      ∃ err,
        x.operator_sub y .towards_zero = .error err ∧
        isOverflow err = true := by
  sorry

/-- `downward` `x - y` succeeds exactly when the exact difference is at least `-Number.top` and below
`Number.top_plus_ten`. `hrange` leaves out the differences where the early overflow check differs (FV_M1_19). -/
theorem Number.operator_sub_ok_iff_downward (x y : Number)
    (hx : x.isNormalized) (hy : y.isNormalized) (hx0 : x.mantissa_ ≠ 0) (hy0 : y.mantissa_ ≠ 0)
    (hrange : (x.toRat - y.toRat ≤ -Number.top_plus_one ∨ -Number.top ≤ x.toRat - y.toRat) ∧
      (x.toRat - y.toRat < Number.top_plus_one ∨ Number.top_plus_ten ≤ x.toRat - y.toRat)) :
    (∃ result, x.operator_sub y .downward = .ok result) ↔
      -Number.top ≤ x.toRat - y.toRat ∧ x.toRat - y.toRat < Number.top_plus_ten := by
  sorry

/-- A difference left out by `hrange`: it is at least `-Number.top` and below `Number.top_plus_ten`, and `downward`
`x - y` fails with an overflow error. -/
theorem Number.operator_sub_ok_iff_downward_attained :
    ∃ x y : Number,
      x.isNormalized ∧
      y.isNormalized ∧
      x.mantissa_ ≠ 0 ∧
      y.mantissa_ ≠ 0 ∧
      (-Number.top ≤ x.toRat - y.toRat ∧ x.toRat - y.toRat < Number.top_plus_ten) ∧
      ∃ err,
        x.operator_sub y .downward = .error err ∧
        isOverflow err = true := by
  sorry

/-- `upward` `x - y` succeeds exactly when the exact difference is above `-Number.top_plus_ten` and at most
`Number.top`. `hrange` leaves out the differences where the early overflow check differs (FV_M1_19). -/
theorem Number.operator_sub_ok_iff_upward (x y : Number)
    (hx : x.isNormalized) (hy : y.isNormalized) (hx0 : x.mantissa_ ≠ 0) (hy0 : y.mantissa_ ≠ 0)
    (hrange : (x.toRat - y.toRat ≤ -Number.top_plus_ten ∨ -Number.top_plus_one < x.toRat - y.toRat) ∧
      (x.toRat - y.toRat ≤ Number.top ∨ Number.top_plus_one ≤ x.toRat - y.toRat)) :
    (∃ result, x.operator_sub y .upward = .ok result) ↔
      -Number.top_plus_ten < x.toRat - y.toRat ∧ x.toRat - y.toRat ≤ Number.top := by
  sorry

/-- A difference left out by `hrange`: it is above `-Number.top_plus_ten` and at most `Number.top`, and `upward` `x - y`
fails with an overflow error. -/
theorem Number.operator_sub_ok_iff_upward_attained :
    ∃ x y : Number,
      x.isNormalized ∧
      y.isNormalized ∧
      x.mantissa_ ≠ 0 ∧
      y.mantissa_ ≠ 0 ∧
      (-Number.top_plus_ten < x.toRat - y.toRat ∧ x.toRat - y.toRat ≤ Number.top) ∧
      ∃ err,
        x.operator_sub y .upward = .error err ∧
        isOverflow err = true := by
  sorry

/-- `to_nearest` `x / y` succeeds exactly when the exact quotient is below `Number.top_plus_five` in size. `hrange`
leaves out the quotients where the early overflow check differs (FV_M1_19). -/
theorem Number.operator_div_ok_iff_to_nearest (x y : Number)
    (hx : x.isNormalized) (hy : y.isNormalized) (hx0 : x.mantissa_ ≠ 0) (hy0 : y.mantissa_ ≠ 0)
    (hrange : |x.toRat / y.toRat| < Number.top_plus_one ∨ Number.top_plus_five ≤ |x.toRat / y.toRat|) :
    (∃ result, x.operator_div y .to_nearest = .ok result) ↔
      |x.toRat / y.toRat| < Number.top_plus_five := by
  sorry

/-- A quotient left out by `hrange`: it is below `Number.top_plus_five` in size, and `to_nearest` `x / y` fails with an
overflow error. -/
theorem Number.operator_div_ok_iff_to_nearest_attained :
    ∃ x y : Number,
      x.isNormalized ∧
      y.isNormalized ∧
      x.mantissa_ ≠ 0 ∧
      y.mantissa_ ≠ 0 ∧
      |x.toRat / y.toRat| < Number.top_plus_five ∧
      ∃ err,
        x.operator_div y .to_nearest = .error err ∧
        isOverflow err = true := by
  sorry

/-- `towards_zero` `x / y` succeeds exactly when the exact quotient is below `Number.top_plus_ten` in size. `hrange`
leaves out the quotients where the early overflow check differs (FV_M1_19). -/
theorem Number.operator_div_ok_iff_towards_zero (x y : Number)
    (hx : x.isNormalized) (hy : y.isNormalized) (hx0 : x.mantissa_ ≠ 0) (hy0 : y.mantissa_ ≠ 0)
    (hrange : |x.toRat / y.toRat| < Number.top_plus_one ∨ Number.top_plus_ten ≤ |x.toRat / y.toRat|) :
    (∃ result, x.operator_div y .towards_zero = .ok result) ↔
      |x.toRat / y.toRat| < Number.top_plus_ten := by
  sorry

/-- A quotient left out by `hrange`: it is below `Number.top_plus_ten` in size, and `towards_zero` `x / y` fails with an
overflow error. -/
theorem Number.operator_div_ok_iff_towards_zero_attained :
    ∃ x y : Number,
      x.isNormalized ∧
      y.isNormalized ∧
      x.mantissa_ ≠ 0 ∧
      y.mantissa_ ≠ 0 ∧
      |x.toRat / y.toRat| < Number.top_plus_ten ∧
      ∃ err,
        x.operator_div y .towards_zero = .error err ∧
        isOverflow err = true := by
  sorry

/-- `downward` `x / y` succeeds exactly when the exact quotient is at least `-Number.top` and below
`Number.top_plus_ten`. `hrange` leaves out the quotients where the early overflow check differs (FV_M1_19). -/
theorem Number.operator_div_ok_iff_downward (x y : Number)
    (hx : x.isNormalized) (hy : y.isNormalized) (hx0 : x.mantissa_ ≠ 0) (hy0 : y.mantissa_ ≠ 0)
    (hrange : (x.toRat / y.toRat ≤ -Number.top_plus_one ∨ -Number.top ≤ x.toRat / y.toRat) ∧
      (x.toRat / y.toRat < Number.top_plus_one ∨ Number.top_plus_ten ≤ x.toRat / y.toRat)) :
    (∃ result, x.operator_div y .downward = .ok result) ↔
      -Number.top ≤ x.toRat / y.toRat ∧ x.toRat / y.toRat < Number.top_plus_ten := by
  sorry

/-- A quotient left out by `hrange`: it is at least `-Number.top` and below `Number.top_plus_ten`, and `downward`
`x / y` fails with an overflow error. -/
theorem Number.operator_div_ok_iff_downward_attained :
    ∃ x y : Number,
      x.isNormalized ∧
      y.isNormalized ∧
      x.mantissa_ ≠ 0 ∧
      y.mantissa_ ≠ 0 ∧
      (-Number.top ≤ x.toRat / y.toRat ∧ x.toRat / y.toRat < Number.top_plus_ten) ∧
      ∃ err,
        x.operator_div y .downward = .error err ∧
        isOverflow err = true := by
  sorry

/-- `upward` `x / y` succeeds exactly when the exact quotient is above `-Number.top_plus_ten` and at most `Number.top`.
`hrange` leaves out the quotients where the early overflow check differs (FV_M1_19). -/
theorem Number.operator_div_ok_iff_upward (x y : Number)
    (hx : x.isNormalized) (hy : y.isNormalized) (hx0 : x.mantissa_ ≠ 0) (hy0 : y.mantissa_ ≠ 0)
    (hrange : (x.toRat / y.toRat ≤ -Number.top_plus_ten ∨ -Number.top_plus_one < x.toRat / y.toRat) ∧
      (x.toRat / y.toRat ≤ Number.top ∨ Number.top_plus_one ≤ x.toRat / y.toRat)) :
    (∃ result, x.operator_div y .upward = .ok result) ↔
      -Number.top_plus_ten < x.toRat / y.toRat ∧ x.toRat / y.toRat ≤ Number.top := by
  sorry

/-- A quotient left out by `hrange`: it is above `-Number.top_plus_ten` and at most `Number.top`, and `upward` `x / y`
fails with an overflow error. -/
theorem Number.operator_div_ok_iff_upward_attained :
    ∃ x y : Number,
      x.isNormalized ∧
      y.isNormalized ∧
      x.mantissa_ ≠ 0 ∧
      y.mantissa_ ≠ 0 ∧
      (-Number.top_plus_ten < x.toRat / y.toRat ∧ x.toRat / y.toRat ≤ Number.top) ∧
      ∃ err,
        x.operator_div y .upward = .error err ∧
        isOverflow err = true := by
  sorry

/-- In `to_nearest`, `x * y` succeeds exactly when the exact product is below `Number.top_plus_five` in size. -/
theorem Number.operator_mul_ok_iff_to_nearest (x y : Number)
    (hx : x.isNormalized) (hy : y.isNormalized) (hx0 : x.mantissa_ ≠ 0) (hy0 : y.mantissa_ ≠ 0) :
    (∃ result, x.operator_mul y .to_nearest = .ok result) ↔
      |x.toRat * y.toRat| < Number.top_plus_five := by
  sorry

/-- In `towards_zero`, `x * y` succeeds exactly when the exact product is below `Number.top_plus_ten` in size. -/
theorem Number.operator_mul_ok_iff_towards_zero (x y : Number)
    (hx : x.isNormalized) (hy : y.isNormalized) (hx0 : x.mantissa_ ≠ 0) (hy0 : y.mantissa_ ≠ 0) :
    (∃ result, x.operator_mul y .towards_zero = .ok result) ↔
      |x.toRat * y.toRat| < Number.top_plus_ten := by
  sorry

/-- In `downward`, `x * y` succeeds exactly when the exact product is at least `-Number.top` and below
`Number.top_plus_ten`. -/
theorem Number.operator_mul_ok_iff_downward (x y : Number)
    (hx : x.isNormalized) (hy : y.isNormalized) (hx0 : x.mantissa_ ≠ 0) (hy0 : y.mantissa_ ≠ 0) :
    (∃ result, x.operator_mul y .downward = .ok result) ↔
      -Number.top ≤ x.toRat * y.toRat ∧ x.toRat * y.toRat < Number.top_plus_ten := by
  sorry

/-- In `upward`, `x * y` succeeds exactly when the exact product is above `-Number.top_plus_ten` and at most
`Number.top`. -/
theorem Number.operator_mul_ok_iff_upward (x y : Number)
    (hx : x.isNormalized) (hy : y.isNormalized) (hx0 : x.mantissa_ ≠ 0) (hy0 : y.mantissa_ ≠ 0) :
    (∃ result, x.operator_mul y .upward = .ok result) ↔
      -Number.top_plus_ten < x.toRat * y.toRat ∧ x.toRat * y.toRat ≤ Number.top := by
  sorry

/-- In `to_nearest`, `x + y` fails with an overflow error when the exact sum is at least `Number.top_plus_five` in size.
-/
theorem Number.operator_add_overflow_to_nearest (x y : Number)
    (hx : x.isNormalized) (hy : y.isNormalized) (hx0 : x.mantissa_ ≠ 0) (hy0 : y.mantissa_ ≠ 0)
    (h : Number.top_plus_five ≤ |x.toRat + y.toRat|) :
    ∃ err, x.operator_add y .to_nearest = .error err ∧ isOverflow err = true := by
  sorry

/-- In `towards_zero`, `x + y` fails with an overflow error when the exact sum is at least `Number.top_plus_ten` in
size. -/
theorem Number.operator_add_overflow_towards_zero (x y : Number)
    (hx : x.isNormalized) (hy : y.isNormalized) (hx0 : x.mantissa_ ≠ 0) (hy0 : y.mantissa_ ≠ 0)
    (h : Number.top_plus_ten ≤ |x.toRat + y.toRat|) :
    ∃ err, x.operator_add y .towards_zero = .error err ∧ isOverflow err = true := by
  sorry

/-- `downward` `x + y` fails with an overflow error when the exact sum is below `-Number.top` or at least
`Number.top_plus_ten`. `hrange` leaves out the sums where the early overflow check differs (FV_M1_19). -/
theorem Number.operator_add_overflow_downward (x y : Number)
    (hx : x.isNormalized) (hy : y.isNormalized) (hx0 : x.mantissa_ ≠ 0) (hy0 : y.mantissa_ ≠ 0)
    (hrange : x.toRat + y.toRat ≤ -Number.top_plus_one ∨ -Number.top ≤ x.toRat + y.toRat)
    (h : x.toRat + y.toRat < -Number.top ∨ Number.top_plus_ten ≤ x.toRat + y.toRat) :
    ∃ err, x.operator_add y .downward = .error err ∧ isOverflow err = true := by
  sorry

/-- A sum left out by `hrange`: it is below `-Number.top`, and `downward` `x + y` returns a result. -/
theorem Number.operator_add_overflow_downward_attained :
    ∃ x y : Number,
      x.isNormalized ∧
      y.isNormalized ∧
      x.mantissa_ ≠ 0 ∧
      y.mantissa_ ≠ 0 ∧
      x.toRat + y.toRat < -Number.top ∧
      ∃ result,
        x.operator_add y .downward = .ok result := by
  sorry

/-- `upward` `x + y` fails with an overflow error when the exact sum is at most `-Number.top_plus_ten` or above
`Number.top`. `hrange` leaves out the sums where the early overflow check differs (FV_M1_19). -/
theorem Number.operator_add_overflow_upward (x y : Number)
    (hx : x.isNormalized) (hy : y.isNormalized) (hx0 : x.mantissa_ ≠ 0) (hy0 : y.mantissa_ ≠ 0)
    (hrange : x.toRat + y.toRat ≤ Number.top ∨ Number.top_plus_one ≤ x.toRat + y.toRat)
    (h : x.toRat + y.toRat ≤ -Number.top_plus_ten ∨ Number.top < x.toRat + y.toRat) :
    ∃ err, x.operator_add y .upward = .error err ∧ isOverflow err = true := by
  sorry

/-- A sum left out by `hrange`: it is above `Number.top`, and `upward` `x + y` returns a result. -/
theorem Number.operator_add_overflow_upward_attained :
    ∃ x y : Number,
      x.isNormalized ∧
      y.isNormalized ∧
      x.mantissa_ ≠ 0 ∧
      y.mantissa_ ≠ 0 ∧
      Number.top < x.toRat + y.toRat ∧
      ∃ result,
        x.operator_add y .upward = .ok result := by
  sorry

/-- In `to_nearest`, `x - y` fails with an overflow error when the exact difference is at least `Number.top_plus_five`
in size. -/
theorem Number.operator_sub_overflow_to_nearest (x y : Number)
    (hx : x.isNormalized) (hy : y.isNormalized) (hx0 : x.mantissa_ ≠ 0) (hy0 : y.mantissa_ ≠ 0)
    (h : Number.top_plus_five ≤ |x.toRat - y.toRat|) :
    ∃ err, x.operator_sub y .to_nearest = .error err ∧ isOverflow err = true := by
  sorry

/-- In `towards_zero`, `x - y` fails with an overflow error when the exact difference is at least `Number.top_plus_ten`
in size. -/
theorem Number.operator_sub_overflow_towards_zero (x y : Number)
    (hx : x.isNormalized) (hy : y.isNormalized) (hx0 : x.mantissa_ ≠ 0) (hy0 : y.mantissa_ ≠ 0)
    (h : Number.top_plus_ten ≤ |x.toRat - y.toRat|) :
    ∃ err, x.operator_sub y .towards_zero = .error err ∧ isOverflow err = true := by
  sorry

/-- `downward` `x - y` fails with an overflow error when the exact difference is below `-Number.top` or at least
`Number.top_plus_ten`. `hrange` leaves out the differences where the early overflow check differs (FV_M1_19). -/
theorem Number.operator_sub_overflow_downward (x y : Number)
    (hx : x.isNormalized) (hy : y.isNormalized) (hx0 : x.mantissa_ ≠ 0) (hy0 : y.mantissa_ ≠ 0)
    (hrange : x.toRat - y.toRat ≤ -Number.top_plus_one ∨ -Number.top ≤ x.toRat - y.toRat)
    (h : x.toRat - y.toRat < -Number.top ∨ Number.top_plus_ten ≤ x.toRat - y.toRat) :
    ∃ err, x.operator_sub y .downward = .error err ∧ isOverflow err = true := by
  sorry

/-- A difference left out by `hrange`: it is below `-Number.top`, and `downward` `x - y` returns a result. -/
theorem Number.operator_sub_overflow_downward_attained :
    ∃ x y : Number,
      x.isNormalized ∧
      y.isNormalized ∧
      x.mantissa_ ≠ 0 ∧
      y.mantissa_ ≠ 0 ∧
      x.toRat - y.toRat < -Number.top ∧
      ∃ result,
        x.operator_sub y .downward = .ok result := by
  sorry

/-- `upward` `x - y` fails with an overflow error when the exact difference is at most `-Number.top_plus_ten` or above
`Number.top`. `hrange` leaves out the differences where the early overflow check differs (FV_M1_19). -/
theorem Number.operator_sub_overflow_upward (x y : Number)
    (hx : x.isNormalized) (hy : y.isNormalized) (hx0 : x.mantissa_ ≠ 0) (hy0 : y.mantissa_ ≠ 0)
    (hrange : x.toRat - y.toRat ≤ Number.top ∨ Number.top_plus_one ≤ x.toRat - y.toRat)
    (h : x.toRat - y.toRat ≤ -Number.top_plus_ten ∨ Number.top < x.toRat - y.toRat) :
    ∃ err, x.operator_sub y .upward = .error err ∧ isOverflow err = true := by
  sorry

/-- A difference left out by `hrange`: it is above `Number.top`, and `upward` `x - y` returns a result. -/
theorem Number.operator_sub_overflow_upward_attained :
    ∃ x y : Number,
      x.isNormalized ∧
      y.isNormalized ∧
      x.mantissa_ ≠ 0 ∧
      y.mantissa_ ≠ 0 ∧
      Number.top < x.toRat - y.toRat ∧
      ∃ result,
        x.operator_sub y .upward = .ok result := by
  sorry

/-- In `to_nearest`, `x / y` fails with an overflow error when the exact quotient is at least `Number.top_plus_five` in
size. -/
theorem Number.operator_div_overflow_to_nearest (x y : Number)
    (hx : x.isNormalized) (hy : y.isNormalized) (hx0 : x.mantissa_ ≠ 0) (hy0 : y.mantissa_ ≠ 0)
    (h : Number.top_plus_five ≤ |x.toRat / y.toRat|) :
    ∃ err, x.operator_div y .to_nearest = .error err ∧ isOverflow err = true := by
  sorry

/-- In `towards_zero`, `x / y` fails with an overflow error when the exact quotient is at least `Number.top_plus_ten` in
size. -/
theorem Number.operator_div_overflow_towards_zero (x y : Number)
    (hx : x.isNormalized) (hy : y.isNormalized) (hx0 : x.mantissa_ ≠ 0) (hy0 : y.mantissa_ ≠ 0)
    (h : Number.top_plus_ten ≤ |x.toRat / y.toRat|) :
    ∃ err, x.operator_div y .towards_zero = .error err ∧ isOverflow err = true := by
  sorry

/-- `downward` `x / y` fails with an overflow error when the exact quotient is below `-Number.top` or at least
`Number.top_plus_ten`. `hrange` leaves out the quotients where the early overflow check differs (FV_M1_19). -/
theorem Number.operator_div_overflow_downward (x y : Number)
    (hx : x.isNormalized) (hy : y.isNormalized) (hx0 : x.mantissa_ ≠ 0) (hy0 : y.mantissa_ ≠ 0)
    (hrange : x.toRat / y.toRat ≤ -Number.top_plus_one ∨ -Number.top ≤ x.toRat / y.toRat)
    (h : x.toRat / y.toRat < -Number.top ∨ Number.top_plus_ten ≤ x.toRat / y.toRat) :
    ∃ err, x.operator_div y .downward = .error err ∧ isOverflow err = true := by
  sorry

/-- A quotient left out by `hrange`: it is below `-Number.top`, and `downward` `x / y` returns a result. -/
theorem Number.operator_div_overflow_downward_attained :
    ∃ x y : Number,
      x.isNormalized ∧
      y.isNormalized ∧
      x.mantissa_ ≠ 0 ∧
      y.mantissa_ ≠ 0 ∧
      x.toRat / y.toRat < -Number.top ∧
      ∃ result,
        x.operator_div y .downward = .ok result := by
  sorry

/-- `upward` `x / y` fails with an overflow error when the exact quotient is at most `-Number.top_plus_ten` or above
`Number.top`. `hrange` leaves out the quotients where the early overflow check differs (FV_M1_19). -/
theorem Number.operator_div_overflow_upward (x y : Number)
    (hx : x.isNormalized) (hy : y.isNormalized) (hx0 : x.mantissa_ ≠ 0) (hy0 : y.mantissa_ ≠ 0)
    (hrange : x.toRat / y.toRat ≤ Number.top ∨ Number.top_plus_one ≤ x.toRat / y.toRat)
    (h : x.toRat / y.toRat ≤ -Number.top_plus_ten ∨ Number.top < x.toRat / y.toRat) :
    ∃ err, x.operator_div y .upward = .error err ∧ isOverflow err = true := by
  sorry

/-- A quotient left out by `hrange`: it is above `Number.top`, and `upward` `x / y` returns a result. -/
theorem Number.operator_div_overflow_upward_attained :
    ∃ x y : Number,
      x.isNormalized ∧
      y.isNormalized ∧
      x.mantissa_ ≠ 0 ∧
      y.mantissa_ ≠ 0 ∧
      Number.top < x.toRat / y.toRat ∧
      ∃ result,
        x.operator_div y .upward = .ok result := by
  sorry

/-- In `to_nearest`, `x * y` fails with an overflow error when the exact product is at least `Number.top_plus_five` in
size. -/
theorem Number.operator_mul_overflow_to_nearest (x y : Number)
    (hx : x.isNormalized) (hy : y.isNormalized) (hx0 : x.mantissa_ ≠ 0) (hy0 : y.mantissa_ ≠ 0)
    (h : Number.top_plus_five ≤ |x.toRat * y.toRat|) :
    ∃ err, x.operator_mul y .to_nearest = .error err ∧ isOverflow err = true := by
  sorry

/-- In `towards_zero`, `x * y` fails with an overflow error when the exact product is at least `Number.top_plus_ten` in
size. -/
theorem Number.operator_mul_overflow_towards_zero (x y : Number)
    (hx : x.isNormalized) (hy : y.isNormalized) (hx0 : x.mantissa_ ≠ 0) (hy0 : y.mantissa_ ≠ 0)
    (h : Number.top_plus_ten ≤ |x.toRat * y.toRat|) :
    ∃ err, x.operator_mul y .towards_zero = .error err ∧ isOverflow err = true := by
  sorry

/-- In `downward`, `x * y` fails with an overflow error when the exact product is below `-Number.top` or at least
`Number.top_plus_ten`. -/
theorem Number.operator_mul_overflow_downward (x y : Number)
    (hx : x.isNormalized) (hy : y.isNormalized) (hx0 : x.mantissa_ ≠ 0) (hy0 : y.mantissa_ ≠ 0)
    (h : x.toRat * y.toRat < -Number.top ∨ Number.top_plus_ten ≤ x.toRat * y.toRat) :
    ∃ err, x.operator_mul y .downward = .error err ∧ isOverflow err = true := by
  sorry

/-- In `upward`, `x * y` fails with an overflow error when the exact product is at most `-Number.top_plus_ten` or above
`Number.top`. -/
theorem Number.operator_mul_overflow_upward (x y : Number)
    (hx : x.isNormalized) (hy : y.isNormalized) (hx0 : x.mantissa_ ≠ 0) (hy0 : y.mantissa_ ≠ 0)
    (h : x.toRat * y.toRat ≤ -Number.top_plus_ten ∨ Number.top < x.toRat * y.toRat) :
    ∃ err, x.operator_mul y .upward = .error err ∧ isOverflow err = true := by
  sorry

end XRPL.Model.Protocol
