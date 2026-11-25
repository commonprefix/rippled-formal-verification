import XRPL.Model.Protocol.Rounding
import XRPL.Properties.Protocol.Number.Common.Constants
import XRPL.Properties.Protocol.Number.Common.ToRatLemmas
import XRPL.Properties.Protocol.Number.Common.Closest.Tightness
import XRPL.Properties.Protocol.Number.Common.Closest.GridPoint
import XRPL.Properties.Protocol.Number.Constructors.FromRepExact
import XRPL.Properties.Protocol.Number.Sub.RoundsToRepresentable
import XRPL.Properties.Protocol.Number.Totality

/-! # Amounts held at an exponent

`Number.isAtExponent` says a value is a whole number of units at an exponent. A `to_nearest` subtraction of two such
amounts succeeds and is exact while the difference stays below `2^63` units. -/

namespace XRPL.Model.Protocol

/-- The exact reading of `Number.isAtExponent`: a whole number of units at the exponent, below the bound. -/
def Number.AtExponent (value : ℚ) (exponent : Int) (bound : ℕ) : Prop :=
  ∃ m : ℕ, m < bound ∧ value = (m : ℚ) * (10 : ℚ) ^ exponent

lemma NumericType.mantissaBound_pos (nt : NumericType) : 0 < nt.mantissaBound := by
  sorry

lemma NumericType.mantissaBound_le (nt : NumericType) : nt.mantissaBound ≤ 2 ^ 63 := by
  sorry

/-- Every integer count below `2^63` units at a scale with exponent room is a normalized `Number`. -/
lemma Number.exists_normalized_int_mul_pow (a : ℤ) (s : Int)
    (ha : -2 ^ 63 < a ∧ a < 2 ^ 63) (hs : minExponent + 18 ≤ s ∧ s ≤ maxExponent - 1) :
    ∃ w : Number, w.isNormalized ∧ w.toRat = (a : ℚ) * (10 : ℚ) ^ s := by
  sorry

/-- A `to_nearest` rounding of a representable value is that value. -/
lemma Number.roundsToRepresentable_eq (d : Number) (truth : ℚ)
    (hR : d.RoundsToRepresentable truth .to_nearest) (w : Number) (hw : w.isNormalized)
    (hwt : w.toRat = truth) : d.toRat = truth := by
  sorry

/-- A `to_nearest` sum that fits a `Number` is exact. -/
lemma Number.operator_add_exact_of_fits {x y r : Number} (hx : x.isNormalized) (hy : y.isNormalized)
    (hok : x.operator_add y .to_nearest = .ok r)
    (hfit : ∃ w : Number, w.isNormalized ∧ w.toRat = x.toRat + y.toRat) : r.toRat = x.toRat + y.toRat := by
  sorry

/-- A `to_nearest` difference that fits a `Number` is exact. -/
lemma Number.operator_sub_exact_of_fits {x y r : Number} (hx : x.isNormalized) (hy : y.isNormalized)
    (hok : x.operator_sub y .to_nearest = .ok r)
    (hfit : ∃ w : Number, w.isNormalized ∧ w.toRat = x.toRat - y.toRat) : r.toRat = x.toRat - y.toRat := by
  sorry

/-- A `to_nearest` rounding never lands above a representable value that bounds the truth. -/
lemma Number.roundsToRepresentable_le (d : Number) (truth : ℚ)
    (hR : d.RoundsToRepresentable truth .to_nearest) (w : Number) (hw : w.isNormalized)
    (hwt : truth ≤ w.toRat) : d.toRat ≤ w.toRat := by
  sorry

/-- A `to_nearest` rounding never lands below a representable value under the truth. -/
lemma Number.roundsToRepresentable_ge (d : Number) (truth : ℚ)
    (hR : d.RoundsToRepresentable truth .to_nearest) (w : Number) (hw : w.isNormalized)
    (hwt : w.toRat ≤ truth) : w.toRat ≤ d.toRat := by
  sorry

/-- A nonzero normalized nonnegative `Number` below `10^19` units at a scale has its exponent at
most the scale: its 19-digit mantissa cannot sit any higher. -/
lemma Number.exponent_le_of_toRat_lt_of_ne (n : Number) (s : Int) (hn : n.isNormalized)
    (hneg : n.negative_ = false) (hm0 : n.mantissa_ ≠ 0)
    (hlt : n.toRat < (10 : ℚ) ^ (19 : ℕ) * (10 : ℚ) ^ s) : n.exponent_ ≤ s := by
  sorry

/-- The same bound for any normalized nonnegative `Number`, given the scale is in exponent range. -/
lemma Number.exponent_le_of_toRat_lt (n : Number) (s : Int) (hn : n.isNormalized)
    (hneg : n.negative_ = false) (hs : minExponent + 18 ≤ s)
    (hlt : n.toRat < (10 : ℚ) ^ (19 : ℕ) * (10 : ℚ) ^ s) : n.exponent_ ≤ s := by
  sorry

/-- `Number.isAtExponent` read exactly, for a normalized nonnegative amount. -/
theorem Number.isAtExponent_iff (value : Number) (exponent : Int) (nt : NumericType) (hn : value.isNormalized)
    (hnn : 0 ≤ value.toRat) :
    value.isAtExponent exponent nt = true ↔ Number.AtExponent value.toRat exponent nt.mantissaBound := by
  sorry

/-- A successful `to_nearest` subtraction of two whole-unit amounts at one scale is exact while the
difference stays below `2^63` units. -/
lemma Number.operator_sub_toRat_of_grid (x y d : Number) (a b : ℤ) (s : Int)
    (hx : x.isNormalized) (hy : y.isNormalized)
    (hxv : x.toRat = (a : ℚ) * (10 : ℚ) ^ s) (hyv : y.toRat = (b : ℚ) * (10 : ℚ) ^ s)
    (hab : -2 ^ 63 < a - b ∧ a - b < 2 ^ 63) (hs : minExponent + 18 ≤ s ∧ s ≤ maxExponent - 1)
    (hok : x.operator_sub y .to_nearest = .ok d) :
    d.toRat = ((a - b : ℤ) : ℚ) * (10 : ℚ) ^ s := by
  sorry

/-- A successful `to_nearest` addition of two whole-unit amounts at one scale is exact while the
sum stays below `2^63` units. -/
lemma Number.operator_add_toRat_of_grid (x y d : Number) (a b : ℤ) (s : Int)
    (hx : x.isNormalized) (hy : y.isNormalized)
    (hxv : x.toRat = (a : ℚ) * (10 : ℚ) ^ s) (hyv : y.toRat = (b : ℚ) * (10 : ℚ) ^ s)
    (hab : -2 ^ 63 < a + b ∧ a + b < 2 ^ 63) (hs : minExponent + 18 ≤ s ∧ s ≤ maxExponent - 1)
    (hok : x.operator_add y .to_nearest = .ok d) :
    d.toRat = ((a + b : ℤ) : ℚ) * (10 : ℚ) ^ s := by
  sorry

/-- Subtracting two nonnegative whole-unit amounts below `2^63` units at an STAmount scale always succeeds. -/
lemma Number.operator_sub_ok_of_grid (x y : Number) (a b : ℕ) (s : Int)
    (hx : x.isNormalized) (hy : y.isNormalized)
    (hxv : x.toRat = (a : ℚ) * (10 : ℚ) ^ s) (hyv : y.toRat = (b : ℚ) * (10 : ℚ) ^ s)
    (ha : a < 2 ^ 63) (hb : b < 2 ^ 63) (hs : cMinOffset ≤ s ∧ s ≤ cMaxOffset) :
    ∃ d, x.operator_sub y .to_nearest = .ok d := by
  sorry

/-- An integer in `(-2^63, 2^63)` is a normalized `Number`. -/
lemma Number.exists_of_int (q : ℚ) (hd : q.den = 1) (hlo : -2 ^ 63 < q) (hhi : q < 2 ^ 63) :
    ∃ w : Number, w.isNormalized ∧ w.toRat = q := by
  sorry

/-- A normalized nonnegative `Number` below `10 ^ 96` leaves the headroom
`operator_add` needs. -/
lemma Number.exponent_headroom_of_lt (n : Number) (hn : n.isNormalized) (h0 : 0 ≤ n.toRat)
    (hlt : n.toRat < 10 ^ 96) : n.exponent_ + 22 ≤ maxExponent := by
  sorry

/-- Adding two nonnegative normalized values below `10^96` never throws. -/
lemma Number.operator_add_ok_of_lt (x y : Number) (mode : rounding_mode) (hx : x.isNormalized)
    (hy : y.isNormalized) (hx0 : 0 ≤ x.toRat) (hxlt : x.toRat < 10 ^ 96) (hy0 : 0 ≤ y.toRat)
    (hylt : y.toRat < 10 ^ 96) : ∃ result, x.operator_add y mode = .ok result := by
  sorry

/-- Subtracting two nonnegative normalized values below `10^96` never throws. -/
lemma Number.operator_sub_ok_of_lt (x y : Number) (mode : rounding_mode) (hx : x.isNormalized)
    (hy : y.isNormalized) (hx0 : 0 ≤ x.toRat) (hxlt : x.toRat < 10 ^ 96) (hy0 : 0 ≤ y.toRat)
    (hylt : y.toRat < 10 ^ 96) : ∃ result, x.operator_sub y mode = .ok result := by
  sorry

/-- Subtracting zero gives the same `Number`, in every rounding mode. -/
lemma Number.operator_sub_zero (x : Number) (mode : rounding_mode) :
    x.operator_sub Number.zero mode = .ok x := by
  sorry

/-- Rounding up keeps the order of the values. A result that is zero, or that rounds a smaller nonnegative
value up, is at most a result that rounds a larger value up. -/
lemma Number.toRat_le_of_rounds_upward (q q' : Number) (t t' : ℚ) (hq' : q'.isNormalized)
    (ht : 0 ≤ t) (htt : t ≤ t')
    (hq : q.mantissa_ = 0 ∨ Number.RoundsToRepresentable q t .upward)
    (hr' : Number.RoundsToRepresentable q' t' .upward) :
    q.toRat ≤ q'.toRat := by
  sorry

/-- A larger positive normalized `Number` never has a smaller exponent. -/
lemma Number.exponent_le_of_le (x y : Number) (hx : x.isNormalized) (hy : y.isNormalized)
    (hx0 : x.mantissa_ ≠ 0) (hpos : 0 < x.toRat) (hxy : x.toRat ≤ y.toRat) :
    x.exponent_ ≤ y.exponent_ := by
  sorry

end XRPL.Model.Protocol
