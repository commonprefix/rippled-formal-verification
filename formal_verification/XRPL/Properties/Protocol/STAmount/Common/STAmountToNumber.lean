import XRPL.Properties.Protocol.STAmount.Mul.Common.IOU
import XRPL.Properties.Protocol.STAmount.Add.Common.Integral
import XRPL.Properties.Protocol.IntAmount.ToNumber.ToNumber
import XRPL.Properties.Protocol.Common.AmountArith
import XRPL.Properties.Protocol.Number.Common.Constants

/-! # `STAmount.toNumber` exactness on canonical amounts

Amounts produced by `ofNumber` and `roundToExponent` are canonical for their
type. The `Number` tree proves `toNumber` exactness for the two canonical shapes
separately. This file packages both into one value-exact, normalized `Number`
statement.

* fractional (`IOUCanonical`): `toNumber` is the exact 19-digit lift.
* integral (`IntegralCanonical`, mantissa fits `Int64`): `toNumber` routes through
  `IntAmount.toNumber`, exact and integer-valued (`den = 1`). This also covers the
  integral zero. -/

namespace XRPL.Model.Protocol

/-- **`toNumber` is value-exact and normalized on a canonical IOU amount.** The
19-digit lift preserves the value and is normalized. -/
lemma STAmount.toNumber_iou_exact (s : STAmount) (mode : rounding_mode)
    (hc : s.IOUCanonical) :
    ∃ sn : Number, s.toNumber mode = .ok sn ∧ sn.toRat = s.toRat ∧ sn.isNormalized :=
  ⟨⟨s.mIsNegative, s.mValue * 10 * 10 * 10, s.mOffset - 3⟩,
    STAmount.toNumber_iou_canonical s mode hc,
    STAmount.toNumber_iou_canonical_toRat s hc,
    STAmount.toNumber_iou_canonical_isNormalized s hc⟩

/-- The value of a canonical (offset-`0`) integral amount is the cast of its
signed drops, an integer. -/
lemma STAmount.IntegralCanonical.toRat_eq_signedDrops (s : STAmount)
    (hc : s.IntegralCanonical) :
    s.toRat = (s.signedDrops : ℚ) :=
  STAmount.toRat_of_offset_zero s hc.offset_zero

/-- A canonical integral amount whose magnitude fits `2^63 - 1` has a value
within `2^63 - 1` of zero. -/
lemma STAmount.IntegralCanonical.abs_toRat_le_of_mValue_le (s : STAmount) (hc : s.IntegralCanonical)
    (hsz : s.mValue.toNat ≤ 2 ^ 63 - 1) : |s.toRat| ≤ 2 ^ 63 - 1 := by
  rw [STAmount.abs_toRat, hc.offset_zero, zpow_zero, mul_one]
  have h1 : (s.mValue.toNat : ℚ) ≤ ((2 ^ 63 - 1 : ℕ) : ℚ) := by exact_mod_cast hsz
  have h2 : ((2 ^ 63 - 1 : ℕ) : ℚ) = 2 ^ 63 - 1 := by norm_num
  linarith

/-- A canonical integral amount is integer-valued. -/
lemma STAmount.IntegralCanonical.den_eq_one (s : STAmount) (hc : s.IntegralCanonical) :
    s.toRat.den = 1 := by
  rw [STAmount.IntegralCanonical.toRat_eq_signedDrops s hc]
  exact Rat.den_intCast _

/-- **`toNumber` is value-exact, normalized, and integer-valued on an offset-`0`
integral amount within `maxRep`.** It needs no bound from the numeric type, so it
also covers custom integral types whose bound exceeds `maxRep`. -/
lemma STAmount.toNumber_offset_zero_exact (s : STAmount) (mode : rounding_mode)
    (hint : s.mNumericType.isIntegral = true) (hoff : s.mOffset = 0)
    (hval : s.mValue.toNat ≤ maxRep.toNat) :
    ∃ sn : Number, s.toNumber mode = .ok sn ∧ sn.toRat = s.toRat ∧ sn.isNormalized ∧
      s.toRat.den = 1 := by
  have hint' : s.integral = true := hint
  have hbnd : s.mValue.toNat ≤ 9223372036854775807 := by rw [maxRep_val] at hval; exact hval
  have hmin : Int64.minValue.toInt = (-9223372036854775808 : ℤ) := by decide
  have hmax' : Int64.maxValue.toInt = (9223372036854775807 : ℤ) := by decide
  have hsd_lo : Int64.minValue.toInt ≤ s.signedDrops := by
    unfold STAmount.signedDrops; rw [hmin]; split <;> omega
  have hsd_hi : s.signedDrops ≤ Int64.maxValue.toInt := by
    unfold STAmount.signedDrops; rw [hmax']; split <;> omega
  have hsd_toInt : s.signedDrops.toInt64.toInt = s.signedDrops :=
    AmountArith.toInt_toInt64_self hsd_lo hsd_hi
  have h_ne_min : s.signedDrops.toInt64 ≠ Int64.minValue := by
    intro h
    have heq : s.signedDrops.toInt64.toInt = Int64.minValue.toInt := by rw [h]
    rw [hsd_toInt, hmin] at heq
    revert heq
    unfold STAmount.signedDrops
    split <;> omega
  have hroute : s.toNumber mode = IntAmount.toNumber ⟨s.signedDrops.toInt64⟩ mode := by
    unfold STAmount.toNumber STAmount.intAmount
    rw [if_pos hint', if_pos hint']
  obtain ⟨xn, hokn, hvaln, hnorm⟩ :=
    IntAmount.toNumber_exact ⟨s.signedDrops.toInt64⟩ mode h_ne_min
  have hsd_val : s.toRat = (s.signedDrops : ℚ) := STAmount.toRat_of_offset_zero s hoff
  refine ⟨xn, by rw [hroute]; exact hokn, ?_, hnorm, ?_⟩
  · rw [hvaln]
    show (s.signedDrops.toInt64.toInt : ℚ) = s.toRat
    rw [hsd_toInt, hsd_val]
  · rw [hsd_val]
    exact Rat.den_intCast _

/-- `toNumber` exactness on a small canonical integral amount (the size bound on
the stored magnitude replaces the type-level `maxValue` bound). -/
lemma STAmount.toNumber_integral_small_exact (s : STAmount) (mode : rounding_mode)
    (hc : s.IntegralCanonical) (hsz : s.mValue.toNat ≤ 2 ^ 63 - 1) :
    ∃ sn : Number, s.toNumber mode = .ok sn ∧ sn.toRat = s.toRat ∧ sn.isNormalized := by
  obtain ⟨sn, hok, hv, hn, -⟩ := STAmount.toNumber_offset_zero_exact s mode hc.is_integral
    hc.offset_zero (by rw [maxRep_val]; omega)
  exact ⟨sn, hok, hv, hn⟩

/-- **`toNumber` is value-exact, normalized, and integer-valued on a canonical
integral amount** whose type's `maxValue` fits `maxRep`, as for `native` and
`int64`. This also covers the integral zero. -/
lemma STAmount.toNumber_integral_exact (s : STAmount) (mode : rounding_mode)
    (hc : s.IntegralCanonical)
    (hmax : s.mNumericType.maxValue.toNat ≤ maxRep.toNat) :
    ∃ sn : Number, s.toNumber mode = .ok sn ∧ sn.toRat = s.toRat ∧ sn.isNormalized ∧
      s.toRat.den = 1 :=
  STAmount.toNumber_offset_zero_exact s mode hc.is_integral hc.offset_zero
    (le_trans hc.in_range hmax)

/-- The canonical storage shapes `toNumber` is value-exact on: the fractional
canonical form, or the integral canonical form with the stored magnitude within
`Int64`. -/
def STAmount.ExactCanonical (s : STAmount) : Prop :=
  s.IOUCanonical ∨ (s.IntegralCanonical ∧ s.mValue.toNat ≤ 2 ^ 63 - 1)

/-- A canonical amount that is not integral is in the fractional canonical form. -/
lemma STAmount.ExactCanonical.iouCanonical {s : STAmount} (hc : s.ExactCanonical)
    (hfr : s.integral = false) : s.IOUCanonical :=
  hc.resolve_right fun h => Bool.false_ne_true (hfr.symm.trans h.1.is_integral)

/-- A canonical amount that is integral is in the integral canonical form, within
`Int64`. -/
lemma STAmount.ExactCanonical.integralCanonical {s : STAmount} (hc : s.ExactCanonical)
    (hint : s.integral = true) : s.IntegralCanonical ∧ s.mValue.toNat ≤ 2 ^ 63 - 1 :=
  hc.resolve_left fun h => by
    have hfr : s.integral = false := by unfold STAmount.integral; rw [h.is_fractional]; rfl
    rw [hint] at hfr
    exact absurd hfr (by decide)

/-- `toNumber` is value-exact and normalized on any `ExactCanonical` amount. -/
lemma STAmount.toNumber_exact_canonical (s : STAmount) (mode : rounding_mode)
    (hc : s.ExactCanonical) :
    ∃ sn : Number, s.toNumber mode = .ok sn ∧ sn.toRat = s.toRat ∧ sn.isNormalized := by
  rcases hc with hiou | ⟨hint, hsz⟩
  · exact STAmount.toNumber_iou_exact s mode hiou
  · exact STAmount.toNumber_integral_small_exact s mode hint hsz

/-- A canonical amount converts to a normalized `Number` of the same value. -/
lemma STAmount.toNumber_exact_of (a : STAmount) (m : Number) (hc : a.ExactCanonical)
    (h : a.toNumber .to_nearest = .ok m) : m.toRat = a.toRat ∧ m.isNormalized := by
  obtain ⟨sn, hsn, hv, hn⟩ := STAmount.toNumber_exact_canonical a .to_nearest hc
  rw [hsn, Except.ok.injEq] at h
  subst h
  exact ⟨hv, hn⟩

end XRPL.Model.Protocol
