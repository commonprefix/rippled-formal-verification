import XRPL.Properties.Protocol.STAmount.Range.Success

/-! # When the `STAmount` operations fail

An operation returns an error when its exact value, rounded once in the mode, is not an amount of the type. XRP add
and subtract never fail (FV_M1_24). An MPT sum past int64, or equal to `-2^63`, wraps (FV_M1_26). -/

namespace XRPL.Model.Protocol

/-- For a Number that is not negative, or in `to_nearest` or `towards_zero` (`hsign`), the conversion to an
amount fails when the Number rounds out of the range of the type. -/
theorem STAmount.ofNumber_overflow (nt : NumericType) (n : Number) (mode : rounding_mode) (hn : n.isNormalized)
    (hnt : nt = .fractional ∨ nt = NumericType.native ∨ nt = NumericType.int64)
    (hsign : 0 ≤ n.toRat ∨ mode = .to_nearest ∨ mode = .towards_zero)
    (h : ¬ STAmount.RoundsInRange nt mode n.toRat) :
    ∃ err, STAmount.ofNumber nt n mode = .error err := by
  sorry

/-- With a mantissa within int64 (`hm`), making an amount from a mantissa and an exponent fails when
`mantissa * 10 ^ exponent` rounds out of the range of the type. -/
theorem STAmount.checked_overflow (nt : NumericType) (m : UInt64) (e : Int) (neg : Bool) (mode : rounding_mode)
    (hnt : nt = .fractional ∨ nt = NumericType.native ∨ nt = NumericType.int64)
    (hm : m ≤ maxRep)
    (h : ¬ STAmount.RoundsInRange nt mode (STAmount.unchecked nt m e neg).toRat) :
    ∃ err, STAmount.checked nt m e neg mode = .error err := by
  sorry

/-- IOU addition fails when the exact sum rounds out of the IOU range. In `to_nearest` the exact sum must
itself be a Number (`hfit`). -/
theorem STAmount.operator_add_overflow_iou (v1 v2 : STAmount) (mode : rounding_mode) (h1 : v1.IOUCanonical)
    (h2 : v2.IOUCanonical)
    (hfit : mode = .to_nearest → ∃ n : Number, n.isNormalized ∧ n.toRat = v1.toRat + v2.toRat)
    (h : ¬ STAmount.RoundsInRange .fractional mode (v1.toRat + v2.toRat)) :
    ∃ err, STAmount.operator_add v1 v2 mode = .error err := by
  sorry

/-- MPT addition fails when the sum is out of the MPT range. -/
theorem STAmount.operator_add_overflow_mpt (v1 v2 : STAmount) (mode : rounding_mode)
    (h1 : v1.IntegralCanonical) (h2 : v2.IntegralCanonical)
    (ht1 : v1.mNumericType = NumericType.int64) (ht2 : v2.mNumericType = NumericType.int64)
    (h : ¬ STAmount.RoundsInRange NumericType.int64 mode (v1.toRat + v2.toRat)) :
    ∃ err, STAmount.operator_add v1 v2 mode = .error err := by
  sorry

/-- IOU subtraction fails when the exact difference rounds out of the IOU range. In `to_nearest` the exact
difference must itself be a Number (`hfit`). -/
theorem STAmount.operator_sub_overflow_iou (v1 v2 : STAmount) (mode : rounding_mode) (h1 : v1.IOUCanonical)
    (h2 : v2.IOUCanonical)
    (hfit : mode = .to_nearest → ∃ n : Number, n.isNormalized ∧ n.toRat = v1.toRat - v2.toRat)
    (h : ¬ STAmount.RoundsInRange .fractional mode (v1.toRat - v2.toRat)) :
    ∃ err, STAmount.operator_sub v1 v2 mode = .error err := by
  sorry

/-- MPT subtraction fails when the difference is out of the MPT range. -/
theorem STAmount.operator_sub_overflow_mpt (v1 v2 : STAmount) (mode : rounding_mode)
    (h1 : v1.IntegralCanonical) (h2 : v2.IntegralCanonical)
    (ht1 : v1.mNumericType = NumericType.int64) (ht2 : v2.mNumericType = NumericType.int64)
    (h : ¬ STAmount.RoundsInRange NumericType.int64 mode (v1.toRat - v2.toRat)) :
    ∃ err, STAmount.operator_sub v1 v2 mode = .error err := by
  sorry

/-- An MPT sum above `2^63 - 1` whose int64 addition wraps around: `(2^63 - 1) + 2`. -/
theorem STAmount.operator_add_overflow_mpt_attained :
    ∃ (v1 v2 : STAmount) (mode : rounding_mode),
      v1.IntegralCanonical ∧
      v2.IntegralCanonical ∧
      v1.mNumericType = NumericType.int64 ∧
      v2.mNumericType = NumericType.int64 ∧
      ¬ STAmount.RoundsInRange NumericType.int64 mode (v1.toRat + v2.toRat) ∧
      STAmount.operator_add v1 v2 mode = .error .wrap := by
  sorry

/-- An MPT difference above `2^63 - 1` whose int64 addition wraps around: `(2^63 - 1) - (-2)`. -/
theorem STAmount.operator_sub_overflow_mpt_attained :
    ∃ (v1 v2 : STAmount) (mode : rounding_mode),
      v1.IntegralCanonical ∧
      v2.IntegralCanonical ∧
      v1.mNumericType = NumericType.int64 ∧
      v2.mNumericType = NumericType.int64 ∧
      ¬ STAmount.RoundsInRange NumericType.int64 mode (v1.toRat - v2.toRat) ∧
      STAmount.operator_sub v1 v2 mode = .error .wrap := by
  sorry

/-- The MPT sum `-2^63`, where negating the int64 sum wraps around: `-(2^63 - 1) + -1`. -/
theorem STAmount.operator_add_overflow_mpt_minInt64_attained :
    ∃ (v1 v2 : STAmount) (mode : rounding_mode),
      v1.IntegralCanonical ∧
      v2.IntegralCanonical ∧
      v1.mNumericType = NumericType.int64 ∧
      v2.mNumericType = NumericType.int64 ∧
      ¬ STAmount.RoundsInRange NumericType.int64 mode (v1.toRat + v2.toRat) ∧
      STAmount.operator_add v1 v2 mode = .error .wrap := by
  sorry

/-- The MPT difference `-2^63`, where negating the int64 sum wraps around: `-(2^63 - 1) - 1`. -/
theorem STAmount.operator_sub_overflow_mpt_minInt64_attained :
    ∃ (v1 v2 : STAmount) (mode : rounding_mode),
      v1.IntegralCanonical ∧
      v2.IntegralCanonical ∧
      v1.mNumericType = NumericType.int64 ∧
      v2.mNumericType = NumericType.int64 ∧
      ¬ STAmount.RoundsInRange NumericType.int64 mode (v1.toRat - v2.toRat) ∧
      STAmount.operator_sub v1 v2 mode = .error .wrap := by
  sorry

end XRPL.Model.Protocol
