import XRPL.Properties.Protocol.STAmount.Range.Common.OfNumber
import XRPL.Properties.Protocol.STAmount.Range.Common.CheckedIOU
import XRPL.Properties.Protocol.STAmount.Range.Common.IntegralAdd
import XRPL.Properties.Protocol.STAmount.Range.Common.IOUAdd
import XRPL.Properties.Protocol.STAmount.Range.Common.Witnesses

/-! # When the `STAmount` operations return a result

An operation should succeed exactly when its exact value, rounded once in the mode, is an amount of the type `nt`.
Where the code breaks this, the theorem carries one hypothesis that keeps the bug out, and an `_attained` witness. -/

namespace XRPL.Model.Protocol

/-- For a Number that is not negative, or in `to_nearest` or `towards_zero` (`hsign`), the conversion to an
amount returns a result exactly when the Number rounds into the range of the type. -/
theorem STAmount.ofNumber_ok_iff (nt : NumericType) (n : Number) (mode : rounding_mode) (hn : n.isNormalized)
    (hnt : nt = .fractional ∨ nt = NumericType.native ∨ nt = NumericType.int64)
    (hsign : 0 ≤ n.toRat ∨ mode = .to_nearest ∨ mode = .towards_zero) :
    (∃ result, STAmount.ofNumber nt n mode = .ok result) ↔ STAmount.RoundsInRange nt mode n.toRat := by
  sorry

/-- A negative Number that `downward` conversion accepts although it rounds out of range: XRP from
`-(10^17 + 0.1)` returns `-10^17`. -/
theorem STAmount.ofNumber_ok_iff_attained :
    ∃ (nt : NumericType) (n : Number) (mode : rounding_mode) (result : STAmount),
      n.isNormalized ∧
      (nt = .fractional ∨ nt = NumericType.native ∨ nt = NumericType.int64) ∧
      STAmount.ofNumber nt n mode = .ok result ∧
      ¬ STAmount.RoundsInRange nt mode n.toRat := by
  sorry

/-- With a mantissa within int64 (`hm`), making an amount from a mantissa and an exponent returns a result
exactly when `mantissa * 10 ^ exponent` rounds into the range of the type. -/
theorem STAmount.checked_ok_iff (nt : NumericType) (m : UInt64) (e : Int) (neg : Bool) (mode : rounding_mode)
    (hnt : nt = .fractional ∨ nt = NumericType.native ∨ nt = NumericType.int64)
    (hm : m ≤ maxRep) :
    (∃ result, STAmount.checked nt m e neg mode = .ok result) ↔
      STAmount.RoundsInRange nt mode (STAmount.unchecked nt m e neg).toRat := by
  sorry

/-- A mantissa above the largest int64 that is accepted although it is out of range: MPT `2^63` returns
`2^63 - 8`. -/
theorem STAmount.checked_ok_iff_attained :
    ∃ (nt : NumericType) (m : UInt64) (e : Int) (neg : Bool) (mode : rounding_mode) (result : STAmount),
      (nt = .fractional ∨ nt = NumericType.native ∨ nt = NumericType.int64) ∧
      STAmount.checked nt m e neg mode = .ok result ∧
      ¬ STAmount.RoundsInRange nt mode (STAmount.unchecked nt m e neg).toRat := by
  sorry

/-- An IOU mantissa above the largest int64 that is in range: `2^63` at exponent 0. Reading it as an int64 wraps
around (FV_M1_25). -/
theorem STAmount.checked_ok_iff_iou_attained :
    ∃ (m : UInt64) (e : Int) (mode : rounding_mode),
      STAmount.RoundsInRange .fractional mode (STAmount.unchecked .fractional m e false).toRat ∧
      STAmount.checked .fractional m e false mode = .error .wrap := by
  sorry

/-- IOU addition returns a result exactly when the exact sum rounds into the IOU range. In `to_nearest` the
exact sum must itself be a Number (`hfit`). -/
theorem STAmount.operator_add_ok_iff_iou (v1 v2 : STAmount) (mode : rounding_mode) (h1 : v1.IOUCanonical)
    (h2 : v2.IOUCanonical)
    (hfit : mode = .to_nearest → ∃ n : Number, n.isNormalized ∧ n.toRat = v1.toRat + v2.toRat) :
    (∃ result, STAmount.operator_add v1 v2 mode = .ok result) ↔
      STAmount.RoundsInRange .fractional mode (v1.toRat + v2.toRat) := by
  sorry

/-- A `to_nearest` sum inside the IOU range that fails because it is rounded twice:
`9999999999999999e80 + 4996000000000000e64`. -/
theorem STAmount.operator_add_ok_iff_iou_attained :
    ∃ (v1 v2 : STAmount) (mode : rounding_mode),
      v1.IOUCanonical ∧
      v2.IOUCanonical ∧
      STAmount.RoundsInRange .fractional mode (v1.toRat + v2.toRat) ∧
      ∃ err,
        STAmount.operator_add v1 v2 mode = .error err := by
  sorry

/-- XRP addition always returns a result, because the sum is not checked against the largest XRP amount
(FV_M1_24). So every sum in the XRP range returns a result, but a result does not mean the sum is in range. -/
theorem STAmount.operator_add_ok_xrp (v1 v2 : STAmount) (mode : rounding_mode)
    (h1 : v1.IntegralCanonical) (h2 : v2.IntegralCanonical)
    (ht1 : v1.mNumericType = NumericType.native) (ht2 : v2.mNumericType = NumericType.native) :
    ∃ result, STAmount.operator_add v1 v2 mode = .ok result := by
  sorry

/-- An XRP sum above `10^17` that is returned although it is out of range: `10^17 + 1`. -/
theorem STAmount.operator_add_ok_xrp_attained :
    ∃ (v1 v2 : STAmount) (mode : rounding_mode) (result : STAmount),
      v1.IntegralCanonical ∧
      v2.IntegralCanonical ∧
      v1.mNumericType = NumericType.native ∧
      v2.mNumericType = NumericType.native ∧
      STAmount.operator_add v1 v2 mode = .ok result ∧
      ¬ STAmount.RoundsInRange NumericType.native mode (v1.toRat + v2.toRat) := by
  sorry

/-- MPT addition returns a result exactly when the sum is in the MPT range. -/
theorem STAmount.operator_add_ok_iff_mpt (v1 v2 : STAmount) (mode : rounding_mode)
    (h1 : v1.IntegralCanonical) (h2 : v2.IntegralCanonical)
    (ht1 : v1.mNumericType = NumericType.int64) (ht2 : v2.mNumericType = NumericType.int64) :
    (∃ result, STAmount.operator_add v1 v2 mode = .ok result) ↔
      STAmount.RoundsInRange NumericType.int64 mode (v1.toRat + v2.toRat) := by
  sorry

/-- IOU subtraction returns a result exactly when the exact difference rounds into the IOU range. In
`to_nearest` the exact difference must itself be a Number (`hfit`). -/
theorem STAmount.operator_sub_ok_iff_iou (v1 v2 : STAmount) (mode : rounding_mode) (h1 : v1.IOUCanonical)
    (h2 : v2.IOUCanonical)
    (hfit : mode = .to_nearest → ∃ n : Number, n.isNormalized ∧ n.toRat = v1.toRat - v2.toRat) :
    (∃ result, STAmount.operator_sub v1 v2 mode = .ok result) ↔
      STAmount.RoundsInRange .fractional mode (v1.toRat - v2.toRat) := by
  sorry

/-- A `to_nearest` difference inside the IOU range that fails because it is rounded twice:
`9999999999999999e80 - (-4996000000000000e64)`. -/
theorem STAmount.operator_sub_ok_iff_iou_attained :
    ∃ (v1 v2 : STAmount) (mode : rounding_mode),
      v1.IOUCanonical ∧
      v2.IOUCanonical ∧
      STAmount.RoundsInRange .fractional mode (v1.toRat - v2.toRat) ∧
      ∃ err,
        STAmount.operator_sub v1 v2 mode = .error err := by
  sorry

/-- XRP subtraction always returns a result, because the difference is not checked against the largest XRP amount
(FV_M1_24). -/
theorem STAmount.operator_sub_ok_xrp (v1 v2 : STAmount) (mode : rounding_mode)
    (h1 : v1.IntegralCanonical) (h2 : v2.IntegralCanonical)
    (ht1 : v1.mNumericType = NumericType.native) (ht2 : v2.mNumericType = NumericType.native) :
    ∃ result, STAmount.operator_sub v1 v2 mode = .ok result := by
  sorry

/-- An XRP difference above `10^17` that is returned although it is out of range: `10^17 - (-1)`. -/
theorem STAmount.operator_sub_ok_xrp_attained :
    ∃ (v1 v2 : STAmount) (mode : rounding_mode) (result : STAmount),
      v1.IntegralCanonical ∧
      v2.IntegralCanonical ∧
      v1.mNumericType = NumericType.native ∧
      v2.mNumericType = NumericType.native ∧
      STAmount.operator_sub v1 v2 mode = .ok result ∧
      ¬ STAmount.RoundsInRange NumericType.native mode (v1.toRat - v2.toRat) := by
  sorry

/-- MPT subtraction returns a result exactly when the difference is in the MPT range. -/
theorem STAmount.operator_sub_ok_iff_mpt (v1 v2 : STAmount) (mode : rounding_mode)
    (h1 : v1.IntegralCanonical) (h2 : v2.IntegralCanonical)
    (ht1 : v1.mNumericType = NumericType.int64) (ht2 : v2.mNumericType = NumericType.int64) :
    (∃ result, STAmount.operator_sub v1 v2 mode = .ok result) ↔
      STAmount.RoundsInRange NumericType.int64 mode (v1.toRat - v2.toRat) := by
  sorry

end XRPL.Model.Protocol
