import XRPL.Properties.Protocol.STAmount.Range.Overflow
import XRPL.Properties.Protocol.STAmount.Range.Common.Wrap

/-! # Exactly where the `STAmount` operations wrap around

An int64 wraps when a mantissa above the largest int64 is read as an int64, when an MPT sum overflows int64, and
when the MPT sum `-2^63` is negated. XRP addition and subtraction never wrap. -/

namespace XRPL.Model.Protocol

/-- An amount read as an int64 (C++ `xrp`, `mpt`) wraps exactly when it is an XRP or MPT amount with a mantissa
above the largest int64. -/
theorem STAmount.intAmount_wrap_iff (s : STAmount) :
    s.intAmount = .error .wrap ↔ s.integral = true ∧ maxRep < s.mValue :=
  STAmount.intAmount_wrap_iff_proof s

/-- An XRP and an MPT amount with mantissa `2^63`: reading each as an int64 wraps around. -/
theorem STAmount.intAmount_wrap_iff_attained :
    ∃ (xrp mpt : STAmount),
      xrp.mNumericType = NumericType.native ∧
      mpt.mNumericType = NumericType.int64 ∧
      xrp.intAmount = .error .wrap ∧
      mpt.intAmount = .error .wrap :=
  ⟨⟨NumericType.native, 9223372036854775808, 0, false⟩, ⟨NumericType.int64, 9223372036854775808, 0, false⟩, rfl,
    rfl, STAmount.intAmount_wrap_witness_xrp, STAmount.intAmount_wrap_witness_mpt⟩

/-- An amount read as an `IOUAmount` (C++ `iou`) wraps exactly when it is an IOU amount with a mantissa above the
largest int64. -/
theorem STAmount.iou_wrap_iff (s : STAmount) (mode : rounding_mode) :
    s.iou mode = .error .wrap ↔ s.integral = false ∧ maxRep < s.mValue :=
  STAmount.iou_wrap_iff_proof s mode

/-- An amount of any type converted to a Number wraps exactly when its mantissa is above the largest int64. -/
theorem STAmount.toNumber_wrap_iff (s : STAmount) (mode : rounding_mode) :
    s.toNumber mode = .error .wrap ↔ maxRep < s.mValue :=
  STAmount.toNumber_wrap_iff_proof s mode

/-- Making an amount from a mantissa and an exponent wraps exactly when it is an IOU amount with a mantissa
above the largest int64. -/
theorem STAmount.checked_wrap_iff (nt : NumericType) (m : UInt64) (e : Int) (neg : Bool) (mode : rounding_mode) :
    STAmount.checked nt m e neg mode = .error .wrap ↔ nt.isIntegral = false ∧ maxRep < m :=
  STAmount.checked_wrap_iff_proof nt m e neg mode

/-- Making an amount from a Number never wraps. -/
theorem STAmount.ofNumber_no_wrap (nt : NumericType) (n : Number) (mode : rounding_mode) :
    STAmount.ofNumber nt n mode ≠ .error .wrap :=
  STAmount.ofNumber_ne_wrap nt n mode

/-- MPT addition wraps exactly when the sum is out of the MPT range. -/
theorem STAmount.operator_add_wrap_iff_mpt (v1 v2 : STAmount) (mode : rounding_mode)
    (h1 : v1.IntegralCanonical) (h2 : v2.IntegralCanonical)
    (ht1 : v1.mNumericType = NumericType.int64) (ht2 : v2.mNumericType = NumericType.int64) :
    STAmount.operator_add v1 v2 mode = .error .wrap ↔
      ¬ STAmount.RoundsInRange NumericType.int64 mode (v1.toRat + v2.toRat) :=
  STAmount.operator_add_wrap_iff_mpt_proof v1 v2 mode h1 h2 ht1 ht2

/-- MPT subtraction wraps exactly when the difference is out of the MPT range. -/
theorem STAmount.operator_sub_wrap_iff_mpt (v1 v2 : STAmount) (mode : rounding_mode)
    (h1 : v1.IntegralCanonical) (h2 : v2.IntegralCanonical)
    (ht1 : v1.mNumericType = NumericType.int64) (ht2 : v2.mNumericType = NumericType.int64) :
    STAmount.operator_sub v1 v2 mode = .error .wrap ↔
      ¬ STAmount.RoundsInRange NumericType.int64 mode (v1.toRat - v2.toRat) :=
  STAmount.operator_sub_wrap_iff_mpt_proof v1 v2 mode h1 h2 ht1 ht2

/-- IOU addition never wraps. -/
theorem STAmount.operator_add_no_wrap_iou (v1 v2 : STAmount) (mode : rounding_mode) (h1 : v1.IOUCanonical)
    (h2 : v2.IOUCanonical) : STAmount.operator_add v1 v2 mode ≠ .error .wrap :=
  STAmount.operator_add_no_wrap_iou_proof v1 v2 mode h1 h2

/-- IOU subtraction never wraps. -/
theorem STAmount.operator_sub_no_wrap_iou (v1 v2 : STAmount) (mode : rounding_mode) (h1 : v1.IOUCanonical)
    (h2 : v2.IOUCanonical) : STAmount.operator_sub v1 v2 mode ≠ .error .wrap :=
  STAmount.operator_sub_no_wrap_iou_proof v1 v2 mode h1 h2

end XRPL.Model.Protocol
