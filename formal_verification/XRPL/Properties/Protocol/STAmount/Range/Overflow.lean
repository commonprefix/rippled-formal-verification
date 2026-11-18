import XRPL.Properties.Protocol.STAmount.Range.Success

/-! # When the `STAmount` operations fail

Each theorem is the other half of the matching one in `Success.lean`, with the same hypotheses: when the exact
value, rounded once in the mode, is not an amount of the type, the operation returns an error. XRP add and
subtract have no such theorem, because they never fail (FV_M1_24, see the `_xrp_attained` witnesses there). For an
MPT sum past int64 the error is the model's wrap error, where C++ returns the wrapped value (FV_M1_26, see the
`_mpt_attained` witnesses here). -/

namespace XRPL.Model.Protocol

/-- For a Number that is not negative, or in `to_nearest` or `towards_zero` (`hsign`), the conversion to an
amount fails when the Number rounds out of the range of the type. -/
theorem STAmount.ofNumber_overflow (nt : NumericType) (n : Number) (mode : rounding_mode) (hn : n.isNormalized)
    (hnt : nt = .fractional ∨ nt = NumericType.native ∨ nt = NumericType.int64)
    (hsign : 0 ≤ n.toRat ∨ mode = .to_nearest ∨ mode = .towards_zero)
    (h : ¬ STAmount.RoundsInRange nt mode n.toRat) :
    ∃ err, STAmount.ofNumber nt n mode = .error err :=
  exists_error_of_not_exists_ok (mt (STAmount.ofNumber_ok_iff nt n mode hn hnt hsign).mp h)

/-- With a mantissa within int64 (`hm`), making an amount from a mantissa and an exponent fails when
`mantissa * 10 ^ exponent` rounds out of the range of the type. -/
theorem STAmount.checked_overflow (nt : NumericType) (m : UInt64) (e : Int) (neg : Bool) (mode : rounding_mode)
    (hnt : nt = .fractional ∨ nt = NumericType.native ∨ nt = NumericType.int64)
    (hm : m ≤ maxRep)
    (h : ¬ STAmount.RoundsInRange nt mode (STAmount.unchecked nt m e neg).toRat) :
    ∃ err, STAmount.checked nt m e neg mode = .error err :=
  exists_error_of_not_exists_ok (mt (STAmount.checked_ok_iff nt m e neg mode hnt hm).mp h)

/-- IOU addition fails when the exact sum rounds out of the IOU range. In `to_nearest` the exact sum must
itself be a Number (`hfit`). -/
theorem STAmount.operator_add_overflow_iou (v1 v2 : STAmount) (mode : rounding_mode) (h1 : v1.IOUCanonical)
    (h2 : v2.IOUCanonical)
    (hfit : mode = .to_nearest → ∃ n : Number, n.isNormalized ∧ n.toRat = v1.toRat + v2.toRat)
    (h : ¬ STAmount.RoundsInRange .fractional mode (v1.toRat + v2.toRat)) :
    ∃ err, STAmount.operator_add v1 v2 mode = .error err :=
  exists_error_of_not_exists_ok (mt (STAmount.operator_add_ok_iff_iou v1 v2 mode h1 h2 hfit).mp h)

/-- Unless the exact sum is `-2^63` (`hmin`), MPT addition fails when the sum is out of the MPT range. -/
theorem STAmount.operator_add_overflow_mpt (v1 v2 : STAmount) (mode : rounding_mode)
    (h1 : v1.IntegralCanonical) (h2 : v2.IntegralCanonical)
    (ht1 : v1.mNumericType = NumericType.int64) (ht2 : v2.mNumericType = NumericType.int64)
    (hmin : v1.toRat + v2.toRat ≠ minInt64)
    (h : ¬ STAmount.RoundsInRange NumericType.int64 mode (v1.toRat + v2.toRat)) :
    ∃ err, STAmount.operator_add v1 v2 mode = .error err :=
  exists_error_of_not_exists_ok (mt (STAmount.operator_add_ok_iff_mpt v1 v2 mode h1 h2 ht1 ht2 hmin).mp h)

/-- IOU subtraction fails when the exact difference rounds out of the IOU range. In `to_nearest` the exact
difference must itself be a Number (`hfit`). -/
theorem STAmount.operator_sub_overflow_iou (v1 v2 : STAmount) (mode : rounding_mode) (h1 : v1.IOUCanonical)
    (h2 : v2.IOUCanonical)
    (hfit : mode = .to_nearest → ∃ n : Number, n.isNormalized ∧ n.toRat = v1.toRat - v2.toRat)
    (h : ¬ STAmount.RoundsInRange .fractional mode (v1.toRat - v2.toRat)) :
    ∃ err, STAmount.operator_sub v1 v2 mode = .error err :=
  exists_error_of_not_exists_ok (mt (STAmount.operator_sub_ok_iff_iou v1 v2 mode h1 h2 hfit).mp h)

/-- Unless the exact difference is `-2^63` (`hmin`), MPT subtraction fails when the difference is out of the MPT
range. -/
theorem STAmount.operator_sub_overflow_mpt (v1 v2 : STAmount) (mode : rounding_mode)
    (h1 : v1.IntegralCanonical) (h2 : v2.IntegralCanonical)
    (ht1 : v1.mNumericType = NumericType.int64) (ht2 : v2.mNumericType = NumericType.int64)
    (hmin : v1.toRat - v2.toRat ≠ minInt64)
    (h : ¬ STAmount.RoundsInRange NumericType.int64 mode (v1.toRat - v2.toRat)) :
    ∃ err, STAmount.operator_sub v1 v2 mode = .error err :=
  exists_error_of_not_exists_ok (mt (STAmount.operator_sub_ok_iff_mpt v1 v2 mode h1 h2 ht1 ht2 hmin).mp h)

/-- An MPT sum above `2^63 - 1` whose int64 addition wraps around: `(2^63 - 1) + 2`. The model stops with its wrap
error, where C++ returns the wrapped value `-(2^63 - 1)`. -/
theorem STAmount.operator_add_overflow_mpt_attained :
    ∃ (v1 v2 : STAmount) (mode : rounding_mode),
      v1.IntegralCanonical ∧
      v2.IntegralCanonical ∧
      v1.mNumericType = NumericType.int64 ∧
      v2.mNumericType = NumericType.int64 ∧
      ¬ STAmount.RoundsInRange NumericType.int64 mode (v1.toRat + v2.toRat) ∧
      STAmount.operator_add v1 v2 mode = .error .wrap :=
  ⟨⟨NumericType.int64, 9223372036854775807, 0, false⟩, ⟨NumericType.int64, 2, 0, false⟩, .to_nearest,
    STAmount.mpt_wrap_witness_canonical_left, STAmount.mpt_wrap_witness_canonical_right false, rfl, rfl,
    STAmount.operator_add_mpt_wrap_witness_out, STAmount.operator_add_mpt_wrap_witness⟩

/-- An MPT difference above `2^63 - 1` whose int64 addition wraps around: `(2^63 - 1) - (-2)`. -/
theorem STAmount.operator_sub_overflow_mpt_attained :
    ∃ (v1 v2 : STAmount) (mode : rounding_mode),
      v1.IntegralCanonical ∧
      v2.IntegralCanonical ∧
      v1.mNumericType = NumericType.int64 ∧
      v2.mNumericType = NumericType.int64 ∧
      ¬ STAmount.RoundsInRange NumericType.int64 mode (v1.toRat - v2.toRat) ∧
      STAmount.operator_sub v1 v2 mode = .error .wrap :=
  ⟨⟨NumericType.int64, 9223372036854775807, 0, false⟩, ⟨NumericType.int64, 2, 0, true⟩, .to_nearest,
    STAmount.mpt_wrap_witness_canonical_left, STAmount.mpt_wrap_witness_canonical_right true, rfl, rfl,
    STAmount.operator_sub_mpt_wrap_witness_out, STAmount.operator_sub_mpt_wrap_witness⟩

end XRPL.Model.Protocol
