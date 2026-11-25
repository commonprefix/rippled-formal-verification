import XRPL.Properties.Protocol.STAmount.Range.Common.Units
import XRPL.Properties.Protocol.STAmount.Common.RoundToScalePlumbing
import XRPL.Properties.Protocol.STAmount.Common.DiscreteDefs

/-! # Inputs where an operation and the range of the type disagree

Each input below either returns a result although the exact value rounds out of range, or fails although the
exact value rounds into range, or stops with the wrap error. They are evaluated on the model. -/

namespace XRPL.Model.Protocol

/-- The Number `-(10^17 + 0.1)` is normalized. -/
lemma STAmount.ofNumber_range_witness_normalized : (⟨true, 1000000000000000001, -1⟩ : Number).isNormalized := by
  decide

/-- `downward` conversion of `-(10^17 + 0.1)` to XRP returns `-10^17`. -/
lemma STAmount.ofNumber_range_witness :
    STAmount.ofNumber NumericType.native ⟨true, 1000000000000000001, -1⟩ .downward
      = .ok ⟨NumericType.native, 100000000000000000, 0, true⟩ := by
  decide +kernel

/-- `-(10^17 + 0.1)` rounded down is below the smallest XRP amount. -/
lemma STAmount.ofNumber_range_witness_out :
    ¬ STAmount.RoundsInRange NumericType.native .downward (⟨true, 1000000000000000001, -1⟩ : Number).toRat := by
  have hv : (⟨true, 1000000000000000001, -1⟩ : Number).toRat = -(1000000000000000001 / 10) := by
    decide +kernel
  rw [STAmount.roundsInRange_native_iff, hv]
  simp only [RoundsWithinUnits]
  norm_num

/-- MPT from mantissa `2^63` returns `2^63 - 8`. -/
lemma STAmount.checked_range_witness :
    STAmount.checked NumericType.int64 9223372036854775808 0 false .to_nearest
      = .ok ⟨NumericType.int64, 9223372036854775800, 0, false⟩ := by
  decide +kernel

/-- `2^63` is above the largest MPT amount. -/
lemma STAmount.checked_range_witness_out :
    ¬ STAmount.RoundsInRange NumericType.int64 .to_nearest
      (STAmount.unchecked NumericType.int64 9223372036854775808 0 false).toRat := by
  have hv : (STAmount.unchecked NumericType.int64 9223372036854775808 0 false).toRat = 9223372036854775808 := by
    decide +kernel
  rw [STAmount.roundsInRange_int64_iff, hv]
  simp only [RoundsWithinUnits]
  norm_num

/-- IOU from mantissa `2^63` stops with the wrap error: the mantissa does not fit an int64. -/
lemma STAmount.checked_iou_range_witness :
    STAmount.checked .fractional 9223372036854775808 0 false .to_nearest = .error .wrap := by
  decide +kernel

/-- `2^63` rounds to the IOU amount `9223372036854776e3`. -/
lemma STAmount.checked_iou_range_witness_in :
    STAmount.RoundsInRange .fractional .to_nearest
      (STAmount.unchecked .fractional 9223372036854775808 0 false).toRat := by
  have hv : (STAmount.unchecked .fractional 9223372036854775808 0 false).toRat = 9223372036854775808 := by
    decide +kernel
  rw [hv]
  simp only [STAmount.RoundsInRange]
  rw [abs_of_nonneg (by norm_num)]
  norm_num

/-- The largest IOU amount `9999999999999999e80` is canonical. -/
lemma STAmount.iou_range_witness_canonical_left :
    (⟨.fractional, 9999999999999999, 80, false⟩ : STAmount).IOUCanonical :=
  ⟨by decide, by decide, by decide, by decide, by decide⟩

/-- `4996000000000000e64` with either sign is canonical. -/
lemma STAmount.iou_range_witness_canonical_right (neg : Bool) :
    (⟨.fractional, 4996000000000000, 64, neg⟩ : STAmount).IOUCanonical := by
  cases neg <;> exact ⟨by decide, by decide, by decide, by decide, by decide⟩

/-- `to_nearest` `9999999999999999e80 + 4996000000000000e64` fails with an overflow error. -/
lemma STAmount.operator_add_iou_range_witness :
    STAmount.operator_add ⟨.fractional, 9999999999999999, 80, false⟩
      ⟨.fractional, 4996000000000000, 64, false⟩ .to_nearest = .error .overflow := by
  decide +kernel

/-- `to_nearest` `9999999999999999e80 - (-4996000000000000e64)` fails with an overflow error. -/
lemma STAmount.operator_sub_iou_range_witness :
    STAmount.operator_sub ⟨.fractional, 9999999999999999, 80, false⟩
      ⟨.fractional, 4996000000000000, 64, true⟩ .to_nearest = .error .overflow := by
  decide +kernel

/-- The exact sum `9999999999999999.4996e80` is below the midpoint, so it rounds to the largest IOU amount. -/
lemma STAmount.operator_add_iou_range_witness_in :
    STAmount.RoundsInRange .fractional .to_nearest
      ((⟨.fractional, 9999999999999999, 80, false⟩ : STAmount).toRat +
        (⟨.fractional, 4996000000000000, 64, false⟩ : STAmount).toRat) := by
  have h1 : (⟨.fractional, 9999999999999999, 80, false⟩ : STAmount).toRat = 9999999999999999 * 10 ^ 80 := by
    decide +kernel
  have h2 : (⟨.fractional, 4996000000000000, 64, false⟩ : STAmount).toRat = 4996000000000000 * 10 ^ 64 := by
    decide +kernel
  rw [h1, h2]
  simp only [STAmount.RoundsInRange]
  rw [abs_of_nonneg (by norm_num)]
  norm_num

/-- The same exact value as a difference. -/
lemma STAmount.operator_sub_iou_range_witness_in :
    STAmount.RoundsInRange .fractional .to_nearest
      ((⟨.fractional, 9999999999999999, 80, false⟩ : STAmount).toRat -
        (⟨.fractional, 4996000000000000, 64, true⟩ : STAmount).toRat) := by
  have h1 : (⟨.fractional, 9999999999999999, 80, false⟩ : STAmount).toRat = 9999999999999999 * 10 ^ 80 := by
    decide +kernel
  have h2 : (⟨.fractional, 4996000000000000, 64, true⟩ : STAmount).toRat = -(4996000000000000 * 10 ^ 64) := by
    decide +kernel
  rw [h1, h2]
  simp only [STAmount.RoundsInRange]
  rw [abs_of_nonneg (by norm_num)]
  norm_num

/-- The largest XRP amount `10^17` is canonical. -/
lemma STAmount.xrp_range_witness_canonical_left :
    (⟨NumericType.native, 100000000000000000, 0, false⟩ : STAmount).IntegralCanonical :=
  ⟨by decide, by decide, by decide⟩

/-- One drop with either sign is a canonical XRP amount. -/
lemma STAmount.xrp_range_witness_canonical_right (neg : Bool) :
    (⟨NumericType.native, 1, 0, neg⟩ : STAmount).IntegralCanonical := by
  cases neg <;> exact ⟨by decide, by decide, by decide⟩

/-- XRP `10^17 + 1` returns `10^17 + 1`. -/
lemma STAmount.operator_add_xrp_range_witness :
    STAmount.operator_add ⟨NumericType.native, 100000000000000000, 0, false⟩
      ⟨NumericType.native, 1, 0, false⟩ .to_nearest
      = .ok ⟨NumericType.native, 100000000000000001, 0, false⟩ := by
  decide +kernel

/-- XRP `10^17 - (-1)` returns `10^17 + 1`. -/
lemma STAmount.operator_sub_xrp_range_witness :
    STAmount.operator_sub ⟨NumericType.native, 100000000000000000, 0, false⟩
      ⟨NumericType.native, 1, 0, true⟩ .to_nearest
      = .ok ⟨NumericType.native, 100000000000000001, 0, false⟩ := by
  decide +kernel

/-- `10^17 + 1` is above the largest XRP amount. -/
lemma STAmount.operator_add_xrp_range_witness_out :
    ¬ STAmount.RoundsInRange NumericType.native .to_nearest
      ((⟨NumericType.native, 100000000000000000, 0, false⟩ : STAmount).toRat +
        (⟨NumericType.native, 1, 0, false⟩ : STAmount).toRat) := by
  have h1 : (⟨NumericType.native, 100000000000000000, 0, false⟩ : STAmount).toRat = 100000000000000000 := by
    decide +kernel
  have h2 : (⟨NumericType.native, 1, 0, false⟩ : STAmount).toRat = 1 := by decide +kernel
  rw [STAmount.roundsInRange_native_iff, h1, h2]
  simp only [RoundsWithinUnits]
  norm_num

/-- The same exact value as a difference. -/
lemma STAmount.operator_sub_xrp_range_witness_out :
    ¬ STAmount.RoundsInRange NumericType.native .to_nearest
      ((⟨NumericType.native, 100000000000000000, 0, false⟩ : STAmount).toRat -
        (⟨NumericType.native, 1, 0, true⟩ : STAmount).toRat) := by
  have h1 : (⟨NumericType.native, 100000000000000000, 0, false⟩ : STAmount).toRat = 100000000000000000 := by
    decide +kernel
  have h2 : (⟨NumericType.native, 1, 0, true⟩ : STAmount).toRat = -1 := by decide +kernel
  rw [STAmount.roundsInRange_native_iff, h1, h2]
  simp only [RoundsWithinUnits]
  norm_num

/-- The smallest MPT amount `-(2^63 - 1)` is canonical. -/
lemma STAmount.mpt_range_witness_canonical_left :
    (⟨NumericType.int64, 9223372036854775807, 0, true⟩ : STAmount).IntegralCanonical :=
  ⟨by decide, by decide, by decide⟩

/-- One unit with either sign is a canonical MPT amount. -/
lemma STAmount.mpt_range_witness_canonical_right (neg : Bool) :
    (⟨NumericType.int64, 1, 0, neg⟩ : STAmount).IntegralCanonical := by
  cases neg <;> exact ⟨by decide, by decide, by decide⟩

/-- MPT `-(2^63 - 1) + -1` stops with the wrap error: the sum is `-2^63`, and its negation does not fit an int64. -/
lemma STAmount.operator_add_mpt_range_witness :
    STAmount.operator_add ⟨NumericType.int64, 9223372036854775807, 0, true⟩
      ⟨NumericType.int64, 1, 0, true⟩ .to_nearest = .error .wrap := by
  decide +kernel

/-- MPT `-(2^63 - 1) - 1` stops with the wrap error in the same way. -/
lemma STAmount.operator_sub_mpt_range_witness :
    STAmount.operator_sub ⟨NumericType.int64, 9223372036854775807, 0, true⟩
      ⟨NumericType.int64, 1, 0, false⟩ .to_nearest = .error .wrap := by
  decide +kernel

/-- `-2^63` is below the smallest MPT amount. -/
lemma STAmount.operator_add_mpt_range_witness_out :
    ¬ STAmount.RoundsInRange NumericType.int64 .to_nearest
      ((⟨NumericType.int64, 9223372036854775807, 0, true⟩ : STAmount).toRat +
        (⟨NumericType.int64, 1, 0, true⟩ : STAmount).toRat) := by
  have h1 : (⟨NumericType.int64, 9223372036854775807, 0, true⟩ : STAmount).toRat = -9223372036854775807 := by
    decide +kernel
  have h2 : (⟨NumericType.int64, 1, 0, true⟩ : STAmount).toRat = -1 := by decide +kernel
  rw [STAmount.roundsInRange_int64_iff, h1, h2]
  simp only [RoundsWithinUnits]
  norm_num

/-- The same exact value as a difference. -/
lemma STAmount.operator_sub_mpt_range_witness_out :
    ¬ STAmount.RoundsInRange NumericType.int64 .to_nearest
      ((⟨NumericType.int64, 9223372036854775807, 0, true⟩ : STAmount).toRat -
        (⟨NumericType.int64, 1, 0, false⟩ : STAmount).toRat) := by
  have h1 : (⟨NumericType.int64, 9223372036854775807, 0, true⟩ : STAmount).toRat = -9223372036854775807 := by
    decide +kernel
  have h2 : (⟨NumericType.int64, 1, 0, false⟩ : STAmount).toRat = 1 := by decide +kernel
  rw [STAmount.roundsInRange_int64_iff, h1, h2]
  simp only [RoundsWithinUnits]
  norm_num

/-- The largest MPT amount, `2^63 - 1`, is canonical. -/
lemma STAmount.mpt_wrap_witness_canonical_left :
    (⟨NumericType.int64, 9223372036854775807, 0, false⟩ : STAmount).IntegralCanonical :=
  ⟨by decide, by decide, by decide⟩

/-- Two units with either sign are a canonical MPT amount. -/
lemma STAmount.mpt_wrap_witness_canonical_right (neg : Bool) :
    (⟨NumericType.int64, 2, 0, neg⟩ : STAmount).IntegralCanonical := by
  cases neg <;> exact ⟨by decide, by decide, by decide⟩

/-- MPT `(2^63 - 1) + 2` stops with the wrap error: the int64 sum does not fit. -/
lemma STAmount.operator_add_mpt_wrap_witness :
    STAmount.operator_add ⟨NumericType.int64, 9223372036854775807, 0, false⟩
      ⟨NumericType.int64, 2, 0, false⟩ .to_nearest = .error .wrap := by
  decide +kernel

/-- MPT `(2^63 - 1) - (-2)` stops with the wrap error in the same way. -/
lemma STAmount.operator_sub_mpt_wrap_witness :
    STAmount.operator_sub ⟨NumericType.int64, 9223372036854775807, 0, false⟩
      ⟨NumericType.int64, 2, 0, true⟩ .to_nearest = .error .wrap := by
  decide +kernel

/-- `2^63 + 1` is above the largest MPT amount. -/
lemma STAmount.operator_add_mpt_wrap_witness_out :
    ¬ STAmount.RoundsInRange NumericType.int64 .to_nearest
      ((⟨NumericType.int64, 9223372036854775807, 0, false⟩ : STAmount).toRat +
        (⟨NumericType.int64, 2, 0, false⟩ : STAmount).toRat) := by
  have h1 : (⟨NumericType.int64, 9223372036854775807, 0, false⟩ : STAmount).toRat = 9223372036854775807 := by
    decide +kernel
  have h2 : (⟨NumericType.int64, 2, 0, false⟩ : STAmount).toRat = 2 := by decide +kernel
  rw [STAmount.roundsInRange_int64_iff, h1, h2]
  simp only [RoundsWithinUnits]
  norm_num

/-- The same exact value as a difference. -/
lemma STAmount.operator_sub_mpt_wrap_witness_out :
    ¬ STAmount.RoundsInRange NumericType.int64 .to_nearest
      ((⟨NumericType.int64, 9223372036854775807, 0, false⟩ : STAmount).toRat -
        (⟨NumericType.int64, 2, 0, true⟩ : STAmount).toRat) := by
  have h1 : (⟨NumericType.int64, 9223372036854775807, 0, false⟩ : STAmount).toRat = 9223372036854775807 := by
    decide +kernel
  have h2 : (⟨NumericType.int64, 2, 0, true⟩ : STAmount).toRat = -2 := by decide +kernel
  rw [STAmount.roundsInRange_int64_iff, h1, h2]
  simp only [RoundsWithinUnits]
  norm_num

/-- XRP with mantissa `2^63` read as an int64 stops with the wrap error. -/
lemma STAmount.intAmount_wrap_witness_xrp :
    (⟨NumericType.native, 9223372036854775808, 0, false⟩ : STAmount).intAmount = .error .wrap := by
  decide +kernel

/-- MPT with mantissa `2^63` read as an int64 stops with the wrap error. -/
lemma STAmount.intAmount_wrap_witness_mpt :
    (⟨NumericType.int64, 9223372036854775808, 0, false⟩ : STAmount).intAmount = .error .wrap := by
  decide +kernel

end XRPL.Model.Protocol
