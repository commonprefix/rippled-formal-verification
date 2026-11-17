import XRPL.Properties.Protocol.IOUAmount.Common.Underflow
import XRPL.Properties.Protocol.STAmount.Add.Common.IOU
import XRPL.Properties.Protocol.STAmount.Add.Common.DirectedSupport
import XRPL.Properties.Protocol.STAmount.Sub.Common.Neg

/-! # Underflow of IOU `STAmount` sums and differences

An IOU sum or difference of two canonical amounts is zero only when the exact value is below `10⁻⁸¹` in
magnitude. The conversions to and from `IOUAmount` are exact, so this is the `IOUAmount` addition fact. -/

namespace XRPL.Model.Protocol

/-- An IOU `STAmount` sum is zero only when the exact sum is below `10⁻⁸¹` in magnitude. -/
lemma STAmount.operator_add_underflow_truth_small_iou_proof (v1 v2 result : STAmount) (mode : rounding_mode)
    (hc1 : v1.IOUCanonical) (hc2 : v2.IOUCanonical)
    (hok : STAmount.operator_add v1 v2 mode = .ok result) (hres0 : result.mValue = 0) :
    |v1.toRat + v2.toRat| < (10 : ℚ) ^ (-81 : ℤ) := by
  have hcmp : STAmount.areComparable v1 v2 = true := by
    rcases hb : STAmount.areComparable v1 v2 with _ | _
    · rw [STAmount.operator_add, hb] at hok; simp at hok
    · rfl
  rw [STAmount.operator_add, if_neg (by rw [hcmp]; decide)] at hok
  have hv2ne : v2.mValue ≠ 0 := by intro h; have := hc2.mant_lo; rw [h] at this; simp at this
  have hv1ne : v1.mValue ≠ 0 := by intro h; have := hc1.mant_lo; rw [h] at this; simp at this
  have hint1 : ¬ v1.integral = true := by
    unfold STAmount.integral; rw [hc1.is_fractional]; decide
  rw [if_neg (by simpa using hv2ne), if_neg (by simpa using hv1ne), if_neg hint1,
    STAmount.iou_canonical_id v1 mode hc1, STAmount.iou_canonical_id v2 mode hc2] at hok
  simp only at hok
  set i1 : IOUAmount := ⟨v1.signedDrops.toInt64, v1.mOffset⟩ with hi1
  set i2 : IOUAmount := ⟨v2.signedDrops.toInt64, v2.mOffset⟩ with hi2
  cases hadd : IOUAmount.operator_add i1 i2 mode with
  | error e => rw [hadd] at hok; simp at hok
  | ok sumI =>
    rw [hadd] at hok
    simp only at hok
    have hm : minExponent = -32768 := rfl
    have hM : maxExponent = 32768 := rfl
    have hi1n : i1.mantissa_.toInt.natAbs = v1.mValue.toNat := STAmount.iou_canonical_mantissa_natAbs v1 hc1
    have hi2n : i2.mantissa_.toInt.natAbs = v2.mValue.toNat := STAmount.iou_canonical_mantissa_natAbs v2 hc2
    have hr1 : i1.InRange16 := ⟨by rw [hi1n]; exact hc1.mant_lo, by rw [hi1n]; exact hc1.mant_hi,
      by have := hc1.exp_lo; show (-96 : ℤ) ≤ v1.mOffset; omega,
      by have := hc1.exp_hi; show v1.mOffset ≤ 80; omega⟩
    have hr2 : i2.InRange16 := ⟨by rw [hi2n]; exact hc2.mant_lo, by rw [hi2n]; exact hc2.mant_hi,
      by have := hc2.exp_lo; show (-96 : ℤ) ≤ v2.mOffset; omega,
      by have := hc2.exp_hi; show v2.mOffset ≤ 80; omega⟩
    -- a nonzero IOU sum packs into a nonzero `STAmount`
    have hsumI0 : sumI.mantissa_ = 0 := by
      by_contra hne
      have h_truth_ne := IOUAmount.operator_add_truth_ne_of_result i1 i2 sumI mode hr1 hr2 hadd hne
      have hsumI_range : sumI.InRange16 :=
        IOUAmount.operator_add_InRange16_anyMode i1 i2 sumI mode hr1.mant_lo hr1.mant_hi hr2.mant_lo hr2.mant_hi
          (by have := hr1.exp_lo; omega) (by have := hr1.exp_hi; omega)
          (by have := hr2.exp_lo; omega) (by have := hr2.exp_hi; omega) h_truth_ne hadd hne
      have hpack := STAmount.ofIOU_canonical sumI mode hsumI_range
      rw [hok] at hpack
      have hres_eq : result = ⟨.fractional, sumI.mantissa_.toInt.natAbs.toUInt64, sumI.exponent_,
          decide (sumI.mantissa_ < 0)⟩ := Except.ok.inj hpack
      have hmv : sumI.mantissa_.toInt.natAbs.toUInt64 = 0 := by rw [hres_eq] at hres0; exact hres0
      have h_toNat : (sumI.mantissa_.toInt.natAbs.toUInt64).toNat = sumI.mantissa_.toInt.natAbs :=
        UInt64.toNat_ofNat_of_lt' (by rw [uint64_size_val]; have := hsumI_range.mant_hi; omega)
      rw [hmv] at h_toNat
      have hlo := hsumI_range.mant_lo
      rw [← h_toNat] at hlo
      simp at hlo
    rw [← STAmount.iou_canonical_toRat v1 hc1, ← STAmount.iou_canonical_toRat v2 hc2]
    exact IOUAmount.operator_add_underflow_truth_small_proof i1 i2 sumI mode hr1 hr2 hadd hsumI0

/-- An IOU `STAmount` difference is zero only when the exact difference is below `10⁻⁸¹` in magnitude, since
`v1 - v2 = v1 + (-v2)`. -/
lemma STAmount.operator_sub_underflow_truth_small_iou_proof (v1 v2 result : STAmount) (mode : rounding_mode)
    (hc1 : v1.IOUCanonical) (hc2 : v2.IOUCanonical)
    (hok : STAmount.operator_sub v1 v2 mode = .ok result) (hres0 : result.mValue = 0) :
    |v1.toRat - v2.toRat| < (10 : ℚ) ^ (-81 : ℤ) := by
  have h := STAmount.operator_add_underflow_truth_small_iou_proof v1 v2.operator_neg result mode hc1
    hc2.operator_neg hok hres0
  rwa [STAmount.operator_neg_toRat, ← sub_eq_add_neg] at h

end XRPL.Model.Protocol
