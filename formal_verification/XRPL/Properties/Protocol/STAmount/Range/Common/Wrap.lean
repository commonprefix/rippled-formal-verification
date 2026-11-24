import XRPL.Properties.Protocol.Common.Wrap
import XRPL.Properties.Protocol.STAmount.Range.Common.IntegralAdd

/-! # Exactly where the `STAmount` operations wrap around

`xrp`, `mpt` and `iou` read the mantissa as an int64, so an operation through them wraps exactly when the mantissa
is above the largest int64. IOU sums use 16-digit mantissas, so they never wrap. -/

namespace XRPL.Model.Protocol

/-- A mantissa is above the largest int64 exactly when the amount does not fit. -/
lemma STAmount.maxRep_lt_iff_not_fits (s : STAmount) : maxRep < s.mValue ↔ ¬ s.Fits := by
  unfold STAmount.Fits
  rw [UInt64.lt_iff_toNat_lt, show maxRep.toNat = 9223372036854775807 from by decide]
  omega

/-- Proof of `STAmount.intAmount_wrap_iff`. -/
lemma STAmount.intAmount_wrap_iff_proof (s : STAmount) :
    s.intAmount = .error .wrap ↔ s.integral = true ∧ maxRep < s.mValue := by
  constructor
  · intro h
    have hint : s.integral = true := by
      by_contra hc
      unfold STAmount.intAmount at h
      rw [ite_eq_right hc] at h
      cases h
    exact ⟨hint, (STAmount.maxRep_lt_iff_not_fits s).mpr fun hf => STAmount.intAmount_ne_wrap s hf h⟩
  · rintro ⟨hint, hlt⟩
    unfold STAmount.intAmount
    rw [ite_eq_left hint, STAmount.signedDropsChecked_eq_wrap.mpr hlt, err_bind]

/-- Proof of `STAmount.iou_wrap_iff`. -/
lemma STAmount.iou_wrap_iff_proof (s : STAmount) (mode : rounding_mode) :
    s.iou mode = .error .wrap ↔ s.integral = false ∧ maxRep < s.mValue := by
  constructor
  · intro h
    have hint : s.integral = false := by
      by_contra hc
      unfold STAmount.iou at h
      rw [ite_eq_left (by simpa using hc)] at h
      cases h
    exact ⟨hint, (STAmount.maxRep_lt_iff_not_fits s).mpr fun hf => STAmount.iou_ne_wrap s mode hf h⟩
  · rintro ⟨hint, hlt⟩
    unfold STAmount.iou
    rw [ite_eq_right (by rw [hint]; decide), STAmount.signedDropsChecked_eq_wrap.mpr hlt, err_bind]

/-- Proof of `STAmount.toNumber_wrap_iff`. -/
lemma STAmount.toNumber_wrap_iff_proof (s : STAmount) (mode : rounding_mode) :
    s.toNumber mode = .error .wrap ↔ maxRep < s.mValue := by
  constructor
  · intro h
    exact (STAmount.maxRep_lt_iff_not_fits s).mpr fun hf => STAmount.toNumber_ne_wrap s mode hf h
  · intro hlt
    unfold STAmount.toNumber
    by_cases hint : s.integral = true
    · rw [ite_eq_left hint, (STAmount.intAmount_wrap_iff_proof s).mpr ⟨hint, hlt⟩]
    · rw [ite_eq_right hint, (STAmount.iou_wrap_iff_proof s mode).mpr ⟨by simpa using hint, hlt⟩]

/-- An XRP or MPT amount is brought to its stored form through a Number, which never wraps. -/
lemma STAmount.canonicalize_integral_ne_wrap (s : STAmount) (mode : rounding_mode) (hint : s.integral = true) :
    s.canonicalize mode ≠ .error .wrap := by
  unfold STAmount.canonicalize
  rw [ite_eq_left hint]
  split_ne_wrap [IntAmount.ofNumber_ne_wrap]

/-- Proof of `STAmount.checked_wrap_iff`. -/
lemma STAmount.checked_wrap_iff_proof (nt : NumericType) (m : UInt64) (e : Int) (neg : Bool)
    (mode : rounding_mode) :
    STAmount.checked nt m e neg mode = .error .wrap ↔ nt.isIntegral = false ∧ maxRep < m := by
  constructor
  · intro h
    have hnt : nt.isIntegral = false := by
      by_contra hc
      exact STAmount.canonicalize_integral_ne_wrap (STAmount.unchecked nt m e neg) mode
        (by simpa [STAmount.integral, STAmount.unchecked] using hc) h
    refine ⟨hnt, ?_⟩
    by_contra hc
    refine STAmount.checked_ne_wrap nt m e neg mode ?_ h
    rw [UInt64.lt_iff_toNat_lt, show maxRep.toNat = 9223372036854775807 from by decide] at hc
    omega
  · rintro ⟨hnt, hlt⟩
    unfold STAmount.checked STAmount.canonicalize
    rw [ite_eq_right (by simp [STAmount.integral, STAmount.unchecked, hnt]),
      (STAmount.iou_wrap_iff_proof _ mode).mpr ⟨by simp [STAmount.integral, STAmount.unchecked, hnt], hlt⟩]

/-- Proof of `STAmount.operator_add_no_wrap_iou`. -/
lemma STAmount.operator_add_no_wrap_iou_proof (v1 v2 : STAmount) (mode : rounding_mode) (h1 : v1.IOUCanonical)
    (h2 : v2.IOUCanonical) : STAmount.operator_add v1 v2 mode ≠ .error .wrap :=
  STAmount.operator_add_ne_wrap v1 v2 mode (STAmount.Fits.of_lt (by have := h1.mant_hi; omega))
    (STAmount.Fits.of_lt (by have := h2.mant_hi; omega))
    (fun hi => absurd hi (by unfold STAmount.integral; rw [h1.is_fractional]; decide))

/-- Proof of `STAmount.operator_sub_no_wrap_iou`. -/
lemma STAmount.operator_sub_no_wrap_iou_proof (v1 v2 : STAmount) (mode : rounding_mode) (h1 : v1.IOUCanonical)
    (h2 : v2.IOUCanonical) : STAmount.operator_sub v1 v2 mode ≠ .error .wrap :=
  STAmount.operator_add_no_wrap_iou_proof v1 v2.operator_neg mode h1 h2.operator_neg

end XRPL.Model.Protocol
