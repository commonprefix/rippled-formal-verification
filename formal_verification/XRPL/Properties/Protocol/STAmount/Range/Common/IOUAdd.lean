import XRPL.Properties.Protocol.STAmount.Range.Common.IOU16
import XRPL.Properties.Protocol.STAmount.Add.Common.Underflow
import XRPL.Properties.Protocol.Number.Add.RoundsToRepresentable
import XRPL.Properties.Protocol.Number.Add.Common.NormalizedSum
import XRPL.Properties.Protocol.Number.Add.Common.SuccessCondition
import XRPL.Properties.Protocol.Number.Common.NumberBridge

/-! # When adding IOU amounts returns a result

The 19-digit Number sum never fails for IOU operands, so the addition succeeds exactly when the rounding to 16 digits
does. The two roundings act as one in the directed modes, and in `to_nearest` when the exact sum is a Number. -/

namespace XRPL.Model.Protocol

/-- The largest IOU amount `9999999999999999 * 10^80` as a Number. -/
lemma Number.iouTop_facts (neg : Bool) :
    (⟨neg, 9999999999999999000, 77⟩ : Number).isNormalized ∧
      (⟨neg, 9999999999999999000, 77⟩ : Number).toRat
        = (if neg = true then (-1 : ℚ) else 1) * (9999999999999999 * 10 ^ 80) := by
  cases neg <;> exact ⟨by decide, by decide +kernel⟩

/-- The first value past the IOU range, `10^96`, as a Number. -/
lemma Number.iouNext_facts (neg : Bool) :
    (⟨neg, 1000000000000000000, 78⟩ : Number).isNormalized ∧
      (⟨neg, 1000000000000000000, 78⟩ : Number).toRat = (if neg = true then (-1 : ℚ) else 1) * 10 ^ 96 := by
  cases neg <;> exact ⟨by decide, by decide +kernel⟩

/-- A Number sum is in the IOU range exactly when the exact sum is. In `to_nearest` this needs the exact sum to
be a Number (`hfit`), so that the sum is not rounded. -/
lemma Number.operator_add_roundsInRange_iff (x y sum : Number) (mode : rounding_mode)
    (hx : x.isNormalized) (hy : y.isNormalized)
    (hadd : Number.operator_add x y mode = .ok sum) (hsum : sum.mantissa_ ≠ 0)
    (hfit : mode = .to_nearest → ∃ n : Number, n.isNormalized ∧ n.toRat = x.toRat + y.toRat) :
    STAmount.RoundsInRange .fractional mode sum.toRat ↔
      STAmount.RoundsInRange .fractional mode (x.toRat + y.toRat) := by
  obtain ⟨hT, hTv⟩ := Number.iouTop_facts false
  obtain ⟨hT', hTv'⟩ := Number.iouTop_facts true
  obtain ⟨hN, hNv⟩ := Number.iouNext_facts false
  obtain ⟨hN', hNv'⟩ := Number.iouNext_facts true
  simp only [Bool.false_eq_true, ite_false, one_mul] at hTv hNv
  simp only [ite_true, neg_one_mul] at hTv' hNv'
  cases mode with
  | to_nearest =>
    obtain ⟨n, hn, hnv⟩ := hfit rfl
    rw [Number.RoundsToRepresentable.eq_of_representable sum _
      (Number.operator_add_rounded_to_nearest x y sum hx hy hadd) n hn hnv]
  | towards_zero =>
    have h := Number.operator_add_rounded_towards_zero x y sum hx hy hadd
    simp only [Number.RoundsToRepresentable] at h
    simp only [STAmount.RoundsInRange]
    by_cases hv : x.toRat + y.toRat ≥ 0
    · -- the largest Number at or below a value that is not negative
      rw [ite_eq_left hv] at h
      obtain ⟨n, hlow, hval⟩ := h
      have h1 := Number.lower_le _ n hlow
      have h0 := Number.lower_tight _ n hlow Number.zero (Or.inl rfl) (by rw [Number.toRat_zero]; exact hv)
      rw [Number.toRat_zero] at h0
      rw [hval, abs_of_nonneg h0, abs_of_nonneg hv]
      constructor
      · intro hlt
        by_contra hc
        have := Number.lower_tight _ n hlow _ hN (by rw [hNv]; exact not_lt.mp hc)
        rw [hNv] at this
        linarith
      · intro hlt
        linarith
    · -- the smallest Number at or above a negative value
      rw [ite_eq_right hv] at h
      obtain ⟨n, hup, hval⟩ := h
      have hv' : x.toRat + y.toRat < 0 := not_le.mp hv
      have h1 := Number.le_upper _ n hup
      have h0 := Number.upper_tight _ n hup Number.zero (Or.inl rfl) (by rw [Number.toRat_zero]; exact hv'.le)
      rw [Number.toRat_zero] at h0
      rw [hval, abs_of_nonpos h0, abs_of_neg hv']
      constructor
      · intro hlt
        by_contra hc
        have := Number.upper_tight _ n hup _ hN' (by rw [hNv']; linarith [not_lt.mp hc])
        rw [hNv'] at this
        linarith
      · intro hlt
        linarith
  | downward =>
    obtain ⟨n, hlow, hval⟩ := Number.operator_add_rounded_downward x y sum hx hy hadd hsum
    have h1 := Number.lower_le _ n hlow
    simp only [STAmount.RoundsInRange]
    rw [hval]
    constructor
    · rintro ⟨hlo, hhi⟩
      refine ⟨by linarith, ?_⟩
      by_contra hc
      have := Number.lower_tight _ n hlow _ hN (by rw [hNv]; exact not_lt.mp hc)
      rw [hNv] at this
      linarith
    · rintro ⟨hlo, hhi⟩
      refine ⟨?_, by linarith⟩
      have := Number.lower_tight _ n hlow _ hT' (by rw [hTv']; exact hlo)
      rwa [hTv'] at this
  | upward =>
    obtain ⟨n, hup, hval⟩ := Number.operator_add_rounded_upward x y sum hx hy hadd hsum
    have h1 := Number.le_upper _ n hup
    simp only [STAmount.RoundsInRange]
    rw [hval]
    constructor
    · rintro ⟨hlo, hhi⟩
      refine ⟨?_, by linarith⟩
      by_contra hc
      have := Number.upper_tight _ n hup _ hN' (by rw [hNv']; exact not_lt.mp hc)
      rw [hNv'] at this
      linarith
    · rintro ⟨hlo, hhi⟩
      refine ⟨by linarith, ?_⟩
      have := Number.upper_tight _ n hup _ hT (by rw [hTv]; exact hhi)
      rwa [hTv] at this

/-- An IOU amount with a zero mantissa packs into the zero `STAmount`. -/
lemma STAmount.ofIOUAmount_of_mantissa_zero (a : IOUAmount) (mode : rounding_mode) (hm : a.mantissa_ = 0) :
    STAmount.ofIOUAmount a mode = .ok ⟨.fractional, 0, -100, false⟩ := by
  have hmag : (0 : Int64).magnitude = 0 := by decide
  rw [STAmount.ofIOUAmount_of_ne mode (by rw [hm]; decide)]
  unfold STAmount.canonicalize STAmount.iou STAmount.signedDropsChecked UInt64.toInt64Checked
  simp [hm, STAmount.unchecked, STAmount.integral, NumericType.isIntegral,
    IOUAmount.ofMantissaExp, IOUAmount.normalize, hmag, IOUAmount.signum, IOUAmount.zero, ok_bind]

/-- The size of an in-range IOU amount is below `10^96`. -/
lemma IOUAmount.InRange16.abs_toRat_lt {a : IOUAmount} (ha : a.InRange16) : |a.toRat| < (10 : ℚ) ^ (96 : ℤ) := by
  rw [IOUAmount.abs_toRat_eq a]
  have hm : (a.mantissa_.toInt.natAbs : ℚ) < (10 : ℚ) ^ 16 := by exact_mod_cast ha.mant_hi
  have hpow : (10 : ℚ) ^ a.exponent_ ≤ (10 : ℚ) ^ (80 : ℤ) := zpow_le_zpow_right₀ (by norm_num) ha.exp_hi
  have hpos : (0 : ℚ) < (10 : ℚ) ^ a.exponent_ := zpow_pos (by norm_num) _
  have h96 : (10 : ℚ) ^ (96 : ℤ) = (10 : ℚ) ^ 16 * (10 : ℚ) ^ (80 : ℤ) := by norm_num
  rw [h96]
  nlinarith

/-- Adding two in-range IOU amounts returns a result exactly when the exact sum rounds into the IOU range. In
`to_nearest` this needs the exact sum to be a Number (`hfit`). -/
lemma IOUAmount.operator_add_ok_iff (x y : IOUAmount) (mode : rounding_mode) (hx : x.InRange16)
    (hy : y.InRange16)
    (hfit : mode = .to_nearest → ∃ n : Number, n.isNormalized ∧ n.toRat = x.toRat + y.toRat) :
    (∃ r, IOUAmount.operator_add x y mode = .ok r) ↔
      STAmount.RoundsInRange .fractional mode (x.toRat + y.toRat) := by
  have hminE : minExponent = -32768 := rfl
  have hmaxE : maxExponent = 32768 := rfl
  have hxm : x.mantissa_ ≠ 0 := by intro h; have := hx.mant_lo; rw [h] at this; simp at this
  have hym : y.mantissa_ ≠ 0 := by intro h; have := hy.mant_lo; rw [h] at this; simp at this
  obtain ⟨xn, hxn_eq, hxn_val, hxn_norm, hxn_ne⟩ := IOUAmount.toNumber_canonical x mode hx.mant_lo hx.mant_hi
    (by have := hx.exp_lo; omega) (by have := hx.exp_hi; omega)
  obtain ⟨yn, hyn_eq, hyn_val, hyn_norm, hyn_ne⟩ := IOUAmount.toNumber_canonical y mode hy.mant_lo hy.mant_hi
    (by have := hy.exp_lo; omega) (by have := hy.exp_hi; omega)

  -- the 19-digit sum never fails for IOU operands
  have hbound : |xn.toRat + yn.toRat| < 9223372036854775811 * (10 : ℚ) ^ (maxExponent : ℤ) := by
    have h1 := hx.abs_toRat_lt
    have h2 := hy.abs_toRat_lt
    have htri := abs_add_le x.toRat y.toRat
    have hpow : (10 : ℚ) ^ (96 : ℤ) ≤ (10 : ℚ) ^ (maxExponent : ℤ) :=
      zpow_le_zpow_right₀ (by norm_num) (by omega)
    have hpos : (0 : ℚ) < (10 : ℚ) ^ (96 : ℤ) := zpow_pos (by norm_num) _
    rw [hxn_val, hyn_val]
    linarith
  obtain ⟨sum, hadd⟩ := (Number.operator_add_ok_iff_proof xn yn mode hxn_norm hyn_norm hxn_ne hyn_ne).mpr hbound
  have hsn := Number.operator_add_isNormalized_any xn yn sum mode hxn_norm hyn_norm hadd
  have hiou : IOUAmount.operator_add x y mode = IOUAmount.ofNumber sum mode := by
    unfold IOUAmount.operator_add
    rw [ite_eq_right (by simpa using hym), ite_eq_right (by simpa using hxm), hxn_eq, hyn_eq]
    simp only
    rw [hadd]
  rw [← hxn_val, ← hyn_val] at hfit ⊢
  constructor
  · rintro ⟨r, hr⟩
    by_cases hr0 : r.mantissa_ = 0
    · -- a zero result means a sum below `10^-81` in size
      have hsmall := IOUAmount.operator_add_underflow_truth_small_proof x y r mode hx hy hr hr0
      rw [← hxn_val, ← hyn_val] at hsmall
      rw [STAmount.roundsInRange_fractional_iff]
      refine roundsWithinUnits_of_abs_le mode _ _ _ (zpow_pos (by norm_num) _) ?_
      have h81 : (10 : ℚ) ^ (-81 : ℤ) ≤ ((9999999999999999 : ℕ) : ℚ) * (10 : ℚ) ^ (80 : ℤ) := by norm_num
      linarith
    · rw [hiou] at hr
      have hs0 := IOUAmount.ofNumber_mantissa_ne_zero sum mode r hr hr0
      rw [← Number.operator_add_roundsInRange_iff xn yn sum mode hxn_norm hyn_norm hadd hs0 hfit,
        ← IOUAmount.ofNumber_ok_iff sum mode hsn]
      exact ⟨r, hr⟩
  · intro hrange
    rw [hiou]
    by_cases hs0 : sum.mantissa_ = 0
    · exact ⟨_, IOUAmount.ofNumber_zero_mantissa sum mode hs0⟩
    · rw [IOUAmount.ofNumber_ok_iff sum mode hsn,
        Number.operator_add_roundsInRange_iff xn yn sum mode hxn_norm hyn_norm hadd hs0 hfit]
      exact hrange

/-- A canonical IOU amount as an in-range `IOUAmount`. -/
lemma STAmount.IOUCanonical.inRange16 {s : STAmount} (hc : s.IOUCanonical) :
    (⟨s.signedDrops.toInt64, s.mOffset⟩ : IOUAmount).InRange16 := by
  have hn := STAmount.iou_canonical_mantissa_natAbs s hc
  exact ⟨by rw [hn]; exact hc.mant_lo, by rw [hn]; exact hc.mant_hi, hc.exp_lo, hc.exp_hi⟩

/-- Adding two canonical IOU `STAmount`s returns a result exactly when the `IOUAmount` addition does. -/
lemma STAmount.operator_add_iou_ok_iff_iouAmount (v1 v2 : STAmount) (mode : rounding_mode)
    (hc1 : v1.IOUCanonical) (hc2 : v2.IOUCanonical) :
    (∃ result, STAmount.operator_add v1 v2 mode = .ok result) ↔
      ∃ r, IOUAmount.operator_add ⟨v1.signedDrops.toInt64, v1.mOffset⟩ ⟨v2.signedDrops.toInt64, v2.mOffset⟩
        mode = .ok r := by
  have hcmp : STAmount.areComparable v1 v2 = true := by
    unfold STAmount.areComparable
    rw [hc1.is_fractional, hc2.is_fractional]
    rfl
  have hv2ne : v2.mValue ≠ 0 := by intro h; have := hc2.mant_lo; rw [h] at this; simp at this
  have hv1ne : v1.mValue ≠ 0 := by intro h; have := hc1.mant_lo; rw [h] at this; simp at this
  have hint1 : ¬ v1.integral = true := by
    unfold STAmount.integral; rw [hc1.is_fractional]; decide
  have hr1 := hc1.inRange16
  have hr2 := hc2.inRange16
  rw [STAmount.operator_add, ite_eq_right (by rw [hcmp]; decide), ite_eq_right (by simpa using hv2ne),
    ite_eq_right (by simpa using hv1ne), ite_eq_right hint1, STAmount.iou_canonical_id v1 mode hc1,
    STAmount.iou_canonical_id v2 mode hc2]
  simp only
  cases hadd : IOUAmount.operator_add ⟨v1.signedDrops.toInt64, v1.mOffset⟩
      ⟨v2.signedDrops.toInt64, v2.mOffset⟩ mode with
  | error err => exact iff_of_false (by simp) (by simp)
  | ok sumI =>
    refine iff_of_true ?_ ⟨sumI, rfl⟩
    simp only
    by_cases hs0 : sumI.mantissa_ = 0
    · exact ⟨_, STAmount.ofIOUAmount_of_mantissa_zero sumI mode hs0⟩
    · -- a nonzero sum is a 16-digit amount in range, which packs exactly
      have h_truth_ne := IOUAmount.operator_add_truth_ne_of_result _ _ sumI mode hr1 hr2 hadd hs0
      have hsumI_range : sumI.InRange16 :=
        IOUAmount.operator_add_InRange16_anyMode _ _ sumI mode hr1.mant_lo hr1.mant_hi hr2.mant_lo hr2.mant_hi
          (by have := hr1.exp_lo; unfold minExponent; omega) (by have := hr1.exp_hi; unfold maxExponent; omega)
          (by have := hr2.exp_lo; unfold minExponent; omega) (by have := hr2.exp_hi; unfold maxExponent; omega)
          h_truth_ne hadd hs0
      exact ⟨_, STAmount.ofIOU_canonical sumI mode hsumI_range⟩

/-- Proof of `STAmount.operator_add_ok_iff_iou`. -/
lemma STAmount.operator_add_ok_iff_iou_proof (v1 v2 : STAmount) (mode : rounding_mode) (h1 : v1.IOUCanonical)
    (h2 : v2.IOUCanonical)
    (hfit : mode = .to_nearest → ∃ n : Number, n.isNormalized ∧ n.toRat = v1.toRat + v2.toRat) :
    (∃ result, STAmount.operator_add v1 v2 mode = .ok result) ↔
      STAmount.RoundsInRange .fractional mode (v1.toRat + v2.toRat) := by
  rw [STAmount.operator_add_iou_ok_iff_iouAmount v1 v2 mode h1 h2,
    ← STAmount.iou_canonical_toRat v1 h1, ← STAmount.iou_canonical_toRat v2 h2]
  rw [← STAmount.iou_canonical_toRat v1 h1, ← STAmount.iou_canonical_toRat v2 h2] at hfit
  exact IOUAmount.operator_add_ok_iff _ _ mode h1.inRange16 h2.inRange16 hfit

/-- Proof of `STAmount.operator_sub_ok_iff_iou`. Subtraction is addition of the negated amount. -/
lemma STAmount.operator_sub_ok_iff_iou_proof (v1 v2 : STAmount) (mode : rounding_mode) (h1 : v1.IOUCanonical)
    (h2 : v2.IOUCanonical)
    (hfit : mode = .to_nearest → ∃ n : Number, n.isNormalized ∧ n.toRat = v1.toRat - v2.toRat) :
    (∃ result, STAmount.operator_sub v1 v2 mode = .ok result) ↔
      STAmount.RoundsInRange .fractional mode (v1.toRat - v2.toRat) := by
  have htruth : v1.toRat + v2.operator_neg.toRat = v1.toRat - v2.toRat := by
    rw [STAmount.operator_neg_toRat]; ring
  rw [← htruth] at hfit ⊢
  exact STAmount.operator_add_ok_iff_iou_proof v1 v2.operator_neg mode h1 h2.operator_neg hfit

end XRPL.Model.Protocol
