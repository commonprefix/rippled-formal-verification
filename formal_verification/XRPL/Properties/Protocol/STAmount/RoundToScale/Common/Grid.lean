import XRPL.Properties.Protocol.STAmount.RoundToScale.Common.Sum
import XRPL.Properties.Protocol.Number.AtExponent
import XRPL.Properties.Protocol.Number.Sub.ZeroShape
import XRPL.Properties.Protocol.Number.Add.RoundsToRepresentable
import XRPL.Properties.Protocol.STAmount.Common.OfNumberRounding

/-! # `STAmount.roundToExponent` on a grid point

An IOU amount that is a whole number of units at scale `s` is already on the `10^s` grid, so rounding
it to the scale returns it unchanged. The reference-sum pipeline is exact at every step: the sum with
`10^15` units is a 16-digit value, and the difference is the amount again. -/

namespace XRPL.Model.Protocol

/-- `IOUAmount.ofNumber` then `ofIOUAmount` repack a nonnegative 19-digit record with three trailing
zeros exactly, as the 16-digit record of the same value. -/
private lemma STAmount.repack_exact (x : Number) (mode : rounding_mode) (hx : x.isNormalized)
    (hneg : x.negative_ = false) (hm0 : x.mantissa_ ≠ 0) (hmod : x.mantissa_.toNat % 1000 = 0)
    (he_lo : (-96 : ℤ) ≤ x.exponent_ + 3) (he_hi : x.exponent_ + 3 ≤ 80) :
    IOUAmount.ofNumber x mode = .ok ⟨(x.mantissa_ / 10 / 10 / 10).toInt64, x.exponent_ + 3⟩ ∧
      STAmount.ofIOUAmount ⟨(x.mantissa_ / 10 / 10 / 10).toInt64, x.exponent_ + 3⟩ mode =
        .ok ⟨.fractional, x.mantissa_ / 10 / 10 / 10, x.exponent_ + 3, false⟩ ∧
      (⟨.fractional, x.mantissa_ / 10 / 10 / 10, x.exponent_ + 3, false⟩ : STAmount).IOUCanonical ∧
      (⟨.fractional, x.mantissa_ / 10 / 10 / 10, x.exponent_ + 3, false⟩ : STAmount).toRat = x.toRat := by
  obtain ⟨hlo, hhi⟩ := hx.mantissaBounds_nat hm0
  set q : UInt64 := x.mantissa_ / 10 / 10 / 10 with hq_def
  have hq : q.toNat = x.mantissa_.toNat / 1000 := m_div_thousand_toNat _
  have hq_lo : 10 ^ 15 ≤ q.toNat := by rw [hq]; omega
  have hq_hi : q.toNat < 10 ^ 16 := by rw [hq]; omega
  have hq_fit : q.toNat < 2 ^ 63 := by omega
  have hq_pos : 0 < q.toNat := by omega
  -- the 16-digit renormalization drops the three zeros
  have hntr := normalizeToRange_16_exact x mode hlo hhi hmod
    (by unfold minExponent; omega) (by unfold maxExponent; omega)
  rw [hneg] at hntr
  simp only [Bool.false_eq_true, if_false] at hntr
  have hof : IOUAmount.ofNumber x mode = .ok ⟨q.toInt64, x.exponent_ + 3⟩ := by
    unfold IOUAmount.ofNumber IOUAmount.fromNumber
    rw [hntr]
    simp only []
    rw [if_neg (by unfold cMaxOffset; omega), if_neg (by unfold cMinOffset; omega)]
  -- the repack keeps the mantissa and the sign
  have hnatAbs : q.toInt64.toInt.natAbs = q.toNat := by
    simpa using signed_mantissa_natAbs false q hq_fit
  have hdec : decide (q.toInt64 < 0) = false := by
    simpa using signed_mantissa_decide_neg false q hq_fit hq_pos
  have hr : (⟨q.toInt64, x.exponent_ + 3⟩ : IOUAmount).InRange16 :=
    { mant_lo := by show 10 ^ 15 ≤ q.toInt64.toInt.natAbs; rw [hnatAbs]; exact hq_lo
      mant_hi := by show q.toInt64.toInt.natAbs < 10 ^ 16; rw [hnatAbs]; exact hq_hi
      exp_lo := he_lo
      exp_hi := he_hi }
  have hpack : STAmount.ofIOUAmount ⟨q.toInt64, x.exponent_ + 3⟩ mode =
      .ok ⟨.fractional, q, x.exponent_ + 3, false⟩ := by
    rw [STAmount.ofIOU_canonical _ mode hr]
    congr 1
    show (⟨.fractional, q.toInt64.toInt.natAbs.toUInt64, x.exponent_ + 3, decide (q.toInt64 < 0)⟩ : STAmount) = _
    rw [hdec, hnatAbs]
    congr 1
    rw [← UInt64.toNat_inj, UInt64.toNat_ofNat_of_lt' (by rw [uint64_size_val]; omega)]
  have hc : (⟨.fractional, q, x.exponent_ + 3, false⟩ : STAmount).IOUCanonical :=
    ⟨rfl, hq_lo, hq_hi, he_lo, he_hi⟩
  -- the value is unchanged
  have hval : (⟨.fractional, q, x.exponent_ + 3, false⟩ : STAmount).toRat = x.toRat := by
    rw [STAmount.toRat_of_nonneg _ rfl, Number.toRat_of_nonneg x hneg]
    show (q.toNat : ℚ) * 10 ^ (x.exponent_ + 3) = (x.mantissa_.toNat : ℚ) * 10 ^ x.exponent_
    have hmul : (x.mantissa_.toNat / 1000 : ℕ) * 1000 = x.mantissa_.toNat := Nat.div_mul_cancel (by omega)
    have hcast : ((x.mantissa_.toNat / 1000 : ℕ) : ℚ) * 1000 = (x.mantissa_.toNat : ℚ) := by
      exact_mod_cast hmul
    rw [hq, zpow_add₀ (by norm_num : (10 : ℚ) ≠ 0), ← hcast]
    norm_num
    ring
  exact ⟨hof, hpack, hc, hval⟩

/-- A nonnegative canonical IOU amount that is a whole number of units at scale `s`, with `s` at least
`-81`, is already on the grid: `roundToExponent` returns it unchanged in `.to_nearest` mode. -/
lemma STAmount.roundToExponent_grid_self (value : STAmount) (s : ℤ) (k : ℕ)
    (hc : value.IOUCanonical) (hneg : value.mIsNegative = false) (hk : 1 ≤ k)
    (hval : value.toRat = (k : ℚ) * (10 : ℚ) ^ s) (h_s : (-81 : ℤ) ≤ s) (h_s_hi : s ≤ 80) :
    STAmount.roundToExponent value s .to_nearest = .ok value := by
  by_cases hexp : s ≤ value.exponent
  · exact STAmount.roundToExponent_eq_self value s _ (Or.inr (Or.inr hexp))
  push Not at hexp
  have hexp' : value.mOffset < s := hexp
  have h_int : value.integral = false := by
    unfold STAmount.integral; rw [hc.is_fractional]; rfl
  have h_mv : value.mValue ≠ 0 := by
    intro h0
    have h1 : value.mValue.toNat = 0 := by rw [h0]; rfl
    have := hc.mant_lo
    omega
  have hz : value.isZero = false := by simp [STAmount.isZero, h_mv]
  have hps : (0 : ℚ) < (10 : ℚ) ^ s := zpow_pos (by norm_num) _
  -- the amount is below `10^15` units: it sits under the first grid point with 16 digits
  have hk_hi : k < 10 ^ 15 := by
    have hv := STAmount.toRat_of_nonneg value hneg
    have hm : (value.mValue.toNat : ℚ) < 10 ^ 16 := by exact_mod_cast hc.mant_hi
    have hp : (10 : ℚ) ^ value.mOffset ≤ (10 : ℚ) ^ (s - 1) :=
      zpow_le_zpow_right₀ (by norm_num) (by omega)
    have h10 : (10 : ℚ) ^ (s - 1) * 10 = (10 : ℚ) ^ s := by
      rw [← zpow_add_one₀ (by norm_num : (10 : ℚ) ≠ 0)]; congr 1; ring
    have hlt : (k : ℚ) * 10 ^ s < 10 ^ 15 * 10 ^ s := by
      calc (k : ℚ) * 10 ^ s = value.toRat := hval.symm
        _ = (value.mValue.toNat : ℚ) * 10 ^ value.mOffset := hv
        _ ≤ (value.mValue.toNat : ℚ) * 10 ^ (s - 1) := mul_le_mul_of_nonneg_left hp (by positivity)
        _ < 10 ^ 16 * 10 ^ (s - 1) := mul_lt_mul_of_pos_right hm (zpow_pos (by norm_num) _)
        _ = 10 ^ 15 * 10 ^ s := by rw [← h10]; ring
    have hk' : (k : ℚ) < 10 ^ 15 := lt_of_mul_lt_mul_right hlt hps.le
    exact_mod_cast hk'
  have hkMin : kMinValue.toNat = 10 ^ 15 := by decide
  -- the active branch: reference, sum, difference
  unfold STAmount.roundToExponent
  rw [if_neg (by rw [h_int]; exact Bool.false_ne_true), if_neg (by rw [hz]; exact Bool.false_ne_true),
    if_neg (not_le.mpr hexp)]
  have hchk : STAmount.checked value.mNumericType kMinValue s value.negative .to_nearest =
      .ok ⟨.fractional, kMinValue, s, false⟩ := by
    rw [hc.is_fractional]
    show STAmount.checked .fractional kMinValue s value.mIsNegative .to_nearest = _
    rw [hneg]
    exact STAmount.checked_reference s false .to_nearest (by omega) h_s_hi
  rw [hchk]
  simp only []
  set refA : STAmount := ⟨.fractional, kMinValue, s, false⟩ with hrefA_def
  have hcr : refA.IOUCanonical :=
    ⟨rfl, by show 10 ^ 15 ≤ kMinValue.toNat; omega, by show kMinValue.toNat < 10 ^ 16; omega,
      by show (-96 : ℤ) ≤ s; omega, h_s_hi⟩
  have hrefA_val : refA.toRat = (10 : ℚ) ^ 15 * 10 ^ s := by
    rw [STAmount.toRat_of_nonneg refA rfl]
    show (kMinValue.toNat : ℚ) * 10 ^ s = _
    rw [hkMin]; push_cast; ring
  -- the sum with the reference is `(10^15 + k)` units, a 16-digit value, so it is exact
  rw [STAmount.operator_add_iou_unfold value refA .to_nearest hc hcr]
  set v1n : Number := ⟨value.mIsNegative, value.mValue * 10 * 10 * 10, value.mOffset - 3⟩ with hv1n_def
  set v2n : Number := ⟨refA.mIsNegative, refA.mValue * 10 * 10 * 10, refA.mOffset - 3⟩ with hv2n_def
  have hv1_norm : v1n.isNormalized :=
    lift_isNormalized _ _ _ hc.mant_lo hc.mant_hi
      (by have := hc.exp_lo; unfold minExponent; omega)
      (by have := hc.exp_hi; unfold maxExponent; omega)
  have hv2_norm : v2n.isNormalized :=
    lift_isNormalized _ _ _ hcr.mant_lo hcr.mant_hi
      (by have := hcr.exp_lo; unfold minExponent; omega)
      (by have := hcr.exp_hi; unfold maxExponent; omega)
  have hv1_val : v1n.toRat = value.toRat := lift_toRat value hc.mant_hi
  have hv2_val : v2n.toRat = refA.toRat := lift_toRat refA hcr.mant_hi
  obtain ⟨n₁, h_add₁⟩ := Number.operator_add_ok_of_exp v1n v2n .to_nearest hv1_norm hv2_norm
    (by show value.mOffset - 3 + 22 ≤ maxExponent; have := hc.exp_hi; unfold maxExponent; omega)
    (by show s - 3 + 22 ≤ maxExponent; unfold maxExponent; omega)
  obtain ⟨x₁, hx₁_norm, hx₁_neg, hx₁_mant, hx₁_val, hx₁_mod, hx₁_lo, hx₁_hi⟩ :=
    exists_normalized_of_int_mul_pow (10 ^ 15 + k) s (by omega) (by omega)
      (by unfold minExponent; omega) (by unfold maxExponent; omega)
  have hx₁_sum : x₁.toRat = v1n.toRat + v2n.toRat := by
    rw [hx₁_val, hv1_val, hv2_val, hval, hrefA_val]; push_cast; ring
  have hn₁_val : n₁.toRat = x₁.toRat :=
    (Number.roundsToRepresentable_eq n₁ _
      (operator_add_rounded_to_nearest _ _ _ hv1_norm hv2_norm h_add₁) x₁ hx₁_norm hx₁_sum).trans
      hx₁_sum.symm
  have hn₁ : n₁ = x₁ :=
    (operator_add_isNormalized_to_nearest_sz _ _ _ hv1_norm hv2_norm h_add₁).toRat_inj hx₁_norm hn₁_val
  rw [hn₁] at h_add₁
  obtain ⟨hof₁, hpack₁, hsum_c, hsum_val⟩ :=
    STAmount.repack_exact x₁ .to_nearest hx₁_norm hx₁_neg hx₁_mant hx₁_mod (by omega) (by omega)
  set sum : STAmount := ⟨.fractional, x₁.mantissa_ / 10 / 10 / 10, x₁.exponent_ + 3, false⟩ with hsum_def
  rw [h_add₁]
  simp only []
  rw [hof₁]
  simp only []
  rw [hpack₁]
  simp only []
  -- taking the reference back is exact too: the difference is the amount
  unfold STAmount.operator_sub
  have h_negRef : refA.operator_neg = ⟨.fractional, kMinValue, s, true⟩ := by
    rw [STAmount.operator_neg_of_ne refA (by show kMinValue ≠ 0; decide)]
    rfl
  rw [h_negRef]
  set negRef : STAmount := ⟨.fractional, kMinValue, s, true⟩ with hnegRef_def
  have hcneg : negRef.IOUCanonical :=
    ⟨rfl, by show 10 ^ 15 ≤ kMinValue.toNat; omega, by show kMinValue.toNat < 10 ^ 16; omega,
      by show (-96 : ℤ) ≤ s; omega, h_s_hi⟩
  have hnegRef_val : negRef.toRat = -((10 : ℚ) ^ 15 * 10 ^ s) := by
    rw [STAmount.toRat_of_neg negRef rfl]
    show -((kMinValue.toNat : ℚ) * 10 ^ s) = _
    rw [hkMin]; push_cast; ring
  rw [STAmount.operator_add_iou_unfold sum negRef .to_nearest hsum_c hcneg]
  set s1n : Number := ⟨sum.mIsNegative, sum.mValue * 10 * 10 * 10, sum.mOffset - 3⟩ with hs1n_def
  set s2n : Number := ⟨negRef.mIsNegative, negRef.mValue * 10 * 10 * 10, negRef.mOffset - 3⟩
    with hs2n_def
  have hs1_norm : s1n.isNormalized :=
    lift_isNormalized _ _ _ hsum_c.mant_lo hsum_c.mant_hi
      (by have := hsum_c.exp_lo; unfold minExponent; omega)
      (by have := hsum_c.exp_hi; unfold maxExponent; omega)
  have hs2_norm : s2n.isNormalized :=
    lift_isNormalized _ _ _ hcneg.mant_lo hcneg.mant_hi
      (by have := hcneg.exp_lo; unfold minExponent; omega)
      (by have := hcneg.exp_hi; unfold maxExponent; omega)
  have hs1_val : s1n.toRat = sum.toRat := lift_toRat sum hsum_c.mant_hi
  have hs2_val : s2n.toRat = negRef.toRat := lift_toRat negRef hcneg.mant_hi
  have hs1_mant : s1n.mantissa_ ≠ 0 := by
    intro h0
    have h1 : s1n.mantissa_.toNat = 0 := by rw [h0]; rfl
    have hM : (sum.mValue * 10 * 10 * 10).toNat = sum.mValue.toNat * 1000 :=
      m_mul_thousand_no_overflow hsum_c.mant_hi
    have h2 : s1n.mantissa_.toNat = sum.mValue.toNat * 1000 := hM
    have := hsum_c.mant_lo
    omega
  have hs2_mant : s2n.mantissa_ ≠ 0 := by
    intro h0
    have h1 : s2n.mantissa_.toNat = 0 := by rw [h0]; rfl
    have h2 : s2n.mantissa_.toNat = 10 ^ 18 := by
      show (kMinValue * 10 * 10 * 10).toNat = 10 ^ 18
      decide
    omega
  have h_diff : s1n.negative_ ≠ s2n.negative_ := by
    show false ≠ true
    decide
  obtain ⟨n₂, h_add₂⟩ := Number.operator_add_ok_of_exp s1n s2n .to_nearest hs1_norm hs2_norm
    (by show x₁.exponent_ + 3 - 3 + 22 ≤ maxExponent; unfold maxExponent; omega)
    (by show s - 3 + 22 ≤ maxExponent; unfold maxExponent; omega)
  obtain ⟨w, hw_norm, hw_neg, hw_mant, hw_val, hw_mod, hw_lo, hw_hi⟩ :=
    exists_normalized_of_int_mul_pow k s hk (by omega)
      (by unfold minExponent; omega) (by unfold maxExponent; omega)
  have hw_sum : w.toRat = s1n.toRat + s2n.toRat := by
    rw [hw_val, hs1_val, hs2_val, hsum_val, hx₁_val, hnegRef_val]; push_cast; ring
  have hn₂_val : n₂.toRat = w.toRat := by
    rw [operator_add_exact_diff_sign s1n s2n n₂ .to_nearest hs1_norm hs2_norm hs1_mant hs2_mant h_diff
      w hw_norm hw_sum h_add₂]
    exact hw_sum.symm
  have hn₂ : n₂ = w :=
    (operator_add_isNormalized_to_nearest_sz _ _ _ hs1_norm hs2_norm h_add₂).toRat_inj hw_norm hn₂_val
  rw [hn₂] at h_add₂
  obtain ⟨hof₂, hpack₂, hr_c, hr_val⟩ :=
    STAmount.repack_exact w .to_nearest hw_norm hw_neg hw_mant hw_mod (by omega) (by omega)
  rw [h_add₂]
  simp only []
  rw [hof₂]
  simp only []
  rw [hpack₂]
  -- the repacked grid point is the amount itself
  have hr0 : (⟨.fractional, w.mantissa_ / 10 / 10 / 10, w.exponent_ + 3, false⟩ : STAmount).mValue ≠ 0 := by
    intro h0
    have := hr_c.mant_lo
    rw [h0] at this
    exact absurd this (by decide)
  have hr_eq : (⟨.fractional, w.mantissa_ / 10 / 10 / 10, w.exponent_ + 3, false⟩ : STAmount) = value :=
    STAmount.eq_of_exactCanonical _ value (Or.inl hr_c) (Or.inl hc)
      (by rw [hc.is_fractional]) hr0 (by rw [hr_val, hw_val, hval])
  rw [hr_eq]

end XRPL.Model.Protocol
