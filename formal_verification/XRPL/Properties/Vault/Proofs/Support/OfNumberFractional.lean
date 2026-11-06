import XRPL.Properties.Protocol.STAmount.Common.OfNumberBoundary

/-! # A fractional `ofNumber` that cannot throw

The IOU conversion rounds a 19-digit value to 16 digits and stores it. It throws only when the
rounded exponent passes the IOU ceiling, so a value well inside the IOU range always converts. -/

namespace XRPL.Model.Protocol

/-- The 16-digit `normalizeToRange` of a 19-digit value never throws while the exponent leaves room
for a carry. -/
lemma normalizeToRange_16_ok (n : Number) (mode : rounding_mode)
    (h_lo : 10 ^ 18 ≤ n.mantissa_.toNat) (h_hi : n.mantissa_.toNat < 10 ^ 19)
    (he_lo : minExponent ≤ n.exponent_ + 3) (he_hi : n.exponent_ + 4 ≤ maxExponent) :
    ∃ p, n.normalizeToRange cMinValue cMaxValue mode = .ok p := by
  obtain ⟨g, -, -, -, h_red⟩ :=
    doNormalize_small_facts n.negative_ n.mantissa_ n.exponent_ mode h_lo h_hi he_lo (by omega)
  have hm3 : (n.mantissa_ / 10 / 10 / 10).toNat = n.mantissa_.toNat / 1000 :=
    m_div_thousand_toNat n.mantissa_
  have hcMax : cMaxValue.toNat = 10 ^ 16 - 1 := by decide
  have hcMin : cMinValue.toNat = 10 ^ 15 := by decide
  unfold Number.normalizeToRange
  rw [h_red]
  by_cases hround : (g.round mode == 1
      || (g.round mode == 0 && (n.mantissa_ / 10 / 10 / 10) % 2 == 1)) = true
  · by_cases hcusp : n.mantissa_ / 10 / 10 / 10 = cMaxValue
    · -- the carry at the top of the range moves up one exponent
      rw [hcusp, doRoundUp_small_cusp g n.negative_ (n.exponent_ + 3) mode
        .normalize2 (by rw [hcusp] at hround; exact hround) (by omega) (by omega)]
      exact ⟨_, by ntr_tail⟩
    · have hlt : n.mantissa_.toNat / 1000 < cMaxValue.toNat := by
        have hne : (n.mantissa_ / 10 / 10 / 10).toNat ≠ cMaxValue.toNat :=
          fun h => hcusp (UInt64.toNat_inj.mp h)
        rw [hcMax, hm3] at hne; rw [hcMax]; omega
      rw [doRoundUp_small_fire g n.negative_ _ (n.exponent_ + 3) mode
        .normalize2 hround (by rw [hcMin, hm3]; omega) (by rw [hm3]; exact hlt) (by omega) (by omega)]
      exact ⟨_, by ntr_tail⟩
  · rw [doRoundUp_small_truncate g n.negative_ _ (n.exponent_ + 3) mode
      .normalize2 (by simpa using hround) (by rw [hcMin, hm3]; omega)
      (by rw [hcMax, hm3]; omega) (by omega) (by omega)]
    exact ⟨_, by ntr_tail⟩

/-- A fractional `ofNumber` of a nonzero 19-digit value never throws while the rounded exponent
stays at or below the IOU ceiling `cMaxOffset`. -/
lemma STAmount.ofNumber_fractional_ok (r : Number) (mode : rounding_mode)
    (hr_lo : 10 ^ 18 ≤ r.mantissa_.toNat) (hr_hi : r.mantissa_.toNat < 10 ^ 19)
    (hre_lo : minExponent ≤ r.exponent_) (hre_hi : r.exponent_ + 4 ≤ cMaxOffset) :
    ∃ result, STAmount.ofNumber .fractional r mode = .ok result := by
  have hr_ne : r.mantissa_ ≠ 0 := by intro h; rw [h] at hr_lo; simp at hr_lo
  have hmne : (r.mantissa_ != 0) = true := by simp [hr_ne]
  have hneg_eq : decide (r.signum < 0) = r.negative_ := by
    unfold Number.signum
    rcases hrn : r.negative_ with _ | _ <;>
      simp only [hmne, if_true, if_false, Bool.false_eq_true] <;> decide
  set neg : Bool := decide (r.signum < 0) with hneg_def
  set working : Number := if neg then r.operator_neg else r with hw_def
  have hw_mant : working.mantissa_ = r.mantissa_ := by
    rw [hw_def]; rcases neg with _ | _
    · simp
    · simp [Number.operator_neg_mantissa_of_ne r hr_ne]
  have hw_exp : working.exponent_ = r.exponent_ := by
    rw [hw_def]; rcases neg with _ | _
    · simp
    · simp only [if_true]; unfold Number.operator_neg; rw [if_neg (by simpa using hr_ne)]
  have hw_neg : working.negative_ = false := by
    rw [hw_def, hneg_eq]
    by_cases hrn : r.negative_ = true
    · rw [if_pos hrn, Number.operator_neg_negative_of_ne r hr_ne]; simp [hrn]
    · rw [if_neg hrn]; simpa using hrn
  have hw_lo : 10 ^ 18 ≤ working.mantissa_.toNat := by rw [hw_mant]; exact hr_lo
  have hw_hi : working.mantissa_.toNat < 10 ^ 19 := by rw [hw_mant]; exact hr_hi
  have hme : maxExponent = 32768 := rfl
  have hco : cMaxOffset = 80 := rfl
  -- the 16-digit rounding succeeds, with a canonical mantissa and an exponent at most one above
  obtain ⟨⟨mant, exp⟩, hnorm⟩ := normalizeToRange_16_ok working mode hw_lo hw_hi
    (by rw [hw_exp]; omega) (by rw [hw_exp]; omega)
  obtain ⟨⟨hmlo, hmhi⟩, ⟨hexp_lo3, -⟩, hsgn⟩ :=
    normalizeToRange_iou_ok_facts working mode mant exp hw_lo hw_hi (by rw [hw_exp]; omega)
      (by rw [hw_exp]; omega) hnorm
  have hexp_hi := (normalizeToRange_16_exp_range working mode mant exp hw_lo hw_hi
    (by rw [hw_exp]; omega) (by rw [hw_exp]; omega) hnorm).2
  have hmant_pos : 0 ≤ mant.toInt := hsgn.1 hw_neg
  have hmant_natAbs : mant.toInt.natAbs = mant.toUInt64.toNat := by
    have := toUInt64_toNat_of_nonneg mant hmant_pos; omega
  have hmtu_lo : 10 ^ 15 ≤ mant.toUInt64.toNat := by
    rw [← hmant_natAbs]; have := hmlo; rw [(by decide : cMinValue.toNat = 10 ^ 15)] at this
    exact this
  have hmtu_hi : mant.toUInt64.toNat < 10 ^ 16 := by
    rw [← hmant_natAbs]; have := hmhi; rw [(by decide : cMaxValue.toNat = 10 ^ 16 - 1)] at this
    omega
  -- the stored IOU amount is the rounded mantissa at an exponent within the ceiling
  have hnorm' : working.normalizeToRange kMinValue kMaxValue mode = .ok (mant, exp) := hnorm
  unfold STAmount.ofNumber
  rw [if_neg (by decide), ← hneg_def, ← hw_def, hnorm']
  simp only []
  rw [Int64.toUInt64Checked_of_nonneg (Int64.le_iff_toInt_le.mpr (by simpa using hmant_pos)), ok_bind]
  have h_int : ¬ (STAmount.unchecked .fractional mant.toUInt64 exp neg).integral = true := by
    simp [STAmount.integral, STAmount.unchecked, NumericType.isIntegral]
  have h_fit : mant.toUInt64.toNat < 2 ^ 63 := by omega
  have h_sd : (STAmount.unchecked .fractional mant.toUInt64 exp neg).signedDrops.toInt64
      = if neg then -mant.toUInt64.toInt64 else mant.toUInt64.toInt64 := by
    apply Int64.toInt_inj.mp
    rw [STAmount.signedDrops_toInt64_toInt _
          (show (STAmount.unchecked .fractional mant.toUInt64 exp neg).mValue.toNat < 10 ^ 16 from hmtu_hi),
        signed_mantissa_toInt neg mant.toUInt64 h_fit]
    show (STAmount.unchecked .fractional mant.toUInt64 exp neg).signedDrops = _
    unfold STAmount.signedDrops STAmount.unchecked
    rcases neg <;> simp
  have hiou : (STAmount.unchecked .fractional mant.toUInt64 exp neg).iou mode
      = (if exp > cMaxOffset then .error .overflow
         else if exp < cMinOffset then .ok IOUAmount.zero
         else .ok ⟨if neg then -mant.toUInt64.toInt64 else mant.toUInt64.toInt64, exp⟩) := by
    unfold STAmount.iou
    rw [if_neg h_int]
    unfold IOUAmount.ofMantissaExp
    rw [STAmount.signedDrops_toInt64Checked _ h_fit, ok_bind, h_sd]
    exact IOUAmount.normalize_canonical16 mant.toUInt64 exp neg mode hmtu_lo hmtu_hi
      (by rw [hw_exp] at hexp_lo3; omega) (by omega)
  rw [STAmount.checked]
  unfold STAmount.canonicalize
  rw [if_neg h_int, hiou, if_neg (by rw [hw_exp] at hexp_hi; omega)]
  split_ifs <;> exact ⟨_, rfl⟩

end XRPL.Model.Protocol
