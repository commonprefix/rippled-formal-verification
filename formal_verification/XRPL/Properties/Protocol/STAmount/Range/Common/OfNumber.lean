import XRPL.Properties.Protocol.STAmount.Range.Common.Checked
import XRPL.Properties.Protocol.STAmount.Range.Common.IOU16
import XRPL.Properties.Protocol.STAmount.FromNumber.Common.RoundsProofs

/-! # When `STAmount.ofNumber` returns a result

`ofNumber` drops the sign of the Number, rounds the size in the mode and puts the sign back. For XRP and MPT the
size is rounded to a whole number by `Number.to_rep`. For IOU it is rounded to 16 digits. -/

namespace XRPL.Model.Protocol

/-- `to_rep` reads a Number only through its public mantissa and exponent. -/
lemma Number.to_rep_eq_unchecked (n : Number) (mode : rounding_mode) :
    n.to_rep mode = (Number.unchecked n.negative_
      (if n.mantissa_ > maxRep then n.mantissa_ / 10 else n.mantissa_) n.exponent).to_rep mode := by
  have hle : ¬ (if n.mantissa_ > maxRep then n.mantissa_ / 10 else n.mantissa_) > maxRep := by
    rw [gt_iff_lt, UInt64.lt_iff_toNat_lt]
    have h63 : maxRep.toNat = 9223372036854775807 := by decide
    have hlt := UInt64.toNat_lt_size n.mantissa_
    rw [uint64_size_val] at hlt
    split
    · rw [UInt64.toNat_div, uint64_ten_toNat]
      omega
    · rename_i h
      have := UInt64.le_iff_toNat_le.mp (UInt64.not_lt.mp h)
      omega
  have h1 : (Number.unchecked n.negative_
      (if n.mantissa_ > maxRep then n.mantissa_ / 10 else n.mantissa_) n.exponent).mantissa = n.mantissa := by
    dsimp +instances only [Number.mantissa, Number.unchecked]
    rw [ite_eq_right hle]
  have h2 : (Number.unchecked n.negative_
      (if n.mantissa_ > maxRep then n.mantissa_ / 10 else n.mantissa_) n.exponent).exponent = n.exponent := by
    dsimp +instances only [Number.exponent, Number.unchecked]
    rw [ite_eq_right hle]
  rw [Number.to_rep_eq_spec, Number.to_rep_eq_spec]
  unfold Number.to_repSpec
  simp only [h1, h2]
  rfl

/-- `to_rep` on a normalized Number that is not negative. The value splits into a whole part `q` and a fraction
`f`. The result is `q` or `q + 1`, or an error when that is above `maxRep`. -/
lemma Number.to_rep_nonneg_eq (w : Number) (mode : rounding_mode) (hw : w.isNormalized)
    (hneg : w.negative_ = false) :
    ∃ (q : ℤ) (f : ℚ) (up : Bool), 0 ≤ q ∧ 0 ≤ f ∧ f < 1 ∧ w.toRat = (q : ℚ) + f ∧
      (up = true ↔ RoundsUp mode false q f) ∧
      (q + (if up = true then 1 else 0) ≤ (maxRep.toNat : ℤ) →
        ∃ r : Int64, w.to_rep mode = .ok r ∧ r.toInt = q + (if up = true then 1 else 0)) ∧
      ((maxRep.toNat : ℤ) < q + (if up = true then 1 else 0) → ∃ err, w.to_rep mode = .error err) := by
  set m' : UInt64 := if w.mantissa_ > maxRep then w.mantissa_ / 10 else w.mantissa_ with hm'
  have h63 : maxRep.toNat = 9223372036854775807 := by decide
  have hm'_nat : (m'.toNat : ℤ) = w.mantissa.toInt := by
    rw [Number.mantissa_toInt w, hneg, hm']
    simp only [Bool.false_eq_true, ite_false, one_mul]
    split
    · rw [UInt64.toNat_div, uint64_ten_toNat]
    · rfl
  have hm'_le : m'.toNat ≤ maxRep.toNat := by
    have := Number.mantissa_natAbs_le w
    omega
  have hval : (m'.toNat : ℚ) * 10 ^ w.exponent = w.toRat := by
    rw [← Number.mantissa_mul_exponent_eq_toRat w hw, ← hm'_nat]
    norm_cast
  obtain ⟨q, f, up, hq, hf0, hf1, hqf, hup, hok, herr⟩ :=
    Number.to_rep_unchecked_eq false m' w.exponent mode hm'_le
  have hrep : w.to_rep mode = (Number.unchecked false m' w.exponent).to_rep mode := by
    rw [Number.to_rep_eq_unchecked w mode, hneg]
  rw [← hrep] at hok herr
  refine ⟨q, f, up, hq, hf0, hf1, by rw [← hval, hqf], hup, fun h => ?_, herr⟩
  obtain ⟨r, hr, hrv⟩ := hok h
  exact ⟨r, hr, by simpa using hrv⟩

/-- `ofNumber` on an integral type returns a result exactly when the Number rounds into range. The type must have
`1 ≤ maxValue ≤ 2^63 - 1` and `maxValue < 10 ^ (maxOffset + 1)`, as XRP and MPT do. -/
lemma STAmount.ofNumber_ok_iff_integral (mv : UInt64) (mo : Int) (ms msh : UInt64) (n : Number)
    (mode : rounding_mode) (hn : n.isNormalized)
    (hsign : 0 ≤ n.toRat ∨ mode = .to_nearest ∨ mode = .towards_zero)
    (hmv1 : 1 ≤ mv.toNat) (hmv : mv.toNat ≤ 9223372036854775807)
    (hmo : (mv.toNat : ℚ) + 1 ≤ (10 : ℚ) ^ (mo + 1)) :
    (∃ result, STAmount.ofNumber (.integral mv mo ms msh) n mode = .ok result) ↔
      STAmount.RoundsInRange (.integral mv mo ms msh) mode n.toRat := by
  have h63 : maxRep.toNat = 9223372036854775807 := by decide
  obtain ⟨hw_norm, hw_neg, -, -, hw_val⟩ := STAmount.ofNumber_working_facts n hn
  unfold STAmount.ofNumber
  dsimp +instances only [NumericType.isIntegral]
  rw [ite_eq_left rfl]
  set w : Number := if decide (n.signum < 0) = true then n.operator_neg else n with hw
  obtain ⟨q, f, up, hq, hf0, hf1, hwq, hup, hok, herr⟩ := Number.to_rep_nonneg_eq w mode hw_norm hw_neg

  -- the sign does not change whether one is added, under `hsign`
  have hup' : up = true ↔ RoundsUp mode n.negative_ q f := by
    rcases hsign with h0 | hmode
    · rw [Number.negative_false_of_nonneg n hn h0]
      exact hup
    · exact hup.trans (roundsUp_sign_irrelevant mode false n.negative_ q f hmode)
  rw [STAmount.roundsInRange_integral_iff, hw_val, hwq,
    ← mul_one ((if n.negative_ = true then (-1 : ℚ) else 1) * ((q : ℚ) + f)),
    ← roundsWithinUnits_iff mode n.negative_ q mv.toNat f 1 up hq hf0 hf1 one_pos hup']
  have hc0 : 0 ≤ q + (if up = true then 1 else 0) := by split <;> omega
  by_cases hfit : q + (if up = true then 1 else 0) ≤ (maxRep.toNat : ℤ)
  · -- the whole number fits `int64`, and `checked` compares it with the largest amount
    obtain ⟨r, hr, hrv⟩ := hok hfit
    rw [hr]
    simp only []
    rw [Int64.toUInt64Checked_of_nonneg (Int64.le_iff_toInt_le.mpr (by simpa [hrv] using hc0)), ok_bind]
    have hru : (r.toUInt64.toNat : ℤ) = q + (if up = true then 1 else 0) := by
      rw [toUInt64_toNat_of_nonneg r (by rw [hrv]; exact hc0), hrv]
    rw [STAmount.checked_ok_iff_integral mv mo ms msh r.toUInt64 0 _ mode (by omega) hmv1 hmv hmo,
      STAmount.roundsInRange_integral_iff, STAmount.unchecked_toRat]
    have hval0 : (r.toUInt64.toNat : ℚ) * 10 ^ (0 : ℤ)
        = ((q + (if up = true then 1 else 0) : ℤ) : ℚ) + 0 := by
      rw [zpow_zero, mul_one, add_zero, ← hru]
      norm_cast
    rw [hval0, ← mul_one ((if decide (n.signum < 0) = true then (-1 : ℚ) else 1) * _),
      ← roundsWithinUnits_iff mode (decide (n.signum < 0)) _ mv.toNat 0 1 false hc0 (le_refl _) (by norm_num)
        one_pos ⟨fun h => absurd h (by decide), fun h => absurd h (not_roundsUp_zero mode _ _)⟩]
    simp
  · -- the whole number does not fit `int64`
    obtain ⟨err, herr'⟩ := herr (by omega)
    rw [herr']
    exact iff_of_false (by simp) (by omega)

/-- In `to_nearest` and `towards_zero` a value is in range exactly when its negation is. -/
lemma STAmount.roundsInRange_neg_iff (nt : NumericType) (mode : rounding_mode)
    (hmode : mode = .to_nearest ∨ mode = .towards_zero) (v : ℚ) :
    STAmount.RoundsInRange nt mode (-v) ↔ STAmount.RoundsInRange nt mode v := by
  rcases hmode with rfl | rfl <;> cases nt <;> simp only [STAmount.RoundsInRange, abs_neg]

/-- `checked` on a 16-digit IOU mantissa returns a result exactly when the exponent is at most 80. -/
lemma STAmount.checked_iou16_ok_iff (mant : UInt64) (exp : Int) (neg : Bool) (mode : rounding_mode)
    (h_lo : 10 ^ 15 ≤ mant.toNat) (h_hi : mant.toNat < 10 ^ 16)
    (he_lo : minExponent + 3 ≤ exp) (he_hi : exp ≤ maxExponent) :
    (∃ result, STAmount.checked .fractional mant exp neg mode = .ok result) ↔ exp ≤ cMaxOffset := by
  have h_fit : mant.toNat < 2 ^ 63 := by omega
  have h_int : ¬ (STAmount.unchecked .fractional mant exp neg).integral = true := by
    simp [STAmount.integral, STAmount.unchecked, NumericType.isIntegral]
  have h_sd : (STAmount.unchecked .fractional mant exp neg).signedDrops.toInt64
      = if neg then -mant.toInt64 else mant.toInt64 := by
    apply Int64.toInt_inj.mp
    rw [STAmount.signedDrops_toInt64_toInt _
          (show (STAmount.unchecked .fractional mant exp neg).mValue.toNat < 10 ^ 16 from h_hi),
        signed_mantissa_toInt neg mant h_fit]
    show (STAmount.unchecked .fractional mant exp neg).signedDrops = _
    unfold STAmount.signedDrops STAmount.unchecked
    rcases neg <;> simp
  have hiou : (STAmount.unchecked .fractional mant exp neg).iou mode
      = (if exp > cMaxOffset then .error .overflow
         else if exp < cMinOffset then .ok IOUAmount.zero
         else .ok ⟨if neg then -mant.toInt64 else mant.toInt64, exp⟩) := by
    rw [STAmount.iou_eq mode h_int h_fit]
    unfold IOUAmount.ofMantissaExp
    rw [h_sd]
    exact IOUAmount.normalize_canonical16 mant exp neg mode h_lo h_hi he_lo he_hi
  rw [STAmount.checked]
  unfold STAmount.canonicalize
  rw [ite_eq_right h_int, hiou]
  by_cases hhi : exp > cMaxOffset
  · rw [ite_eq_left hhi]
    exact iff_of_false (by simp) (by omega)
  · rw [ite_eq_right hhi]
    refine iff_of_true ?_ (by omega)
    by_cases hlo : exp < cMinOffset
    · rw [ite_eq_left hlo]
      exact ⟨_, rfl⟩
    · rw [ite_eq_right hlo]
      exact ⟨_, rfl⟩

/-- An IOU `ofNumber` returns a result exactly when the 16-digit rounding of the Number without its sign does. -/
lemma STAmount.ofNumber_fractional_ok_iff_iou (n : Number) (mode : rounding_mode) (hn : n.isNormalized) :
    (∃ result, STAmount.ofNumber .fractional n mode = .ok result) ↔
      ∃ r, IOUAmount.ofNumber (if decide (n.signum < 0) = true then n.operator_neg else n) mode = .ok r := by
  by_cases hm0 : n.mantissa_ = 0
  · -- zero
    rw [Number.eq_zero_of_mantissa_zero n hn hm0, STAmount.ofNumber_fractional_zero]
    exact iff_of_true ⟨_, rfl⟩ ⟨_, IOUAmount.ofNumber_zero_mantissa _ mode rfl⟩
  obtain ⟨-, hw_neg, hw_mant, hw_exp, -⟩ := STAmount.ofNumber_working_facts n hn
  obtain ⟨h_lo, h_hi⟩ := mantissaBounds_nat_of (hn.mantissaBounds hm0)
  have hemin := Number.exponent_ge_min n hn hm0
  unfold STAmount.ofNumber
  rw [ite_eq_right (by decide)]
  set w : Number := if decide (n.signum < 0) = true then n.operator_neg else n with hw
  have hw_lo : 10 ^ 18 ≤ w.mantissa_.toNat := by rw [hw_mant]; exact h_lo
  have hw_hi : w.mantissa_.toNat < 10 ^ 19 := by rw [hw_mant]; exact h_hi
  cases hnorm : w.normalizeToRange kMinValue kMaxValue mode with
  | error err =>
    have hnorm' : w.normalizeToRange cMinValue cMaxValue mode = .error err := hnorm
    refine iff_of_false (by simp) ?_
    rintro ⟨r, hr⟩
    unfold IOUAmount.ofNumber IOUAmount.fromNumber at hr
    rw [hnorm'] at hr
    exact absurd hr (by simp)
  | ok me =>
    obtain ⟨mant, exp⟩ := me
    have hnorm' : w.normalizeToRange cMinValue cMaxValue mode = .ok (mant, exp) := hnorm
    rw [IOUAmount.ofNumber_ok_iff_of_norm w mode mant exp hnorm']
    simp only
    have hexp3 := normalizeToRange_iou_exp_hi w mode mant exp hw_lo hw_hi hnorm'
    obtain ⟨⟨hmlo, hmhi⟩, ⟨hexp_lo3, hexp_le⟩, hsgn⟩ :=
      normalizeToRange_iou_ok_facts w mode mant exp hw_lo hw_hi (by omega) hexp3 hnorm'
    have hmant_pos : 0 ≤ mant.toInt := hsgn.1 hw_neg
    have hmant_natAbs : mant.toInt.natAbs = mant.toUInt64.toNat := by
      have := toUInt64_toNat_of_nonneg mant hmant_pos; omega
    have hmtu_lo : 10 ^ 15 ≤ mant.toUInt64.toNat := by
      rw [← hmant_natAbs]; exact hmlo
    have hmtu_hi : mant.toUInt64.toNat < 10 ^ 16 := by
      rw [← hmant_natAbs]
      have h := hmhi
      rw [show cMaxValue.toNat = 10 ^ 16 - 1 from by decide] at h
      omega
    rw [Int64.toUInt64Checked_of_nonneg (Int64.le_iff_toInt_le.mpr (by simpa using hmant_pos)), ok_bind]
    exact STAmount.checked_iou16_ok_iff mant.toUInt64 exp _ mode hmtu_lo hmtu_hi (by omega) hexp_le

/-- An IOU `ofNumber` returns a result exactly when the Number rounds into the IOU range. -/
lemma STAmount.ofNumber_ok_iff_fractional (n : Number) (mode : rounding_mode) (hn : n.isNormalized)
    (hsign : 0 ≤ n.toRat ∨ mode = .to_nearest ∨ mode = .towards_zero) :
    (∃ result, STAmount.ofNumber .fractional n mode = .ok result) ↔
      STAmount.RoundsInRange .fractional mode n.toRat := by
  obtain ⟨hw_norm, -, -, -, hw_val⟩ := STAmount.ofNumber_working_facts n hn
  rw [STAmount.ofNumber_fractional_ok_iff_iou n mode hn, IOUAmount.ofNumber_ok_iff _ mode hw_norm, hw_val]
  rcases hsign with h0 | hmode
  · rw [Number.negative_false_of_nonneg n hn h0]
    simp
  · rcases n.negative_ with _ | _
    · simp
    · simp only [ite_true, neg_one_mul]
      exact (STAmount.roundsInRange_neg_iff .fractional mode hmode _).symm

/-- Proof of `STAmount.ofNumber_ok_iff`. -/
lemma STAmount.ofNumber_ok_iff_proof (nt : NumericType) (n : Number) (mode : rounding_mode)
    (hn : n.isNormalized) (hnt : nt = .fractional ∨ nt = NumericType.native ∨ nt = NumericType.int64)
    (hsign : 0 ≤ n.toRat ∨ mode = .to_nearest ∨ mode = .towards_zero) :
    (∃ result, STAmount.ofNumber nt n mode = .ok result) ↔ STAmount.RoundsInRange nt mode n.toRat := by
  rcases hnt with rfl | rfl | rfl
  · exact STAmount.ofNumber_ok_iff_fractional n mode hn hsign
  · exact STAmount.ofNumber_ok_iff_integral 100000000000000000 17 3000000000 2095475792 n mode hn hsign
      (by decide) (by decide) (by
        show ((100000000000000000 : ℕ) : ℚ) + 1 ≤ _
        norm_num)
  · exact STAmount.ofNumber_ok_iff_integral 9223372036854775807 18 3037000499 2147483648 n mode hn hsign
      (by decide) (by decide) (by
        show ((9223372036854775807 : ℕ) : ℚ) + 1 ≤ _
        norm_num)

end XRPL.Model.Protocol
