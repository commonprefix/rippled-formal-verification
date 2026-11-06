import XRPL.Properties.Protocol.Number.Mul.RoundsWithin
import XRPL.Properties.Protocol.Number.Mul.Common.Decompose
import XRPL.Properties.Protocol.Number.Common.Rounding.SmallRangeBound
import XRPL.Properties.Protocol.Number.Common.Rounding.SmallRange
import XRPL.Properties.Protocol.STAmount.Add.Common.IOU
import XRPL.Properties.Protocol.STAmount.Common.RoundToScaleHelpers
import XRPL.Properties.Protocol.STAmount.Common.DiscreteDefs
import XRPL.Properties.Protocol.Number.Common.Int64Lemmas

/-! # IOU re-rounding to 16 digits

`STAmount.ofNumber` rounds a 19-digit `Number` back to a 16-digit IOU amount within one ULP, and within half a ULP
in `to_nearest`. The file also covers `checked` and `toNumber` on canonical IOU amounts. -/

namespace XRPL.Model.Protocol

/-- `IOUAmount.normalize` on a canonical 16-digit signed mantissa. The 19-digit re-lift and 16-digit
re-round are exact, so the only effect is the `[cMinOffset, cMaxOffset]` exponent clamp. -/
lemma IOUAmount.normalize_canonical16 (mant : UInt64) (exp : Int) (neg : Bool) (mode : rounding_mode)
    (h_lo : 10 ^ 15 ≤ mant.toNat) (h_hi : mant.toNat < 10 ^ 16)
    (he_lo : minExponent + 3 ≤ exp) (he_hi : exp ≤ maxExponent) :
    IOUAmount.normalize ⟨if neg then -mant.toInt64 else mant.toInt64, exp⟩ mode
      = (if exp > cMaxOffset then .error .overflow
         else if exp < cMinOffset then .ok IOUAmount.zero
         else .ok ⟨if neg then -mant.toInt64 else mant.toInt64, exp⟩) := by
  have h_fit : mant.toNat < 2 ^ 63 := by omega
  set sd : Int64 := if neg then -mant.toInt64 else mant.toInt64 with hsd
  have h_natAbs : sd.toInt.natAbs = mant.toNat := signed_mantissa_natAbs neg mant h_fit
  have h_neg_dec : decide (sd < 0) = neg := signed_mantissa_decide_neg neg mant h_fit (by omega)
  have h_mAbs : sd.toInt.natAbs.toUInt64 = mant := by
    rw [h_natAbs]
    exact UInt64.toNat_inj.mp (UInt64.toNat_ofNat_of_lt' (by rw [uint64_size_val]; omega))
  have h_sd_ne : ¬ ((⟨sd, exp⟩ : IOUAmount).mantissa_ == 0) = true := by
    show ¬ (sd == 0) = true
    rw [beq_iff_eq]; intro h
    have h0 : sd.toInt.natAbs = 0 := by rw [h]; decide
    rw [h_natAbs] at h0; omega
  unfold IOUAmount.normalize
  rw [if_neg h_sd_ne]
  have h_fr : Number.from_rep (⟨sd, exp⟩ : IOUAmount).mantissa_ (⟨sd, exp⟩ : IOUAmount).exponent_
      largeRange.min largeRange.max mode = .ok ⟨neg, mant * 10 * 10 * 10, exp - 3⟩ := by
    show Number.from_rep sd exp largeRange.min largeRange.max mode = _
    unfold Number.from_rep Number.normalized Number.normalize Number.unchecked
    rw [h_neg_dec, Int64.magnitude_eq, h_mAbs]
    exact doNormalize_large_16digit neg mant exp mode h_lo h_hi (by omega) (by omega)
  rw [h_fr]
  simp only []
  set v : Number := ⟨neg, mant * 10 * 10 * 10, exp - 3⟩ with hv_def
  have hM_toNat : (mant * 10 * 10 * 10).toNat = mant.toNat * 1000 :=
    m_mul_thousand_no_overflow h_hi
  have h_fn : IOUAmount.fromNumber v mode
      = .ok { mantissa_ := if neg then -(v.mantissa_ / 10 / 10 / 10).toInt64
                           else (v.mantissa_ / 10 / 10 / 10).toInt64,
              exponent_ := exp } := by
    unfold IOUAmount.fromNumber
    have h_ntr := normalizeToRange_16_exact v mode
      (by show 10 ^ 18 ≤ (mant * 10 * 10 * 10).toNat; rw [hM_toNat]; omega)
      (by show (mant * 10 * 10 * 10).toNat < 10 ^ 19; rw [hM_toNat]; omega)
      (by show (mant * 10 * 10 * 10).toNat % 1000 = 0; rw [hM_toNat]; omega)
      (by show minExponent ≤ exp - 3 + 3; omega)
      (by show exp - 3 + 3 ≤ maxExponent; omega)
    have h_exp_fix : v.exponent_ + 3 = exp := by show exp - 3 + 3 = exp; ring
    rw [h_exp_fix] at h_ntr
    rw [h_ntr]
  rw [h_fn]
  simp only []
  have h_q3 : v.mantissa_ / 10 / 10 / 10 = mant := by
    apply UInt64.toNat_inj.mp
    show ((mant * 10 * 10 * 10) / 10 / 10 / 10).toNat = mant.toNat
    rw [m_div_thousand_toNat (mant * 10 * 10 * 10), hM_toNat]; omega
  rw [h_q3]

/-- `STAmount.checked` on a canonical 16-digit IOU mantissa. A successful, nonzero result forces the exponent
into `[cMinOffset, cMaxOffset]` and reproduces the record exactly. -/
lemma STAmount.checked_iou_cases (nt : NumericType) (mant : UInt64) (exp : Int) (neg : Bool)
    (mode : rounding_mode)
    (hnt : nt = .fractional)
    (h_lo : 10 ^ 15 ≤ mant.toNat) (h_hi : mant.toNat < 10 ^ 16)
    (he_lo : minExponent + 3 ≤ exp) (he_hi : exp ≤ maxExponent)
    (result : STAmount)
    (hok : STAmount.checked nt mant exp neg mode = .ok result) (hresult : result.mValue ≠ 0) :
    (-96 : ℤ) ≤ exp ∧ exp ≤ 80 ∧ result = ⟨nt, mant, exp, neg⟩ := by
  subst hnt
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
    unfold STAmount.iou
    rw [if_neg h_int]
    unfold IOUAmount.ofMantissaExp
    rw [STAmount.signedDrops_toInt64Checked _ (show (STAmount.unchecked .fractional mant exp neg).mValue.toNat
      < 2 ^ 63 from h_fit), ok_bind, h_sd]
    exact IOUAmount.normalize_canonical16 mant exp neg mode h_lo h_hi he_lo he_hi
  by_cases hhi : exp > cMaxOffset
  · exfalso
    have hb : STAmount.checked .fractional mant exp neg mode = .error .overflow := by
      rw [STAmount.checked]; unfold STAmount.canonicalize
      rw [if_neg h_int, hiou, if_pos hhi]
    rw [hb] at hok; simp at hok
  · by_cases hlo : exp < cMinOffset
    · exfalso; apply hresult
      rw [STAmount.checked] at hok
      unfold STAmount.canonicalize at hok
      rw [if_neg h_int, hiou, if_neg hhi, if_pos hlo] at hok
      simp only [] at hok
      rw [← Except.ok.inj hok]
      show (if IOUAmount.zero.signum < 0 then -IOUAmount.zero.mantissa_
            else IOUAmount.zero.mantissa_).toUInt64 = 0
      decide
    · have hexp_lo : (-96 : ℤ) ≤ exp := by unfold cMinOffset at hlo; omega
      have hexp_hi : exp ≤ 80 := by unfold cMaxOffset at hhi; omega
      refine ⟨hexp_lo, hexp_hi, ?_⟩
      have hc : (⟨.fractional, mant, exp, neg⟩ : STAmount).IOUCanonical :=
        ⟨rfl, h_lo, h_hi, hexp_lo, hexp_hi⟩
      have hcid := STAmount.canonicalize_canonical_id ⟨.fractional, mant, exp, neg⟩ mode hc
      rw [STAmount.checked,
          show STAmount.unchecked .fractional mant exp neg = (⟨.fractional, mant, exp, neg⟩ : STAmount) from rfl,
          hcid] at hok
      exact (Except.ok.inj hok).symm

/-- `checked` of a canonical 16-digit mantissa gives a zero amount only when the
exponent is below the IOU floor `cMinOffset`. -/
lemma STAmount.checked_iou_zero_exp_lt (mant : UInt64) (exp : Int) (neg : Bool)
    (mode : rounding_mode) (h_lo : 10 ^ 15 ≤ mant.toNat) (h_hi : mant.toNat < 10 ^ 16)
    (he_lo : minExponent + 3 ≤ exp) (he_hi : exp ≤ maxExponent) (result : STAmount)
    (hok : STAmount.checked .fractional mant exp neg mode = .ok result)
    (hz : result.mValue = 0) : exp < cMinOffset := by
  by_contra hlo
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
    unfold STAmount.iou
    rw [if_neg h_int]
    unfold IOUAmount.ofMantissaExp
    rw [STAmount.signedDrops_toInt64Checked _ (show (STAmount.unchecked .fractional mant exp neg).mValue.toNat
      < 2 ^ 63 from h_fit), ok_bind, h_sd]
    exact IOUAmount.normalize_canonical16 mant exp neg mode h_lo h_hi he_lo he_hi
  by_cases hhi : exp > cMaxOffset
  · have hb : STAmount.checked .fractional mant exp neg mode = .error .overflow := by
      rw [STAmount.checked]; unfold STAmount.canonicalize
      rw [if_neg h_int, hiou, if_pos hhi]
    rw [hb] at hok; simp at hok
  · have hexp_lo : (-96 : ℤ) ≤ exp := by unfold cMinOffset at hlo; omega
    have hexp_hi : exp ≤ 80 := by unfold cMaxOffset at hhi; omega
    have hc : (⟨.fractional, mant, exp, neg⟩ : STAmount).IOUCanonical :=
      ⟨rfl, h_lo, h_hi, hexp_lo, hexp_hi⟩
    have hcid := STAmount.canonicalize_canonical_id ⟨.fractional, mant, exp, neg⟩ mode hc
    rw [STAmount.checked,
        show STAmount.unchecked .fractional mant exp neg =
            (⟨.fractional, mant, exp, neg⟩ : STAmount) from rfl, hcid] at hok
    rw [← Except.ok.inj hok] at hz
    have : mant.toNat = 0 := by rw [show mant = 0 from hz]; rfl
    omega

/-- The exact 19-digit `Number` view of a canonical IOU `STAmount`: `toNumber`
routes through `iou` (canonical round-trip) then the `×1000` lift. -/
lemma STAmount.toNumber_iou_canonical (s : STAmount) (mode : rounding_mode)
    (hc : s.IOUCanonical) :
    s.toNumber mode = .ok ⟨s.mIsNegative, s.mValue * 10 * 10 * 10, s.mOffset - 3⟩ := by
  have hint : ¬ s.integral = true := by unfold STAmount.integral; rw [hc.is_fractional]; decide
  unfold STAmount.toNumber
  rw [if_neg hint, STAmount.iou_canonical_id s mode hc]
  simp only []
  exact STAmount.iou_toNumber_canonical s mode hc

/-- The lift's value equals the source value. -/
lemma STAmount.toNumber_iou_canonical_toRat (s : STAmount) (hc : s.IOUCanonical) :
    (⟨s.mIsNegative, s.mValue * 10 * 10 * 10, s.mOffset - 3⟩ : Number).toRat = s.toRat := by
  have h_fit : s.mValue.toNat < 2 ^ 63 := by have := hc.mant_hi; omega
  have hmin : largeRange.min.toNat = 1000000000000000000 := largeRange_min_val
  have hm3 : (s.mValue * 10 * 10 * 10).toNat = s.mValue.toNat * 1000 := by
    have hm1 : (s.mValue * 10).toNat = s.mValue.toNat * 10 :=
      m_mul_ten_no_overflow (by have := hc.mant_hi; rw [hmin]; omega)
    have hm2 : (s.mValue * 10 * 10).toNat = s.mValue.toNat * 100 := by
      rw [m_mul_ten_no_overflow (by rw [hm1]; have := hc.mant_hi; rw [hmin]; omega), hm1]; ring
    rw [m_mul_ten_no_overflow (by rw [hm2]; have := hc.mant_hi; rw [hmin]; omega), hm2]; ring
  have hpow : (10 : ℚ) ^ s.mOffset = (10 : ℚ) ^ (s.mOffset - 3) * 1000 := by
    rw [show s.mOffset = (s.mOffset - 3) + 3 from by ring,
        zpow_add₀ (by norm_num : (10 : ℚ) ≠ 0)]; norm_num
  rcases hneg : s.mIsNegative with _ | _
  · rw [Number.toRat_of_nonneg _ rfl, STAmount.toRat_of_nonneg s hneg]
    show (((s.mValue * 10 * 10 * 10).toNat : ℚ)) * 10 ^ (s.mOffset - 3) = _
    rw [hm3, hpow]; push_cast; ring
  · rw [Number.toRat_of_neg _ rfl, STAmount.toRat_of_neg s hneg]
    show -(((s.mValue * 10 * 10 * 10).toNat : ℚ) * 10 ^ (s.mOffset - 3)) = _
    rw [hm3, hpow]; push_cast; ring

/-- The lift is normalized (mantissa `∈ [10¹⁸, 10¹⁹)`). -/
lemma STAmount.toNumber_iou_canonical_isNormalized (s : STAmount) (hc : s.IOUCanonical) :
    (⟨s.mIsNegative, s.mValue * 10 * 10 * 10, s.mOffset - 3⟩ : Number).isNormalized := by
  have hmin : largeRange.min.toNat = 1000000000000000000 := largeRange_min_val
  have hmax : largeRange.max.toNat = 9999999999999999999 := largeRange_max_val
  have hm3 : (s.mValue * 10 * 10 * 10).toNat = s.mValue.toNat * 1000 := by
    have hm1 : (s.mValue * 10).toNat = s.mValue.toNat * 10 :=
      m_mul_ten_no_overflow (by have := hc.mant_hi; rw [hmin]; omega)
    have hm2 : (s.mValue * 10 * 10).toNat = s.mValue.toNat * 100 := by
      rw [m_mul_ten_no_overflow (by rw [hm1]; have := hc.mant_hi; rw [hmin]; omega), hm1]; ring
    rw [m_mul_ten_no_overflow (by rw [hm2]; have := hc.mant_hi; rw [hmin]; omega), hm2]; ring
  right
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · show largeRange.min ≤ s.mValue * 10 * 10 * 10
    rw [UInt64.le_iff_toNat_le, hm3, hmin]; have := hc.mant_lo; omega
  · show s.mValue * 10 * 10 * 10 ≤ largeRange.max
    rw [UInt64.le_iff_toNat_le, hm3, hmax]; have := hc.mant_hi; omega
  · right; show (s.mValue * 10 * 10 * 10).toNat % 10 = 0; rw [hm3]; omega
  · show minExponent ≤ s.mOffset - 3; have := hc.exp_lo; unfold minExponent; omega
  · show s.mOffset - 3 ≤ maxExponent; have := hc.exp_hi; unfold maxExponent; omega

/-- `STAmount.ofNumber` IOU re-rounding bound. Snapping a 19-digit-normalized `Number` `r` to the 16-digit
IOU grid (`normalizeToRange`, then the value-preserving `checked`) loses at most one 16-digit ULP. -/
lemma STAmount.ofNumber_iou_within_ulp (nt : NumericType) (r : Number) (mode : rounding_mode)
    (result : STAmount)
    (hnt : nt = .fractional)
    (hr_lo : 10 ^ 18 ≤ r.mantissa_.toNat) (hr_hi : r.mantissa_.toNat < 10 ^ 19)
    (hre_lo : minExponent ≤ r.exponent_) (hre_hi : r.exponent_ + 4 ≤ maxExponent)
    (hok : STAmount.ofNumber nt r mode = .ok result) (hresult : result.mValue ≠ 0) :
    |result.toRat - r.toRat| ≤ (10 : ℚ) ^ (r.exponent_ + 3)
      ∧ r.exponent_ + 3 ≤ result.exponent := by
  subst hnt
  have hr_ne : r.mantissa_ ≠ 0 := by
    intro h; rw [h] at hr_lo; simp at hr_lo
  have hmne : (r.mantissa_ != 0) = true := by simp [hr_ne]
  have hneg_eq : decide (r.signum < 0) = r.negative_ := by
    unfold Number.signum
    rcases hrn : r.negative_ with _ | _ <;> simp only [hmne, if_true, if_false,
      Bool.false_eq_true] <;> decide
  -- `neg`/`working` as in `ofNumber`. `working = |r|` is non-negative, same magnitude/exponent.
  set neg : Bool := decide (r.signum < 0) with hneg_def
  set working : Number := if neg then r.operator_neg else r with hw_def
  have hw_mant : working.mantissa_ = r.mantissa_ := by
    rw [hw_def]; rcases neg with _ | _
    · simp
    · simp [Number.operator_neg_mantissa_of_ne r hr_ne]
  have hw_exp : working.exponent_ = r.exponent_ := by
    rw [hw_def]; rcases neg with _ | _
    · simp
    · simp only [if_true]; unfold Number.operator_neg
      rw [if_neg (by simpa using hr_ne)]
  have hw_neg : working.negative_ = false := by
    rw [hw_def, hneg_eq]
    by_cases hrn : r.negative_ = true
    · rw [if_pos hrn, Number.operator_neg_negative_of_ne r hr_ne]; simp [hrn]
    · rw [if_neg hrn]; simpa using hrn
  have hw_lo : 10 ^ 18 ≤ working.mantissa_.toNat := by rw [hw_mant]; exact hr_lo
  have hw_hi : working.mantissa_.toNat < 10 ^ 19 := by rw [hw_mant]; exact hr_hi
  have hwe_lo : minExponent ≤ working.exponent_ + 3 := by rw [hw_exp]; omega
  have hwe_hi : working.exponent_ + 4 ≤ maxExponent := by rw [hw_exp]; exact hre_hi
  -- `working.toRat = |r.toRat|`, and `r.toRat = (if neg then -1 else 1) * working.toRat`.
  have hw_toRat_nonneg : 0 ≤ working.toRat := by
    rw [Number.toRat_of_nonneg working hw_neg]; positivity
  have hr_toRat : r.toRat = (if neg then (-1 : ℚ) else 1) * working.toRat := by
    rw [hw_def]
    by_cases hn : neg = true
    · rw [if_pos hn, if_pos hn, Number.toRat_neg]; ring
    · rw [if_neg hn, if_neg hn]; ring
  -- `.fractional` is non-integral, so `ofNumber` reduces to `checked` on the `normalizeToRange` output.
  unfold STAmount.ofNumber at hok
  rw [if_neg (by decide), ← hneg_def, ← hw_def] at hok
  cases hnorm : working.normalizeToRange kMinValue kMaxValue mode with
  | error e => rw [hnorm] at hok; exact absurd hok (by simp)
  | ok me =>
    obtain ⟨mant, exp⟩ := me
    rw [hnorm] at hok
    simp only at hok
    -- 16-digit rounding facts (kMinValue and kMaxValue equal cMinValue and cMaxValue).
    have hnorm' : working.normalizeToRange cMinValue cMaxValue mode = .ok (mant, exp) := hnorm
    have hbound := normalizeToRange_16_within_ulp working mode mant exp hw_lo hw_hi hwe_lo hwe_hi hnorm'
    have hmrange := normalizeToRange_16_mantissa_range working mode mant exp hw_lo hw_hi hwe_lo hwe_hi hnorm'
    have herange := normalizeToRange_16_exp_range working mode mant exp hw_lo hw_hi hwe_lo hwe_hi hnorm'
    have hcMin : cMinValue.toNat = 10 ^ 15 := by decide
    have hcMax : cMaxValue.toNat = 10 ^ 16 - 1 := by decide
    -- `mant ≥ 0`: it is within one ULP of the (large, non-negative) `working.toRat`.
    have hwlarge : (10 : ℚ) ^ (working.exponent_ + 18) ≤ working.toRat := by
      rw [Number.toRat_of_nonneg working hw_neg]
      have h1018 : (10 : ℚ) ^ (18 : ℤ) ≤ (working.mantissa_.toNat : ℚ) := by
        have : ((10 ^ 18 : ℕ) : ℚ) ≤ (working.mantissa_.toNat : ℚ) := by exact_mod_cast hw_lo
        rwa [show ((10 ^ 18 : ℕ) : ℚ) = (10 : ℚ) ^ (18 : ℤ) by push_cast; norm_num] at this
      calc (10 : ℚ) ^ (working.exponent_ + 18)
          = (10 : ℚ) ^ (18 : ℤ) * (10 : ℚ) ^ working.exponent_ := by
            rw [← zpow_add₀ (by norm_num : (10 : ℚ) ≠ 0)]; ring_nf
        _ ≤ (working.mantissa_.toNat : ℚ) * (10 : ℚ) ^ working.exponent_ := by gcongr
    have hmant_pos : 0 ≤ mant.toInt := by
      by_contra hc
      push Not at hc
      have hmant_neg_q : (mant.toInt : ℚ) < 0 := by exact_mod_cast hc
      have hval_neg : (mant.toInt : ℚ) * 10 ^ exp < 0 :=
        mul_neg_of_neg_of_pos hmant_neg_q (zpow_pos (by norm_num) _)
      have hb := abs_le.mp hbound
      have hule : (10 : ℚ) ^ (working.exponent_ + 3) ≤ (10 : ℚ) ^ (working.exponent_ + 18) :=
        zpow_le_zpow_right₀ (by norm_num) (by omega)
      have : working.toRat ≤ (mant.toInt : ℚ) * 10 ^ exp + 10 ^ (working.exponent_ + 3) := by
        linarith [hb.1]
      nlinarith [hwlarge, hule, hval_neg]
    have hmant_natAbs : mant.toInt.natAbs = mant.toUInt64.toNat := by
      have := toUInt64_toNat_of_nonneg mant hmant_pos
      omega
    -- `checked` reproduces the record (exponent forced in range by `hok`/`hresult`).
    have hmtu_lo : 10 ^ 15 ≤ mant.toUInt64.toNat := by
      have := hmrange.1; rw [hcMin] at this; omega
    have hmtu_hi : mant.toUInt64.toNat < 10 ^ 16 := by
      have := hmrange.2; rw [hcMax] at this; omega
    obtain ⟨v, hv, hok⟩ := bind_ok_peel _ _ _ hok
    obtain ⟨-, rfl⟩ := Int64.toUInt64Checked_eq_ok.mp hv
    have hcc := STAmount.checked_iou_cases .fractional mant.toUInt64 exp neg mode rfl
      hmtu_lo hmtu_hi (by rw [hw_exp] at herange; omega) (by rw [hw_exp] at herange; omega) result hok hresult
    obtain ⟨_, _, hres_eq⟩ := hcc
    have hres_toRat : result.toRat = (if neg then (-1 : ℚ) else 1) * ((mant.toInt : ℚ) * 10 ^ exp) := by
      rw [hres_eq, STAmount.toRat_signed]
      show (if neg then (-1 : ℚ) else 1) * (mant.toUInt64.toNat : ℚ) * 10 ^ exp = _
      have : (mant.toUInt64.toNat : ℚ) = (mant.toInt : ℚ) := by
        exact_mod_cast toUInt64_toNat_of_nonneg mant hmant_pos
      rw [this]; ring
    rw [hres_toRat, hr_toRat]
    rw [show (if neg then (-1 : ℚ) else 1) * ((mant.toInt : ℚ) * 10 ^ exp)
          - (if neg then (-1 : ℚ) else 1) * working.toRat
        = (if neg then (-1 : ℚ) else 1) * ((mant.toInt : ℚ) * 10 ^ exp - working.toRat) from by ring,
        abs_mul]
    have hsabs : |(if neg then (-1 : ℚ) else 1)| = 1 := by rcases neg <;> norm_num
    have hexp : r.exponent_ + 3 ≤ result.exponent := by
      rw [hres_eq]; show r.exponent_ + 3 ≤ exp; rw [hw_exp] at herange; omega
    rw [hsabs, one_mul, hw_exp] at *
    exact ⟨hbound, hexp⟩

/-- Tight (half-ULP) `STAmount.ofNumber` IOU bound, `to_nearest`. The round-to-nearest snap lands within
*half* a 16-digit ULP. -/
lemma STAmount.ofNumber_iou_within_half_ulp (nt : NumericType) (r : Number)
    (result : STAmount)
    (hnt : nt = .fractional)
    (hr_lo : 10 ^ 18 ≤ r.mantissa_.toNat) (hr_hi : r.mantissa_.toNat < 10 ^ 19)
    (hre_lo : minExponent ≤ r.exponent_) (hre_hi : r.exponent_ + 4 ≤ maxExponent)
    (hok : STAmount.ofNumber nt r .to_nearest = .ok result) (hresult : result.mValue ≠ 0) :
    |result.toRat - r.toRat| ≤ (1 / 2 : ℚ) * (10 : ℚ) ^ (r.exponent_ + 3)
      ∧ r.exponent_ + 3 ≤ result.exponent := by
  subst hnt
  have hr_ne : r.mantissa_ ≠ 0 := by
    intro h; rw [h] at hr_lo; simp at hr_lo
  have hmne : (r.mantissa_ != 0) = true := by simp [hr_ne]
  have hneg_eq : decide (r.signum < 0) = r.negative_ := by
    unfold Number.signum
    rcases hrn : r.negative_ with _ | _ <;> simp only [hmne, if_true, if_false,
      Bool.false_eq_true] <;> decide
  set neg : Bool := decide (r.signum < 0) with hneg_def
  set working : Number := if neg then r.operator_neg else r with hw_def
  have hw_mant : working.mantissa_ = r.mantissa_ := by
    rw [hw_def]; rcases neg with _ | _
    · simp
    · simp [Number.operator_neg_mantissa_of_ne r hr_ne]
  have hw_exp : working.exponent_ = r.exponent_ := by
    rw [hw_def]; rcases neg with _ | _
    · simp
    · simp only [if_true]; unfold Number.operator_neg
      rw [if_neg (by simpa using hr_ne)]
  have hw_neg : working.negative_ = false := by
    rw [hw_def, hneg_eq]
    by_cases hrn : r.negative_ = true
    · rw [if_pos hrn, Number.operator_neg_negative_of_ne r hr_ne]; simp [hrn]
    · rw [if_neg hrn]; simpa using hrn
  have hw_lo : 10 ^ 18 ≤ working.mantissa_.toNat := by rw [hw_mant]; exact hr_lo
  have hw_hi : working.mantissa_.toNat < 10 ^ 19 := by rw [hw_mant]; exact hr_hi
  have hwe_lo : minExponent ≤ working.exponent_ + 3 := by rw [hw_exp]; omega
  have hwe_hi : working.exponent_ + 4 ≤ maxExponent := by rw [hw_exp]; exact hre_hi
  have hw_toRat_nonneg : 0 ≤ working.toRat := by
    rw [Number.toRat_of_nonneg working hw_neg]; positivity
  have hr_toRat : r.toRat = (if neg then (-1 : ℚ) else 1) * working.toRat := by
    rw [hw_def]
    by_cases hn : neg = true
    · rw [if_pos hn, if_pos hn, Number.toRat_neg]; ring
    · rw [if_neg hn, if_neg hn]; ring
  unfold STAmount.ofNumber at hok
  rw [if_neg (by decide), ← hneg_def, ← hw_def] at hok
  cases hnorm : working.normalizeToRange kMinValue kMaxValue .to_nearest with
  | error e => rw [hnorm] at hok; exact absurd hok (by simp)
  | ok me =>
    obtain ⟨mant, exp⟩ := me
    rw [hnorm] at hok
    simp only at hok
    have hnorm' : working.normalizeToRange cMinValue cMaxValue .to_nearest = .ok (mant, exp) := hnorm
    have hbound := normalizeToRange_16_within_half_ulp working mant exp hw_lo hw_hi hwe_lo hwe_hi hnorm'
    have hmrange := normalizeToRange_16_mantissa_range working .to_nearest mant exp hw_lo hw_hi hwe_lo hwe_hi hnorm'
    have herange := normalizeToRange_16_exp_range working .to_nearest mant exp hw_lo hw_hi hwe_lo hwe_hi hnorm'
    have hcMin : cMinValue.toNat = 10 ^ 15 := by decide
    have hcMax : cMaxValue.toNat = 10 ^ 16 - 1 := by decide
    have hwlarge : (10 : ℚ) ^ (working.exponent_ + 18) ≤ working.toRat := by
      rw [Number.toRat_of_nonneg working hw_neg]
      have h1018 : (10 : ℚ) ^ (18 : ℤ) ≤ (working.mantissa_.toNat : ℚ) := by
        have : ((10 ^ 18 : ℕ) : ℚ) ≤ (working.mantissa_.toNat : ℚ) := by exact_mod_cast hw_lo
        rwa [show ((10 ^ 18 : ℕ) : ℚ) = (10 : ℚ) ^ (18 : ℤ) by push_cast; norm_num] at this
      calc (10 : ℚ) ^ (working.exponent_ + 18)
          = (10 : ℚ) ^ (18 : ℤ) * (10 : ℚ) ^ working.exponent_ := by
            rw [← zpow_add₀ (by norm_num : (10 : ℚ) ≠ 0)]; ring_nf
        _ ≤ (working.mantissa_.toNat : ℚ) * (10 : ℚ) ^ working.exponent_ := by gcongr
    have hmant_pos : 0 ≤ mant.toInt := by
      by_contra hc
      push Not at hc
      have hmant_neg_q : (mant.toInt : ℚ) < 0 := by exact_mod_cast hc
      have hval_neg : (mant.toInt : ℚ) * 10 ^ exp < 0 :=
        mul_neg_of_neg_of_pos hmant_neg_q (zpow_pos (by norm_num) _)
      have hb := abs_le.mp hbound
      have hule : (10 : ℚ) ^ (working.exponent_ + 3) ≤ (10 : ℚ) ^ (working.exponent_ + 18) :=
        zpow_le_zpow_right₀ (by norm_num) (by omega)
      have hppos : (0 : ℚ) < (10 : ℚ) ^ (working.exponent_ + 3) := zpow_pos (by norm_num) _
      have : working.toRat ≤ (mant.toInt : ℚ) * 10 ^ exp + (1 / 2) * 10 ^ (working.exponent_ + 3) := by
        linarith [hb.1]
      nlinarith [hwlarge, hule, hval_neg, hppos]
    have hmant_natAbs : mant.toInt.natAbs = mant.toUInt64.toNat := by
      have := toUInt64_toNat_of_nonneg mant hmant_pos
      omega
    have hmtu_lo : 10 ^ 15 ≤ mant.toUInt64.toNat := by
      have := hmrange.1; rw [hcMin] at this; omega
    have hmtu_hi : mant.toUInt64.toNat < 10 ^ 16 := by
      have := hmrange.2; rw [hcMax] at this; omega
    obtain ⟨v, hv, hok⟩ := bind_ok_peel _ _ _ hok
    obtain ⟨-, rfl⟩ := Int64.toUInt64Checked_eq_ok.mp hv
    have hcc := STAmount.checked_iou_cases .fractional mant.toUInt64 exp neg .to_nearest rfl
      hmtu_lo hmtu_hi (by rw [hw_exp] at herange; omega) (by rw [hw_exp] at herange; omega) result hok hresult
    obtain ⟨_, _, hres_eq⟩ := hcc
    have hres_toRat : result.toRat = (if neg then (-1 : ℚ) else 1) * ((mant.toInt : ℚ) * 10 ^ exp) := by
      rw [hres_eq, STAmount.toRat_signed]
      show (if neg then (-1 : ℚ) else 1) * (mant.toUInt64.toNat : ℚ) * 10 ^ exp = _
      have : (mant.toUInt64.toNat : ℚ) = (mant.toInt : ℚ) := by
        exact_mod_cast toUInt64_toNat_of_nonneg mant hmant_pos
      rw [this]; ring
    rw [hres_toRat, hr_toRat]
    rw [show (if neg then (-1 : ℚ) else 1) * ((mant.toInt : ℚ) * 10 ^ exp)
          - (if neg then (-1 : ℚ) else 1) * working.toRat
        = (if neg then (-1 : ℚ) else 1) * ((mant.toInt : ℚ) * 10 ^ exp - working.toRat) from by ring,
        abs_mul]
    have hsabs : |(if neg then (-1 : ℚ) else 1)| = 1 := by rcases neg <;> norm_num
    have hexp : r.exponent_ + 3 ≤ result.exponent := by
      rw [hres_eq]; show r.exponent_ + 3 ≤ exp; rw [hw_exp] at herange; omega
    rw [hsabs, one_mul, hw_exp] at *
    exact ⟨hbound, hexp⟩

/-- A nonzero `STAmount.ofNumber` result forces a nonzero source mantissa. -/
lemma STAmount.ofNumber_iou_mantissa_ne_zero (nt : NumericType) (r : Number) (mode : rounding_mode)
    (result : STAmount) (hnt : nt = .fractional)
    (hok : STAmount.ofNumber nt r mode = .ok result) (hresult : result.mValue ≠ 0) :
    r.mantissa_ ≠ 0 := by
  subst hnt
  intro hrm
  apply hresult
  set neg : Bool := decide (r.signum < 0) with hneg_def
  set working : Number := if neg then r.operator_neg else r with hw_def
  have hw_mant0 : working.mantissa_ = 0 := by
    rw [hw_def]; by_cases hs : neg = true
    · rw [if_pos hs]; unfold Number.operator_neg
      rw [if_pos (show (r.mantissa_ == 0) = true from by rw [hrm]; rfl)]; rfl
    · rw [if_neg hs]; exact hrm
  have hnz : working.normalizeToRange kMinValue kMaxValue mode
      = .ok ((0 : Int64), Number.zero.exponent_) := by
    unfold Number.normalizeToRange
    rw [show doNormalize working.negative_ working.mantissa_ working.exponent_
          kMinValue kMaxValue mode = .ok Number.zero from by
      rw [doNormalize_eq_spec]
      all_goals try min_fit
      unfold doNormalizeSpec
      rw [if_pos (show (working.mantissa_ == 0) = true from by rw [hw_mant0]; rfl)]]
    ntr_tail
  have hof : STAmount.ofNumber .fractional r mode
      = STAmount.checked .fractional (0 : Int64).toUInt64 Number.zero.exponent_ neg mode := by
    unfold STAmount.ofNumber
    rw [if_neg (by decide), ← hneg_def, ← hw_def, hnz]
    dsimp only
    rw [Int64.toUInt64Checked_of_nonneg (by decide), ok_bind]
  rw [hof] at hok
  have h_unint : ¬ (STAmount.unchecked .fractional (0 : Int64).toUInt64 Number.zero.exponent_ neg).integral = true := by
    simp [STAmount.integral, STAmount.unchecked, NumericType.isIntegral]
  have hsd0 : (STAmount.unchecked .fractional (0 : Int64).toUInt64 Number.zero.exponent_ neg).signedDrops.toInt64
      = (0 : Int64) := by
    show (if neg then -(((0 : Int64).toUInt64).toNat : ℤ) else (((0 : Int64).toUInt64).toNat : ℤ)).toInt64
        = (0 : Int64)
    rcases neg <;> decide
  have hiou0 : (STAmount.unchecked .fractional (0 : Int64).toUInt64 Number.zero.exponent_ neg).iou mode
      = .ok IOUAmount.zero := by
    unfold STAmount.iou
    rw [if_neg h_unint]
    unfold IOUAmount.ofMantissaExp IOUAmount.normalize
    rw [STAmount.signedDrops_toInt64Checked _ (show ((0 : Int64).toUInt64).toNat < 2 ^ 63 by decide), ok_bind, hsd0]
    rfl
  rw [STAmount.checked] at hok
  unfold STAmount.canonicalize at hok
  rw [if_neg h_unint, hiou0] at hok
  simp only at hok
  rw [← Except.ok.inj hok]
  show IOUAmount.zero.mantissa_.magnitude = 0
  decide

end XRPL.Model.Protocol
