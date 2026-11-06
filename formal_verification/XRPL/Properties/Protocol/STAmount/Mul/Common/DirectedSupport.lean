import XRPL.Properties.Protocol.STAmount.Mul.Common.IOU
import XRPL.Properties.Protocol.STAmount.Add.Common.DirectedSupport
import XRPL.Properties.Protocol.Number.Mul.RoundsWithin
import XRPL.Properties.Protocol.Number.Mul.Common.Decompose

/-! # Directed-mode IOU re-rounding

Directed-mode bounds of `STAmount.ofNumber` on IOU amounts, mostly for non-negative operands, which avoids the
sign flip of rounding `|r|`. Also the sign of a `Number` product. -/

namespace XRPL.Model.Protocol

lemma STAmount.ofNumber_iou_rounds_within (nt : NumericType) (r : Number) (mode : rounding_mode)
    (result : STAmount)
    (hnt : nt = .fractional)
    (h_nonneg : r.negative_ = false)
    (hr_lo : 10 ^ 18 ≤ r.mantissa_.toNat) (hr_hi : r.mantissa_.toNat < 10 ^ 19)
    (hre_lo : minExponent ≤ r.exponent_) (hre_hi : r.exponent_ + 4 ≤ maxExponent)
    (hok : STAmount.ofNumber nt r mode = .ok result) (hresult : result.mValue ≠ 0) :
    RoundsWithin result r.toRat mode ((10 : ℚ) ^ (-15 : ℤ)) := by
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
  -- `.fractional` is not integral, so `ofNumber` reduces to `checked` on the `normalizeToRange` output.
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
    -- non-negativity ⟹ neg = false, so the result tracks `working = r` with no sign flip
    have hneg_false : neg = false := by
      rw [hneg_def]; unfold Number.signum; rw [h_nonneg]
      simp only [hmne, if_true]; decide
    have hwr : working.toRat = r.toRat := by rw [hr_toRat, hneg_false]; simp
    have hres' : result.toRat = (mant.toInt : ℚ) * 10 ^ exp := by rw [hres_toRat, hneg_false]; simp
    have hmag : |result.toRat - r.toRat| ≤ (10 : ℚ) ^ (r.exponent_ + 3) := by
      rw [hres', ← hwr, ← hw_exp]; exact hbound
    have hmag' : |result.toRat - r.toRat| ≤ |r.toRat| * (10 : ℚ) ^ (-15 : ℤ) := by
      refine le_trans hmag ?_
      rw [show |r.toRat| = (r.mantissa_.toNat : ℚ) * 10 ^ r.exponent_ by
            rw [Number.toRat_of_nonneg r h_nonneg, abs_of_nonneg (by positivity)]]
      have e2 : (10 : ℚ) ^ (r.exponent_ + 3) = 10 ^ (18 : ℤ) * 10 ^ (r.exponent_ - 15) := by
        rw [show (r.exponent_ + 3 : ℤ) = 18 + (r.exponent_ - 15) by ring, zpow_add₀ (by norm_num : (10:ℚ) ≠ 0)]
      have e1 : (r.mantissa_.toNat : ℚ) * 10 ^ r.exponent_ * 10 ^ (-15 : ℤ)
          = (r.mantissa_.toNat : ℚ) * 10 ^ (r.exponent_ - 15) := by
        rw [mul_assoc, ← zpow_add₀ (by norm_num : (10:ℚ) ≠ 0)]; ring_nf
      rw [e1, e2]
      have hM : (10 : ℚ) ^ (18 : ℤ) ≤ (r.mantissa_.toNat : ℚ) := by
        rw [show (10:ℚ)^(18:ℤ) = (10:ℚ)^(18:ℕ) by norm_num]; exact_mod_cast hr_lo
      gcongr
    have habs2 := abs_le.mp hmag'
    have htr : (RatValued.toRat result : ℚ) = result.toRat := rfl
    -- the re-round of `working = r` is correctly directed (working is non-negative)
    have hnorm_r : r.normalizeToRange cMinValue cMaxValue mode = .ok (mant, exp) := by
      have hwr_eq : working = r := by
        have : working = if neg then r.operator_neg else r := hw_def
        rw [this, hneg_false]; simp
      rw [← hwr_eq]; exact hnorm'
    unfold RoundsWithin
    cases mode with
    | to_nearest => rw [htr]; exact hmag'
    | downward =>
      rw [htr]
      exact ⟨by rw [hres']; exact normalizeToRange_16_downward r mant exp hr_lo hr_hi (by omega) hre_hi hnorm_r,
             by linarith [habs2.1]⟩
    | upward =>
      rw [htr]
      exact ⟨by rw [hres']; exact normalizeToRange_16_upward r mant exp hr_lo hr_hi (by omega) hre_hi hnorm_r,
             by linarith [habs2.2]⟩
    | towards_zero =>
      rw [htr]
      refine ⟨by rw [hres']; exact normalizeToRange_16_towards_zero r mant exp hr_lo hr_hi (by omega) hre_hi hnorm_r, ?_⟩
      have hrev : |r.toRat| - |result.toRat| ≤ |result.toRat - r.toRat| := by
        rw [abs_sub_comm result.toRat r.toRat]; exact abs_sub_abs_le_abs_sub r.toRat result.toRat
      linarith [hrev, hmag']

/-- `towards_zero` snap never increases magnitude, any sign. `STAmount.ofNumber` rounds the magnitude `|r|`
toward zero, so `|result| ≤ |r|` with no non-negativity hypothesis. -/
lemma STAmount.ofNumber_iou_abs_le_towards_zero (nt : NumericType) (r : Number) (result : STAmount)
    (hnt : nt = .fractional)
    (hr_lo : 10 ^ 18 ≤ r.mantissa_.toNat) (hr_hi : r.mantissa_.toNat < 10 ^ 19)
    (hre_lo : minExponent ≤ r.exponent_) (hre_hi : r.exponent_ + 4 ≤ maxExponent)
    (hok : STAmount.ofNumber nt r .towards_zero = .ok result) (hresult : result.mValue ≠ 0) :
    |result.toRat| ≤ |r.toRat| := by
  subst hnt
  have hr_ne : r.mantissa_ ≠ 0 := by intro h; rw [h] at hr_lo; simp at hr_lo
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
    · simp only [if_true]; unfold Number.operator_neg; rw [if_neg (by simpa using hr_ne)]
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
  cases hnorm : working.normalizeToRange kMinValue kMaxValue .towards_zero with
  | error e => rw [hnorm] at hok; exact absurd hok (by simp)
  | ok me =>
    obtain ⟨mant, exp⟩ := me
    rw [hnorm] at hok
    simp only at hok
    have hnorm' : working.normalizeToRange cMinValue cMaxValue .towards_zero = .ok (mant, exp) := hnorm
    have hbound := normalizeToRange_16_within_ulp working .towards_zero mant exp hw_lo hw_hi hwe_lo hwe_hi hnorm'
    have hmrange := normalizeToRange_16_mantissa_range working .towards_zero mant exp hw_lo hw_hi hwe_lo hwe_hi hnorm'
    have herange := normalizeToRange_16_exp_range working .towards_zero mant exp hw_lo hw_hi hwe_lo hwe_hi hnorm'
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
      have : working.toRat ≤ (mant.toInt : ℚ) * 10 ^ exp + 10 ^ (working.exponent_ + 3) := by
        linarith [hb.1]
      nlinarith [hwlarge, hule, hval_neg]
    have hmant_natAbs : mant.toInt.natAbs = mant.toUInt64.toNat := by
      have := toUInt64_toNat_of_nonneg mant hmant_pos; omega
    have hmtu_lo : 10 ^ 15 ≤ mant.toUInt64.toNat := by
      have := hmrange.1; rw [hcMin] at this; omega
    have hmtu_hi : mant.toUInt64.toNat < 10 ^ 16 := by
      have := hmrange.2; rw [hcMax] at this; omega
    obtain ⟨v, hv, hok⟩ := bind_ok_peel _ _ _ hok
    obtain ⟨-, rfl⟩ := Int64.toUInt64Checked_eq_ok.mp hv
    have hcc := STAmount.checked_iou_cases .fractional mant.toUInt64 exp neg .towards_zero rfl
      hmtu_lo hmtu_hi (by rw [hw_exp] at herange; omega) (by rw [hw_exp] at herange; omega) result hok hresult
    obtain ⟨_, _, hres_eq⟩ := hcc
    have hres_toRat : result.toRat = (if neg then (-1 : ℚ) else 1) * ((mant.toInt : ℚ) * 10 ^ exp) := by
      rw [hres_eq, STAmount.toRat_signed]
      show (if neg then (-1 : ℚ) else 1) * (mant.toUInt64.toNat : ℚ) * 10 ^ exp = _
      have : (mant.toUInt64.toNat : ℚ) = (mant.toInt : ℚ) := by
        exact_mod_cast toUInt64_toNat_of_nonneg mant hmant_pos
      rw [this]; ring
    have hmono := normalizeToRange_16_towards_zero working mant exp hw_lo hw_hi hwe_lo hwe_hi hnorm'
    have hwabs : |working.toRat| = |r.toRat| := by
      rw [hr_toRat, abs_mul]; rcases hn : neg with _ | _ <;> simp
    have hres_abs : |result.toRat| = |(mant.toInt : ℚ) * 10 ^ exp| := by
      rw [hres_toRat, abs_mul]; rcases hn : neg with _ | _ <;> simp
    rw [hres_abs, ← hwabs]; exact hmono

/-- The `Number`-multiply result sign is the XOR of the operand signs (any mode). -/
theorem operator_mul_negative_eq (x y result : Number) (mode : rounding_mode)
    (hx : x.isNormalized) (hy : y.isNormalized)
    (hx_ne : x.mantissa_ ≠ 0) (hy_ne : y.mantissa_ ≠ 0)
    (hok : Number.operator_mul x y mode = .ok result) (hresult : result.mantissa_ ≠ 0) :
    result.negative_ = (x.negative_ != y.negative_) := by
  obtain ⟨zn, zm, ze', f, g, res, d⟩ :=
    operator_mul_decompose x y result mode hx hy hx_ne hy_ne hok
  have hzm_ge : zm.toNat ≥ mantissaFloor := by have := d.zm_ge_floorSucc; omega
  have hres_mant_ne : res.mantissa_ ≠ 0 :=
    Number.normalize_mantissa_ne_zero_of_result d.normalizes hresult
  obtain ⟨h_res_min, h_res_max, h_res_exp, h_res_mod⟩ :=
    doRoundUp_output_invariants_upTo_maxRepUp_anyMode g zn zm ze' mode hzm_ge d.zm_le_maxRepUp
      .overflow res d.rounds hres_mant_ne
  have hres_eq : result = res.toNumber :=
    Number.normalize_eq_of_invariants h_res_min h_res_max h_res_exp h_res_mod d.normalizes
  have hres_neg : res.negative_ = zn :=
    doRoundUp_negative_of_mant_ne g zn zm ze' largeRange.min largeRange.max mode
      .overflow res d.rounds hres_mant_ne
  rw [hres_eq, show res.toNumber.negative_ = res.negative_ from rfl, hres_neg]
  exact d.neg_eq

end XRPL.Model.Protocol
