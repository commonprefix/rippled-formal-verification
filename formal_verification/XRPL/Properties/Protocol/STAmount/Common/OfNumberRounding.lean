import XRPL.Properties.Protocol.STAmount.Common.OfNumberBoundary
import XRPL.Properties.Protocol.STAmount.Add.Common.Integral
import XRPL.Properties.Protocol.STAmount.Common.STAmountToNumber
import XRPL.Properties.Protocol.STAmount.Common.OfNumberFacts
import XRPL.Properties.Protocol.Number.AtExponent
import XRPL.Model.Protocol.Exponent
import XRPL.Properties.Protocol.Number.Normalize.NormalizedResult

/-! # Rounding bounds of `STAmount.ofNumber`

How far converting a `Number` into an `STAmount` can move its value, and when it does not move
it. An integral type rounds to a whole unit. A fractional type rounds to a 16-digit mantissa.
`to_nearest` stays within half a unit of the result exponent, and a value already on that grid
converts exactly. -/

namespace XRPL.Model.Protocol

/-- **An integral `ofNumber` stores the `to_rep` integer.** A sign-cleared source goes through
`to_rep`, and the offset-`0` result holds exactly that integer. -/
lemma STAmount.ofNumber_integral_toRat (nt : NumericType) (n : Number)
    (mode : rounding_mode) (result : STAmount)
    (hnt : nt.isIntegral = true) (hneg : n.negative_ = false)
    (hok : STAmount.ofNumber nt n mode = .ok result) :
    ∃ intValue : Int64, n.to_rep mode = .ok intValue ∧ result.toRat = (intValue.toInt : ℚ) := by
  unfold STAmount.ofNumber at hok
  simp only [Number.signum_neg_decide, hneg, Bool.false_eq_true, if_false, if_pos hnt] at hok
  cases hr : n.to_rep mode with
  | error e => rw [hr] at hok; exact absurd hok (by simp)
  | ok intValue =>
    rw [hr] at hok
    simp only [] at hok
    obtain ⟨hnn, hle⟩ := Number.to_rep_nonneg_range n mode intValue hneg hr
    have hval : intValue.toUInt64.toNat ≤ maxRep.toNat :=
      toUInt64_toNat_le_maxRep intValue hnn hle
    refine ⟨intValue, rfl, ?_⟩
    have hexact := STAmount.canonicalize_integral_toRat
      (STAmount.unchecked nt intValue.toUInt64 0 false) result mode
      (show (STAmount.unchecked nt intValue.toUInt64 0 false).integral = true from hnt) rfl
      hval hok
    rw [hexact, STAmount.toRat_of_offset_zero _ rfl]
    show ((intValue.toUInt64.toNat : ℤ) : ℚ) = (intValue.toInt : ℚ)
    rw [toUInt64_toNat_of_nonneg intValue hnn]

/-- **`ofNumber` on an integral type rounds within one unit** of a sign-cleared
normalized `Number`, because the magnitude goes through `to_rep`. -/
lemma STAmount.ofNumber_integral_within_one (nt : NumericType) (n : Number)
    (mode : rounding_mode) (result : STAmount)
    (hnt : nt.isIntegral = true) (hn : n.isNormalized) (hneg : n.negative_ = false)
    (hok : STAmount.ofNumber nt n mode = .ok result) :
    |result.toRat - n.toRat| < 1 := by
  obtain ⟨intValue, hr, hres⟩ := STAmount.ofNumber_integral_toRat nt n mode result hnt hneg hok
  rw [hres]
  exact to_rep_within_one n mode intValue hn hr

/-- **`to_nearest` `ofNumber` on an integral type rounds within half a unit.** -/
lemma STAmount.ofNumber_integral_within_half (nt : NumericType) (n : Number) (result : STAmount)
    (hnt : nt.isIntegral = true) (hn : n.isNormalized) (hneg : n.negative_ = false)
    (hok : STAmount.ofNumber nt n .to_nearest = .ok result) :
    |result.toRat - n.toRat| ≤ 1 / 2 := by
  obtain ⟨intValue, hr, hres⟩ :=
    STAmount.ofNumber_integral_toRat nt n .to_nearest result hnt hneg hok
  rw [hres]
  exact Number.to_rep_to_nearest_within_half n intValue hn hneg hr

/-- The `Number.mantissa` accessor of a zero-mantissa record is zero. -/
lemma Number.mantissa_acc_zero {n : Number} (h : n.mantissa_ = 0) : n.mantissa = 0 := by
  unfold Number.mantissa
  rw [h, if_neg (by decide : ¬ ((0 : UInt64) > maxRep))]
  split <;> decide

/-- A nonzero integral `ofNumber` result forces a nonzero source mantissa. -/
lemma STAmount.ofNumber_integral_source_ne_zero (nt : NumericType) (n : Number)
    (mode : rounding_mode) (a : STAmount)
    (hnt : nt.isIntegral = true)
    (hok : STAmount.ofNumber nt n mode = .ok a) (ha : a.mValue ≠ 0) :
    n.mantissa_ ≠ 0 := by
  intro h0
  set w : Number := if decide (n.signum < 0) = true then n.operator_neg else n with hw
  have hwm : w.mantissa_ = 0 := by
    rw [hw]
    split
    · unfold Number.operator_neg
      rw [if_pos (by rw [h0]; rfl)]
      rfl
    · exact h0
  have hrep : w.to_rep mode = .ok 0 := by
    unfold Number.to_rep
    rw [if_pos (show (w.mantissa == 0) = true from by
      rw [Number.mantissa_acc_zero hwm]; decide)]
  unfold STAmount.ofNumber at hok
  rw [if_pos hnt, ← hw, hrep] at hok
  simp only [] at hok
  rw [show ((0 : rep).toUInt64) = (0 : UInt64) from by decide] at hok
  rw [STAmount.checked, STAmount.canonicalize,
    if_pos (show (STAmount.unchecked nt 0 0 (decide (n.signum < 0))).integral = true from hnt),
    if_pos (show ((STAmount.unchecked nt 0 0 (decide (n.signum < 0))).mValue == 0
      || decide ((STAmount.unchecked nt 0 0 (decide (n.signum < 0))).mOffset ≤ -20)) = true
      from rfl)] at hok
  apply ha
  rw [← Except.ok.inj hok]

/-- **`ofNumber` on an integral type keeps a whole number exactly**, in every mode. -/
lemma STAmount.ofNumber_integral_exact (nt : NumericType) (n : Number)
    (mode : rounding_mode) (a : STAmount)
    (hnt : nt.isIntegral = true)
    (hn : n.isNormalized) (hden : n.toRat.den = 1)
    (hok : STAmount.ofNumber nt n mode = .ok a) :
    a.toRat = n.toRat := by
  by_cases hm : n.mantissa_ = 0
  · -- zero source, zero result
    have hn0 : n.toRat = 0 := Number.toRat_eq_zero_of_mantissa_zero n hm
    have ha0 : a.mValue = 0 := by
      by_contra hc
      exact STAmount.ofNumber_integral_source_ne_zero nt n mode a hnt hok hc hm
    rw [hn0, STAmount.toRat_signed, ha0]
    simp
  unfold STAmount.ofNumber at hok
  rw [if_pos hnt] at hok
  set w : Number := if decide (n.signum < 0) = true then n.operator_neg else n with hw
  have hwn : w = if n.negative_ = true then n.operator_neg else n := by
    rw [hw, Number.signum_neg_decide]
  have hw_norm : w.isNormalized := by
    rw [hwn]
    rcases hb : n.negative_ with _ | _
    · rw [if_neg Bool.false_ne_true]; exact hn
    · rw [if_pos rfl]; exact Number.operator_neg_isNormalized n hn
  have hneg_rec : n.operator_neg = { n with negative_ := !n.negative_ } := by
    unfold Number.operator_neg
    rw [if_neg (by simpa using hm)]
  have hw_exp : w.exponent_ = n.exponent_ := by
    rw [hwn]
    rcases hb : n.negative_ with _ | _
    · rw [if_neg Bool.false_ne_true]
    · rw [if_pos rfl, hneg_rec]
  have hw_neg : w.negative_ = false := by
    rw [hwn]
    rcases hb : n.negative_ with _ | _
    · rw [if_neg Bool.false_ne_true]; exact hb
    · rw [if_pos rfl, hneg_rec]
      simp [hb]
  have hw_val : w.toRat = (if n.negative_ = true then (-1 : ℚ) else 1) * n.toRat := by
    rw [hwn]
    rcases hb : n.negative_ with _ | _
    · rw [if_neg Bool.false_ne_true, if_neg Bool.false_ne_true]
      ring
    · rw [if_pos rfl, if_pos rfl, Number.toRat_neg]; ring
  cases hrep : w.to_rep mode with
  | error e => rw [hrep] at hok; exact absurd hok (by simp)
  | ok intValue =>
    rw [hrep] at hok
    simp only [] at hok
    rw [STAmount.checked] at hok
    have hwden : w.toRat.den = 1 := by
      rw [hw_val]
      rcases hb : n.negative_ with _ | _
      · simpa using hden
      · rw [if_pos rfl, neg_one_mul, Rat.neg_den]
        exact hden
    have hkey : (intValue.toInt : ℚ) = w.toRat := by
      have hone := to_rep_within_one w mode intValue hw_norm hrep
      have hwq : w.toRat = (w.toRat.num : ℚ) := by
        conv_lhs => rw [← Rat.num_div_den w.toRat]
        rw [hwden]; simp
      rw [hwq] at hone ⊢
      have habs : |intValue.toInt - w.toRat.num| < 1 := by
        rw [← Int.cast_sub, ← Int.cast_abs] at hone
        exact_mod_cast hone
      have heq : intValue.toInt = w.toRat.num := by
        have := abs_lt.mp habs
        omega
      rw [heq]
    have hw_nonneg : 0 ≤ w.toRat := by
      rw [Number.toRat_of_nonneg w hw_neg]; positivity
    have hiv_nonneg : (0 : ℤ) ≤ intValue.toInt := by
      have : (0 : ℚ) ≤ (intValue.toInt : ℚ) := by rw [hkey]; exact hw_nonneg
      exact_mod_cast this
    have hiv_le : intValue.toInt ≤ (2 : ℤ) ^ 63 - 1 := by
      have := Int64.toInt_lt intValue
      omega
    have htu : (intValue.toUInt64.toNat : ℤ) = intValue.toInt :=
      toUInt64_toNat_of_nonneg intValue hiv_nonneg
    have hfit : intValue.toUInt64.toNat ≤ maxRep.toNat := by
      rw [maxRep_val]
      omega
    have hexact := STAmount.canonicalize_integral_toRat _ a mode
      (show (STAmount.unchecked nt intValue.toUInt64 0 (decide (n.signum < 0))).integral = true
        from hnt) rfl hfit hok
    rw [hexact, STAmount.toRat_of_offset_zero _ rfl]
    show ((if decide (n.signum < 0) = true then -(intValue.toUInt64.toNat : ℤ)
      else (intValue.toUInt64.toNat : ℤ) : ℤ) : ℚ) = n.toRat
    rw [Number.signum_neg_decide]
    rcases hb : n.negative_ with _ | _
    · rw [if_neg Bool.false_ne_true]
      have : ((intValue.toUInt64.toNat : ℤ) : ℚ) = n.toRat := by
        rw [htu, hkey, hw_val, hb]; simp
      exact_mod_cast this
    · rw [if_pos rfl]
      have h1 : ((intValue.toUInt64.toNat : ℤ) : ℚ) = -n.toRat := by
        rw [htu, hkey, hw_val, hb]; simp
      push_cast
      push_cast at h1
      linarith

/-- **`to_nearest` `ofNumber` on the fractional type rounds within half a unit of the result
exponent.** A nonzero normalized source and a nonzero result, with no exponent hypothesis: the
success of the conversion already bounds the source exponent. -/
lemma STAmount.ofNumber_iou_to_nearest_within_half (n : Number) (result : STAmount)
    (hn : n.isNormalized) (hn0 : n.mantissa_ ≠ 0)
    (hok : STAmount.ofNumber .fractional n .to_nearest = .ok result) (hresult : result.mValue ≠ 0) :
    |result.toRat - n.toRat| ≤ (1 / 2 : ℚ) * (10 : ℚ) ^ result.exponent := by
  have hb := mantissaBounds_nat_of (hn.mantissaBounds hn0)
  have hemin := Number.exponent_ge_min n hn hn0
  have hexp := STAmount.ofNumber_iou_success_exp_range n .to_nearest result hb.1 hb.2 hemin hok
    hresult
  obtain ⟨hbound, hle⟩ := STAmount.ofNumber_iou_within_half_ulp .fractional n result rfl hb.1 hb.2
    hemin hexp hok hresult
  calc |result.toRat - n.toRat| ≤ (1 / 2 : ℚ) * (10 : ℚ) ^ (n.exponent_ + 3) := hbound
    _ ≤ (1 / 2 : ℚ) * (10 : ℚ) ^ result.exponent :=
      mul_le_mul_of_nonneg_left (zpow_le_zpow_right₀ (by norm_num) hle) (by norm_num)

/-- A zero source converts to a zero fractional amount, in every mode. -/
lemma STAmount.ofNumber_fractional_zero (mode : rounding_mode) :
    STAmount.ofNumber .fractional Number.zero mode = .ok ⟨.fractional, 0, -100, false⟩ := by
  cases mode <;> rfl

/-- A positive normalized `Number` whose mantissa ends in three zeros converts to `STAmount`
exactly, in every mode: the 16-digit amount drops those zeros and raises the exponent by `3`. -/
lemma STAmount.ofNumber_fractional_of_trailing_zeros (n : Number) (mode : rounding_mode)
    (hn : n.isNormalized) (hm0 : n.mantissa_ ≠ 0) (hneg : n.negative_ = false)
    (hmod : n.mantissa_.toNat % 1000 = 0)
    (he_lo : (-96 : Int) ≤ n.exponent_ + 3) (he_hi : n.exponent_ + 3 ≤ 80) :
    STAmount.ofNumber .fractional n mode =
      .ok ⟨.fractional, n.mantissa_ / 10 / 10 / 10, n.exponent_ + 3, false⟩ := by
  have hz : n ≠ Number.zero := fun h => hm0 (by rw [h]; rfl)
  obtain ⟨hlo, hhi, _, _, _⟩ := hn.resolve_left hz
  have hlo' : 10 ^ 18 ≤ n.mantissa_.toNat := by
    have := UInt64.le_iff_toNat_le.mp hlo; simpa [largeRange] using this
  have hhi' : n.mantissa_.toNat < 10 ^ 19 := by
    have := UInt64.le_iff_toNat_le.mp hhi; simp [largeRange] at this; omega
  have hm3 : (n.mantissa_ / 10 / 10 / 10).toNat = n.mantissa_.toNat / 1000 :=
    m_div_thousand_toNat n.mantissa_
  -- the dropped digits are zero, so the 16-digit rounding is exact in every mode
  have hnorm := normalizeToRange_16_exact n mode hlo' hhi' hmod
    (by unfold minExponent; omega) (by unfold maxExponent; omega)
  rw [hneg, if_neg (by decide)] at hnorm
  have hsig : decide (n.signum < 0) = false := by
    unfold Number.signum; simp [hneg, hm0]
  unfold STAmount.ofNumber
  simp only [hsig, Bool.false_eq_true, if_false]
  rw [if_neg (by decide)]
  rw [show n.normalizeToRange kMinValue kMaxValue mode =
    n.normalizeToRange cMinValue cMaxValue mode from rfl, hnorm]
  simp only
  rw [show (n.mantissa_ / 10 / 10 / 10).toInt64.toUInt64 = n.mantissa_ / 10 / 10 / 10 from
    UInt64.toUInt64_toInt64 _]
  -- the 16-digit record is already canonical, so `checked` keeps it
  exact STAmount.canonicalize_canonical_id _ mode
    ⟨rfl, by show 10 ^ 15 ≤ (n.mantissa_ / 10 / 10 / 10).toNat; omega,
      by show (n.mantissa_ / 10 / 10 / 10).toNat < 10 ^ 16; omega, he_lo, he_hi⟩

/-- **`to_nearest` `ofNumber` rounds within half a unit of the result exponent**, for every
numeric type. An integral result has exponent `0`, so the bound is `1/2`. -/
lemma STAmount.ofNumber_to_nearest_within_half (nt : NumericType) (n : Number) (result : STAmount)
    (hn : n.isNormalized) (h0 : 0 ≤ n.toRat)
    (hok : STAmount.ofNumber nt n .to_nearest = .ok result) (hresult : result.mValue ≠ 0) :
    |result.toRat - n.toRat| ≤ (1 / 2 : ℚ) * (10 : ℚ) ^ result.exponent := by
  cases hnt : nt with
  | integral mv mo ms msh =>
    rw [hnt] at hok
    have hint : (NumericType.integral mv mo ms msh).isIntegral = true := rfl
    have hoff : result.exponent = 0 :=
      (STAmount.ofNumber_integral_canonical _ _ _ result hint hok).1.offset_zero
    rw [hoff, zpow_zero, mul_one]
    exact STAmount.ofNumber_integral_within_half _ _ result hint hn
      (Number.negative_false_of_nonneg n hn h0)
      hok
  | fractional =>
    rw [hnt] at hok
    by_cases hm : n.mantissa_ = 0
    · rw [Number.eq_zero_of_mantissa_zero n hn hm, STAmount.ofNumber_fractional_zero,
        Except.ok.injEq] at hok
      exact absurd (by rw [← hok]) hresult
    · exact STAmount.ofNumber_iou_to_nearest_within_half n result hn hm hok hresult

/-- **A nonzero `ofNumber` result is stored canonically.** A fractional result has a 16-digit
mantissa and an in-range exponent. An integral result has offset `0` and fits `2^63 - 1`. -/
lemma STAmount.ofNumber_exactCanonical (nt : NumericType) (n : Number) (mode : rounding_mode)
    (result : STAmount) (hn : n.isNormalized) (h0 : 0 ≤ n.toRat)
    (hok : STAmount.ofNumber nt n mode = .ok result) (hresult : result.mValue ≠ 0) :
    result.ExactCanonical := by
  cases hnt : nt with
  | integral mv mo ms msh =>
    rw [hnt] at hok
    have hint : (NumericType.integral mv mo ms msh).isIntegral = true := rfl
    have hic := (STAmount.ofNumber_integral_canonical _ _ _ result hint hok).1
    obtain ⟨iv, hr, hres⟩ :=
      STAmount.ofNumber_integral_toRat _ n mode result hint
        (Number.negative_false_of_nonneg n hn h0) hok
    obtain ⟨hnn, hle⟩ := Number.to_rep_nonneg_range n mode iv
      (Number.negative_false_of_nonneg n hn h0) hr
    refine Or.inr ⟨hic, ?_⟩
    have hsd := STAmount.IntegralCanonical.toRat_eq_signedDrops result hic
    rw [hres] at hsd
    have hsd' : iv.toInt = result.signedDrops := by exact_mod_cast hsd
    have hmr : (maxRep.toNat : ℤ) = 9223372036854775807 := by rw [maxRep_val]; rfl
    unfold STAmount.signedDrops at hsd'
    split_ifs at hsd' <;> omega
  | fractional =>
    rw [hnt] at hok
    by_cases hm : n.mantissa_ = 0
    · rw [Number.eq_zero_of_mantissa_zero n hn hm, STAmount.ofNumber_fractional_zero,
        Except.ok.injEq] at hok
      exact absurd (by rw [← hok]) hresult
    · have hb := mantissaBounds_nat_of (hn.mantissaBounds hm)
      exact Or.inl (STAmount.ofNumber_iou_ok_facts n mode result hb.1 hb.2
        (Number.exponent_ge_min n hn hm) hok hresult).1

/-- An amount whose exponent is at or above `e` is a whole multiple of `10 ^ e`. -/
private lemma STAmount.toRat_eq_int_mul_of_exponent_ge (a : STAmount) (e : ℤ)
    (h : e ≤ a.exponent) : ∃ z : ℤ, a.toRat = (z : ℚ) * (10 : ℚ) ^ e := by
  obtain ⟨w, hw⟩ := STAmount.exists_int_grid a
  obtain ⟨k, hk⟩ : ∃ k : ℕ, a.exponent = e + k := ⟨(a.exponent - e).toNat, by omega⟩
  refine ⟨w * 10 ^ k, ?_⟩
  rw [hw, hk, zpow_add₀ (by norm_num : (10 : ℚ) ≠ 0), zpow_natCast]
  push_cast; ring

/-- **`to_nearest` `ofNumber` never rounds above an amount the numeric type holds.** A source at
most a canonical amount `a` of the same type converts to at most `a`: `a` sits on the result's
grid, so any result above `a` is a full unit above it, more than the half-unit rounding. -/
lemma STAmount.ofNumber_to_nearest_le_of_canonical (nt : NumericType) (n : Number)
    (result a : STAmount) (hn : n.isNormalized) (h0 : 0 ≤ n.toRat)
    (ha : a.ExactCanonical) (hat : a.mNumericType = nt) (hle : n.toRat ≤ a.toRat)
    (hok : STAmount.ofNumber nt n .to_nearest = .ok result) (hresult : result.mValue ≠ 0) :
    result.toRat ≤ a.toRat := by
  cases hnt : nt with
  | integral mv mo ms msh =>
    rw [hnt] at hok hat
    have hint : (NumericType.integral mv mo ms msh).isIntegral = true := rfl
    obtain ⟨iv, hr, hres⟩ :=
      STAmount.ofNumber_integral_toRat _ n .to_nearest result hint
        (Number.negative_false_of_nonneg n hn h0) hok
    have hhalf := Number.to_rep_to_nearest_within_half n iv hn
      (Number.negative_false_of_nonneg n hn h0) hr
    rcases ha with hiou | ⟨hic, _⟩
    · exact absurd (hat.symm.trans hiou.is_fractional) (by simp)
    have haint : (a.toRat.num : ℚ) = a.toRat :=
      Rat.coe_int_num_of_den_eq_one (STAmount.IntegralCanonical.den_eq_one a hic)
    rw [hres, ← haint]
    rw [← haint] at hle
    have h1 := (abs_le.mp hhalf).2
    by_contra hgt
    have hgt' : a.toRat.num < iv.toInt := by exact_mod_cast not_le.mp hgt
    have hstep : (a.toRat.num : ℚ) + 1 ≤ iv.toInt := by exact_mod_cast hgt'
    linarith
  | fractional =>
    rw [hnt] at hok hat
    by_cases hm : n.mantissa_ = 0
    · rw [Number.eq_zero_of_mantissa_zero n hn hm, STAmount.ofNumber_fractional_zero,
        Except.ok.injEq] at hok
      exact absurd (by rw [← hok]) hresult
    rcases ha with hiou | ⟨hic, _⟩
    swap
    · have := hic.is_integral; rw [hat] at this; exact absurd this (by decide)
    have hb := mantissaBounds_nat_of (hn.mantissaBounds hm)
    have hemin := Number.exponent_ge_min n hn hm
    have hexp := STAmount.ofNumber_iou_success_exp_range n .to_nearest result hb.1 hb.2 hemin hok
      hresult
    obtain ⟨hbound, hrexp⟩ := STAmount.ofNumber_iou_within_half_ulp .fractional n result rfl hb.1
      hb.2 hemin hexp hok hresult
    set u : ℚ := (10 : ℚ) ^ (n.exponent_ + 3) with hu
    have hu0 : 0 < u := zpow_pos (by norm_num) _
    have hpos : ∀ e : ℤ, (0 : ℚ) < (10 : ℚ) ^ e := fun e => zpow_pos (by norm_num) e
    -- `a` is at least the source, so its offset is at least `n.exponent_ + 3`
    have hnabs : |n.toRat| = (n.mantissa_.toNat : ℚ) * (10 : ℚ) ^ n.exponent_ := abs_toRat_eq n
    have haabs : |a.toRat| = (a.mValue.toNat : ℚ) * (10 : ℚ) ^ a.mOffset := STAmount.abs_toRat a
    have hml : ((10 ^ 18 : ℕ) : ℚ) ≤ (n.mantissa_.toNat : ℚ) := by exact_mod_cast hb.1
    have hah : (a.mValue.toNat : ℚ) < ((10 ^ 16 : ℕ) : ℚ) := by exact_mod_cast hiou.mant_hi
    push_cast at hml hah
    have hoff : n.exponent_ + 3 ≤ a.mOffset := by
      by_contra hlt
      have hle' : a.mOffset + 1 ≤ n.exponent_ + 3 := by omega
      have h1 : (a.mValue.toNat : ℚ) * (10 : ℚ) ^ a.mOffset < 10 ^ 16 * (10 : ℚ) ^ a.mOffset :=
        mul_lt_mul_of_pos_right hah (hpos _)
      have h2 : (10 : ℚ) ^ 16 * (10 : ℚ) ^ a.mOffset ≤ 10 ^ 18 * (10 : ℚ) ^ n.exponent_ := by
        have e1 : (10 : ℚ) ^ 16 * (10 : ℚ) ^ a.mOffset = (10 : ℚ) ^ (a.mOffset + 16) := by
          rw [zpow_add₀ (by norm_num : (10 : ℚ) ≠ 0)]; norm_num; ring
        have e2 : (10 : ℚ) ^ 18 * (10 : ℚ) ^ n.exponent_ = (10 : ℚ) ^ (n.exponent_ + 18) := by
          rw [zpow_add₀ (by norm_num : (10 : ℚ) ≠ 0)]; norm_num; ring
        rw [e1, e2]
        exact zpow_le_zpow_right₀ (by norm_num) (by omega)
      have h3 : (10 : ℚ) ^ 18 * (10 : ℚ) ^ n.exponent_ ≤
          (n.mantissa_.toNat : ℚ) * (10 : ℚ) ^ n.exponent_ :=
        mul_le_mul_of_nonneg_right hml (hpos _).le
      have hnle : |n.toRat| ≤ |a.toRat| := by
        rw [abs_of_nonneg h0, abs_of_nonneg (le_trans h0 hle)]; exact hle
      linarith
    -- both `result` and `a` are whole multiples of `u`
    obtain ⟨w, hw'⟩ :=
      STAmount.toRat_eq_int_mul_of_exponent_ge result (n.exponent_ + 3) (by omega)
    obtain ⟨z, hz'⟩ := STAmount.toRat_eq_int_mul_of_exponent_ge a (n.exponent_ + 3) hoff
    rw [← hu] at hw' hz'
    by_contra hgt
    have hgt' : a.toRat < result.toRat := not_le.mp hgt
    rw [hw', hz'] at hgt'
    have hint_lt : z < w := by
      have := lt_of_mul_lt_mul_right hgt' hu0.le
      exact_mod_cast this
    have hstep : (z : ℚ) * u + u ≤ (w : ℚ) * u := by
      have : (z : ℚ) + 1 ≤ (w : ℚ) := by exact_mod_cast hint_lt
      nlinarith
    have h1 := (abs_le.mp hbound).2
    rw [hw'] at h1
    rw [hz'] at hle
    linarith

/-- **A nonnegative source converts to a nonnegative amount**, for every numeric type. -/
lemma STAmount.ofNumber_nonneg (nt : NumericType) (n : Number) (mode : rounding_mode)
    (result : STAmount) (hn : n.isNormalized) (hneg : n.negative_ = false)
    (hok : STAmount.ofNumber nt n mode = .ok result) : 0 ≤ result.toRat := by
  cases hnt : nt with
  | integral mv mo ms msh =>
    rw [hnt] at hok
    have hint : (NumericType.integral mv mo ms msh).isIntegral = true := rfl
    obtain ⟨iv, hr, hres⟩ :=
      STAmount.ofNumber_integral_toRat _ n mode result hint hneg hok
    rw [hres]
    exact_mod_cast (Number.to_rep_nonneg_range n mode iv hneg hr).1
  | fractional =>
    rw [hnt] at hok
    by_cases hz : result.mValue = 0
    · have : result.toRat = 0 := by unfold STAmount.toRat; simp [hz]
      rw [this]
    by_cases hm : n.mantissa_ = 0
    · rw [Number.eq_zero_of_mantissa_zero n hn hm, STAmount.ofNumber_fractional_zero,
        Except.ok.injEq] at hok
      exact absurd (by rw [← hok]) hz
    have hb := mantissaBounds_nat_of (hn.mantissaBounds hm)
    have hemin := Number.exponent_ge_min n hn hm
    have hexp := STAmount.ofNumber_iou_success_exp_range n mode result hb.1 hb.2 hemin hok hz
    obtain ⟨mant, exp, _, hval, _, hcast, _⟩ := STAmount.ofNumber_iou_snap_pos .fractional n mode
      result rfl hneg hb.1 hb.2 hemin hexp hok hz
    rw [hval, hcast]
    positivity

/-- **A canonically stored amount is below `10 ^ 96` in magnitude.** A fractional amount has a
16-digit mantissa and offset at most `80`, an integral one fits `2^63 - 1`. -/
lemma STAmount.ExactCanonical.abs_lt (s : STAmount) (hc : s.ExactCanonical) :
    |s.toRat| < 10 ^ 96 := by
  rw [STAmount.abs_toRat]
  rcases hc with hiou | ⟨hic, hsz⟩
  · have hm : (s.mValue.toNat : ℚ) < ((10 ^ 16 : ℕ) : ℚ) := by exact_mod_cast hiou.mant_hi
    push_cast at hm
    have he : (10 : ℚ) ^ s.mOffset ≤ (10 : ℚ) ^ (80 : ℤ) :=
      zpow_le_zpow_right₀ (by norm_num) hiou.exp_hi
    have hp : (0 : ℚ) < (10 : ℚ) ^ s.mOffset := zpow_pos (by norm_num) _
    calc (s.mValue.toNat : ℚ) * (10 : ℚ) ^ s.mOffset < 10 ^ 16 * (10 : ℚ) ^ s.mOffset :=
          mul_lt_mul_of_pos_right hm hp
      _ ≤ 10 ^ 16 * (10 : ℚ) ^ (80 : ℤ) := by gcongr
      _ = 10 ^ 96 := by norm_num
  · rw [hic.offset_zero, zpow_zero, mul_one]
    have : (s.mValue.toNat : ℚ) ≤ ((2 ^ 63 - 1 : ℕ) : ℚ) := by exact_mod_cast hsz
    have h2 : ((2 ^ 63 - 1 : ℕ) : ℚ) < 10 ^ 96 := by norm_num
    linarith

/-- The exponent of a Number written as an `STAmount` is `-100` (zero) or in
`[-96, 80]`. -/
lemma numberExponent_range (n : Number) (nt : NumericType) (e : Int)
    (hok : numberExponent n nt = .ok e) : e = -100 ∨ ((-96 : ℤ) ≤ e ∧ e ≤ 80) := by
  unfold numberExponent at hok
  cases ha : STAmount.ofNumber nt n .to_nearest with
  | error err => rw [ha] at hok; exact absurd hok (by simp [bind, Except.bind])
  | ok a =>
    rw [ha] at hok
    simp only [bind, Except.bind, pure, Except.pure, Except.ok.injEq] at hok
    subst hok
    cases hnt : nt.isIntegral
    · have hfr : nt = .fractional := by
        cases nt with
        | integral _ _ _ _ => simp [NumericType.isIntegral] at hnt
        | fractional => rfl
      exact STAmount.ofNumber_fractional_offset nt n .to_nearest a hfr ha
    · have hoff := (STAmount.ofNumber_integral_canonical nt n .to_nearest a hnt ha).1.offset_zero
      right
      show (-96 : ℤ) ≤ a.mOffset ∧ a.mOffset ≤ 80
      rw [hoff]; norm_num

/-- Every successful `STAmount.toNumber` gives a normalized `Number`. -/
lemma STAmount.toNumber_isNormalized (s : STAmount) (mode : rounding_mode) (n : Number)
    (hok : s.toNumber mode = .ok n) : n.isNormalized := by
  unfold STAmount.toNumber at hok
  split at hok
  · split at hok
    · exact absurd hok (by simp)
    · exact Number.from_rep_isNormalized _ _ mode n hok
  · split at hok
    · exact absurd hok (by simp)
    · exact Number.from_rep_isNormalized _ _ mode n hok

/-- Every successful `STAmount.roundToNumericType` gives a normalized `Number`. -/
lemma STAmount.roundToNumericType_isNormalized (nt : NumericType) (v : Number)
    (mode : rounding_mode) (scale : Option Int) (n : Number)
    (hok : STAmount.roundToNumericType nt v mode scale = .ok n) : n.isNormalized := by
  unfold STAmount.roundToNumericType at hok
  repeat' split at hok
  all_goals first
    | exact absurd hok (by simp)
    | exact STAmount.toNumber_isNormalized _ _ n hok

/-- **A to-nearest `ofNumber` result is at least a canonical amount below its source**, for a
nonnegative source. The mirror of `ofNumber_to_nearest_le_of_canonical`. -/
lemma STAmount.ofNumber_to_nearest_ge_of_canonical (nt : NumericType) (n : Number)
    (result a : STAmount) (hn : n.isNormalized) (h0 : 0 ≤ n.toRat)
    (ha : a.ExactCanonical) (hat : a.mNumericType = nt) (hle : a.toRat ≤ n.toRat)
    (hok : STAmount.ofNumber nt n .to_nearest = .ok result) (hresult : result.mValue ≠ 0) :
    a.toRat ≤ result.toRat := by
  cases hnt : nt with
  | integral mv mo ms msh =>
    rw [hnt] at hok hat
    have hint : (NumericType.integral mv mo ms msh).isIntegral = true := rfl
    obtain ⟨iv, hr, hres⟩ :=
      STAmount.ofNumber_integral_toRat _ n .to_nearest result hint
        (Number.negative_false_of_nonneg n hn h0) hok
    have hhalf := Number.to_rep_to_nearest_within_half n iv hn
      (Number.negative_false_of_nonneg n hn h0) hr
    rcases ha with hiou | ⟨hic, _⟩
    · exact absurd (hat.symm.trans hiou.is_fractional) (by simp)
    have haint : (a.toRat.num : ℚ) = a.toRat :=
      Rat.coe_int_num_of_den_eq_one (STAmount.IntegralCanonical.den_eq_one a hic)
    rw [hres, ← haint]
    rw [← haint] at hle
    have h1 := (abs_le.mp hhalf).1
    by_contra hlt
    have hlt' : iv.toInt < a.toRat.num := by exact_mod_cast not_le.mp hlt
    have hstep : (iv.toInt : ℚ) + 1 ≤ a.toRat.num := by exact_mod_cast hlt'
    linarith
  | fractional =>
    rw [hnt] at hok hat
    by_cases hm : n.mantissa_ = 0
    · rw [Number.eq_zero_of_mantissa_zero n hn hm, STAmount.ofNumber_fractional_zero,
        Except.ok.injEq] at hok
      exact absurd (by rw [← hok]) hresult
    rcases ha with hiou | ⟨hic, _⟩
    swap
    · have := hic.is_integral; rw [hat] at this; exact absurd this (by decide)
    have hb := mantissaBounds_nat_of (hn.mantissaBounds hm)
    have hemin := Number.exponent_ge_min n hn hm
    have hexp := STAmount.ofNumber_iou_success_exp_range n .to_nearest result hb.1 hb.2 hemin hok
      hresult
    obtain ⟨hbound, hrexp⟩ := STAmount.ofNumber_iou_within_half_ulp .fractional n result rfl hb.1
      hb.2 hemin hexp hok hresult
    set u : ℚ := (10 : ℚ) ^ (n.exponent_ + 3) with hu
    have hu0 : 0 < u := zpow_pos (by norm_num) _
    have hpos : ∀ e : ℤ, (0 : ℚ) < (10 : ℚ) ^ e := fun e => zpow_pos (by norm_num) e
    -- `result` is a whole multiple of `u`, within half of it from the source
    obtain ⟨w, hw'⟩ :=
      STAmount.toRat_eq_int_mul_of_exponent_ge result (n.exponent_ + 3) (by omega)
    rw [← hu] at hw'
    have h1 := (abs_le.mp hbound).1
    rw [hw'] at h1
    by_cases hoff : n.exponent_ + 3 ≤ a.mOffset
    · -- `a` is a whole multiple of `u` too
      obtain ⟨z, hz'⟩ := STAmount.toRat_eq_int_mul_of_exponent_ge a (n.exponent_ + 3) hoff
      rw [← hu] at hz'
      rw [hw', hz']
      by_contra hgt
      have hgt' : (w : ℚ) * u < (z : ℚ) * u := not_le.mp hgt
      have hint_lt : w < z := by
        have := lt_of_mul_lt_mul_right hgt' hu0.le
        exact_mod_cast this
      have hstep : (w : ℚ) * u + u ≤ (z : ℚ) * u := by
        have : (w : ℚ) + 1 ≤ (z : ℚ) := by exact_mod_cast hint_lt
        nlinarith
      rw [hz'] at hle
      linarith
    · -- `a` sits below `10 ^ (exponent + 18)`, which is on the grid of `u` and at most the source
      have hlt : a.mOffset + 1 ≤ n.exponent_ + 3 := by omega
      have hnabs : |n.toRat| = (n.mantissa_.toNat : ℚ) * (10 : ℚ) ^ n.exponent_ := abs_toRat_eq n
      have haabs : |a.toRat| = (a.mValue.toNat : ℚ) * (10 : ℚ) ^ a.mOffset := STAmount.abs_toRat a
      have hml : ((10 ^ 18 : ℕ) : ℚ) ≤ (n.mantissa_.toNat : ℚ) := by exact_mod_cast hb.1
      have hah : (a.mValue.toNat : ℚ) < ((10 ^ 16 : ℕ) : ℚ) := by exact_mod_cast hiou.mant_hi
      push_cast at hml hah
      have hB : (10 : ℚ) ^ (n.exponent_ + 18) = ((10 ^ 15 : ℤ) : ℚ) * u := by
        rw [hu, show n.exponent_ + 18 = 15 + (n.exponent_ + 3) by ring,
          zpow_add₀ (by norm_num : (10 : ℚ) ≠ 0)]
        push_cast; norm_num
      have haB : a.toRat < (10 : ℚ) ^ (n.exponent_ + 18) := by
        have h1 : (a.mValue.toNat : ℚ) * (10 : ℚ) ^ a.mOffset < 10 ^ 16 * (10 : ℚ) ^ a.mOffset :=
          mul_lt_mul_of_pos_right hah (hpos _)
        have h2 : (10 : ℚ) ^ 16 * (10 : ℚ) ^ a.mOffset ≤ (10 : ℚ) ^ (n.exponent_ + 18) := by
          have e1 : (10 : ℚ) ^ 16 * (10 : ℚ) ^ a.mOffset = (10 : ℚ) ^ (a.mOffset + 16) := by
            rw [zpow_add₀ (by norm_num : (10 : ℚ) ≠ 0)]; norm_num; ring
          rw [e1]
          exact zpow_le_zpow_right₀ (by norm_num) (by omega)
        linarith [le_abs_self a.toRat]
      have hBn : (10 : ℚ) ^ (n.exponent_ + 18) ≤ n.toRat := by
        have e2 : (10 : ℚ) ^ (n.exponent_ + 18) = 10 ^ 18 * (10 : ℚ) ^ n.exponent_ := by
          rw [zpow_add₀ (by norm_num : (10 : ℚ) ≠ 0)]; norm_num; ring
        have h3 : (10 : ℚ) ^ 18 * (10 : ℚ) ^ n.exponent_ ≤
            (n.mantissa_.toNat : ℚ) * (10 : ℚ) ^ n.exponent_ :=
          mul_le_mul_of_nonneg_right hml (hpos _).le
        rw [e2, ← abs_of_nonneg h0, hnabs]
        exact h3
      -- so `result` is at least `10 ^ (exponent + 18)`
      have hrB : (10 : ℚ) ^ (n.exponent_ + 18) ≤ result.toRat := by
        rw [hw', hB]
        by_contra hgt
        have hgt' : (w : ℚ) * u < ((10 ^ 15 : ℤ) : ℚ) * u := not_le.mp hgt
        have hint_lt : w < 10 ^ 15 := by
          have := lt_of_mul_lt_mul_right hgt' hu0.le
          exact_mod_cast this
        have hstep : (w : ℚ) * u + u ≤ ((10 ^ 15 : ℤ) : ℚ) * u := by
          have : (w : ℚ) + 1 ≤ ((10 ^ 15 : ℤ) : ℚ) := by exact_mod_cast hint_lt
          nlinarith
        rw [hB] at hBn
        linarith
      linarith

/-- **A fractional `ofNumber` of a source whose exponent is at least `-99` is never zero.** The
result exponent is at least three above the source exponent, so it never falls below the
smallest offset `-96`, where the conversion would flush to zero. -/
lemma STAmount.ofNumber_iou_ne_zero_of_exponent (n : Number) (mode : rounding_mode)
    (result : STAmount) (hn : n.isNormalized) (hn0 : n.mantissa_ ≠ 0)
    (hexp : (-99 : ℤ) ≤ n.exponent_) (hok : STAmount.ofNumber .fractional n mode = .ok result) :
    result.mValue ≠ 0 := by
  intro hr0
  have hb := mantissaBounds_nat_of (hn.mantissaBounds hn0)
  have hemin := Number.exponent_ge_min n hn hn0
  -- the sign-cleared source keeps the mantissa and exponent
  have hmne : (n.mantissa_ != 0) = true := by simp [hn0]
  have hneg_eq : decide (n.signum < 0) = n.negative_ := Number.signum_neg_decide n
  set neg : Bool := decide (n.signum < 0) with hneg_def
  set working : Number := if neg then n.operator_neg else n with hw_def
  have hw_mant : working.mantissa_ = n.mantissa_ := by
    rw [hw_def]; rcases neg with _ | _
    · simp
    · simp [Number.operator_neg_mantissa_of_ne n hn0]
  have hw_exp : working.exponent_ = n.exponent_ := by
    rw [hw_def]; rcases neg with _ | _
    · simp
    · simp only [if_true]; unfold Number.operator_neg; rw [if_neg (by simpa using hn0)]
  have hw_neg : working.negative_ = false := by
    rw [hw_def, hneg_eq]
    by_cases hrn : n.negative_ = true
    · rw [if_pos hrn, Number.operator_neg_negative_of_ne n hn0]; simp [hrn]
    · rw [if_neg hrn]; simpa using hrn
  have hw_lo : 10 ^ 18 ≤ working.mantissa_.toNat := by rw [hw_mant]; exact hb.1
  have hw_hi : working.mantissa_.toNat < 10 ^ 19 := by rw [hw_mant]; exact hb.2
  unfold STAmount.ofNumber at hok
  rw [if_neg (by decide), ← hneg_def, ← hw_def] at hok
  cases hnorm : working.normalizeToRange kMinValue kMaxValue mode with
  | error e => rw [hnorm] at hok; exact absurd hok (by simp)
  | ok me =>
    obtain ⟨mant, exp⟩ := me
    rw [hnorm] at hok
    simp only at hok
    have hnorm' : working.normalizeToRange cMinValue cMaxValue mode = .ok (mant, exp) := hnorm
    have hexp_hi3 : working.exponent_ + 3 ≤ maxExponent :=
      normalizeToRange_iou_exp_hi working mode mant exp hw_lo hw_hi hnorm'
    obtain ⟨⟨hmlo, hmhi⟩, ⟨hexp_lo3, hexp_le⟩, hsgn⟩ :=
      normalizeToRange_iou_ok_facts working mode mant exp hw_lo hw_hi
        (by rw [hw_exp]; omega) hexp_hi3 hnorm'
    have hmant_pos : 0 ≤ mant.toInt := hsgn.1 hw_neg
    have hmant_natAbs : mant.toInt.natAbs = mant.toUInt64.toNat := by
      have := toUInt64_toNat_of_nonneg mant hmant_pos; omega
    have hmtu_lo : 10 ^ 15 ≤ mant.toUInt64.toNat := by
      rw [← hmant_natAbs]; have := hmlo
      rw [(by decide : cMinValue.toNat = 10 ^ 15)] at this
      exact this
    have hmtu_hi : mant.toUInt64.toNat < 10 ^ 16 := by
      rw [← hmant_natAbs]; have := hmhi
      rw [(by decide : cMaxValue.toNat = 10 ^ 16 - 1)] at this
      omega
    have hlt := STAmount.checked_iou_zero_exp_lt mant.toUInt64 exp neg mode hmtu_lo hmtu_hi
      (by rw [hw_exp] at hexp_lo3; omega) hexp_le result hok hr0
    rw [hw_exp] at hexp_lo3
    unfold cMinOffset at hlt
    omega

/-- **A nonzero canonical amount's value converts to a nonzero amount.** The source
is at or above the 16-digit floor of the type, so no rounding flushes it to zero. -/
lemma STAmount.ofNumber_ne_zero_of_canonical (nt : NumericType) (n : Number)
    (mode : rounding_mode) (result a : STAmount) (hn : n.isNormalized)
    (ha : a.ExactCanonical) (hat : a.mNumericType = nt) (ha0 : a.mValue ≠ 0)
    (heq : n.toRat = a.toRat) (hok : STAmount.ofNumber nt n mode = .ok result) :
    result.mValue ≠ 0 := by
  have hna : n.toRat ≠ 0 := heq ▸ STAmount.toRat_ne_zero a ha0
  have hn0 : n.mantissa_ ≠ 0 := fun h => hna (Number.toRat_eq_zero_of_mantissa_zero n h)
  intro hr0
  have hr : result.toRat = 0 := by unfold STAmount.toRat; simp [hr0]
  cases hnt : nt with
  | integral mv mo ms msh =>
    rw [hnt] at hok hat
    have hint : (NumericType.integral mv mo ms msh).isIntegral = true := rfl
    rcases ha with hiou | ⟨hic, _⟩
    · exact absurd (hat.symm.trans hiou.is_fractional) (by simp)
    have hden : n.toRat.den = 1 := by
      rw [heq]; exact STAmount.IntegralCanonical.den_eq_one a hic
    have hex := STAmount.ofNumber_integral_exact _ n mode result hint hn hden hok
    rw [hr] at hex
    exact hna hex.symm
  | fractional =>
    rw [hnt] at hok hat
    rcases ha with hiou | ⟨hic, _⟩
    swap
    · have := hic.is_integral
      unfold STAmount.integral at this
      rw [hat] at this
      exact absurd this (by decide)
    have hb := mantissaBounds_nat_of (hn.mantissaBounds hn0)
    have hemin := Number.exponent_ge_min n hn hn0
    -- the amount's offset is at most three above the source exponent
    have hoff : a.mOffset ≤ n.exponent_ + 3 := by
      by_contra hgt
      push Not at hgt
      have hnabs : |n.toRat| = (n.mantissa_.toNat : ℚ) * (10 : ℚ) ^ n.exponent_ := abs_toRat_eq n
      have haabs : |a.toRat| = (a.mValue.toNat : ℚ) * (10 : ℚ) ^ a.mOffset := STAmount.abs_toRat a
      have hmh : (n.mantissa_.toNat : ℚ) < ((10 ^ 19 : ℕ) : ℚ) := by exact_mod_cast hb.2
      have hal : ((10 ^ 15 : ℕ) : ℚ) ≤ (a.mValue.toNat : ℚ) := by exact_mod_cast hiou.mant_lo
      push_cast at hmh hal
      have hpos : ∀ e : ℤ, (0 : ℚ) < (10 : ℚ) ^ e := fun e => zpow_pos (by norm_num) e
      have habs : (a.mValue.toNat : ℚ) * (10 : ℚ) ^ a.mOffset =
          (n.mantissa_.toNat : ℚ) * (10 : ℚ) ^ n.exponent_ := by rw [← haabs, ← hnabs, heq]
      have h1 : (10 : ℚ) ^ 15 * (10 : ℚ) ^ a.mOffset ≤
          (a.mValue.toNat : ℚ) * (10 : ℚ) ^ a.mOffset :=
        mul_le_mul_of_nonneg_right hal (hpos _).le
      have h2 : (10 : ℚ) ^ 19 * (10 : ℚ) ^ n.exponent_ ≤ 10 ^ 15 * (10 : ℚ) ^ a.mOffset := by
        have : (10 : ℚ) ^ 15 * (10 : ℚ) ^ a.mOffset = (10 : ℚ) ^ (a.mOffset + 15) := by
          rw [zpow_add₀ (by norm_num : (10 : ℚ) ≠ 0)]; norm_num; ring
        have h' : (10 : ℚ) ^ 19 * (10 : ℚ) ^ n.exponent_ = (10 : ℚ) ^ (n.exponent_ + 19) := by
          rw [zpow_add₀ (by norm_num : (10 : ℚ) ≠ 0)]; norm_num; ring
        rw [this, h']
        exact zpow_le_zpow_right₀ (by norm_num) (by omega)
      have h3 : (n.mantissa_.toNat : ℚ) * (10 : ℚ) ^ n.exponent_ <
          (10 : ℚ) ^ 19 * (10 : ℚ) ^ n.exponent_ :=
        mul_lt_mul_of_pos_right hmh (hpos _)
      linarith
    exact STAmount.ofNumber_iou_ne_zero_of_exponent n mode result hn hn0
      (by have := hiou.exp_lo; omega) hok hr0

/-- **A to-nearest `ofNumber` keeps a value a canonical amount holds**, for a nonnegative
source: the result equals that amount. -/
lemma STAmount.ofNumber_to_nearest_eq_of_canonical (nt : NumericType) (n : Number)
    (result a : STAmount) (hn : n.isNormalized) (h0 : 0 ≤ n.toRat)
    (ha : a.ExactCanonical) (hat : a.mNumericType = nt) (heq : n.toRat = a.toRat)
    (hok : STAmount.ofNumber nt n .to_nearest = .ok result) :
    result.toRat = a.toRat := by
  by_cases ha0 : a.mValue = 0
  · -- a zero amount: the source is the zero `Number`, which converts to zero
    have hav : a.toRat = 0 := by unfold STAmount.toRat; simp [ha0]
    have hnz : n = Number.zero := (Number.toRat_eq_zero_iff_eq_zero hn).mp (by rw [heq, hav])
    rw [hav]
    cases hnt : nt with
    | integral mv mo ms msh =>
      rw [hnt] at hok
      have hden : n.toRat.den = 1 := by rw [heq, hav]; rfl
      rw [STAmount.ofNumber_integral_exact _ n _ result rfl hn hden hok, heq, hav]
    | fractional =>
      rw [hnt, hnz, STAmount.ofNumber_fractional_zero, Except.ok.injEq] at hok
      rw [← hok]
      unfold STAmount.toRat
      simp
  have hresult := STAmount.ofNumber_ne_zero_of_canonical nt n .to_nearest result a hn ha hat ha0
    heq hok
  exact le_antisymm
    (STAmount.ofNumber_to_nearest_le_of_canonical nt n result a hn h0 ha hat heq.le hok hresult)
    (STAmount.ofNumber_to_nearest_ge_of_canonical nt n result a hn h0 ha hat heq.ge hok hresult)

/-- **A positive 16-digit IOU amount lies between `10^(e + 15)` and `10^(e + 16)`**, where `e` is its
exponent. The upper bound keeps one unit of room: the amount is at most `10^(e + 16) - 10^e`. -/
lemma STAmount.IOUCanonical.toRat_bounds (s : STAmount) (hs : s.IOUCanonical) (hpos : 0 < s.toRat) :
    (10 : ℚ) ^ (s.exponent + 15) ≤ s.toRat ∧
      s.toRat + (10 : ℚ) ^ s.exponent ≤ (10 : ℚ) ^ (s.exponent + 16) := by
  have hp : (0 : ℚ) < (10 : ℚ) ^ s.exponent := zpow_pos (by norm_num) _
  have habs := STAmount.abs_toRat s
  rw [abs_of_pos hpos] at habs
  have hmlo : ((10 ^ 15 : ℕ) : ℚ) ≤ (s.mValue.toNat : ℚ) := by exact_mod_cast hs.mant_lo
  have hmhi : (s.mValue.toNat : ℚ) + 1 ≤ ((10 ^ 16 : ℕ) : ℚ) := by
    have := hs.mant_hi; exact_mod_cast this
  push_cast at hmlo hmhi
  have hexp : s.exponent = s.mOffset := rfl
  rw [zpow_add₀ (by norm_num : (10 : ℚ) ≠ 0), zpow_add₀ (by norm_num : (10 : ℚ) ≠ 0), habs, ← hexp]
  norm_num
  constructor
  · rw [mul_comm]; exact mul_le_mul_of_nonneg_right hmlo hp.le
  · nlinarith

/-- **A to-nearest `ofNumber` returns a canonical amount its source is very close to.** A
nonnegative source within `½ · 10 ^ (a.exponent - 1)` of a positive canonical amount `a` of the
same type converts to `a`. The rounding moves the source by at most half a unit, and the other
canonical amounts are at least a tenth of a unit away from `a`. -/
lemma STAmount.ofNumber_to_nearest_eq_of_near_canonical (nt : NumericType) (n : Number)
    (result a : STAmount) (hn : n.isNormalized) (h0 : 0 ≤ n.toRat)
    (ha : a.ExactCanonical) (hat : a.mNumericType = nt) (ha0 : 0 < a.toRat)
    (hnear : |n.toRat - a.toRat| < (1 / 2 : ℚ) * (10 : ℚ) ^ (a.exponent - 1))
    (hok : STAmount.ofNumber nt n .to_nearest = .ok result) (hresult : result.mValue ≠ 0) :
    result.toRat = a.toRat := by
  have hp : ∀ k : ℤ, (0 : ℚ) < (10 : ℚ) ^ k := fun k => zpow_pos (by norm_num) k
  have hu : (1 / 2 : ℚ) * (10 : ℚ) ^ (a.exponent - 1) = (10 : ℚ) ^ a.exponent / 20 := by
    rw [zpow_sub₀ (by norm_num : (10 : ℚ) ≠ 0)]; ring
  rw [hu] at hnear
  obtain ⟨hnear_lo, hnear_hi⟩ := abs_lt.mp hnear
  cases hnt : nt with
  | integral mv mo ms msh =>
    rw [hnt] at hok hat
    have hint : (NumericType.integral mv mo ms msh).isIntegral = true := rfl
    rcases ha with hiou | ⟨hic, _⟩
    · exact absurd (hat.symm.trans hiou.is_fractional) (by simp)
    -- both values are whole numbers, less than one apart
    have hoff : a.exponent = 0 := hic.offset_zero
    rw [hoff, zpow_zero] at hnear_lo hnear_hi
    have hneg := Number.negative_false_of_nonneg n hn h0
    have hhalf := abs_le.mp (STAmount.ofNumber_integral_within_half _ n result hint hn hneg hok)
    obtain ⟨iv, _, hres⟩ := STAmount.ofNumber_integral_toRat _ n .to_nearest result hint hneg hok
    have hsd := STAmount.IntegralCanonical.toRat_eq_signedDrops a hic
    have h1 : ((iv.toInt - a.signedDrops : ℤ) : ℚ) < 1 := by
      push_cast; rw [← hres, ← hsd]; linarith [hhalf.2]
    have h2 : (-1 : ℚ) < ((iv.toInt - a.signedDrops : ℤ) : ℚ) := by
      push_cast; rw [← hres, ← hsd]; linarith [hhalf.1]
    have h1' : iv.toInt - a.signedDrops < 1 := by exact_mod_cast h1
    have h2' : -1 < iv.toInt - a.signedDrops := by exact_mod_cast h2
    rw [hres, hsd, show iv.toInt = a.signedDrops by omega]
  | fractional =>
    rw [hnt] at hok hat
    have hiou : a.IOUCanonical :=
      ha.iouCanonical (by unfold STAmount.integral; rw [hat]; rfl)
    -- `a` has 16 digits: `10^(e+15) ≤ a ≤ 10^(e+16) - 10^e`
    obtain ⟨halo, hahi⟩ := STAmount.IOUCanonical.toRat_bounds a hiou ha0
    have hpow15 : (10 : ℚ) ^ (a.exponent + 15) = 10 ^ 15 * (10 : ℚ) ^ a.exponent := by
      rw [zpow_add₀ (by norm_num : (10 : ℚ) ≠ 0)]; norm_num; ring
    -- the source is positive, so it has a nonzero mantissa
    have hn_pos : 0 < n.toRat := by
      have : (10 : ℚ) ^ a.exponent / 20 < (10 : ℚ) ^ (a.exponent + 15) := by
        rw [hpow15]; linarith [hp a.exponent]
      linarith
    have hn0 : n.mantissa_ ≠ 0 := fun h => by
      rw [Number.toRat_eq_zero_of_mantissa_zero n h] at hn_pos; exact lt_irrefl _ hn_pos
    have hb := mantissaBounds_nat_of (hn.mantissaBounds hn0)
    have hemin := Number.exponent_ge_min n hn hn0
    have hexp := STAmount.ofNumber_iou_success_exp_range n .to_nearest result hb.1 hb.2 hemin hok
      hresult
    obtain ⟨hbound, hle⟩ := STAmount.ofNumber_iou_within_half_ulp .fractional n result rfl hb.1
      hb.2 hemin hexp hok hresult
    -- the source lies between `10^(t + 15)` and `10^(t + 16)`, where `t` is its exponent plus 3
    have hnabs := abs_toRat_eq n
    rw [abs_of_pos hn_pos] at hnabs
    have hnm_lo : ((10 ^ 18 : ℕ) : ℚ) ≤ (n.mantissa_.toNat : ℚ) := by exact_mod_cast hb.1
    have hnm_hi : (n.mantissa_.toNat : ℚ) < ((10 ^ 19 : ℕ) : ℚ) := by exact_mod_cast hb.2
    push_cast at hnm_lo hnm_hi
    have hn_lo : (10 : ℚ) ^ (n.exponent_ + 18) ≤ n.toRat := by
      rw [hnabs, zpow_add₀ (by norm_num : (10 : ℚ) ≠ 0)]
      norm_num
      rw [mul_comm]
      exact mul_le_mul_of_nonneg_right hnm_lo (hp _).le
    have hn_hi : n.toRat < (10 : ℚ) ^ (n.exponent_ + 19) := by
      rw [hnabs, zpow_add₀ (by norm_num : (10 : ℚ) ≠ 0)]
      norm_num
      rw [mul_comm]
      exact mul_lt_mul_of_pos_left hnm_hi (hp _)
    -- so the source exponent plus 3 is `a.exponent - 1` or `a.exponent`
    have ht_le : n.exponent_ + 3 ≤ a.exponent := by
      by_contra h
      push Not at h
      have : (10 : ℚ) ^ (a.exponent + 16) ≤ (10 : ℚ) ^ (n.exponent_ + 18) :=
        zpow_le_zpow_right₀ (by norm_num) (by omega)
      have : (10 : ℚ) ^ a.exponent / 20 < (10 : ℚ) ^ a.exponent := by linarith [hp a.exponent]
      linarith
    have ht_ge : a.exponent - 1 ≤ n.exponent_ + 3 := by
      by_contra h
      push Not at h
      have h14 : (10 : ℚ) ^ (n.exponent_ + 19) ≤ (10 : ℚ) ^ (a.exponent + 14) :=
        zpow_le_zpow_right₀ (by norm_num) (by omega)
      have hpow14 : (10 : ℚ) ^ (a.exponent + 14) = 10 ^ 14 * (10 : ℚ) ^ a.exponent := by
        rw [zpow_add₀ (by norm_num : (10 : ℚ) ≠ 0)]; norm_num; ring
      rw [hpow14] at h14
      rw [hpow15] at halo
      linarith [hp a.exponent]
    -- both amounts are whole multiples of `10^t`, less than one such unit apart
    obtain ⟨za, hza⟩ := STAmount.toRat_eq_int_mul_of_exponent_ge a (n.exponent_ + 3) ht_le
    obtain ⟨zr, hzr⟩ := STAmount.toRat_eq_int_mul_of_exponent_ge result (n.exponent_ + 3) hle
    have hstep : (10 : ℚ) ^ a.exponent / 20 ≤ (1 / 2 : ℚ) * (10 : ℚ) ^ (n.exponent_ + 3) := by
      have : (10 : ℚ) ^ (a.exponent - 1) ≤ (10 : ℚ) ^ (n.exponent_ + 3) :=
        zpow_le_zpow_right₀ (by norm_num) ht_ge
      rw [zpow_sub₀ (by norm_num : (10 : ℚ) ≠ 0)] at this
      linarith
    have hdiff : |result.toRat - a.toRat| < (10 : ℚ) ^ (n.exponent_ + 3) := by
      have h := abs_sub_le result.toRat n.toRat a.toRat
      linarith [abs_lt.mpr ⟨hnear_lo, hnear_hi⟩]
    rw [hzr, hza, ← sub_mul, abs_mul, abs_of_pos (hp _)] at hdiff
    have hlt : |((zr - za : ℤ) : ℚ)| < 1 := by
      push_cast
      exact (mul_lt_iff_lt_one_left (hp _)).mp hdiff
    obtain ⟨hl1, hl2⟩ := abs_lt.mp hlt
    have hl1' : -1 < zr - za := by exact_mod_cast hl1
    have hl2' : zr - za < 1 := by exact_mod_cast hl2
    rw [hzr, hza, show zr = za by omega]

/-- Two 16-digit mantissas that give the same value cannot sit at exponents more
than one digit apart: the finer one would need a 17th digit. -/
private lemma mant16_exp_le (ma mb : ℕ) (ea eb : ℤ) (ha_hi : ma < 10 ^ 16)
    (hb_lo : 10 ^ 15 ≤ mb) (h : (ma : ℚ) * 10 ^ ea = (mb : ℚ) * 10 ^ eb) : eb ≤ ea := by
  by_contra hlt
  push Not at hlt
  obtain ⟨k, hk⟩ : ∃ k : ℕ, eb = ea + ((k + 1 : ℕ) : ℤ) :=
    ⟨(eb - ea - 1).toNat, by push_cast; omega⟩
  rw [hk, zpow_add₀ (by norm_num : (10 : ℚ) ≠ 0), zpow_natCast] at h
  have hp : (0 : ℚ) < 10 ^ ea := zpow_pos (by norm_num) _
  have h2 : (ma : ℚ) = mb * 10 ^ (k + 1) := by
    have h' : (ma : ℚ) * 10 ^ ea = ((mb : ℚ) * 10 ^ (k + 1)) * 10 ^ ea := by rw [h]; ring
    exact mul_right_cancel₀ (ne_of_gt hp) h'
  have hten : (10 : ℚ) ≤ 10 ^ (k + 1) := by
    calc (10 : ℚ) = 10 ^ 1 := by norm_num
      _ ≤ 10 ^ (k + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
  have hal : (ma : ℚ) < 10 ^ 16 := by exact_mod_cast ha_hi
  have hbl : (10 : ℚ) ^ 15 ≤ mb := by exact_mod_cast hb_lo
  nlinarith

/-- **Two canonical amounts of one numeric type with the same value are equal.** A
canonical amount stores one mantissa, exponent and sign for each nonzero value. -/
lemma STAmount.eq_of_exactCanonical (a b : STAmount) (ha : a.ExactCanonical)
    (hb : b.ExactCanonical) (hnt : a.mNumericType = b.mNumericType) (ha0 : a.mValue ≠ 0)
    (h : a.toRat = b.toRat) : a = b := by
  have hb0 : b.mValue ≠ 0 := by
    intro h0
    apply STAmount.toRat_ne_zero a ha0
    rw [h, STAmount.toRat_signed, h0]
    simp
  -- the sign is the sign of the value
  have hneg_iff : ∀ s : STAmount, s.mValue ≠ 0 → (s.toRat < 0 ↔ s.mIsNegative = true) := by
    intro s hs
    have hm : (0 : ℚ) < (s.mValue.toNat : ℚ) := by
      have hs' : s.mValue.toNat ≠ 0 := fun h0 => hs (by rw [← UInt64.toNat_inj]; simpa using h0)
      exact_mod_cast Nat.pos_of_ne_zero hs'
    have hp : (0 : ℚ) < 10 ^ s.mOffset := zpow_pos (by norm_num) _
    rw [STAmount.toRat_signed]
    rcases s.mIsNegative with _ | _
    · simp only [Bool.false_eq_true, if_false, one_mul, iff_false, not_lt]
      positivity
    · simp only [if_true, iff_true]
      nlinarith [mul_pos hm hp]
  have hsign : a.mIsNegative = b.mIsNegative := by
    have ha' := hneg_iff a ha0
    have hb' := hneg_iff b hb0
    rw [h] at ha'
    cases hna : a.mIsNegative <;> cases hnb : b.mIsNegative <;> simp_all
  -- the magnitudes agree, and a canonical magnitude fixes the mantissa and exponent
  have habs : (a.mValue.toNat : ℚ) * 10 ^ a.mOffset = (b.mValue.toNat : ℚ) * 10 ^ b.mOffset := by
    rw [← STAmount.abs_toRat, ← STAmount.abs_toRat, h]
  have hpow : ∀ e : ℤ, (0 : ℚ) < 10 ^ e := fun e => zpow_pos (by norm_num) e
  have hparts : a.mValue = b.mValue ∧ a.mOffset = b.mOffset := by
    rcases ha with hia | ⟨hia, _⟩ <;> rcases hb with hib | ⟨hib, _⟩
    · have he : a.mOffset = b.mOffset :=
        le_antisymm (mant16_exp_le _ _ _ _ hib.mant_hi hia.mant_lo habs.symm)
          (mant16_exp_le _ _ _ _ hia.mant_hi hib.mant_lo habs)
      rw [he] at habs
      have hm : (a.mValue.toNat : ℚ) = b.mValue.toNat :=
        mul_right_cancel₀ (ne_of_gt (hpow b.mOffset)) habs
      exact ⟨UInt64.toNat_inj.mp (by exact_mod_cast hm), he⟩
    · have := hib.is_integral
      rw [← hnt, hia.is_fractional] at this
      exact absurd this (by decide)
    · have := hia.is_integral
      rw [hnt, hib.is_fractional] at this
      exact absurd this (by decide)
    · rw [hia.offset_zero, hib.offset_zero] at habs ⊢
      simp only [zpow_zero, mul_one] at habs
      exact ⟨UInt64.toNat_inj.mp (by exact_mod_cast habs), rfl⟩
  cases a
  cases b
  simp only [STAmount.mk.injEq]
  exact ⟨hnt, hparts.1, hparts.2, hsign⟩

/-- Rounding zero to a numeric type gives zero, at every scale. -/
lemma STAmount.roundToNumericType_zero (nt : NumericType) (e : Int) :
    STAmount.roundToNumericType nt Number.zero .upward (some e) = .ok Number.zero := by
  cases nt with
  | fractional =>
    have h2 : (⟨.fractional, 0, -100, false⟩ : STAmount).toNumber .upward = .ok Number.zero := by
      rfl
    simp [STAmount.roundToNumericType, STAmount.ofNumber_fractional_zero, STAmount.roundToExponent,
      STAmount.integral, STAmount.isZero, NumericType.isIntegral, h2]
  | integral mv mo ms msh =>
    have h1 : STAmount.ofNumber (.integral mv mo ms msh) Number.zero .upward =
        .ok ⟨.integral mv mo ms msh, 0, 0, false⟩ := by
      simp [STAmount.ofNumber, NumericType.isIntegral, STAmount.checked, STAmount.unchecked,
        STAmount.canonicalize, STAmount.integral, Number.signum]
      rfl
    have h2 : (⟨.integral mv mo ms msh, 0, 0, false⟩ : STAmount).toNumber .upward =
        .ok Number.zero := by
      rfl
    simp [STAmount.roundToNumericType, h1, STAmount.integral, NumericType.isIntegral, h2]

/-- `⌈M / 1000⌉` as a quotient plus a carry when the remainder is nonzero. -/
private lemma ceil_div_thousand (M : ℕ) :
    ⌈(M : ℚ) / 1000⌉ = ((M / 1000 + (if M % 1000 ≠ 0 then 1 else 0) : ℕ) : ℤ) := by
  have hdm : (M : ℚ) / 1000 = ((M / 1000 : ℕ) : ℚ) + ((M % 1000 : ℕ) : ℚ) / 1000 := by
    have hq : (M : ℚ) = 1000 * ((M / 1000 : ℕ) : ℚ) + ((M % 1000 : ℕ) : ℚ) := by
      exact_mod_cast (Nat.div_add_mod M 1000).symm
    rw [hq]
    ring
  have hr1 : ((M % 1000 : ℕ) : ℚ) < 1000 := by exact_mod_cast Nat.mod_lt M (by norm_num)
  rw [Int.ceil_eq_iff, hdm]
  split_ifs with h
  · have hrp : (0 : ℚ) < ((M % 1000 : ℕ) : ℚ) := by exact_mod_cast Nat.pos_of_ne_zero h
    have hz : (((M / 1000 + 1 : ℕ) : ℤ) : ℚ) = ((M / 1000 : ℕ) : ℚ) + 1 := by norm_cast
    rw [hz]
    constructor <;> linarith [div_pos hrp (by norm_num : (0 : ℚ) < 1000),
      (div_lt_one (by norm_num : (0 : ℚ) < 1000)).mpr hr1]
  · have hr : M % 1000 = 0 := by simpa using h
    have hz : (((M / 1000 + 0 : ℕ) : ℤ) : ℚ) = ((M / 1000 : ℕ) : ℚ) := by norm_cast
    rw [hz, hr, Nat.cast_zero, zero_div, add_zero]
    constructor <;> linarith

/-- **An upward fractional `ofNumber` rounds up onto the 16-digit grid of its source.** A
nonzero result is the ceiling of a nonnegative source at scale `10 ^ (exponent + 3)`, three
digits above the source's 19-digit mantissa. -/
lemma STAmount.ofNumber_iou_upward_ceil (n : Number) (result : STAmount) (hn : n.isNormalized)
    (hn0 : n.mantissa_ ≠ 0) (h0 : 0 ≤ n.toRat)
    (hok : STAmount.ofNumber .fractional n .upward = .ok result) (hresult : result.mValue ≠ 0) :
    RoundsToRepresentableAt result n.toRat (n.exponent_ + 3) .upward := by
  have hb := mantissaBounds_nat_of (hn.mantissaBounds hn0)
  have hemin := Number.exponent_ge_min n hn hn0
  have hneg := Number.negative_false_of_nonneg n hn h0
  have hexp := STAmount.ofNumber_iou_success_exp_range n .upward result hb.1 hb.2 hemin hok
    hresult
  obtain ⟨mant, exp, hnr, hval, -⟩ := STAmount.ofNumber_iou_snap_pos .fractional n .upward result
    rfl hneg hb.1 hb.2 hemin hexp hok hresult
  obtain ⟨hceil, -⟩ := normalizeToRange_16_ceil_pos n mant exp hneg hb.1 hb.2 (by omega) hexp hnr
  have hnv : n.toRat = (n.mantissa_.toNat : ℚ) * 10 ^ n.exponent_ := by
    rw [← abs_of_nonneg h0]
    exact abs_toRat_eq n
  have hdiv : n.toRat / 10 ^ (n.exponent_ + 3) = (n.mantissa_.toNat : ℚ) / 1000 := by
    rw [hnv, zpow_add₀ (by norm_num : (10 : ℚ) ≠ 0)]
    field_simp
    norm_num
  show result.toRat = (⌈n.toRat / 10 ^ (n.exponent_ + 3)⌉ : ℚ) * 10 ^ (n.exponent_ + 3)
  rw [hval, hceil, hdiv, ceil_div_thousand]
  norm_cast

end XRPL.Model.Protocol
