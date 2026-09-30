import XRPL.Properties.Vault.Proofs.Support.STAmountFacts

/-! # Integral amounts

Facts about integral `STAmount`s: `canonicalize`, `ofNumber` and `toNumber` on integer-valued
amounts. -/

namespace XRPL.Model.Protocol

/-- **Forward totality of the integral `STAmount.canonicalize`.** An offset-`0`,
sign-cleared integral record whose magnitude fits both `maxRep` and the numeric
type's carried bound canonicalizes without error: the nested `to_rep` succeeds by
`Number.to_rep_ok_of_nonneg_exp_nonpos` (offset `0`, so its own adjusted exponent is
nonpositive), and the resulting magnitude, still within `maxRep`, clears the
type's `maxValue` check. -/
lemma STAmount.canonicalize_integral_ok (s : STAmount) (mode : rounding_mode)
    (hint : s.integral = true) (hoff : s.mOffset = 0) (hsneg : s.mIsNegative = false)
    (hv : s.mValue.toNat ≤ maxRep.toNat) (hvmax : maxRep.toNat ≤ s.mNumericType.maxValue.toNat)
    (hmaxoff : (0 : Int) ≤ s.mNumericType.maxOffset) :
    ∃ result, s.canonicalize mode = .ok result := by
  rw [STAmount.canonicalize, if_pos hint]
  by_cases hz : (s.mValue == 0 || decide (s.mOffset ≤ -20)) = true
  · exact ⟨_, by rw [if_pos hz]⟩
  · rw [if_neg hz,
        if_neg (show ¬ s.mOffset > s.mNumericType.maxOffset from by rw [hoff]; omega)]
    simp only [IntAmount.ofNumber]
    obtain ⟨r2, hr2⟩ := Number.to_rep_ok_of_nonneg_exp_nonpos
      (Number.unchecked s.mIsNegative s.mValue s.mOffset) mode
      (show (Number.unchecked s.mIsNegative s.mValue s.mOffset).negative_ = false from hsneg)
      (show (Number.unchecked s.mIsNegative s.mValue s.mOffset).exponent ≤ 0 from by
        unfold Number.exponent
        rw [if_neg (show ¬ (Number.unchecked s.mIsNegative s.mValue s.mOffset).mantissa_ > maxRep
          from by show ¬ s.mValue > maxRep; rw [gt_iff_lt, UInt64.lt_iff_toNat_lt]; omega)]
        exact le_of_eq hoff)
    rw [hr2]
    simp only []
    have hr2rng := Number.to_rep_nonneg_range
      (Number.unchecked s.mIsNegative s.mValue s.mOffset) mode r2 hsneg hr2
    rw [if_neg (show ¬ r2.toInt.natAbs.toUInt64 > s.mNumericType.maxValue from by
      rw [gt_iff_lt, UInt64.lt_iff_toNat_lt]
      have habs : (r2.toInt.natAbs : ℤ) = r2.toInt := Int.natAbs_of_nonneg hr2rng.1
      have habs_le : r2.toInt.natAbs ≤ maxRep.toNat := by
        have : (r2.toInt.natAbs : ℤ) ≤ (maxRep.toNat : ℤ) := by rw [habs]; exact hr2rng.2
        exact_mod_cast this
      have hlt64 : r2.toInt.natAbs < 2 ^ 64 := by
        have : maxRep.toNat < 2 ^ 64 := by rw [maxRep_val]; norm_num
        omega
      rw [UInt64.toNat_ofNat_of_lt' (by rw [uint64_size_val]; exact hlt64)]
      omega)]
    exact ⟨_, rfl⟩

/-- **Forward totality of the integral `STAmount.ofNumber`.** A normalized,
nonnegative `Number` whose value fits `2 ^ 63 - 1` converts into any integral
numeric type whose carried `maxValue` covers `maxRep` and whose `maxOffset` is
nonnegative. The sign flag resolves to `false`, `to_rep` succeeds (its adjusted
exponent is nonpositive by `Number.exponent_fn_le_zero_of_cap`), and the repack
`checked` canonicalizes without error. -/
lemma STAmount.ofNumber_integral_ok_of_cap (nt : NumericType) (n : Number)
    (mode : rounding_mode) (hnt : nt.isIntegral = true)
    (hmaxval : maxRep.toNat ≤ nt.maxValue.toNat) (hmaxoff : (0 : Int) ≤ nt.maxOffset)
    (hnorm : n.isNormalized) (hneg : n.negative_ = false) (hcap : n.toRat ≤ 2 ^ 63 - 1) :
    ∃ result, STAmount.ofNumber nt n mode = .ok result := by
  unfold STAmount.ofNumber
  rw [if_pos hnt]
  set neg : Bool := decide (n.signum < 0) with hneg_def
  set working : Number := if neg then n.operator_neg else n with hw_def
  have hnegf : neg = false := by
    rw [hneg_def]
    apply decide_eq_false
    unfold Number.signum
    rw [hneg]; simp only [Bool.false_eq_true, if_false]
    split <;> norm_num
  have hwn : working = n := by rw [hw_def, hnegf]; simp only [Bool.false_eq_true, if_false]
  rw [hwn]
  have hexp0 : n.exponent ≤ 0 := Number.exponent_fn_le_zero_of_cap n hnorm hneg hcap
  obtain ⟨r, hr⟩ := Number.to_rep_ok_of_nonneg_exp_nonpos n mode hneg hexp0
  rw [hr]
  simp only []
  rw [hnegf]
  have hrrng := Number.to_rep_nonneg_range n mode r hneg hr
  have hru64 : r.toUInt64.toNat ≤ maxRep.toNat := toUInt64_toNat_le_maxRep r hrrng.1 hrrng.2
  obtain ⟨result, hres⟩ := STAmount.canonicalize_integral_ok
    (STAmount.unchecked nt r.toUInt64 0 false) mode hnt rfl rfl hru64 hmaxval hmaxoff
  exact ⟨result, by rw [STAmount.checked]; exact hres⟩

/-- **Share-total / payout `ofNumber .int64` totality (both caller modes).** The
emptying run's two integral conversions -- the stored share total (`.to_nearest`)
and the priced payout (`.downward`) -- succeed for any normalized nonnegative
`Number` bounded by `2 ^ 63 - 1`. `NumericType.int64` carries `maxValue = maxRep`
and `maxOffset = 18`, so the general cap totality applies directly. -/
lemma STAmount.ofNumber_int64_ok (n : Number) (mode : rounding_mode)
    (hnorm : n.isNormalized) (hneg : n.negative_ = false) (hcap : n.toRat ≤ 2 ^ 63 - 1) :
    ∃ result, STAmount.ofNumber .int64 n mode = .ok result :=
  STAmount.ofNumber_integral_ok_of_cap .int64 n mode (by decide) (by decide) (by decide)
    hnorm hneg hcap

/-- The value of a canonical integral amount is bounded by its type's carried
maximum. -/
lemma STAmount.IntegralCanonical.abs_toRat_le (s : STAmount) (hc : s.IntegralCanonical) :
    |s.toRat| ≤ (s.mNumericType.maxValue.toNat : ℚ) := by
  rw [STAmount.abs_toRat, hc.offset_zero]
  have := hc.in_range
  simp only [zpow_zero, mul_one]
  exact_mod_cast this

/-- **`ofNumber` on an integral type rounds within one unit** of a sign-cleared
normalized `Number`. The integral packing routes the magnitude through `to_rep`,
which lands within one of the value; a non-negative source keeps the sign bit
clear so the stored value is exactly the `to_rep` integer. -/
lemma STAmount.ofNumber_integral_within_one (nt : NumericType) (n : Number)
    (mode : rounding_mode) (result : STAmount)
    (hnt : nt.isIntegral = true) (hn : n.isNormalized) (hneg : n.negative_ = false)
    (hok : STAmount.ofNumber nt n mode = .ok result) :
    |result.toRat - n.toRat| < 1 := by
  unfold STAmount.ofNumber at hok
  simp only [Number.signum_neg_decide, hneg, Bool.false_eq_true, if_false, if_pos hnt] at hok
  cases hr : n.to_rep mode with
  | error e => rw [hr] at hok; exact absurd hok (by simp)
  | ok intValue =>
    rw [hr] at hok
    simp only [] at hok
    obtain ⟨hnn, hle⟩ :=
      Number.to_rep_nonneg_range n mode intValue hneg hr
    have hval : intValue.toUInt64.toNat ≤ maxRep.toNat :=
      toUInt64_toNat_le_maxRep intValue hnn hle
    have hres : result.toRat = (intValue.toInt : ℚ) := by
      have hexact := STAmount.canonicalize_integral_toRat
        (STAmount.unchecked nt intValue.toUInt64 0 false) result mode
        (show (STAmount.unchecked nt intValue.toUInt64 0 false).integral = true from hnt) rfl
        hval hok
      rw [hexact, STAmount.toRat_of_offset_zero _ rfl]
      show ((intValue.toUInt64.toNat : ℤ) : ℚ) = (intValue.toInt : ℚ)
      rw [toUInt64_toNat_of_nonneg intValue hnn]
    rw [hres]
    exact to_rep_within_one n mode intValue hn hr

/-- The `int64` zero amount reduces to the canonical record `⟨.int64, 0, 0, false⟩`. -/
lemma STAmount.zero_int64_eq : STAmount.zero .int64 = ⟨.int64, 0, 0, false⟩ := by decide

/-- The `int64` zero amount has zero exact value. -/
lemma STAmount.zero_int64_toRat : (STAmount.zero .int64).toRat = 0 := by
  rw [STAmount.zero_int64_eq, STAmount.toRat_signed]; norm_num

/-- The `int64` zero amount carries the `int64` numeric type. -/
lemma STAmount.zero_int64_mNumericType : (STAmount.zero .int64).mNumericType = .int64 := by
  rw [STAmount.zero_int64_eq]

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

/-- `STAmount.ofNumber` on an integral type is value-exact for a normalized
integer-valued `Number` (`den = 1`). -/
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

/-- `STAmount.ofNumber` on an integral type is monotone for integer-valued
normalized inputs, in any rounding mode (the conversion is exact). -/
lemma STAmount.ofNumber_integral_toRat_mono (nt : NumericType)
    (n₁ n₂ : Number) (a₁ a₂ : STAmount) (mode₁ mode₂ : rounding_mode)
    (hnt : nt.isIntegral = true)
    (hn₁ : n₁.isNormalized) (hn₂ : n₂.isNormalized)
    (hden₁ : n₁.toRat.den = 1) (hden₂ : n₂.toRat.den = 1)
    (hok₁ : STAmount.ofNumber nt n₁ mode₁ = .ok a₁)
    (hok₂ : STAmount.ofNumber nt n₂ mode₂ = .ok a₂)
    (hle : n₁.toRat ≤ n₂.toRat) : a₁.toRat ≤ a₂.toRat := by
  rw [STAmount.ofNumber_integral_exact nt n₁ mode₁ a₁ hnt hn₁ hden₁ hok₁,
      STAmount.ofNumber_integral_exact nt n₂ mode₂ a₂ hnt hn₂ hden₂ hok₂]
  exact hle

/-- A successful `ofNumber` on any numeric type forces a nonzero source mantissa
from a nonzero result: integral via `to_rep`, fractional via the 16-digit snap. -/
lemma STAmount.ofNumber_source_ne_zero (nt : NumericType) (n : Number) (mode : rounding_mode)
    (result : STAmount)
    (hok : STAmount.ofNumber nt n mode = .ok result) (hres : result.mValue ≠ 0) :
    n.mantissa_ ≠ 0 := by
  by_cases hint : nt.isIntegral = true
  · exact STAmount.ofNumber_integral_source_ne_zero nt n mode result hint hok hres
  · have hnt_frac : nt = .fractional := by
      cases nt with
      | fractional => rfl
      | integral mv mo ms msh => simp [NumericType.isIntegral] at hint
    exact STAmount.ofNumber_iou_mantissa_ne_zero nt n mode result hnt_frac hok hres

/-- A fractional `ofNumber` on a normalized source lands canonical-or-zero. -/
lemma STAmount.ofNumber_frac_shape (nt : NumericType) (n : Number) (mode : rounding_mode)
    (result : STAmount) (hnt : nt.isIntegral = false) (hn : n.isNormalized)
    (hok : STAmount.ofNumber nt n mode = .ok result) :
    result.IOUCanonical ∨ result.mValue = 0 := by
  have hfr : nt = .fractional := by
    cases nt with
    | fractional => rfl
    | integral mv mo ms msh => simp [NumericType.isIntegral] at hnt
  subst hfr
  by_cases hm : n.mantissa_ = 0
  · refine Or.inr ?_
    by_contra h
    exact (STAmount.ofNumber_source_ne_zero .fractional n mode result hok h) hm
  · obtain ⟨hlo19, hhi19⟩ := hn.mantissaBounds_nat hm
    have hexp_lo : minExponent ≤ n.exponent_ := by
      rcases hn with h0 | ⟨_, _, _, hlo, _⟩
      · exact absurd (show n.mantissa_ = 0 by rw [h0]; rfl) hm
      · exact hlo
    exact STAmount.ofNumber_iou_canonical_or_zero n mode result hlo19 hhi19 hexp_lo hok

lemma STAmount.ofNumber_signtrue_nonpos (nt : NumericType) (n : Number) (mode : rounding_mode)
    (result : STAmount) (hnt : nt.isIntegral = false) (hn : n.isNormalized)
    (hneg : n.negative_ = true)
    (hok : STAmount.ofNumber nt n mode = .ok result) : result.toRat ≤ 0 := by
  have hfr : nt = .fractional := by
    cases nt with
    | fractional => rfl
    | integral mv mo ms msh => simp [NumericType.isIntegral] at hnt
  subst hfr
  by_cases hz : result.mValue = 0
  · rw [STAmount.toRat_signed, hz]; simp
  have hn_ne : n.mantissa_ ≠ 0 :=
    STAmount.ofNumber_source_ne_zero .fractional n mode result hok hz
  -- the packing runs on the ABS value with the sign bit set
  have hw : (if decide (n.signum < 0) = true then n.operator_neg else n) = n.operator_neg := by
    rw [Number.signum_neg_decide, hneg]; simp
  unfold STAmount.ofNumber at hok
  simp only [Number.signum_neg_decide, hneg] at hok
  rw [if_neg (by decide : ¬ (NumericType.fractional).isIntegral = true)] at hok
  simp only [if_true] at hok
  rw [show kMinValue = cMinValue from rfl, show kMaxValue = cMaxValue from rfl] at hok
  set w := n.operator_neg with hwdef
  have hwm : w.mantissa_ = n.mantissa_ := by
    rw [hwdef]; unfold Number.operator_neg; simp [hn_ne]
  have hwe : w.exponent_ = n.exponent_ := by
    rw [hwdef]; unfold Number.operator_neg; simp [hn_ne]
  have hwneg : w.negative_ = false := by
    rw [hwdef]; unfold Number.operator_neg; simp [hn_ne, hneg]
  obtain ⟨hlo19, hhi19⟩ := hn.mantissaBounds_nat hn_ne
  have hexp_lo : minExponent ≤ n.exponent_ := by
    rcases hn with h0 | ⟨_, _, _, hlo, _⟩
    · exact absurd (show n.mantissa_ = 0 by rw [h0]; rfl) hn_ne
    · exact hlo
  cases hnorm : w.normalizeToRange cMinValue cMaxValue mode with
  | error e => rw [hnorm] at hok; exact absurd hok (by simp)
  | ok me =>
    obtain ⟨mant, exp⟩ := me
    rw [hnorm] at hok
    simp only [] at hok
    have hexp_hi : w.exponent_ + 3 ≤ maxExponent :=
      normalizeToRange_iou_exp_hi w mode mant exp (by rw [hwm]; exact hlo19)
        (by rw [hwm]; exact hhi19) hnorm
    obtain ⟨⟨hmlo, hmhi⟩, -, hsgn⟩ :=
      normalizeToRange_iou_ok_facts w mode mant exp (by rw [hwm]; exact hlo19)
        (by rw [hwm]; exact hhi19) (by rw [hwe]; omega) hexp_hi hnorm
    have hmant_nn : 0 ≤ mant.toInt := hsgn.1 hwneg
    have hfit : mant.toUInt64.toNat < 2 ^ 63 := by
      have hna : mant.toInt.natAbs = mant.toUInt64.toNat := by
        have := toUInt64_toNat_of_nonneg mant hmant_nn; omega
      have hcm : cMaxValue.toNat = 10 ^ 16 - 1 := by decide
      omega
    exact STAmount.canonicalize_signtrue_nonpos
      (STAmount.unchecked .fractional mant.toUInt64 exp true) result mode rfl rfl hfit hok

/-- **A `to_nearest` fractional pack never overshoots a 16-digit-representable bound.** -/
lemma STAmount.ofNumber_frac_le_canonical (n : Number) (g result : STAmount)
    (hn : n.isNormalized) (hnneg : n.negative_ = false)
    (hg : g.IOUCanonical) (hgneg : g.mIsNegative = false)
    (hle : n.toRat ≤ g.toRat)
    (hok : STAmount.ofNumber .fractional n .to_nearest = .ok result) :
    result.toRat ≤ g.toRat := by
  have hgval : g.toRat = (g.mValue.toNat : ℚ) * (10:ℚ) ^ g.mOffset :=
    STAmount.toRat_of_nonneg g hgneg
  have hgnn : 0 ≤ g.toRat := by rw [hgval]; positivity
  by_cases hrz : result.mValue = 0
  · rw [STAmount.toRat_signed, hrz]; simpa using hgnn
  have hnm : n.mantissa_ ≠ 0 :=
    STAmount.ofNumber_source_ne_zero .fractional n .to_nearest result hok hrz
  obtain ⟨hlo19, hhi19⟩ := hn.mantissaBounds_nat hnm
  have hexp_lo : minExponent ≤ n.exponent_ := by
    rcases hn with h0 | ⟨_, _, _, hlo, _⟩
    · exact absurd (show n.mantissa_ = 0 by rw [h0]; rfl) hnm
    · exact hlo
  have hexp_hi : n.exponent_ + 4 ≤ maxExponent :=
    STAmount.ofNumber_iou_success_exp_range n .to_nearest result hlo19 hhi19 hexp_lo hok hrz
  obtain ⟨mant, exp, hnorm, hval, hexpq, hcast, hmlo, hmhi, helo, hehi⟩ :=
    STAmount.ofNumber_iou_snap_pos .fractional n .to_nearest result rfl hnneg
      hlo19 hhi19 hexp_lo hexp_hi hok hrz
  obtain ⟨k, hk, hk_lt, hkval⟩ :=
    normalizeToRange_16_bracket n .to_nearest mant exp hlo19 hhi19 (by omega) (by omega) hnorm
  rw [hnneg] at hkval
  simp only [Bool.false_eq_true, if_false, one_mul] at hkval
  -- value forms
  have hnval : n.toRat = (n.mantissa_.toNat : ℚ) * (10:ℚ) ^ n.exponent_ :=
    Number.toRat_of_nonneg n hnneg
  set M : ℕ := n.mantissa_.toNat with hM
  set mg : ℕ := g.mValue.toNat with hmg
  have hmg_lo : 10 ^ 15 ≤ mg := hg.mant_lo
  have hmg_hi : mg < 10 ^ 16 := hg.mant_hi
  have hrval : result.toRat = (k : ℚ) * (10:ℚ) ^ (n.exponent_ + 3) := by rw [hval, hkval]
  rw [hrval, hgval]
  have hpe : (0:ℚ) < (10:ℚ) ^ (n.exponent_ + 3) := zpow_pos (by norm_num) _
  have hpg : (0:ℚ) < (10:ℚ) ^ g.mOffset := zpow_pos (by norm_num) _
  have hpn : (0:ℚ) < (10:ℚ) ^ n.exponent_ := zpow_pos (by norm_num) _
  have hle' : (M : ℚ) * (10:ℚ) ^ n.exponent_ ≤ (mg : ℚ) * (10:ℚ) ^ g.mOffset := by
    rw [← hnval, ← hgval]; exact hle
  have hsplit : (10:ℚ) ^ (n.exponent_ + 3) = (10:ℚ) ^ n.exponent_ * 1000 := by
    rw [zpow_add₀ (by norm_num : (10:ℚ) ≠ 0)]; norm_num
  rcases lt_trichotomy (n.exponent_ + 3) g.mOffset with he | he | he
  · -- the bound sits a whole decade band above: separation on the mantissa ranges
    have hkle : (k : ℚ) ≤ 10 ^ 16 := by
      have : k ≤ 10 ^ 16 := by rcases hk with h | h <;> omega
      exact_mod_cast this
    have hstep : (10:ℚ) ^ (16:ℤ) * (10:ℚ) ^ (n.exponent_ + 3) ≤ (10:ℚ) ^ (15:ℤ) * 10 ^ g.mOffset := by
      rw [← zpow_add₀ (by norm_num : (10:ℚ) ≠ 0), ← zpow_add₀ (by norm_num : (10:ℚ) ≠ 0)]
      exact zpow_le_zpow_right₀ (by norm_num) (by omega)
    have h16 : ((10:ℚ) ^ (16:ℤ)) = (10:ℚ) ^ 16 := by norm_num
    have h15 : ((10:ℚ) ^ (15:ℤ)) = (10:ℚ) ^ 15 := by norm_num
    have hmgq : ((10:ℚ) ^ 15) ≤ (mg : ℚ) := by exact_mod_cast hmg_lo
    calc (k : ℚ) * (10:ℚ) ^ (n.exponent_ + 3)
        ≤ (10:ℚ) ^ 16 * (10:ℚ) ^ (n.exponent_ + 3) :=
          mul_le_mul_of_nonneg_right hkle (le_of_lt hpe)
      _ ≤ (10:ℚ) ^ 15 * (10:ℚ) ^ g.mOffset := by rw [← h16, ← h15]; exact hstep
      _ ≤ (mg : ℚ) * (10:ℚ) ^ g.mOffset := mul_le_mul_of_nonneg_right hmgq (le_of_lt hpg)
  · -- same band: compare mantissas, with the carry case excluded by the half-ULP bound
    rw [← he]
    rw [← he] at hle'
    have hMle : (M : ℚ) ≤ 1000 * (mg : ℚ) := by
      rw [hsplit] at hle'
      nlinarith [hle', hpn]
    have hMleN : M ≤ 1000 * mg := by exact_mod_cast hMle
    have hkmg : k ≤ mg := by
      rcases hk with h | h
      · omega
      · by_contra hcon
        push_neg at hcon
        have hMd : M / 1000 = mg := by omega
        have hmod : M % 1000 = 0 := by omega
        -- the source is exactly on the 16-digit grid, so `to_nearest` cannot carry
        have hhalf := normalizeToRange_16_within_half_ulp n mant exp hlo19 hhi19 (by omega)
          (by omega) hnorm
        rw [hkval, hnval] at hhalf
        have hMexact : (M : ℚ) * (10:ℚ) ^ n.exponent_
            = ((M / 1000 : ℕ) : ℚ) * (10:ℚ) ^ (n.exponent_ + 3) := by
          rw [hsplit]
          have : (M : ℚ) = ((M / 1000 : ℕ) : ℚ) * 1000 := by
            have : M = (M / 1000) * 1000 := by omega
            exact_mod_cast congrArg (Nat.cast : ℕ → ℚ) this
          rw [this]; ring
        rw [hMexact, ← sub_mul, abs_mul, abs_of_pos hpe] at hhalf
        have : |(k : ℚ) - ((M / 1000 : ℕ) : ℚ)| ≤ 1/2 := by
          nlinarith [hhalf, hpe, abs_nonneg ((k : ℚ) - ((M / 1000 : ℕ) : ℚ))]
        rw [h] at this
        push_cast at this
        rw [show ((M / 1000 : ℕ) : ℚ) + 1 - ((M / 1000 : ℕ) : ℚ) = 1 from by ring] at this
        norm_num at this
    have hkmgq : (k : ℚ) ≤ (mg : ℚ) := by exact_mod_cast hkmg
    exact mul_le_mul_of_nonneg_right hkmgq (le_of_lt hpe)
  · -- the bound sits a band BELOW the source: impossible, since `n ≤ g`
    exfalso
    have hmgq : (mg : ℚ) < (10:ℚ) ^ 16 := by exact_mod_cast hmg_hi
    have hMq : ((10:ℚ) ^ 18) ≤ (M : ℚ) := by exact_mod_cast hlo19
    have hstep : (10:ℚ) ^ (16:ℤ) * (10:ℚ) ^ g.mOffset ≤ (10:ℚ) ^ (18:ℤ) * 10 ^ n.exponent_ := by
      rw [← zpow_add₀ (by norm_num : (10:ℚ) ≠ 0), ← zpow_add₀ (by norm_num : (10:ℚ) ≠ 0)]
      exact zpow_le_zpow_right₀ (by norm_num) (by omega)
    have h16 : ((10:ℚ) ^ (16:ℤ)) = (10:ℚ) ^ 16 := by norm_num
    have h18 : ((10:ℚ) ^ (18:ℤ)) = (10:ℚ) ^ 18 := by norm_num
    have hglt : (mg : ℚ) * (10:ℚ) ^ g.mOffset < (10:ℚ) ^ 16 * (10:ℚ) ^ g.mOffset :=
      mul_lt_mul_of_pos_right hmgq hpg
    have : (10:ℚ) ^ 16 * (10:ℚ) ^ g.mOffset ≤ (M : ℚ) * (10:ℚ) ^ n.exponent_ := by
      rw [← h16] at *
      calc (10:ℚ) ^ (16:ℤ) * (10:ℚ) ^ g.mOffset
          ≤ (10:ℚ) ^ (18:ℤ) * (10:ℚ) ^ n.exponent_ := hstep
        _ ≤ (M : ℚ) * (10:ℚ) ^ n.exponent_ := by
            rw [h18]; exact mul_le_mul_of_nonneg_right hMq (le_of_lt hpn)
    linarith

/-- The integral `canonicalize` on an offset-`0` amount within `maxRep`
reproduces the type, keeps offset `0`, stays within `maxRep`, and preserves
the value. Structural strengthening of `canonicalize_integral_toRat`. -/
lemma STAmount.canonicalize_integral_facts (s result : STAmount) (mode : rounding_mode)
    (hint : s.integral = true) (hoff : s.mOffset = 0)
    (hval_le : s.mValue.toNat ≤ maxRep.toNat)
    (hok : s.canonicalize mode = .ok result) :
    result.mNumericType = s.mNumericType ∧ result.mOffset = 0 ∧
    result.mValue.toNat ≤ maxRep.toNat ∧ result.toRat = s.toRat := by
  have htoRat := STAmount.canonicalize_integral_toRat s result mode hint hoff hval_le hok
  rw [STAmount.canonicalize, if_pos hint] at hok
  by_cases hz : s.mValue == 0
  · rw [if_pos (by rw [hz]; rfl)] at hok
    have hres := Except.ok.inj hok
    subst hres
    exact ⟨rfl, rfl, Nat.zero_le _, htoRat⟩
  · have hz' : (s.mValue == 0) = false := by simpa using hz
    rw [if_neg (by rw [hz', hoff]; decide)] at hok
    by_cases hmoff : s.mOffset > s.mNumericType.maxOffset
    · rw [if_pos hmoff] at hok; exact absurd hok (by simp)
    rw [if_neg hmoff] at hok
    simp only [hoff, IntAmount.ofNumber] at hok
    cases hr : (Number.unchecked s.mIsNegative s.mValue 0).to_rep mode with
    | error e => rw [hr] at hok; exact absurd hok (by simp)
    | ok r =>
      rw [hr] at hok
      simp only [] at hok
      have hkey := to_rep_exact_of_exponent_zero s.mIsNegative s.mValue mode r hval_le hr
      have hnatAbs : r.toInt.natAbs = s.mValue.toNat := by
        have h1 : (r.toInt : ℚ) = (if s.mIsNegative then (-1 : ℚ) else 1) * s.mValue.toNat := hkey
        have h2 : r.toInt.natAbs = ((if s.mIsNegative then (-1 : ℤ) else 1) * s.mValue.toNat).natAbs := by
          congr 1
          exact_mod_cast (by rcases hn : s.mIsNegative <;>
            simp only [hn, Bool.false_eq_true, ↓reduceIte, Int.reduceNegSucc, neg_mul, one_mul] at h1 ⊢ <;>
            exact_mod_cast h1)
        rw [h2]
        rcases s.mIsNegative <;> simp
      by_cases hrng : r.toInt.natAbs.toUInt64 > s.mNumericType.maxValue
      · rw [if_pos hrng] at hok; exact absurd hok (by simp)
      rw [if_neg hrng] at hok
      have hres := Except.ok.inj hok
      subst hres
      refine ⟨rfl, rfl, ?_, htoRat⟩
      show (r.toInt.natAbs.toUInt64).toNat ≤ maxRep.toNat
      have hlt : r.toInt.natAbs < 2 ^ 64 := by
        rw [hnatAbs]
        have := UInt64.toNat_lt_size s.mValue
        rw [uint64_size_val] at this
        omega
      rw [UInt64.toNat_ofNat_of_lt' (by rw [uint64_size_val]; exact hlt), hnatAbs]
      exact hval_le

/-- **`.downward` `ofNumber` floors within one ULP.** For a normalized sign-cleared
`Number` `n` whose conversion into `nt` lands on a nonzero record, the result never
exceeds `n`, sits within `10 ^ result.exponent` below it, and is non-negative. Both
the integral (`to_rep` floor, exponent `0`) and fractional (16-digit downward snap)
paths obey this. -/
lemma STAmount.ofNumber_downward_floor_bounds (nt : NumericType) (n : Number) (result : STAmount)
    (hn : n.isNormalized) (hneg : n.negative_ = false)
    (hok : STAmount.ofNumber nt n .downward = .ok result) (hres : result.mValue ≠ 0) :
    result.toRat ≤ n.toRat ∧
    n.toRat - result.toRat ≤ (10 : ℚ) ^ result.exponent ∧
    0 ≤ result.toRat := by
  by_cases hint : nt.isIntegral = true
  · -- integral: `to_rep .downward` is the floor, result exponent is `0`
    unfold STAmount.ofNumber at hok
    simp only [Number.signum_neg_decide, hneg, Bool.false_eq_true, if_false, if_pos hint] at hok
    cases hr : n.to_rep .downward with
    | error e => rw [hr] at hok; exact absurd hok (by simp)
    | ok intValue =>
      rw [hr] at hok
      simp only [] at hok
      obtain ⟨hnn, hle⟩ := Number.to_rep_nonneg_range n .downward intValue hneg hr
      have hval : intValue.toUInt64.toNat ≤ maxRep.toNat :=
        toUInt64_toNat_le_maxRep intValue hnn hle
      have hres_val : result.toRat = (intValue.toInt : ℚ) := by
        have hexact := STAmount.canonicalize_integral_toRat
          (STAmount.unchecked nt intValue.toUInt64 0 false) result .downward
          (show (STAmount.unchecked nt intValue.toUInt64 0 false).integral = true from hint) rfl
          hval hok
        rw [hexact, STAmount.toRat_of_offset_zero _ rfl]
        show ((intValue.toUInt64.toNat : ℤ) : ℚ) = (intValue.toInt : ℚ)
        rw [toUInt64_toNat_of_nonneg intValue hnn]
      have hres_exp : result.exponent = 0 := by
        obtain ⟨_, hoff, _⟩ := STAmount.canonicalize_integral_facts
          (STAmount.unchecked nt intValue.toUInt64 0 false) result .downward
          (show (STAmount.unchecked nt intValue.toUInt64 0 false).integral = true from hint)
          rfl hval hok
        exact hoff
      obtain ⟨hfl_le, hfl_lt⟩ := Number.to_rep_downward_floor n intValue hn hneg hr
      refine ⟨by rw [hres_val]; exact hfl_le, ?_, by rw [hres_val]; exact_mod_cast hnn⟩
      rw [hres_val, hres_exp, zpow_zero]
      linarith [hfl_lt]
  · -- fractional: the 16-digit downward snap is within one 16-digit ULP below
    have hnt_frac : nt = .fractional := by
      cases nt with
      | fractional => rfl
      | integral mv mo ms msh => simp [NumericType.isIntegral] at hint
    have hn_ne : n.mantissa_ ≠ 0 :=
      STAmount.ofNumber_iou_mantissa_ne_zero nt n .downward result hnt_frac hok hres
    obtain ⟨hlo19, hhi19⟩ := hn.mantissaBounds_nat hn_ne
    have hexp_lo : minExponent ≤ n.exponent_ := by
      rcases hn with h0 | ⟨_, _, _, hlo, _⟩
      · exact absurd (show n.mantissa_ = 0 by rw [h0]; rfl) hn_ne
      · exact hlo
    have hok' : STAmount.ofNumber .fractional n .downward = .ok result := by
      rw [← hnt_frac]; exact hok
    have hexp_hi : n.exponent_ + 4 ≤ maxExponent :=
      STAmount.ofNumber_iou_success_exp_range n .downward result hlo19 hhi19 hexp_lo hok' hres
    have hrw := STAmount.ofNumber_iou_rounds_within nt n .downward result hnt_frac hneg
      hlo19 hhi19 hexp_lo hexp_hi hok hres
    obtain ⟨hle, -⟩ := hrw
    have hle' : result.toRat ≤ n.toRat := hle
    obtain ⟨hulp, hexp_ge⟩ := STAmount.ofNumber_iou_within_ulp nt n .downward result hnt_frac
      hlo19 hhi19 hexp_lo hexp_hi hok hres
    have hnonneg : 0 ≤ result.toRat := by
      obtain ⟨mant, exp, -, hval, -, hcast, -, -, -, -⟩ :=
        STAmount.ofNumber_iou_snap_pos nt n .downward result hnt_frac hneg
          hlo19 hhi19 hexp_lo hexp_hi hok hres
      rw [hval, hcast]; positivity
    refine ⟨hle', ?_, hnonneg⟩
    have hgap : n.toRat - result.toRat ≤ (10 : ℚ) ^ (n.exponent_ + 3) := by
      have h1 : n.toRat - result.toRat = |result.toRat - n.toRat| := by
        rw [abs_of_nonpos (by linarith [hle'] : result.toRat - n.toRat ≤ 0)]; ring
      rw [h1]; exact hulp
    calc n.toRat - result.toRat ≤ (10 : ℚ) ^ (n.exponent_ + 3) := hgap
      _ ≤ (10 : ℚ) ^ result.exponent := zpow_le_zpow_right₀ (by norm_num) hexp_ge

/-- `STAmount.canonicalize` on an integral offset-`0` record: the result is a
canonical integral record of the same numeric type. -/
lemma STAmount.canonicalize_integral_canonical (s result : STAmount) (mode : rounding_mode)
    (hint : s.integral = true)
    (hok : s.canonicalize mode = .ok result) :
    result.IntegralCanonical ∧ result.mNumericType = s.mNumericType := by
  rw [STAmount.canonicalize, if_pos hint] at hok
  by_cases hz : (s.mValue == 0 || decide (s.mOffset ≤ -20)) = true
  · rw [if_pos hz] at hok
    rw [← Except.ok.inj hok]
    exact ⟨⟨hint, rfl, by simp⟩, rfl⟩
  · rw [if_neg hz] at hok
    by_cases hmoff : s.mOffset > s.mNumericType.maxOffset
    · rw [if_pos hmoff] at hok; exact absurd hok (by simp)
    rw [if_neg hmoff] at hok
    simp only [IntAmount.ofNumber] at hok
    cases hr : (Number.unchecked s.mIsNegative s.mValue s.mOffset).to_rep mode with
    | error e => rw [hr] at hok; exact absurd hok (by simp)
    | ok r =>
      rw [hr] at hok
      simp only [] at hok
      by_cases hrng : r.toInt.natAbs.toUInt64 > s.mNumericType.maxValue
      · rw [if_pos hrng] at hok; exact absurd hok (by simp)
      rw [if_neg hrng] at hok
      rw [← Except.ok.inj hok]
      refine ⟨⟨hint, rfl, ?_⟩, rfl⟩
      show r.toInt.natAbs.toUInt64.toNat ≤ s.mNumericType.maxValue.toNat
      by_contra hcon
      exact hrng (UInt64.lt_iff_toNat_lt.mpr (by omega))

/-- `STAmount.ofNumber` on an integral type: the result is a canonical integral
record of that type. -/
lemma STAmount.ofNumber_integral_canonical (nt : NumericType) (n : Number)
    (mode : rounding_mode) (a : STAmount)
    (hnt : nt.isIntegral = true)
    (hok : STAmount.ofNumber nt n mode = .ok a) :
    a.IntegralCanonical ∧ a.mNumericType = nt := by
  unfold STAmount.ofNumber at hok
  rw [if_pos hnt] at hok
  cases hrep : (if decide (n.signum < 0) = true then n.operator_neg else n).to_rep mode with
  | error e => rw [hrep] at hok; exact absurd hok (by simp)
  | ok intValue =>
    rw [hrep] at hok
    simp only [] at hok
    rw [STAmount.checked] at hok
    exact STAmount.canonicalize_integral_canonical _ a mode
      (show (STAmount.unchecked nt intValue.toUInt64 0 (decide (n.signum < 0))).integral = true
        from hnt) hok

/-- **Integral `STAmount.ofNumber` output shape.** A successful conversion into
an integral numeric type yields an offset-`0` amount of that type whose stored
magnitude fits `maxRep`. -/
lemma STAmount.ofNumber_integral_facts (nt : NumericType) (n : Number)
    (mode : rounding_mode) (result : STAmount)
    (hnt : nt.isIntegral = true)
    (hok : STAmount.ofNumber nt n mode = .ok result) :
    result.mNumericType = nt ∧ result.mOffset = 0 ∧
    result.mValue.toNat ≤ maxRep.toNat := by
  unfold STAmount.ofNumber at hok
  rw [if_pos hnt] at hok
  set neg : Bool := decide (n.signum < 0) with hneg_def
  set working : Number := if neg then n.operator_neg else n with hw_def
  have hsig : n.signum < 0 ↔ n.negative_ = true := by
    unfold Number.signum
    by_cases hnn : n.negative_ = true
    · rw [if_pos hnn]; simp [hnn]
    · rw [if_neg hnn]
      constructor
      · intro h; split at h <;> norm_num at h
      · intro h; exact absurd h hnn
  have hw_neg : working.negative_ = false := by
    rw [hw_def]
    by_cases hneg : neg = true
    · rw [if_pos hneg]
      have hnegn : n.negative_ = true :=
        hsig.mp (of_decide_eq_true (by rw [hneg_def] at hneg; exact hneg))
      unfold Number.operator_neg
      by_cases hm : (n.mantissa_ == 0) = true
      · rw [if_pos hm]; rfl
      · rw [if_neg hm]; simp [hnegn]
    · rw [if_neg hneg]
      by_cases hnegn : n.negative_ = true
      · exfalso; apply hneg; rw [hneg_def]; exact decide_eq_true (hsig.mpr hnegn)
      · simpa using hnegn
  cases hr : working.to_rep mode with
  | error e => rw [hr] at hok; exact absurd hok (by simp)
  | ok intValue =>
    rw [hr] at hok
    simp only [] at hok
    obtain ⟨hnn, hle⟩ := Number.to_rep_nonneg_range working mode intValue hw_neg hr
    have hval : intValue.toUInt64.toNat ≤ maxRep.toNat :=
      toUInt64_toNat_le_maxRep intValue hnn hle
    have hint' : (STAmount.unchecked nt intValue.toUInt64 0 neg).integral = true := hnt
    obtain ⟨h1, h2, h3, _⟩ := STAmount.canonicalize_integral_facts
      (STAmount.unchecked nt intValue.toUInt64 0 neg) result mode hint' rfl hval hok
    exact ⟨h1, h2, h3⟩

/-- **`toNumber` is value-exact, normalized, and integer-valued on an offset-`0`
integral amount within `maxRep`.** Variant of `toNumber_integral_exact` keyed on
the stored magnitude directly, so it also covers custom integral numeric types
whose carried bound exceeds `maxRep`. -/
lemma STAmount.toNumber_integral_exact' (s : STAmount) (mode : rounding_mode)
    (hint : s.mNumericType.isIntegral = true) (hoff : s.mOffset = 0)
    (hval : s.mValue.toNat ≤ maxRep.toNat) :
    ∃ sn : Number, s.toNumber mode = .ok sn ∧ sn.toRat = s.toRat ∧ sn.isNormalized ∧
      s.toRat.den = 1 := by
  have hint' : s.integral = true := hint
  have hbnd : s.mValue.toNat ≤ 9223372036854775807 := by rw [maxRep_val] at hval; exact hval
  have hmin : Int64.minValue.toInt = (-9223372036854775808 : ℤ) := by decide
  have hmax' : Int64.maxValue.toInt = (9223372036854775807 : ℤ) := by decide
  have hsd_lo : Int64.minValue.toInt ≤ s.signedDrops := by
    unfold STAmount.signedDrops; rw [hmin]; split <;> omega
  have hsd_hi : s.signedDrops ≤ Int64.maxValue.toInt := by
    unfold STAmount.signedDrops; rw [hmax']; split <;> omega
  have hsd_toInt : s.signedDrops.toInt64.toInt = s.signedDrops :=
    XRPL.Model.Protocol.AmountArith.toInt_toInt64_self hsd_lo hsd_hi
  have h_ne_min : s.signedDrops.toInt64 ≠ Int64.minValue := by
    intro h
    have heq : s.signedDrops.toInt64.toInt = Int64.minValue.toInt := by rw [h]
    rw [hsd_toInt, hmin] at heq
    revert heq
    unfold STAmount.signedDrops
    split <;> omega
  have hroute : s.toNumber mode = IntAmount.toNumber ⟨s.signedDrops.toInt64⟩ mode := by
    unfold STAmount.toNumber STAmount.intAmount
    rw [if_pos hint', if_pos hint']
  obtain ⟨xn, hokn, hvaln, hnorm⟩ :=
    IntAmount.toNumber_exact ⟨s.signedDrops.toInt64⟩ mode h_ne_min
  have hsd_val : s.toRat = (s.signedDrops : ℚ) := by
    rw [STAmount.toRat_of_offset_zero s hoff]
  refine ⟨xn, by rw [hroute]; exact hokn, ?_, hnorm, ?_⟩
  · rw [hvaln]
    show (s.signedDrops.toInt64.toInt : ℚ) = s.toRat
    rw [hsd_toInt, hsd_val]
  · rw [hsd_val]
    exact Rat.den_intCast _

/-- The `int64` zero amount is `IntegralCanonical`. -/
lemma zero_int64_IntegralCanonical : (STAmount.zero .int64).IntegralCanonical := by
  rw [STAmount.zero_int64_eq]; exact ⟨by decide, by decide, by decide⟩

end XRPL.Model.Protocol
