import XRPL.Properties.Protocol.STAmount.Compare.Compare
import XRPL.Properties.Protocol.STAmount.Div.Common.IOU
import XRPL.Properties.Protocol.STAmount.Mul.Common.DirectedTight
import XRPL.Properties.Protocol.STAmount.RoundToScale.Common.Sum
import XRPL.Properties.Vault.Common.CmpFaithfulCanonical
import XRPL.Properties.Vault.Proofs.Support.NormalizeFacts
import XRPL.Properties.Protocol.STAmount.Common.FracCanonZero
import XRPL.Properties.Protocol.STAmount.Common.OfNumberBoundary
import XRPL.Properties.Protocol.STAmount.Common.OfNumberFacts
import XRPL.Properties.Protocol.Common.Reduction

/-! # `STAmount` facts

Facts about `STAmount`: the fractional (IOU) `ofNumber` and `canonicalize`, grids, zero records. -/

namespace XRPL.Model.Protocol

/-- `operator_neg` only touches the sign bit. -/
lemma STAmount.operator_neg_fields (s : STAmount) :
    s.operator_neg.mNumericType = s.mNumericType ∧
    s.operator_neg.mOffset = s.mOffset ∧
    s.operator_neg.mValue = s.mValue := by
  unfold STAmount.operator_neg
  split <;> exact ⟨rfl, rfl, rfl⟩

/-- The canonical zero amount stores mantissa `0`. -/
lemma STAmount.zero_mValue (nt : NumericType) : (STAmount.zero nt).mValue = 0 := by
  cases nt with
  | fractional => rfl
  | integral mv mo ms msh => rfl

/-- The canonical zero amount is sign-cleared. -/
lemma STAmount.zero_mIsNegative (nt : NumericType) :
    (STAmount.zero nt).mIsNegative = false := by
  cases nt with
  | fractional => rfl
  | integral mv mo ms msh => rfl

/-- A positive amount is stored with a clear sign bit. -/
lemma STAmount.mIsNegative_false_of_pos (a : STAmount) (h : 0 < a.toRat) :
    a.mIsNegative = false := by
  rcases hb : a.mIsNegative with _ | _
  · rfl
  · exfalso
    have := STAmount.toRat_of_neg a hb
    have hnn : (0 : ℚ) ≤ (a.mValue.toNat : ℚ) * 10 ^ a.mOffset := by positivity
    rw [this] at h
    linarith

/-- The canonical zero amount keeps its numeric type. -/
lemma STAmount.zero_mNumericType (nt : NumericType) :
    (STAmount.zero nt).mNumericType = nt := by
  cases nt with
  | fractional => rfl
  | integral mv mo ms msh => rfl

/-- The model's `tecPRECISION_LOSS` guard forces a nonzero stored magnitude on a
fractional amount: a zero amount is `≤ 0`, so the guard would have fired. -/
lemma STAmount.fnp_false_pos (s : STAmount) (hint : s.integral = false)
    (hfnp : s.isFractionalNonPositive = .ok false) : s.mValue ≠ 0 ∧ s.mIsNegative = false := by
  unfold STAmount.isFractionalNonPositive at hfnp
  rw [if_neg (by rw [hint]; exact Bool.false_ne_true)] at hfnp
  unfold STAmount.operator_le STAmount.operator_lt at hfnp
  simp only [STAmount.areComparable, STAmount.zero_mValue, STAmount.zero_mIsNegative,
    STAmount.zero_mNumericType, STAmount.numericType] at hfnp
  constructor
  · intro hz
    simp only [hz] at hfnp
    by_cases hneg : s.mIsNegative = true <;> simp [hneg] at hfnp
  · by_cases hneg : s.mIsNegative = true
    · simp [hneg] at hfnp
    · simpa using hneg

/-- The `tecPRECISION_LOSS` guard passing on a fractional amount means it is
strictly positive. -/
lemma STAmount.nonneg_of_fnp (s : STAmount) (hint : s.integral = false)
    (hfnp : s.isFractionalNonPositive = .ok false) : 0 ≤ s.toRat := by
  rw [STAmount.toRat_of_nonneg s (STAmount.fnp_false_pos s hint hfnp).2]
  positivity

/-- `toNumber` on a zero amount is the canonical zero `Number`, on either numeric
type — both paths short-circuit on the mantissa, so no canonical shape is needed. -/
lemma STAmount.toNumber_zero_eq (s : STAmount) (mode : rounding_mode) (n : Number)
    (hz : s.mValue = 0) (hok : s.toNumber mode = .ok n) : n = Number.zero := by
  by_cases hint : s.integral = true
  · unfold STAmount.toNumber at hok
    rw [if_pos hint] at hok
    unfold STAmount.intAmount at hok
    rw [if_pos hint] at hok
    have hsd : s.signedDrops = 0 := by unfold STAmount.signedDrops; simp [hz]
    simp only [hsd, IntAmount.toNumber, Number.from_rep,
      show ((0 : Int).toInt64).toInt.natAbs.toUInt64 = 0 from by decide,
      Number.normalized_zero_mantissa] at hok
    exact (Except.ok.inj hok).symm
  · have hfr : s.integral = false := by simpa using hint
    exact (Except.ok.inj
      ((STAmount.toNumber_zero_fractional s mode hfr hz).symm.trans hok)).symm

/-- `toNumber` is value-exact and normalized on a zero amount. -/
lemma STAmount.toNumber_zero_facts (s : STAmount) (mode : rounding_mode) (n : Number)
    (hz : s.mValue = 0) (hok : s.toNumber mode = .ok n) :
    n.toRat = s.toRat ∧ n.isNormalized := by
  have hsv : s.toRat = 0 := by rw [STAmount.toRat_signed, hz]; simp
  rw [STAmount.toNumber_zero_eq s mode n hz hok, Number.toRat_zero, hsv]
  exact ⟨rfl, Or.inl rfl⟩

lemma STAmount.canonicalize_signtrue_nonpos (s result : STAmount) (mode : rounding_mode)
    (hfr : s.mNumericType = .fractional) (hneg : s.mIsNegative = true)
    (hfit : s.mValue.toNat < 2 ^ 63)
    (hok : s.canonicalize mode = .ok result) :
    result.toRat ≤ 0 := by
  have hint : ¬ s.integral = true := by unfold STAmount.integral; rw [hfr]; decide
  unfold STAmount.canonicalize at hok
  rw [if_neg hint] at hok
  have hiou : s.iou mode = IOUAmount.ofMantissaExp s.signedDrops.toInt64 s.mOffset mode := by
    unfold STAmount.iou; rw [if_neg hint]
  rw [hiou] at hok
  have hsd_np : s.signedDrops.toInt64.toInt ≤ 0 := by
    rw [STAmount.signedDrops_toInt64_toInt_of_lt s hfit]
    unfold STAmount.signedDrops; rw [hneg]; simp
  cases hone : IOUAmount.ofMantissaExp s.signedDrops.toInt64 s.mOffset mode with
  | error e => rw [hone] at hok; exact absurd hok (by simp)
  | ok i =>
    rw [hone] at hok
    simp only [] at hok
    have hi_np : i.mantissa_.toInt ≤ 0 :=
      IOUAmount.normalize_mantissa_nonpos s.signedDrops.toInt64 s.mOffset mode i hsd_np hone
    have heq := Except.ok.inj hok
    by_cases hz : i.mantissa_ = 0
    · have hmv : result.mValue = 0 := by
        rw [← heq]
        show (if i.signum < 0 then -i.mantissa_ else i.mantissa_).toUInt64 = 0
        rw [hz]
        by_cases hs : i.signum < 0
        · rw [if_pos hs]; decide
        · rw [if_neg hs]; decide
      rw [STAmount.toRat_signed, hmv]; simp
    · have hlt : i.mantissa_.toInt < 0 := by
        rcases lt_or_eq_of_le hi_np with h | h
        · exact h
        · exact absurd (Int64.toInt_inj.mp (by rw [h]; decide)) hz
      have hneg_true : decide (i.signum < 0) = true := by
        rw [decide_eq_true_iff, IOUAmount.signum_neg_iff, Int64.lt_iff_toInt_lt]
        have h0 : (0 : Int64).toInt = 0 := by decide
        omega
      have hcneg : result.mIsNegative = true := by rw [← heq]; exact hneg_true
      exact STAmount.toRat_nonpos_of result hcneg

/-- A fractional `ofNumber` output is the `-100` zero sentinel, or else its exponent
sits in the IOU window. Stated as implications on `result.mValue` so callers can
split on the pack being zero. -/
lemma STAmount.ofNumber_frac_exp_range (nt : NumericType) (n : Number) (mode : rounding_mode)
    (result : STAmount) (hnt : nt.isIntegral = false)
    (hok : STAmount.ofNumber nt n mode = .ok result) :
    (result.mValue = 0 → result.exponent = -100) ∧
      (result.mValue ≠ 0 → ((-96 : ℤ) ≤ result.exponent ∧ result.exponent ≤ 80)) := by
  have hfr : nt = .fractional := by
    cases nt with
    | fractional => rfl
    | integral mv mo ms msh => simp [NumericType.isIntegral] at hnt
  subst hfr
  unfold STAmount.ofNumber at hok
  rw [if_neg (by decide : ¬ (NumericType.fractional).isIntegral = true)] at hok
  cases hnr : (if decide (n.signum < 0) = true then n.operator_neg else n).normalizeToRange
      kMinValue kMaxValue mode with
  | error e => rw [hnr] at hok; exact absurd hok (by simp)
  | ok me =>
    obtain ⟨mant, exp⟩ := me
    rw [hnr] at hok
    simp only [] at hok
    unfold STAmount.checked STAmount.canonicalize at hok
    rw [if_neg (show ¬ (STAmount.unchecked .fractional mant.toUInt64 exp
      (decide (n.signum < 0))).integral = true by
        show ¬ NumericType.fractional.isIntegral = true; decide)] at hok
    cases hi : (STAmount.unchecked .fractional mant.toUInt64 exp
        (decide (n.signum < 0))).iou mode with
    | error e => rw [hi] at hok; exact absurd hok (by simp)
    | ok i =>
      rw [hi] at hok
      simp only [] at hok
      have hiou : (STAmount.unchecked .fractional mant.toUInt64 exp
          (decide (n.signum < 0))).iou mode
          = IOUAmount.ofMantissaExp (STAmount.unchecked .fractional mant.toUInt64 exp
              (decide (n.signum < 0))).signedDrops.toInt64 exp mode := by
        unfold STAmount.iou
        rw [if_neg (show ¬ (STAmount.unchecked .fractional mant.toUInt64 exp
          (decide (n.signum < 0))).integral = true by
            show ¬ NumericType.fractional.isIntegral = true; decide)]
        rfl
      rw [hiou] at hi
      have hexp : result.exponent = i.exponent_ := by rw [← Except.ok.inj hok]; rfl
      have hmv : result.mValue
          = (if i.signum < 0 then -i.mantissa_ else i.mantissa_).toUInt64 := by
        rw [← Except.ok.inj hok]
      have hiff : result.mValue = 0 ↔ i.mantissa_ = 0 := by
        rw [hmv, Int64.toUInt64_eq_zero_iff]
        by_cases hs : i.signum < 0
        · rw [if_pos hs]; exact Int64.neg_eq_zero_iff i.mantissa_
        · rw [if_neg hs]
      refine ⟨fun h0 => ?_, fun hne => ?_⟩
      · rw [hexp]; exact IOUAmount.normalize_zero_exp _ mode i hi (hiff.mp h0)
      · rcases IOUAmount.normalize_exp_range _ mode i hi with ⟨hm0, -⟩ | h
        · exact absurd (hiff.mpr hm0) hne
        · rw [hexp]; exact h

/-- `toNumber` is value-exact and normalized on any deposit-ready amount. -/
lemma STAmount.toNumber_canonical_exact (s : STAmount) (mode : rounding_mode)
    (hc : s.Canonical) :
    ∃ sn : Number, s.toNumber mode = .ok sn ∧ sn.toRat = s.toRat ∧ sn.isNormalized := by
  by_cases hint : s.integral = true
  · obtain ⟨hic, hmax⟩ := hc.1 hint
    obtain ⟨sn, h1, h2, h3, _⟩ := STAmount.toNumber_integral_exact s mode hic hmax
    exact ⟨sn, h1, h2, h3⟩
  · have hfr : s.integral = false := by
      rcases hb : s.integral with _ | _
      · rfl
      · exact absurd hb hint
    exact STAmount.toNumber_iou_exact s mode (hc.2 hfr)

/-- A nonzero deposit-ready amount is at least `10 ^ (-81)` in magnitude. -/
lemma STAmount.Canonical.abs_toRat_ge (s : STAmount) (hc : s.Canonical)
    (hnz : s.mValue ≠ 0) : (10 : ℚ) ^ (-81 : ℤ) ≤ |s.toRat| := by
  rw [STAmount.abs_toRat]
  by_cases hint : s.integral = true
  · obtain ⟨hic, _⟩ := hc.1 hint
    rw [hic.offset_zero]
    have h1 : 1 ≤ s.mValue.toNat := by
      have : s.mValue.toNat ≠ 0 := by
        intro h0
        exact hnz (by rw [← UInt64.toNat_inj] at *; exact h0)
      omega
    have h1q : (1 : ℚ) ≤ (s.mValue.toNat : ℚ) := by exact_mod_cast h1
    have hp : ((10 : ℚ) ^ (-81 : ℤ)) ≤ 1 := by
      rw [show ((-81) : ℤ) = -(81 : ℕ) from rfl, zpow_neg, zpow_natCast]
      rw [inv_le_one_iff₀]
      right
      norm_num
    calc (10 : ℚ) ^ (-81 : ℤ) ≤ 1 := hp
      _ ≤ (s.mValue.toNat : ℚ) * 10 ^ (0 : ℤ) := by norm_num; exact h1
  · have hfr : s.integral = false := by
      rcases hb : s.integral with _ | _
      · rfl
      · exact absurd hb hint
    have hio := hc.2 hfr
    have hm : (10 ^ 15 : ℚ) ≤ (s.mValue.toNat : ℚ) := by exact_mod_cast hio.mant_lo
    have hoff : (10 : ℚ) ^ (-96 : ℤ) ≤ (10 : ℚ) ^ s.mOffset :=
      zpow_le_zpow_right₀ (by norm_num) hio.exp_lo
    have hsplit : (10 : ℚ) ^ (-81 : ℤ) = (10 : ℚ) ^ (15 : ℕ) * (10 : ℚ) ^ (-96 : ℤ) := by
      rw [← zpow_natCast (10 : ℚ) 15, ← zpow_add₀ (by norm_num : (10 : ℚ) ≠ 0)]
      norm_num
    rw [hsplit]
    have h10 : (0 : ℚ) < (10 : ℚ) ^ s.mOffset := zpow_pos (by norm_num) _
    calc (10 : ℚ) ^ (15 : ℕ) * (10 : ℚ) ^ (-96 : ℤ)
        ≤ (10 : ℚ) ^ (15 : ℕ) * (10 : ℚ) ^ s.mOffset := by
          exact mul_le_mul_of_nonneg_left hoff (by positivity)
      _ ≤ (s.mValue.toNat : ℚ) * 10 ^ s.mOffset := by
          exact mul_le_mul_of_nonneg_right (by exact_mod_cast hio.mant_lo) (le_of_lt h10)

/-- The vault `exponent` helper on a fractional asset returns `-100` (zero) or a
clamped IOU offset in `[-96, 80]`. -/
lemma exponent_fractional_offset (n : Number) (e : Int)
    (hok : numberExponent n .fractional = .ok e) :
    e = -100 ∨ ((-96 : ℤ) ≤ e ∧ e ≤ 80) := by
  unfold numberExponent at hok
  obtain ⟨a, ha, he⟩ := bind_ok_peel _ _ _ hok
  have heq : a.exponent = e :=
    Except.ok.inj (show Except.ok a.exponent = .ok e from he)
  rw [← heq]
  exact STAmount.ofNumber_fractional_offset .fractional n .to_nearest a rfl ha

/-- **A fractional `ofNumber` (any mode) that lands on zero came from a source
below the smallest positive IOU value `10⁻⁸¹`.** The exponent-underflow flush to
zero happens in the `checked`/`iou`/`normalize` stage on the sub-`cMinOffset`
exponent, independent of the rounding mode: the 16-digit `normalizeToRange` output
sits below `cMinOffset`, so the 19-digit source exponent is `≤ -100` and its
mantissa keeps the value under `10¹⁹·10⁻¹⁰⁰ = 10⁻⁸¹`. Same statement as
`ofNumber_fractional_zero_below_min`, used by the deposit charge, which snaps upward. -/
lemma STAmount.ofNumber_iou_zero_below_min (nt : NumericType) (n : Number)
    (mode : rounding_mode) (result : STAmount) (hnt : nt.isIntegral = false)
    (hn : n.isNormalized) (hneg : n.negative_ = false) (hnz : n.mantissa_ ≠ 0)
    (hok : STAmount.ofNumber nt n mode = .ok result) (hz : result.mValue = 0) :
    n.toRat < (10 : ℚ) ^ (-81 : ℤ) := by
  have hnt_frac : nt = .fractional := by
    cases nt with
    | fractional => rfl
    | integral mv mo ms msh => simp [NumericType.isIntegral] at hnt
  subst hnt_frac
  obtain ⟨hr_lo, hr_hi⟩ := hn.mantissaBounds_nat hnz
  have hre_lo : minExponent ≤ n.exponent_ := by
    rcases hn with h0 | ⟨_, _, _, hlo, _⟩
    · exact absurd (show n.mantissa_ = 0 by rw [h0]; rfl) hnz
    · exact hlo
  have hneg_dec : decide (n.signum < 0) = false := by rw [Number.signum_neg_decide]; exact hneg
  have hwork : (if decide (n.signum < 0) then n.operator_neg else n) = n := by
    rw [hneg_dec]; simp
  unfold STAmount.ofNumber at hok
  rw [if_neg (by decide : ¬ (NumericType.fractional.isIntegral = true))] at hok
  rw [hwork] at hok
  rw [hneg_dec] at hok
  cases hnorm : n.normalizeToRange kMinValue kMaxValue mode with
  | error e => rw [hnorm] at hok; exact absurd hok (by simp)
  | ok me =>
    obtain ⟨mant, exp⟩ := me
    rw [hnorm] at hok
    simp only at hok
    have hnorm' : n.normalizeToRange cMinValue cMaxValue mode = .ok (mant, exp) := hnorm
    have hexp_hi3 : n.exponent_ + 3 ≤ maxExponent :=
      normalizeToRange_iou_exp_hi n mode mant exp hr_lo hr_hi hnorm'
    obtain ⟨⟨hmlo, hmhi⟩, ⟨hexp_lo3, hexp_le⟩, hsgn⟩ :=
      normalizeToRange_iou_ok_facts n mode mant exp hr_lo hr_hi (by omega) hexp_hi3 hnorm'
    have hmant_pos : 0 ≤ mant.toInt := hsgn.1 hneg
    have hmant_natAbs : mant.toInt.natAbs = mant.toUInt64.toNat := by
      have := toUInt64_toNat_of_nonneg mant hmant_pos; omega
    have hmtu_lo : 10 ^ 15 ≤ mant.toUInt64.toNat := by
      rw [← hmant_natAbs]; have := hmlo; rw [(by decide : cMinValue.toNat = 10 ^ 15)] at this
      exact this
    have hmtu_hi : mant.toUInt64.toNat < 10 ^ 16 := by
      rw [← hmant_natAbs]; have := hmhi; rw [(by decide : cMaxValue.toNat = 10 ^ 16 - 1)] at this
      omega
    have hexp_zero : exp < cMinOffset :=
      STAmount.checked_iou_zero_exp_lt mant.toUInt64 exp false mode
        hmtu_lo hmtu_hi (by omega) hexp_le result hok hz
    have hexp_n : n.exponent_ ≤ -100 := by unfold cMinOffset at hexp_zero; omega
    rw [Number.toRat_of_nonneg n hneg]
    have hm : (n.mantissa_.toNat : ℚ) < (10 : ℚ) ^ (19 : ℕ) := by exact_mod_cast hr_hi
    have hpe_pos : (0 : ℚ) < (10 : ℚ) ^ n.exponent_ := zpow_pos (by norm_num) _
    have hstep : (n.mantissa_.toNat : ℚ) * (10 : ℚ) ^ n.exponent_
        < (10 : ℚ) ^ (19 : ℕ) * (10 : ℚ) ^ n.exponent_ :=
      mul_lt_mul_of_pos_right hm hpe_pos
    have hle2 : (10 : ℚ) ^ (19 : ℕ) * (10 : ℚ) ^ n.exponent_ ≤ (10 : ℚ) ^ (-81 : ℤ) := by
      rw [← zpow_natCast (10 : ℚ) 19, ← zpow_add₀ (by norm_num : (10 : ℚ) ≠ 0)]
      apply zpow_le_zpow_right₀ (by norm_num)
      omega
    linarith [hstep, hle2]

/-- A `false` `operator_gt` on comparable operands is a `≤` on values. Turns the
`computeDeposit` internal guard into the charge bound
`amountDeposit' ≤ amountDeposit`. -/
lemma STAmount.operator_gt_false_le (lhs rhs : STAmount) (h : STAmount.CmpFaithful lhs rhs)
    (hgt : lhs.operator_gt rhs = .ok false) : lhs.toRat ≤ rhs.toRat := by
  rw [STAmount.operator_gt_eq lhs rhs h, Except.ok.injEq, decide_eq_false_iff_not, not_lt] at hgt
  exact hgt

/-- A nonzero canonical amount (fractional or integral) is at least `10 ^ (-81)`
in magnitude. -/
lemma STAmount.canonical_disj_abs_toRat_ge (s : STAmount)
    (hc : s.IOUCanonical ∨ s.IntegralCanonical) (hnz : s.mValue ≠ 0) :
    (10 : ℚ) ^ (-81 : ℤ) ≤ |s.toRat| := by
  rw [STAmount.abs_toRat]
  rcases hc with hio | hint
  · have hoff : (10 : ℚ) ^ (-96 : ℤ) ≤ (10 : ℚ) ^ s.mOffset :=
      zpow_le_zpow_right₀ (by norm_num) hio.exp_lo
    have hsplit : (10 : ℚ) ^ (-81 : ℤ) = (10 : ℚ) ^ (15 : ℕ) * (10 : ℚ) ^ (-96 : ℤ) := by
      rw [← zpow_natCast (10 : ℚ) 15, ← zpow_add₀ (by norm_num : (10 : ℚ) ≠ 0)]; norm_num
    rw [hsplit]
    have h10 : (0 : ℚ) < (10 : ℚ) ^ s.mOffset := zpow_pos (by norm_num) _
    calc (10 : ℚ) ^ (15 : ℕ) * (10 : ℚ) ^ (-96 : ℤ)
        ≤ (10 : ℚ) ^ (15 : ℕ) * (10 : ℚ) ^ s.mOffset :=
          mul_le_mul_of_nonneg_left hoff (by positivity)
      _ ≤ (s.mValue.toNat : ℚ) * 10 ^ s.mOffset :=
          mul_le_mul_of_nonneg_right (by exact_mod_cast hio.mant_lo) (le_of_lt h10)
  · rw [hint.offset_zero]
    have h1 : 1 ≤ s.mValue.toNat := by
      have hne : s.mValue.toNat ≠ 0 := fun h0 => hnz (by rw [← UInt64.toNat_inj]; simpa using h0)
      omega
    have h1q : (1 : ℚ) ≤ (s.mValue.toNat : ℚ) := by exact_mod_cast h1
    have hp : ((10 : ℚ) ^ (-81 : ℤ)) ≤ 1 := by
      rw [show ((-81) : ℤ) = -(81 : ℕ) from rfl, zpow_neg, zpow_natCast, inv_le_one_iff₀]
      right; norm_num
    calc (10 : ℚ) ^ (-81 : ℤ) ≤ 1 := hp
      _ ≤ (s.mValue.toNat : ℚ) * 10 ^ (0 : ℤ) := by simpa using h1q

/-- **A `.downward` fractional `ofNumber` that lands on zero came from a source below
the smallest positive IOU value `10⁻⁸¹`.** The `.downward` snap of a normalized
sign-cleared nonzero `Number` floors to zero exactly when its value is below the grid
minimum `cMinValue · 10^cMinOffset = 10⁻⁸¹`: the 16-digit `normalizeToRange` exponent
runs below `cMinOffset`, so the source exponent is `≤ -100` and its 19-digit mantissa
keeps the value under `10¹⁹ · 10⁻¹⁰⁰ = 10⁻⁸¹`. -/
lemma STAmount.ofNumber_fractional_zero_below_min (nt : NumericType) (n : Number)
    (result : STAmount) (mode : rounding_mode) (hnt : nt.isIntegral = false)
    (hn : n.isNormalized) (hneg : n.negative_ = false) (hnz : n.mantissa_ ≠ 0)
    (hok : STAmount.ofNumber nt n mode = .ok result) (hz : result.mValue = 0) :
    n.toRat < (10 : ℚ) ^ (-81 : ℤ) := by
  have hnt_frac : nt = .fractional := by
    cases nt with
    | fractional => rfl
    | integral mv mo ms msh => simp [NumericType.isIntegral] at hnt
  subst hnt_frac
  obtain ⟨hr_lo, hr_hi⟩ := hn.mantissaBounds_nat hnz
  have hre_lo : minExponent ≤ n.exponent_ := by
    rcases hn with h0 | ⟨_, _, _, hlo, _⟩
    · exact absurd (show n.mantissa_ = 0 by rw [h0]; rfl) hnz
    · exact hlo
  have hneg_dec : decide (n.signum < 0) = false := by rw [Number.signum_neg_decide]; exact hneg
  have hwork : (if decide (n.signum < 0) then n.operator_neg else n) = n := by
    rw [hneg_dec]; simp
  unfold STAmount.ofNumber at hok
  rw [if_neg (by decide : ¬ (NumericType.fractional.isIntegral = true))] at hok
  rw [hwork] at hok
  rw [hneg_dec] at hok
  cases hnorm : n.normalizeToRange kMinValue kMaxValue mode with
  | error e => rw [hnorm] at hok; exact absurd hok (by simp)
  | ok me =>
    obtain ⟨mant, exp⟩ := me
    rw [hnorm] at hok
    simp only at hok
    have hnorm' : n.normalizeToRange cMinValue cMaxValue mode = .ok (mant, exp) := hnorm
    have hexp_hi3 : n.exponent_ + 3 ≤ maxExponent :=
      normalizeToRange_iou_exp_hi n mode mant exp hr_lo hr_hi hnorm'
    obtain ⟨⟨hmlo, hmhi⟩, ⟨hexp_lo3, hexp_le⟩, hsgn⟩ :=
      normalizeToRange_iou_ok_facts n mode mant exp hr_lo hr_hi (by omega) hexp_hi3 hnorm'
    have hmant_pos : 0 ≤ mant.toInt := hsgn.1 hneg
    have hmant_natAbs : mant.toInt.natAbs = mant.toUInt64.toNat := by
      have := toUInt64_toNat_of_nonneg mant hmant_pos; omega
    have hmtu_lo : 10 ^ 15 ≤ mant.toUInt64.toNat := by
      rw [← hmant_natAbs]; have := hmlo; rw [(by decide : cMinValue.toNat = 10 ^ 15)] at this
      exact this
    have hmtu_hi : mant.toUInt64.toNat < 10 ^ 16 := by
      rw [← hmant_natAbs]; have := hmhi; rw [(by decide : cMaxValue.toNat = 10 ^ 16 - 1)] at this
      omega
    have hexp_zero : exp < cMinOffset :=
      STAmount.checked_iou_zero_exp_lt mant.toUInt64 exp false mode hmtu_lo hmtu_hi
        (by omega) hexp_le result hok hz
    have hexp_n : n.exponent_ ≤ -100 := by unfold cMinOffset at hexp_zero; omega
    rw [Number.toRat_of_nonneg n hneg]
    have hm : (n.mantissa_.toNat : ℚ) < (10 : ℚ) ^ (19 : ℕ) := by exact_mod_cast hr_hi
    have hpe_pos : (0 : ℚ) < (10 : ℚ) ^ n.exponent_ := zpow_pos (by norm_num) _
    have hstep : (n.mantissa_.toNat : ℚ) * (10 : ℚ) ^ n.exponent_
        < (10 : ℚ) ^ (19 : ℕ) * (10 : ℚ) ^ n.exponent_ :=
      mul_lt_mul_of_pos_right hm hpe_pos
    have hle2 : (10 : ℚ) ^ (19 : ℕ) * (10 : ℚ) ^ n.exponent_ ≤ (10 : ℚ) ^ (-81 : ℤ) := by
      rw [← zpow_natCast (10 : ℚ) 19, ← zpow_add₀ (by norm_num : (10 : ℚ) ≠ 0)]
      apply zpow_le_zpow_right₀ (by norm_num)
      omega
    linarith [hstep, hle2]

/-- `ofIOUAmount` of the zero `IOUAmount` is the canonical zero record. (The version
in `RoundToScale.Common.Proofs` is `private`, so it is reproven here.) -/
lemma STAmount.ofIOU_zero_rec (mode : rounding_mode) :
    STAmount.ofIOUAmount IOUAmount.zero mode = .ok ⟨.fractional, 0, -100, false⟩ := by
  unfold STAmount.ofIOUAmount STAmount.canonicalize STAmount.iou
  simp only [STAmount.unchecked, STAmount.integral, NumericType.isIntegral,
    Bool.false_eq_true, if_false]
  rfl

/-- **The directed subtraction of an `IOUCanonical` amount from itself flushes to the
canonical zero.** The two 19-digit summands the `IOUAmount` add builds are exact
opposites, so the `Number` cancellation guard returns `Number.zero`, which repacks
to the zero record. Holds on the full `[-96, 80]` scale range (unlike the exact-floor
characterization, which needs `-81`). -/
lemma STAmount.operator_sub_self_zero (a result : STAmount) (mode : rounding_mode)
    (hc : a.IOUCanonical)
    (hok : STAmount.operator_sub a a mode = .ok result) :
    result.mValue = 0 := by
  have h_mv : a.mValue ≠ 0 := by
    intro h0
    have h1 : a.mValue.toNat = 0 := by rw [h0]; rfl
    have := hc.mant_lo; omega
  unfold STAmount.operator_sub at hok
  rw [STAmount.operator_neg_of_ne a h_mv] at hok
  set negA : STAmount := { a with mIsNegative := !a.mIsNegative } with hnegA_def
  have hc_negA : negA.IOUCanonical :=
    { is_fractional := hc.is_fractional
      mant_lo := hc.mant_lo
      mant_hi := hc.mant_hi
      exp_lo := hc.exp_lo
      exp_hi := hc.exp_hi }
  rw [STAmount.operator_add_iou_unfold a negA mode hc hc_negA] at hok
  set s1n : Number := ⟨a.mIsNegative, a.mValue * 10 * 10 * 10, a.mOffset - 3⟩ with hs1n_def
  set s2n : Number := ⟨negA.mIsNegative, negA.mValue * 10 * 10 * 10, negA.mOffset - 3⟩
    with hs2n_def
  obtain ⟨n₂, h_add₂, hok₃⟩ : ∃ n₂, Number.operator_add s1n s2n mode = .ok n₂ ∧
      (match IOUAmount.ofNumber n₂ mode with
       | .error e => (Except.error e : Except Error STAmount)
       | .ok sumI => STAmount.ofIOUAmount sumI mode) = .ok result := by
    match h1 : Number.operator_add s1n s2n mode with
    | .error e => rw [h1] at hok; exact absurd hok (by intro h; cases h)
    | .ok n₂ => rw [h1] at hok; exact ⟨n₂, rfl, hok⟩
  obtain ⟨sumI₂, h_of₂, h_pack₂⟩ : ∃ sumI₂, IOUAmount.ofNumber n₂ mode = .ok sumI₂ ∧
      STAmount.ofIOUAmount sumI₂ mode = .ok result := by
    match h1 : IOUAmount.ofNumber n₂ mode with
    | .error e => rw [h1] at hok₃; exact absurd hok₃ (by intro h; cases h)
    | .ok sumI₂ => rw [h1] at hok₃; exact ⟨sumI₂, rfl, hok₃⟩
  have hs1_norm : s1n.isNormalized :=
    lift_isNormalized a.mIsNegative a.mValue a.mOffset hc.mant_lo hc.mant_hi
      (by have := hc.exp_lo; unfold minExponent; omega)
      (by have := hc.exp_hi; unfold maxExponent; omega)
  have hs2_norm : s2n.isNormalized :=
    lift_isNormalized negA.mIsNegative negA.mValue negA.mOffset hc_negA.mant_lo hc_negA.mant_hi
      (by have := hc_negA.exp_lo; unfold minExponent; omega)
      (by have := hc_negA.exp_hi; unfold maxExponent; omega)
  have hs1_val : s1n.toRat = a.toRat := lift_toRat a hc.mant_hi
  have hs2_val : s2n.toRat = negA.toRat := lift_toRat negA hc_negA.mant_hi
  have hs1_mant : s1n.mantissa_ ≠ 0 := by
    intro h0
    have h1 : s1n.mantissa_.toNat = 0 := by rw [h0]; rfl
    have hM : s1n.mantissa_.toNat = a.mValue.toNat * 1000 :=
      m_mul_thousand_no_overflow hc.mant_hi
    have := hc.mant_lo; omega
  have hs2_mant : s2n.mantissa_ ≠ 0 := by
    intro h0
    have h1 : s2n.mantissa_.toNat = 0 := by rw [h0]; rfl
    have hM : s2n.mantissa_.toNat = negA.mValue.toNat * 1000 :=
      m_mul_thousand_no_overflow hc_negA.mant_hi
    have := hc_negA.mant_lo; omega
  have h_diff : s1n.negative_ ≠ s2n.negative_ := by
    show a.mIsNegative ≠ !a.mIsNegative
    rcases hb : a.mIsNegative with _ | _ <;> simp
  have h_opp : s1n.toRat + s2n.toRat = 0 := by
    rw [hs1_val, hs2_val, STAmount.toRat_signed a, STAmount.toRat_signed negA]
    show ((if a.mIsNegative then (-1 : ℚ) else 1) * (a.mValue.toNat : ℚ) * (10 : ℚ) ^ a.mOffset)
       + ((if (!a.mIsNegative) then (-1 : ℚ) else 1) * (a.mValue.toNat : ℚ)
          * (10 : ℚ) ^ a.mOffset) = 0
    rcases hb : a.mIsNegative with _ | _ <;>
      simp only [Bool.not_false, Bool.not_true, if_true, if_false, Bool.false_eq_true] <;>
      ring
  have h_n₂_val : n₂.toRat = 0 := by
    have h := operator_add_exact_diff_sign s1n s2n n₂ mode hs1_norm hs2_norm
      hs1_mant hs2_mant h_diff Number.zero (Or.inl rfl)
      (by rw [Number.toRat_zero, h_opp]) h_add₂
    rw [h, h_opp]
  have h_n₂_mant : n₂.mantissa_ = 0 := Number.toRat_eq_zero_iff.mp h_n₂_val
  rw [IOUAmount.ofNumber_zero_mant n₂ mode h_n₂_mant] at h_of₂
  have h_sumI₂ : sumI₂ = IOUAmount.zero := Except.ok.inj h_of₂.symm
  rw [h_sumI₂, STAmount.ofIOU_zero_rec mode] at h_pack₂
  rw [← Except.ok.inj h_pack₂]

/-- A nonzero fractional-canonical amount is `Canonical`. -/
lemma STAmount.Canonical.of_iou (s : STAmount) (h : s.IOUCanonical) : s.Canonical := by
  have hintf : s.integral = false := by
    unfold STAmount.integral; rw [h.is_fractional]; decide
  refine ⟨fun hi => ?_, fun _ => h⟩
  rw [hintf] at hi; exact absurd hi Bool.false_ne_true

end XRPL.Model.Protocol
