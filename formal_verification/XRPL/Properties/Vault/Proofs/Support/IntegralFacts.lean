import XRPL.Properties.Vault.Proofs.Support.STAmountFacts
import XRPL.Properties.Protocol.STAmount.Common.OfNumberFacts
import XRPL.Properties.Protocol.STAmount.Common.OfNumberRounding
import XRPL.Properties.Protocol.STAmount.Common.OfNumberTotality

/-! # Integral amounts

Facts about integral `STAmount`s: `canonicalize`, `ofNumber` and `toNumber` on integer-valued
amounts. -/

namespace XRPL.Model.Protocol

/-- The `int64` zero amount reduces to the canonical record `⟨.int64, 0, 0, false⟩`. -/
lemma STAmount.zero_int64_eq : STAmount.zero .int64 = ⟨.int64, 0, 0, false⟩ := by decide

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
  · exact STAmount.ofNumber_iou_mantissa_ne_zero nt n mode result
      (NumericType.eq_fractional_of_not_integral (by simpa using hint)) hok hres

/-- A fractional `ofNumber` of a negative source is at most zero. -/
lemma STAmount.ofNumber_signtrue_nonpos (nt : NumericType) (n : Number) (mode : rounding_mode)
    (result : STAmount) (hnt : nt.isIntegral = false) (hn : n.isNormalized)
    (hneg : n.negative_ = true)
    (hok : STAmount.ofNumber nt n mode = .ok result) : result.toRat ≤ 0 := by
  obtain rfl := NumericType.eq_fractional_of_not_integral hnt
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
  have hexp_lo : minExponent ≤ n.exponent_ := Number.exponent_ge_min n hn hn_ne
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

/-- An integral amount of a negative value is at most zero: the sign survives the conversion. -/
lemma STAmount.ofNumber_integral_negative_nonpos (nt : NumericType) (n : Number) (mode : rounding_mode)
    (result : STAmount) (hnt : nt.isIntegral = true) (hneg : n.negative_ = true)
    (hok : STAmount.ofNumber nt n mode = .ok result) : result.toRat ≤ 0 := by
  unfold STAmount.ofNumber at hok
  simp only [Number.signum_neg_decide, hneg, if_true, if_pos hnt] at hok
  have hwneg : n.operator_neg.negative_ = false := by
    unfold Number.operator_neg
    split
    · rfl
    · simp [hneg]
  cases hr : n.operator_neg.to_rep mode with
  | error e => rw [hr] at hok; exact absurd hok (by simp)
  | ok iv =>
    rw [hr] at hok
    simp only [] at hok
    obtain ⟨hnn, hle⟩ := Number.to_rep_nonneg_range _ mode iv hwneg hr
    have hexact := STAmount.canonicalize_integral_toRat (STAmount.unchecked nt iv.toUInt64 0 true) result mode
      (show (STAmount.unchecked nt iv.toUInt64 0 true).integral = true from hnt) rfl
      (toUInt64_toNat_le_maxRep iv hnn hle) hok
    rw [hexact, STAmount.toRat_signed]
    show (if true = true then (-1 : ℚ) else 1) * _ * _ ≤ 0
    simp only [if_true, neg_mul, one_mul, Left.neg_nonpos_iff]
    positivity

/-- Canonicalizing an offset-`0` integral amount within `maxRep` keeps its type, offset, bound and value. -/
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

/-- A `.downward` conversion of a nonnegative `Number` never exceeds it, is nonnegative, and falls short by at
most one unit of the result's exponent. -/
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
    have hnt_frac : nt = .fractional := NumericType.eq_fractional_of_not_integral (by simpa using hint)
    have hn_ne : n.mantissa_ ≠ 0 :=
      STAmount.ofNumber_iou_mantissa_ne_zero nt n .downward result hnt_frac hok hres
    obtain ⟨hlo19, hhi19⟩ := hn.mantissaBounds_nat hn_ne
    have hexp_lo : minExponent ≤ n.exponent_ := Number.exponent_ge_min n hn hn_ne
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

/-- A successful conversion into an integral numeric type yields an offset-`0` amount of that type whose stored
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

/-- The `int64` zero amount is `IntegralCanonical`. -/
lemma zero_int64_IntegralCanonical : (STAmount.zero .int64).IntegralCanonical := by
  rw [STAmount.zero_int64_eq]; exact ⟨by decide, by decide, by decide⟩

end XRPL.Model.Protocol
