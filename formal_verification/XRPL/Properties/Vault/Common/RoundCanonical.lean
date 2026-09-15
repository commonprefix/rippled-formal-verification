import XRPL.Properties.Vault.Common.OfNumberBoundary
import XRPL.Properties.Vault.Common.Reduction
import XRPL.Properties.Vault.Common.SubZeroShape
import XRPL.Properties.Protocol.STAmount.Div.Common.IOU
import XRPL.Properties.Protocol.STAmount.RoundToScale.Common.Sum
import XRPL.Properties.Protocol.STAmount.Sub.RoundsWithin
import XRPL.Properties.Protocol.STAmount.Common.RoundToScaleHelpers
import XRPL.Properties.Protocol.STAmount.Common.RoundToScalePlumbing

/-! # Canonicity of the `roundToVaultExponent` output

The `Vault.deposit` accuracy headlines only ever hypothesize that the *raw* input
`amountDeposit` is stored canonically (`amountDeposit.Canonical`). Internally the
deposit rounds it with `roundToVaultExponent`, and the rounded amount must itself
be canonical for the `toNumber`-exactness lemmas the exchange proofs consume.

This file derives that fact rather than hypothesizing it. The fractional pipeline
(`iou`/`canonicalize` → `operator_add`/`operator_sub` → `roundToExponent` →
`roundToVaultExponent`) always canonicalizes its fractional output, so the result
is `IOUCanonical`-or-zero; the integral pass is the identity. -/

namespace XRPL.Model.Protocol

set_option maxRecDepth 4000

/-! ## `IOUAmount.normalize` output range -/

/-- A successful `IOUAmount.normalize` output is either a canonical 16-digit
amount (`InRange16`) or the zero amount. The 19-digit `from_rep` re-lift is
`largeRange`-normalized, so the 16-digit `normalizeToRange` snap lands in
`[cMinValue, cMaxValue]`; the `cMinOffset`/`cMaxOffset` clamps that a `.ok`
passed pin the exponent to `[-96, 80]`. -/
lemma IOUAmount.normalize_InRange16_or_zero (a : IOUAmount) (mode : rounding_mode)
    (i : IOUAmount) (hok : IOUAmount.normalize a mode = .ok i) :
    i.InRange16 ∨ i.mantissa_ = 0 := by
  by_cases hi0 : i.mantissa_ = 0
  · exact Or.inr hi0
  refine Or.inl ?_
  unfold IOUAmount.normalize at hok
  by_cases hma : a.mantissa_ = 0
  · rw [if_pos (beq_iff_eq.mpr hma)] at hok
    rw [← Except.ok.inj hok] at hi0
    exact absurd rfl hi0
  · rw [show (a.mantissa_ == 0) = false from beq_eq_false_iff_ne.mpr hma] at hok
    simp only [Bool.false_eq_true, if_false] at hok
    have ham_toInt : a.mantissa_.toInt ≠ 0 := by
      intro h; exact hma (Int64.toInt_inj.mp (by rw [h]; decide))
    cases hfr : Number.from_rep a.mantissa_ a.exponent_ largeRange.min largeRange.max mode with
    | error err => rw [hfr] at hok; exact absurd hok (by simp)
    | ok v =>
      rw [hfr] at hok
      simp only [] at hok
      have hofn : IOUAmount.ofNumber v mode = .ok i := hok
      have hv_ne : v.mantissa_ ≠ 0 := IOUAmount.ofNumber_mantissa_ne_zero v mode i hofn hi0
      have hfr' : (Number.unchecked (a.mantissa_ < 0) a.mantissa_.toInt.natAbs.toUInt64
          a.exponent_).normalize largeRange.min largeRange.max mode = .ok v := hfr
      have hun_ne : (Number.unchecked (a.mantissa_ < 0) a.mantissa_.toInt.natAbs.toUInt64
          a.exponent_).mantissa_ ≠ 0 := by
        show a.mantissa_.toInt.natAbs.toUInt64 ≠ 0
        have hb : a.mantissa_.toInt.natAbs < 2 ^ 64 := by
          have h1 := Int64.le_toInt a.mantissa_
          have h2 := Int64.toInt_lt a.mantissa_
          omega
        have heq : a.mantissa_.toInt.natAbs.toUInt64.toNat = a.mantissa_.toInt.natAbs :=
          UInt64.toNat_ofNat_of_lt hb
        intro h; rw [h] at heq; simp at heq; omega
      have hv_norm : v.isNormalized := normalize_result_isNormalized _ v mode hun_ne hfr' hv_ne
      obtain ⟨hvm_lo, hvm_hi⟩ := hv_norm.mantissaBounds_nat hv_ne
      have hv_exp_lo : minExponent ≤ v.exponent_ := by
        rcases hv_norm with hz | ⟨_, _, _, hlo', _⟩
        · exact absurd (show v.mantissa_ = 0 by rw [hz]; rfl) hv_ne
        · exact hlo'
      cases hfn : IOUAmount.fromNumber v mode with
      | error err =>
        unfold IOUAmount.ofNumber at hofn; rw [hfn] at hofn; exact absurd hofn (by simp)
      | ok r =>
        unfold IOUAmount.ofNumber at hofn
        rw [hfn] at hofn
        simp only [] at hofn
        by_cases hhi : r.exponent_ > cMaxOffset
        · rw [if_pos hhi] at hofn; exact absurd hofn (by simp)
        rw [if_neg hhi] at hofn
        by_cases hlo : r.exponent_ < cMinOffset
        · rw [if_pos hlo] at hofn
          rw [← Except.ok.inj hofn] at hi0
          exact absurd rfl hi0
        rw [if_neg hlo] at hofn
        have hir : i = r := (Except.ok.inj hofn).symm
        unfold IOUAmount.fromNumber at hfn
        cases hnorm : v.normalizeToRange cMinValue cMaxValue mode with
        | error err => rw [hnorm] at hfn; exact absurd hfn (by simp)
        | ok me' =>
          obtain ⟨mm, ee⟩ := me'
          rw [hnorm] at hfn
          simp only [] at hfn
          have hrmm : r = ⟨mm, ee⟩ := (Except.ok.inj hfn).symm
          rw [hrmm] at hhi hlo
          have hexp3 : v.exponent_ + 3 ≤ maxExponent :=
            normalizeToRange_iou_exp_hi v mode mm ee hvm_lo hvm_hi hnorm
          obtain ⟨⟨hmlo, hmhi⟩, _, _⟩ :=
            normalizeToRange_iou_ok_facts v mode mm ee hvm_lo hvm_hi (by omega) hexp3 hnorm
          rw [hir, hrmm]
          refine ⟨?_, ?_, ?_, ?_⟩
          · show 10 ^ 15 ≤ mm.toInt.natAbs
            rw [show cMinValue.toNat = 10 ^ 15 from by decide] at hmlo; exact hmlo
          · show mm.toInt.natAbs < 10 ^ 16
            rw [show cMaxValue.toNat = 10 ^ 16 - 1 from by decide] at hmhi; omega
          · show (-96 : ℤ) ≤ ee
            have := not_lt.mp hlo; unfold cMinOffset at this; omega
          · show ee ≤ (80 : ℤ)
            have := not_lt.mp hhi; unfold cMaxOffset at this; omega

/-- **Sign preservation of `IOUAmount.normalize`.** A nonnegative signed mantissa
stays nonnegative through the 19-digit re-lift and the 16-digit snap: each stage
carries the cleared sign into its output (`doRoundUp` copies the input sign, and a
flushed-to-zero result is nonnegative trivially). Magnitude-free, unlike the
`RoundsWithin` characterizations, so it applies to sub-`10^16` mantissas. -/
lemma IOUAmount.normalize_mantissa_nonneg (m : Int64) (e : Int) (mode : rounding_mode)
    (i : IOUAmount) (hm : 0 ≤ m.toInt)
    (hok : IOUAmount.normalize ⟨m, e⟩ mode = .ok i) :
    0 ≤ i.mantissa_.toInt := by
  by_cases hi0 : i.mantissa_ = 0
  · rw [hi0]; decide
  have hmlt : decide (m < 0) = false := by
    rw [decide_eq_false_iff_not, Int64.lt_iff_toInt_lt]
    have h0 : (0 : Int64).toInt = 0 := by decide
    omega
  unfold IOUAmount.normalize at hok
  by_cases hma : m = 0
  · rw [if_pos (show ((⟨m, e⟩ : IOUAmount).mantissa_ == 0) = true from beq_iff_eq.mpr hma)] at hok
    rw [← Except.ok.inj hok] at hi0; exact absurd rfl hi0
  · have hm_toInt : m.toInt ≠ 0 := fun h => hma (Int64.toInt_inj.mp (by rw [h]; decide))
    rw [show ((⟨m, e⟩ : IOUAmount).mantissa_ == 0) = false from beq_eq_false_iff_ne.mpr hma] at hok
    simp only [Bool.false_eq_true, if_false] at hok
    cases hfr : Number.from_rep m e largeRange.min largeRange.max mode with
    | error err => rw [hfr] at hok; exact absurd hok (by simp)
    | ok v =>
      rw [hfr] at hok
      simp only [] at hok
      have hofn : IOUAmount.ofNumber v mode = .ok i := hok
      have hv_ne : v.mantissa_ ≠ 0 := IOUAmount.ofNumber_mantissa_ne_zero v mode i hofn hi0
      have hfr' : (Number.unchecked (m < 0) m.toInt.natAbs.toUInt64 e).normalize
          largeRange.min largeRange.max mode = .ok v := hfr
      have hun_ne : (Number.unchecked (m < 0) m.toInt.natAbs.toUInt64 e).mantissa_ ≠ 0 := by
        show m.toInt.natAbs.toUInt64 ≠ 0
        have hb : m.toInt.natAbs < 2 ^ 64 := by
          have h1 := Int64.le_toInt m
          have h2 := Int64.toInt_lt m
          omega
        have heq : m.toInt.natAbs.toUInt64.toNat = m.toInt.natAbs :=
          UInt64.toNat_ofNat_of_lt hb
        intro h; rw [h] at heq; simp at heq; omega
      have hv_norm : v.isNormalized :=
        normalize_result_isNormalized _ v mode hun_ne hfr' hv_ne
      obtain ⟨hvm_lo, hvm_hi⟩ := hv_norm.mantissaBounds_nat hv_ne
      have hv_exp_lo : minExponent ≤ v.exponent_ := by
        rcases hv_norm with hz | ⟨_, _, _, hlo', _⟩
        · exact absurd (show v.mantissa_ = 0 by rw [hz]; rfl) hv_ne
        · exact hlo'
      -- Stage 1: the 19-digit re-lift keeps the cleared sign, so `v.negative_ = false`.
      have hvneg : v.negative_ = false := by
        obtain ⟨m3, e3, g3, res, hrup, hres_eq, -, -, -, -⟩ :=
          normalize_doRoundUp_stage _ v mode hun_ne hfr' hv_ne
        have hres_ne : res.mantissa_ ≠ 0 := by rw [hres_eq] at hv_ne; exact hv_ne
        have hsg := doRoundUp_negative_of_mant_ne g3 _ m3 e3 largeRange.min largeRange.max mode
          .normalize2 res hrup hres_ne
        rw [hres_eq]
        show res.negative_ = false
        rw [hsg]; exact hmlt
      -- Stage 2: the 16-digit snap keeps the cleared sign, giving a nonnegative mantissa.
      unfold IOUAmount.ofNumber at hofn
      cases hfn : IOUAmount.fromNumber v mode with
      | error err => rw [hfn] at hofn; exact absurd hofn (by simp)
      | ok r =>
        rw [hfn] at hofn
        simp only [] at hofn
        by_cases hhi : r.exponent_ > cMaxOffset
        · rw [if_pos hhi] at hofn; exact absurd hofn (by simp)
        rw [if_neg hhi] at hofn
        by_cases hlo : r.exponent_ < cMinOffset
        · rw [if_pos hlo] at hofn
          rw [← Except.ok.inj hofn] at hi0; exact absurd rfl hi0
        rw [if_neg hlo] at hofn
        have hir : i = r := (Except.ok.inj hofn).symm
        unfold IOUAmount.fromNumber at hfn
        cases hnorm : v.normalizeToRange cMinValue cMaxValue mode with
        | error err => rw [hnorm] at hfn; exact absurd hfn (by simp)
        | ok me' =>
          obtain ⟨mm, ee⟩ := me'
          rw [hnorm] at hfn
          simp only [] at hfn
          have hrmm : r = ⟨mm, ee⟩ := (Except.ok.inj hfn).symm
          have hexp3 : v.exponent_ + 3 ≤ maxExponent :=
            normalizeToRange_iou_exp_hi v mode mm ee hvm_lo hvm_hi hnorm
          obtain ⟨-, -, hsign⟩ :=
            normalizeToRange_iou_ok_facts v mode mm ee hvm_lo hvm_hi (by omega) hexp3 hnorm
          rw [hir, hrmm]
          exact hsign hvneg

/-- **`canonicalize` of a sign-cleared fractional source is nonnegative.** The
`iou`/`ofMantissaExp`/`normalize` snap preserves the cleared sign
(`normalize_mantissa_nonneg`), so the packed record is nonnegative. Needs only
that the stored magnitude fits `Int64` (`< 2^63`), not the canonical `10^16`
window, so it covers small first-deposit mantissas. -/
lemma STAmount.canonicalize_signfalse_nonneg (s result : STAmount) (mode : rounding_mode)
    (hfr : s.mNumericType = .fractional) (hneg : s.mIsNegative = false)
    (hfit : s.mValue.toNat < 2 ^ 63)
    (hok : s.canonicalize mode = .ok result) :
    0 ≤ result.toRat := by
  have hint : ¬ s.integral = true := by unfold STAmount.integral; rw [hfr]; decide
  unfold STAmount.canonicalize at hok
  rw [if_neg hint] at hok
  have hiou : s.iou mode = IOUAmount.ofMantissaExp s.signedDrops.toInt64 s.mOffset mode := by
    unfold STAmount.iou; rw [if_neg hint]
  rw [hiou] at hok
  have hsd_nn : 0 ≤ s.signedDrops.toInt64.toInt := by
    rw [STAmount.signedDrops_toInt64_toInt_of_lt s hfit]
    unfold STAmount.signedDrops; rw [hneg]; simp
  cases hone : IOUAmount.ofMantissaExp s.signedDrops.toInt64 s.mOffset mode with
  | error e => rw [hone] at hok; exact absurd hok (by simp)
  | ok i =>
    rw [hone] at hok
    simp only [] at hok
    have hi_nn : 0 ≤ i.mantissa_.toInt :=
      IOUAmount.normalize_mantissa_nonneg s.signedDrops.toInt64 s.mOffset mode i hsd_nn hone
    have hneg_false : decide (i.signum < 0) = false := by
      rw [decide_eq_false_iff_not, IOUAmount.signum_neg_iff, Int64.lt_iff_toInt_lt]
      have h0 : (0 : Int64).toInt = 0 := by decide
      omega
    have heq := Except.ok.inj hok
    have hcneg : result.mIsNegative = false := by rw [← heq]; exact hneg_false
    rw [STAmount.toRat_of_nonneg result hcneg]; positivity

/-- A nonnegative amount either is zero or has its sign flag clear. Feeds the
`clampToSumExponent` identity lemmas, which cannot be confused by a signed zero
(`operator_neg` is the identity there). -/
lemma STAmount.sign_clear_of_nonneg (s : STAmount) (h : 0 ≤ s.toRat) :
    s.mValue = 0 ∨ s.mIsNegative = false := by
  by_cases hmv : s.mValue = 0
  · exact Or.inl hmv
  refine Or.inr ?_
  by_contra hc
  have hneg : s.mIsNegative = true := by simpa using hc
  have hsn : s.operator_neg.mIsNegative = false := by
    rw [STAmount.operator_neg_of_ne s hmv]
    show (!s.mIsNegative) = false
    rw [hneg]; rfl
  have hmv' : s.operator_neg.mValue ≠ 0 := by rw [STAmount.operator_neg_mValue]; exact hmv
  have hp := STAmount.toRat_pos_of s.operator_neg hsn hmv'
  rw [STAmount.operator_neg_toRat] at hp
  linarith

/-! ## `normalize` never flushes a normalized nonzero `Number` -/

/-- A normalized nonzero `Number` is at or above the smallest magnitude the
19-digit `normalize` pipeline can represent. -/
lemma Number.abs_toRat_ge_min_of_normalized (n : Number)
    (hn : n.isNormalized) (hne : n.mantissa_ ≠ 0) :
    (10 : ℚ) ^ (18 : ℕ) * (10 : ℚ) ^ (minExponent : ℤ) ≤ |n.toRat| := by
  obtain ⟨hm_lo, -⟩ := hn.mantissaBounds_nat hne
  have hexp : minExponent ≤ n.exponent_ := by
    rcases hn with h0 | ⟨_, _, _, hlo, _⟩
    · exact absurd (show n.mantissa_ = 0 by rw [h0]; rfl) hne
    · exact hlo
  have habs : |n.toRat| = (n.mantissa_.toNat : ℚ) * (10 : ℚ) ^ n.exponent_ := by
    cases hneg : n.negative_ with
    | false => rw [Number.toRat_of_nonneg n hneg, abs_of_nonneg (by positivity)]
    | true => rw [Number.toRat_of_neg n hneg, abs_neg, abs_of_nonneg (by positivity)]
  rw [habs]
  have h1 : (10 : ℚ) ^ (18 : ℕ) ≤ (n.mantissa_.toNat : ℚ) := by exact_mod_cast hm_lo
  have h3 : (0 : ℚ) < (10 : ℚ) ^ (minExponent : ℤ) := zpow_pos (by norm_num) _
  have h2 : (10 : ℚ) ^ (minExponent : ℤ) ≤ (10 : ℚ) ^ n.exponent_ :=
    zpow_le_zpow_right₀ (by norm_num) hexp
  have hmnn : (0 : ℚ) ≤ (n.mantissa_.toNat : ℚ) := by positivity
  calc (10 : ℚ) ^ (18 : ℕ) * (10 : ℚ) ^ (minExponent : ℤ)
      ≤ (n.mantissa_.toNat : ℚ) * (10 : ℚ) ^ (minExponent : ℤ) :=
        mul_le_mul_of_nonneg_right h1 (le_of_lt h3)
    _ ≤ (n.mantissa_.toNat : ℚ) * (10 : ℚ) ^ n.exponent_ :=
        mul_le_mul_of_nonneg_left h2 hmnn

/-- **`normalize` never flushes a normalized nonzero `Number` to zero.** The
underflow characterisation puts a flushed input strictly below
`10 ^ 18 * 10 ^ minExponent`, a magnitude every normalized nonzero `Number`
attains. This is the fact that lets the post-sum grid step be bounded against
the stored total: without it the flushed `ofNumber` output has an unpinned
exponent. -/
lemma Number.normalize_ne_zero_of_normalized (n result : Number) (mode : rounding_mode)
    (hn : n.isNormalized) (hne : n.mantissa_ ≠ 0)
    (hok : n.normalize largeRange.min largeRange.max mode = .ok result) :
    result.mantissa_ ≠ 0 := fun h0 =>
  absurd (normalize_underflow_truth_small n result mode hne hok h0)
    (not_lt.mpr (Number.abs_toRat_ge_min_of_normalized n hn hne))

/-- Magnitude-hypothesis variant of `normalize_ne_zero_of_normalized`, for inputs
that are not themselves 19-digit normalized (the `ofMantissaExp` re-lift). -/
lemma Number.normalize_ne_zero_of_abs_ge (n result : Number) (mode : rounding_mode)
    (hne : n.mantissa_ ≠ 0)
    (hge : (10 : ℚ) ^ (18 : ℕ) * (10 : ℚ) ^ (minExponent : ℤ) ≤ |n.toRat|)
    (hok : n.normalize largeRange.min largeRange.max mode = .ok result) :
    result.mantissa_ ≠ 0 := fun h0 =>
  absurd (normalize_underflow_truth_small n result mode hne hok h0) (not_lt.mpr hge)

/-- **A flushed `ofMantissaExp` output carries the canonical zero exponent.**
Strengthens `ofMantissaExp_exponent_cases`, which leaves the `-100` disjunct
untied to the mantissa. A zero output mantissa can only arise from the
zero-input exit or the `cMinOffset` flush, both returning `IOUAmount.zero`; the
third exit returns a 16-digit-normalized record whose mantissa clears
`cMinValue`, provided the input magnitude clears the 19-digit representable
floor. -/
lemma IOUAmount.ofMantissaExp_zero_exponent (m : Int64) (e : Int) (mode : rounding_mode)
    (i : IOUAmount)
    (hbig : m ≠ 0 →
      (10 : ℚ) ^ (18 : ℕ) * (10 : ℚ) ^ (minExponent : ℤ)
        ≤ (m.toInt.natAbs : ℚ) * (10 : ℚ) ^ e)
    (hok : IOUAmount.ofMantissaExp m e mode = .ok i) (h0 : i.mantissa_ = 0) :
    i.exponent_ = -100 := by
  unfold IOUAmount.ofMantissaExp IOUAmount.normalize at hok
  by_cases hm : (m == 0) = true
  · rw [if_pos hm] at hok
    rw [← Except.ok.inj hok]; rfl
  · rw [if_neg hm] at hok
    have hm_ne : m ≠ 0 := by simpa using hm
    cases hfr : Number.from_rep m e largeRange.min largeRange.max mode with
    | error e' => rw [hfr] at hok; exact absurd hok (by simp)
    | ok v =>
      rw [hfr] at hok
      simp only [] at hok
      cases hfn : IOUAmount.fromNumber v mode with
      | error e' => rw [hfn] at hok; exact absurd hok (by simp)
      | ok r =>
        rw [hfn] at hok
        simp only [] at hok
        by_cases hhi : r.exponent_ > cMaxOffset
        · rw [if_pos hhi] at hok; exact absurd hok (by simp)
        rw [if_neg hhi] at hok
        by_cases hlo : r.exponent_ < cMinOffset
        · rw [if_pos hlo] at hok
          rw [← Except.ok.inj hok]; rfl
        · rw [if_neg hlo] at hok
          exfalso
          have hir : i = r := (Except.ok.inj hok).symm
          have hb : m.toInt.natAbs < 2 ^ 64 := by
            have h1 := Int64.le_toInt m
            have h2 := Int64.toInt_lt m
            omega
          have hmt : m.toInt.natAbs.toUInt64.toNat = m.toInt.natAbs :=
            UInt64.toNat_ofNat_of_lt hb
          have hna_pos : m.toInt.natAbs ≠ 0 := by
            intro hz
            have hz' : m.toInt = 0 := Int.natAbs_eq_zero.mp hz
            exact hm_ne (Int64.toInt_inj.mp (by rw [hz']; decide))
          have hun_ne : (Number.unchecked (m < 0) m.toInt.natAbs.toUInt64 e).mantissa_ ≠ 0 := by
            show m.toInt.natAbs.toUInt64 ≠ 0
            intro hz
            rw [hz] at hmt
            exact hna_pos (by simpa using hmt.symm)
          have hfr' : (Number.unchecked (m < 0) m.toInt.natAbs.toUInt64 e).normalize
              largeRange.min largeRange.max mode = .ok v := hfr
          have hun_abs : |(Number.unchecked (m < 0) m.toInt.natAbs.toUInt64 e).toRat|
              = (m.toInt.natAbs : ℚ) * (10 : ℚ) ^ e := by
            cases hneg : (Number.unchecked (m < 0) m.toInt.natAbs.toUInt64 e).negative_ with
            | false =>
              rw [Number.toRat_of_nonneg _ hneg, abs_of_nonneg (by positivity)]
              show ((m.toInt.natAbs.toUInt64.toNat : ℚ)) * (10 : ℚ) ^ e = _
              rw [hmt]
            | true =>
              rw [Number.toRat_of_neg _ hneg, abs_neg, abs_of_nonneg (by positivity)]
              show ((m.toInt.natAbs.toUInt64.toNat : ℚ)) * (10 : ℚ) ^ e = _
              rw [hmt]
          have hv_ne : v.mantissa_ ≠ 0 :=
            Number.normalize_ne_zero_of_abs_ge _ v mode hun_ne
              (by rw [hun_abs]; exact hbig hm_ne) hfr'
          have hv_norm : v.isNormalized :=
            normalize_result_isNormalized _ v mode hun_ne hfr' hv_ne
          obtain ⟨hvm_lo, hvm_hi⟩ := hv_norm.mantissaBounds_nat hv_ne
          have hexp_lo : minExponent ≤ v.exponent_ := by
            rcases hv_norm with hz | ⟨_, _, _, hlo', _⟩
            · exact absurd (show v.mantissa_ = 0 by rw [hz]; rfl) hv_ne
            · exact hlo'
          unfold IOUAmount.fromNumber at hfn
          cases hnr : v.normalizeToRange cMinValue cMaxValue mode with
          | error e' => rw [hnr] at hfn; exact absurd hfn (by simp)
          | ok me =>
            obtain ⟨mm, ee⟩ := me
            rw [hnr] at hfn
            simp only [] at hfn
            have hrm : r.mantissa_ = mm := by rw [← Except.ok.inj hfn]
            have hexp_hi3 : v.exponent_ + 3 ≤ maxExponent :=
              normalizeToRange_iou_exp_hi v mode mm ee hvm_lo hvm_hi hnr
            obtain ⟨⟨hmlo, -⟩, -, -⟩ :=
              normalizeToRange_iou_ok_facts v mode mm ee hvm_lo hvm_hi (by omega) hexp_hi3 hnr
            have hmm0 : mm = 0 := by rw [← hrm, ← hir]; exact h0
            rw [hmm0] at hmlo
            have : cMinValue.toNat = 10 ^ 15 := by decide
            simp only [this] at hmlo
            exact absurd hmlo (by decide)

/-! ## Canonical-or-zero for a fractional STAmount -/

/-- A deposit-ready fractional amount: fractional type and stored canonically or
zero. The `roundToVaultExponent` fractional pipeline preserves this. -/
def STAmount.FracCanonZero (s : STAmount) : Prop :=
  s.mNumericType = .fractional ∧ (s.IOUCanonical ∨ s.mValue = 0)

/-- `canonicalize` on a fractional record yields a `FracCanonZero` result: the IOU
branch routes `iou → ofMantissaExp → normalize`, whose output is `InRange16`-or-zero
(`normalize_InRange16_or_zero`), and the packed record keeps the fractional type. -/
lemma STAmount.canonicalize_fczr (s result : STAmount) (mode : rounding_mode)
    (hfr : s.mNumericType = .fractional) (hok : s.canonicalize mode = .ok result) :
    result.FracCanonZero := by
  have hint : ¬ s.integral = true := by unfold STAmount.integral; rw [hfr]; decide
  unfold STAmount.canonicalize at hok
  rw [if_neg hint] at hok
  have hiou : s.iou mode = IOUAmount.normalize ⟨s.signedDrops.toInt64, s.mOffset⟩ mode := by
    unfold STAmount.iou IOUAmount.ofMantissaExp; rw [if_neg hint]
  rw [hiou] at hok
  cases hnorm : IOUAmount.normalize ⟨s.signedDrops.toInt64, s.mOffset⟩ mode with
  | error e => rw [hnorm] at hok; exact absurd hok (by simp)
  | ok i =>
    rw [hnorm] at hok
    simp only [] at hok
    have hres : result = { s with
        mValue := (if i.signum < 0 then -i.mantissa_ else i.mantissa_).toUInt64,
        mOffset := i.exponent_,
        mIsNegative := decide (i.signum < 0) } := (Except.ok.inj hok).symm
    have hnt : result.mNumericType = .fractional := by rw [hres]; exact hfr
    refine ⟨hnt, ?_⟩
    rcases IOUAmount.normalize_InRange16_or_zero _ mode i hnorm with hr | hz
    · left
      have h_fit : i.mantissa_.toInt.natAbs < 2 ^ 63 := by have := hr.mant_hi; omega
      have h_absToNat := IOUAmount.absMant_toNat i h_fit
      refine ⟨hnt, ?_, ?_, ?_, ?_⟩
      · show 10 ^ 15 ≤ result.mValue.toNat
        rw [hres]
        show 10 ^ 15 ≤ (if i.signum < 0 then -i.mantissa_ else i.mantissa_).toUInt64.toNat
        rw [h_absToNat]; exact hr.mant_lo
      · show result.mValue.toNat < 10 ^ 16
        rw [hres]
        show (if i.signum < 0 then -i.mantissa_ else i.mantissa_).toUInt64.toNat < 10 ^ 16
        rw [h_absToNat]; exact hr.mant_hi
      · show (-96 : ℤ) ≤ result.mOffset
        rw [hres]; exact hr.exp_lo
      · show result.mOffset ≤ 80
        rw [hres]; exact hr.exp_hi
    · right
      show result.mValue = 0
      rw [hres]
      show (if i.signum < 0 then -i.mantissa_ else i.mantissa_).toUInt64 = 0
      rw [hz]; split <;> decide

/-- **A flushed fractional `canonicalize` output carries the canonical zero
offset.** Strengthens `canonicalize_fractional_offset` by tying its `-100`
disjunct to the mantissa, which is what lets the post-sum grid step be bounded.
`hbig` says the packed magnitude clears the 19-digit representable floor; it is
discharged from `isNormalized` at the `ofNumber` level. -/
lemma STAmount.canonicalize_fractional_zero_offset (s result : STAmount) (mode : rounding_mode)
    (hfr : s.mNumericType = .fractional)
    (hsz : s.mValue.toNat < 10 ^ 16)
    (hbig : s.mValue ≠ 0 →
      (10 : ℚ) ^ (18 : ℕ) * (10 : ℚ) ^ (minExponent : ℤ)
        ≤ (s.mValue.toNat : ℚ) * (10 : ℚ) ^ s.mOffset)
    (hok : s.canonicalize mode = .ok result)
    (h0 : result.mValue = 0) :
    result.mOffset = -100 := by
  have hint : ¬ s.integral = true := by unfold STAmount.integral; rw [hfr]; decide
  unfold STAmount.canonicalize at hok
  rw [if_neg hint] at hok
  have hiou : s.iou mode = IOUAmount.ofMantissaExp s.signedDrops.toInt64 s.mOffset mode := by
    unfold STAmount.iou; rw [if_neg hint]
  rw [hiou] at hok
  cases hone : IOUAmount.ofMantissaExp s.signedDrops.toInt64 s.mOffset mode with
  | error e => rw [hone] at hok; exact absurd hok (by simp)
  | ok i =>
    rw [hone] at hok
    simp only [] at hok
    have heq := Except.ok.inj hok
    have hres : result.mOffset = i.exponent_ := by rw [← heq]
    have hresv : result.mValue
        = (if i.signum < 0 then -i.mantissa_ else i.mantissa_).toUInt64 := by rw [← heq]
    have hsd : s.signedDrops.toInt64.toInt = s.signedDrops :=
      STAmount.signedDrops_toInt64_toInt s hsz
    have hna : s.signedDrops.toInt64.toInt.natAbs = s.mValue.toNat := by
      rw [hsd]; unfold STAmount.signedDrops; split <;> omega
    have hone' : IOUAmount.normalize ⟨s.signedDrops.toInt64, s.mOffset⟩ mode = .ok i := hone
    rcases IOUAmount.normalize_InRange16_or_zero _ mode i hone' with hr | hz
    · -- a 16-digit-canonical output has a nonzero magnitude, contradicting `h0`
      exfalso
      have h_fit : i.mantissa_.toInt.natAbs < 2 ^ 63 := by have := hr.mant_hi; omega
      have h_absToNat := IOUAmount.absMant_toNat i h_fit
      have hval : result.mValue.toNat = i.mantissa_.toInt.natAbs := by rw [hresv, h_absToNat]
      rw [h0] at hval
      have hlo := hr.mant_lo
      simp only [UInt64.toNat_ofNat] at hval
      omega
    · rw [hres]
      refine IOUAmount.ofMantissaExp_zero_exponent _ s.mOffset mode i ?_ hone hz
      intro hm
      rw [hna]
      refine hbig ?_
      intro hzv
      apply hm
      have hsz0 : s.signedDrops = 0 := by
        unfold STAmount.signedDrops; rw [hzv]; split <;> simp
      rw [hsz0]; rfl

/-- **A flushed fractional `ofNumber` output carries the canonical zero offset.**
The `-100` disjunct of `ofNumber_fractional_offset`, now tied to the mantissa. A
normalized nonzero operand clears the 19-digit representable floor, so the only
way to a zero output is one of the two exits that return `IOUAmount.zero`. -/
lemma STAmount.ofNumber_iou_zero_offset (n : Number) (mode : rounding_mode) (A : STAmount)
    (hn : n.isNormalized)
    (hok : STAmount.ofNumber .fractional n mode = .ok A)
    (h0 : A.mValue = 0) : A.mOffset = -100 := by
  by_cases hmz : n.mantissa_ = 0
  · -- a normalized zero-mantissa operand is `Number.zero`, which packs to the
    -- canonical zero record
    rw [Number.eq_zero_of_mantissa_zero n hn hmz] at hok
    rw [show STAmount.ofNumber .fractional Number.zero mode
        = .ok ⟨.fractional, 0, -100, false⟩ from by cases mode <;> rfl] at hok
    rw [← Except.ok.inj hok]
  have hne : n.mantissa_ ≠ 0 := hmz
  obtain ⟨hm_lo, hm_hi⟩ := hn.mantissaBounds_nat hne
  have hexp_lo : minExponent ≤ n.exponent_ := by
    rcases hn with hz | ⟨_, _, _, hlo, _⟩
    · exact absurd (show n.mantissa_ = 0 by rw [hz]; rfl) hne
    · exact hlo
  unfold STAmount.ofNumber at hok
  rw [if_neg (by decide : ¬ NumericType.fractional.isIntegral = true)] at hok
  set w : Number := if decide (n.signum < 0) = true then n.operator_neg else n with hw_def
  have hw_mant : w.mantissa_ = n.mantissa_ := by
    rw [hw_def]; split
    · exact Number.operator_neg_mantissa_of_ne n hne
    · rfl
  have hw_exp : w.exponent_ = n.exponent_ := by
    rw [hw_def]; split
    · unfold Number.operator_neg; rw [if_neg (by simpa using hne)]
    · rfl
  have hw_neg : w.negative_ = false := by
    rw [hw_def]; split
    · rename_i hc
      rw [Number.signum_neg_decide] at hc
      rw [Number.operator_neg_negative_of_ne n hne, hc]; rfl
    · rename_i hc
      rw [Number.signum_neg_decide] at hc
      simpa using hc
  have hw_lo : 10 ^ 18 ≤ w.mantissa_.toNat := by rw [hw_mant]; exact hm_lo
  have hw_hi : w.mantissa_.toNat < 10 ^ 19 := by rw [hw_mant]; exact hm_hi
  cases hnr : w.normalizeToRange kMinValue kMaxValue mode with
  | error e => rw [hnr] at hok; exact absurd hok (by simp)
  | ok me =>
    obtain ⟨mant, exp⟩ := me
    rw [hnr] at hok
    simp only [] at hok
    rw [STAmount.checked] at hok
    have hnr' : w.normalizeToRange cMinValue cMaxValue mode = .ok (mant, exp) := hnr
    have hexp_hi3 : w.exponent_ + 3 ≤ maxExponent :=
      normalizeToRange_iou_exp_hi w mode mant exp hw_lo hw_hi hnr'
    obtain ⟨⟨hmlo, hmhi⟩, ⟨hexp_lo3, -⟩, hsgn⟩ :=
      normalizeToRange_iou_ok_facts w mode mant exp hw_lo hw_hi (by omega) hexp_hi3 hnr'
    have hmant_pos : 0 ≤ mant.toInt := hsgn hw_neg
    have hmant_natAbs : mant.toInt.natAbs = mant.toUInt64.toNat := by
      have := toUInt64_toNat_of_nonneg mant hmant_pos; omega
    refine STAmount.canonicalize_fractional_zero_offset _ A mode rfl ?_ ?_ hok h0
    · -- the packed magnitude is a 16-digit mantissa
      show mant.toUInt64.toNat < 10 ^ 16
      rw [← hmant_natAbs]
      have hcmax : cMaxValue.toNat = 10 ^ 16 - 1 := by decide
      rw [hcmax] at hmhi; omega
    · -- and it clears the 19-digit representable floor
      intro _
      show (10 : ℚ) ^ (18 : ℕ) * (10 : ℚ) ^ (minExponent : ℤ)
        ≤ ((mant.toUInt64.toNat : ℕ) : ℚ) * (10 : ℚ) ^ exp
      have hcmin : cMinValue.toNat = 10 ^ 15 := by decide
      rw [hcmin] at hmlo
      have hmlo' : (10 : ℚ) ^ (15 : ℕ) ≤ ((mant.toUInt64.toNat : ℕ) : ℚ) := by
        rw [← hmant_natAbs]; exact_mod_cast hmlo
      have hstep : minExponent + 3 ≤ exp := by rw [hw_exp] at hexp_lo3; omega
      have hz1 : (10 : ℚ) ^ ((minExponent + 3 : ℤ)) ≤ (10 : ℚ) ^ exp :=
        zpow_le_zpow_right₀ (by norm_num) hstep
      have hprod : (10 : ℚ) ^ (18 : ℕ) * (10 : ℚ) ^ (minExponent : ℤ)
          = (10 : ℚ) ^ (15 : ℕ) * (10 : ℚ) ^ ((minExponent + 3 : ℤ)) := by
        rw [show ((10 : ℚ) ^ (18 : ℕ)) = (10 : ℚ) ^ ((18 : ℤ)) from by norm_num,
          show ((10 : ℚ) ^ (15 : ℕ)) = (10 : ℚ) ^ ((15 : ℤ)) from by norm_num,
          ← zpow_add₀ (by norm_num : (10 : ℚ) ≠ 0),
          ← zpow_add₀ (by norm_num : (10 : ℚ) ≠ 0)]
        congr 1
        try omega
      rw [hprod]
      calc (10 : ℚ) ^ (15 : ℕ) * (10 : ℚ) ^ ((minExponent + 3 : ℤ))
          ≤ ((mant.toUInt64.toNat : ℕ) : ℚ) * (10 : ℚ) ^ ((minExponent + 3 : ℤ)) :=
            mul_le_mul_of_nonneg_right hmlo' (le_of_lt (zpow_pos (by norm_num) _))
        _ ≤ ((mant.toUInt64.toNat : ℕ) : ℚ) * (10 : ℚ) ^ exp :=
            mul_le_mul_of_nonneg_left hz1 (by positivity)

/-- `ofIOUAmount` canonicalizes a fractional record, so its output is
`FracCanonZero`. -/
lemma STAmount.ofIOUAmount_fczr (a : IOUAmount) (mode : rounding_mode) (result : STAmount)
    (hok : STAmount.ofIOUAmount a mode = .ok result) : result.FracCanonZero := by
  unfold STAmount.ofIOUAmount at hok
  exact STAmount.canonicalize_fczr _ result mode rfl hok

/-- Negation preserves `FracCanonZero`: it flips only the sign flag (or is the
identity on zero), leaving the type, magnitude, and exponent untouched. -/
lemma STAmount.operator_neg_fczr (s : STAmount) (h : s.FracCanonZero) :
    s.operator_neg.FracCanonZero := by
  obtain ⟨hnt, hcz⟩ := h
  unfold STAmount.operator_neg
  by_cases hz : s.mValue = 0
  · rw [if_pos (beq_iff_eq.mpr hz)]; exact ⟨hnt, hcz⟩
  · rw [if_neg (fun hb => hz (beq_iff_eq.mp hb))]
    refine ⟨hnt, ?_⟩
    rcases hcz with hc | hcv
    · exact Or.inl ⟨hnt, hc.mant_lo, hc.mant_hi, hc.exp_lo, hc.exp_hi⟩
    · exact Or.inr hcv

/-- `operator_add` of a `FracCanonZero` first operand is `FracCanonZero`: the
`v2 = 0` branch returns the operand, and both other reachable branches
(`v1 = 0` and the IOU add) canonicalize a fractional record. -/
lemma STAmount.operator_add_fczr (v1 v2 result : STAmount) (mode : rounding_mode)
    (h1 : v1.FracCanonZero) (hok : STAmount.operator_add v1 v2 mode = .ok result) :
    result.FracCanonZero := by
  obtain ⟨h1nt, h1cz⟩ := h1
  have hint1 : ¬ v1.integral = true := by unfold STAmount.integral; rw [h1nt]; decide
  unfold STAmount.operator_add at hok
  cases hcmp : STAmount.areComparable v1 v2 with
  | false => rw [if_pos (by rw [hcmp]; decide)] at hok; exact absurd hok (by simp)
  | true =>
    rw [if_neg (by rw [hcmp]; decide)] at hok
    by_cases hv2 : v2.mValue = 0
    · rw [if_pos (beq_iff_eq.mpr hv2)] at hok
      rw [← Except.ok.inj hok]; exact ⟨h1nt, h1cz⟩
    · rw [show (v2.mValue == 0) = false from beq_eq_false_iff_ne.mpr hv2] at hok
      simp only [Bool.false_eq_true, if_false] at hok
      by_cases hv1 : v1.mValue = 0
      · rw [if_pos (beq_iff_eq.mpr hv1)] at hok
        rw [STAmount.checked] at hok
        exact STAmount.canonicalize_fczr _ result mode
          (show (STAmount.unchecked v1.mNumericType v2.mValue v2.mOffset
            v2.mIsNegative).mNumericType = .fractional from h1nt) hok
      · rw [show (v1.mValue == 0) = false from beq_eq_false_iff_ne.mpr hv1] at hok
        simp only [Bool.false_eq_true, if_false] at hok
        rw [if_neg hint1] at hok
        cases hi1 : v1.iou mode with
        | error e => rw [hi1] at hok; exact absurd hok (by simp)
        | ok i1 =>
          rw [hi1] at hok; simp only [] at hok
          cases hi2 : v2.iou mode with
          | error e => rw [hi2] at hok; exact absurd hok (by simp)
          | ok i2 =>
            rw [hi2] at hok; simp only [] at hok
            cases hadd : IOUAmount.operator_add i1 i2 mode with
            | error e => rw [hadd] at hok; exact absurd hok (by simp)
            | ok sumI =>
              rw [hadd] at hok; simp only [] at hok
              exact STAmount.ofIOUAmount_fczr sumI mode result hok

/-- `operator_sub` of a `FracCanonZero` first operand is `FracCanonZero`
(it is `operator_add` against the negated second operand). -/
lemma STAmount.operator_sub_fczr (v1 v2 result : STAmount) (mode : rounding_mode)
    (h1 : v1.FracCanonZero) (hok : STAmount.operator_sub v1 v2 mode = .ok result) :
    result.FracCanonZero := by
  unfold STAmount.operator_sub at hok
  exact STAmount.operator_add_fczr v1 v2.operator_neg result mode h1 hok

/-- `roundToExponent` of a `FracCanonZero` value is `FracCanonZero`: the three
early exits pass the value through, and the general path is
`operator_sub (operator_add value reference) reference`, each preserving the
predicate (the reference is a fractional `checked`). -/
lemma STAmount.roundToExponent_fczr (value result : STAmount) (scale : Int)
    (rounding : rounding_mode) (h : value.FracCanonZero)
    (hok : STAmount.roundToExponent value scale rounding = .ok result) :
    result.FracCanonZero := by
  obtain ⟨hnt, hcz⟩ := h
  have hint : ¬ value.integral = true := by unfold STAmount.integral; rw [hnt]; decide
  unfold STAmount.roundToExponent at hok
  rw [if_neg hint] at hok
  by_cases hz : value.isZero = true
  · rw [if_pos hz] at hok; rw [← Except.ok.inj hok]; exact ⟨hnt, hcz⟩
  · rw [if_neg hz] at hok
    by_cases hge : value.exponent ≥ scale
    · rw [if_pos hge] at hok; rw [← Except.ok.inj hok]; exact ⟨hnt, hcz⟩
    · rw [if_neg hge] at hok
      cases href : STAmount.checked value.mNumericType kMinValue scale value.negative rounding with
      | error e => rw [href] at hok; exact absurd hok (by simp)
      | ok referenceValue =>
        rw [href] at hok; simp only [] at hok
        cases hsum : STAmount.operator_add value referenceValue rounding with
        | error e => rw [hsum] at hok; exact absurd hok (by simp)
        | ok sum =>
          rw [hsum] at hok; simp only [] at hok
          have hsum_fczr : sum.FracCanonZero :=
            STAmount.operator_add_fczr value referenceValue sum rounding ⟨hnt, hcz⟩ hsum
          exact STAmount.operator_sub_fczr sum referenceValue result rounding hsum_fczr hok

/-- `ofNumber` on the fractional type packs its result through `checked`, whose
`canonicalize` output is `FracCanonZero`. -/
lemma STAmount.ofNumber_fczr (n : Number) (mode : rounding_mode) (result : STAmount)
    (hok : STAmount.ofNumber .fractional n mode = .ok result) : result.FracCanonZero := by
  unfold STAmount.ofNumber at hok
  simp only [show NumericType.fractional.isIntegral = false from rfl, Bool.false_eq_true,
    if_false] at hok
  split at hok
  · exact absurd hok (by simp)
  · rw [STAmount.checked] at hok
    exact STAmount.canonicalize_fczr _ result mode rfl hok

/-- **The post-sum clamp keeps a fractional delta `FracCanonZero`.** The negative
branch rounds the magnitude with `roundToExponent`, the positive one repacks the
recovered difference with `ofNumber`; both canonicalize their output. -/
lemma clampToSumExponent_fczr (amount : Number) (delta c : STAmount)
    (hd : delta.FracCanonZero)
    (hok : clampToSumExponent amount delta = .ok c) : c.FracCanonZero := by
  have hint : ¬ delta.integral = true := by
    unfold STAmount.integral; rw [hd.1]; decide
  unfold clampToSumExponent at hok
  simp only [] at hok
  rw [if_neg hint] at hok
  simp only [pure_bind] at hok
  obtain ⟨pe, -, hok⟩ := XRPL.Model.SingleAssetVault.bind_ok_peel _ _ _ hok
  have habs : (if delta.negative = true then delta.operator_neg else delta).FracCanonZero := by
    split
    · exact STAmount.operator_neg_fczr delta hd
    · exact hd
  by_cases hneg : delta.negative = true
  · rw [if_pos hneg] at hok
    exact STAmount.roundToExponent_fczr _ c pe .downward habs hok
  · rw [if_neg hneg] at hok
    obtain ⟨sum, -, hok⟩ := XRPL.Model.SingleAssetVault.bind_ok_peel _ _ _ hok
    obtain ⟨ada, -, hok⟩ := XRPL.Model.SingleAssetVault.bind_ok_peel _ _ _ hok
    exact STAmount.ofNumber_fczr ada .to_nearest c
      (by rw [show delta.numericType = .fractional from hd.1] at hok; exact hok)

/-- **The post-sum clamp preserves canonical-or-zero storage.** The integral pass
is the identity on a sign-cleared amount; the fractional pass canonicalizes. -/
lemma clampToSumExponent_exactCanonical_or_zero (amount : Number) (a c : STAmount)
    (ha : a.ExactCanonical ∨ (a.mNumericType = .fractional ∧ a.mValue = 0))
    (hsgn : a.mValue = 0 ∨ a.mIsNegative = false)
    (hok : clampToSumExponent amount a = .ok c) :
    c.ExactCanonical ∨ (c.mNumericType = .fractional ∧ c.mValue = 0) := by
  by_cases hint : a.integral = true
  · rw [XRPL.Model.SingleAssetVault.clampToSumExponent_integral_pos amount a hint hsgn] at hok
    rw [← Except.ok.inj hok]; exact ha
  · have hnt : a.mNumericType = .fractional := by
      cases h : a.mNumericType with
      | fractional => rfl
      | integral mv mo ms msh =>
        exact absurd (show a.integral = true from by unfold STAmount.integral; rw [h]; rfl) hint
    have hiou : a.IOUCanonical ∨ a.mValue = 0 := by
      rcases ha with hec | ⟨-, h0⟩
      · rcases hec with hio | ⟨hic, -⟩
        · exact Or.inl hio
        · exact absurd (show a.integral = true from hic.is_integral) hint
      · exact Or.inr h0
    obtain ⟨hntc, hczc⟩ := clampToSumExponent_fczr amount a c ⟨hnt, hiou⟩ hok
    rcases hczc with hio | h0
    · exact Or.inl (Or.inl hio)
    · exact Or.inr ⟨hntc, h0⟩

/-- **`toNumber` is value-exact and normalized on a canonical-or-fractional-zero
amount.** Dispatches `toNumber_exact_canonical` and `toNumber_zero_fractional`. -/
lemma STAmount.toNumber_exact_of_ecz (a : STAmount) (cN : Number)
    (hecz : a.ExactCanonical ∨ (a.mNumericType = .fractional ∧ a.mValue = 0))
    (hcN : a.toNumber .to_nearest = .ok cN) :
    cN.toRat = a.toRat ∧ cN.isNormalized := by
  rcases hecz with hexact | ⟨hnt, h0⟩
  · obtain ⟨an, han, hval, hnorm⟩ := STAmount.toNumber_exact_canonical a .to_nearest hexact
    have hcNeq : an = cN := by rw [han] at hcN; exact Except.ok.inj hcN
    rw [← hcNeq]; exact ⟨hval, hnorm⟩
  · have hafr : a.integral = false := by
      show a.mNumericType.isIntegral = false
      rw [hnt]; rfl
    have hczero := STAmount.toNumber_zero_fractional a .to_nearest hafr h0
    have hcNeq : cN = Number.zero := by rw [hczero] at hcN; exact (Except.ok.inj hcN).symm
    subst hcNeq
    refine ⟨?_, Or.inl rfl⟩
    rw [Number.toRat_zero, STAmount.toRat_signed, h0]; simp

/-- `operator_neg` only flips the sign bit, and the canonical-storage predicates
read `mNumericType`/`mValue`/`mOffset`, so it preserves them. -/
lemma STAmount.operator_neg_ecz (a : STAmount)
    (ha : a.ExactCanonical ∨ (a.mNumericType = .fractional ∧ a.mValue = 0)) :
    a.operator_neg.ExactCanonical ∨
      (a.operator_neg.mNumericType = .fractional ∧ a.operator_neg.mValue = 0) := by
  have hnt := STAmount.operator_neg_mNumericType a
  have hmv := STAmount.operator_neg_mValue a
  have hof := STAmount.operator_neg_mOffset a
  rcases ha with hec | ⟨h1, h2⟩
  · refine Or.inl ?_
    rcases hec with hio | ⟨hic, hsz⟩
    · exact Or.inl ⟨by rw [hnt]; exact hio.is_fractional, by rw [hmv]; exact hio.mant_lo,
        by rw [hmv]; exact hio.mant_hi, by rw [hof]; exact hio.exp_lo,
        by rw [hof]; exact hio.exp_hi⟩
    · exact Or.inr ⟨⟨by rw [hnt]; exact hic.is_integral, by rw [hof]; exact hic.offset_zero,
        by rw [hmv, hnt]; exact hic.in_range⟩, by rw [hmv]; exact hsz⟩
  · exact Or.inr ⟨by rw [hnt]; exact h1, by rw [hmv]; exact h2⟩

/-- **The post-sum clamp of a negative delta stores canonically or as a fractional
zero.** Mirror of `clampToSumExponent_exactCanonical_or_zero` for the withdraw and
clawback direction, which clamps `payout.operator_neg`.

No sign hypothesis: the integral branch is the clamp's identity on the *magnitude*
(`clampToSumExponent_integral`), and both of its outcomes -- `a` itself or its
negation -- keep the canonical storage shape. -/
lemma clampToSumExponent_neg_exactCanonical_or_zero (amount : Number) (a c : STAmount)
    (ha : a.ExactCanonical ∨ (a.mNumericType = .fractional ∧ a.mValue = 0))
    (hok : clampToSumExponent amount a.operator_neg = .ok c) :
    c.ExactCanonical ∨ (c.mNumericType = .fractional ∧ c.mValue = 0) := by
  by_cases hint : a.integral = true
  · have hnegint : a.operator_neg.integral = true := by
      show a.operator_neg.mNumericType.isIntegral = true
      rw [STAmount.operator_neg_mNumericType]; exact hint
    rw [XRPL.Model.SingleAssetVault.clampToSumExponent_integral amount a.operator_neg
      hnegint] at hok
    rw [← Except.ok.inj hok]
    split
    · rw [XRPL.Model.SingleAssetVault.STAmount.operator_neg_neg]; exact ha
    · exact STAmount.operator_neg_ecz a ha
  · have hnt : a.mNumericType = .fractional := by
      cases h : a.mNumericType with
      | fractional => rfl
      | integral mv mo ms msh =>
        exact absurd (show a.integral = true from by unfold STAmount.integral; rw [h]; rfl) hint
    have hiou : a.IOUCanonical ∨ a.mValue = 0 := by
      rcases ha with hec | ⟨-, h0⟩
      · rcases hec with hio | ⟨hic, -⟩
        · exact Or.inl hio
        · exact absurd (show a.integral = true from hic.is_integral) hint
      · exact Or.inr h0
    obtain ⟨hntc, hczc⟩ := clampToSumExponent_fczr amount a.operator_neg c
      (STAmount.operator_neg_fczr a ⟨hnt, hiou⟩) hok
    rcases hczc with hio | h0
    · exact Or.inl (Or.inl hio)
    · exact Or.inr ⟨hntc, h0⟩

/-- A zero-mantissa `Number` renormalizes to the zero `IOUAmount`. (The version in
`RoundToScale.Common.Proofs` is `private`, so it is reproven here.) -/
private lemma IOUAmount.ofNumber_zero_mant (n : Number) (mode : rounding_mode)
    (h : n.mantissa_ = 0) :
    IOUAmount.ofNumber n mode = .ok IOUAmount.zero := by
  have hd : doNormalize n.negative_ n.mantissa_ n.exponent_ cMinValue cMaxValue mode
      = .ok Number.zero := by
    unfold doNormalize
    rw [show (n.mantissa_ == 0) = true from beq_iff_eq.mpr h, if_pos rfl]
  unfold IOUAmount.ofNumber IOUAmount.fromNumber Number.normalizeToRange
  rw [hd]
  rfl

/-- `ofIOUAmount` of the zero `IOUAmount` is the canonical zero record. (The version
in `RoundToScale.Common.Proofs` is `private`, so it is reproven here.) -/
private lemma STAmount.ofIOU_zero_rec (mode : rounding_mode) :
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

/-- **The downward `roundToExponent` of a nonnegative value is nonnegative.** The
early exits pass the value through (already nonnegative); the truncation path
floors `value` onto the `10 ^ s` grid, and the floor of a nonnegative value is
nonnegative (`0` is a grid point below it), so the stored result never goes
negative. Uses only the `[-96, 80]` scale range (available from `IOUCanonical`),
never the tighter `-81` the exact-floor characterization needs. -/
theorem STAmount.roundToExponent_downward_nonneg (value result : STAmount) (s : ℤ)
    (hc : value.IOUCanonical) (hs_lo : (-96 : ℤ) ≤ s) (hs_hi : s ≤ 80)
    (hnn : 0 ≤ value.toRat)
    (hok : STAmount.roundToExponent value s .downward = .ok result) :
    0 ≤ result.toRat := by
  have h_int : value.integral = false := by
    unfold STAmount.integral; rw [hc.is_fractional]; rfl
  have h_mv_ne : value.mValue ≠ 0 := by
    intro h0; have h1 : value.mValue.toNat = 0 := by rw [h0]; rfl
    have := hc.mant_lo; omega
  have hpos : 0 < value.toRat :=
    lt_of_le_of_ne hnn (Ne.symm (STAmount.toRat_ne_zero value h_mv_ne))
  have hneg : value.mIsNegative = false := by
    rcases hb : value.mIsNegative with _ | _
    · rfl
    · exfalso
      have hsigned := STAmount.toRat_signed value
      rw [hb] at hsigned
      have hm : (0 : ℚ) ≤ (value.mValue.toNat : ℚ) * 10 ^ value.mOffset := by positivity
      rw [hsigned] at hpos
      simp only [if_true] at hpos
      nlinarith [hpos, hm]
  have h_notZero : ¬ value.isZero = true := by
    unfold STAmount.isZero; rw [beq_eq_false_iff_ne.mpr h_mv_ne]; exact Bool.false_ne_true
  unfold STAmount.roundToExponent at hok
  rw [if_neg (by rw [h_int]; exact Bool.false_ne_true), if_neg h_notZero] at hok
  by_cases h_exp : value.exponent ≥ s
  · rw [if_pos h_exp] at hok; rw [← Except.ok.inj hok]; exact hnn
  · rw [if_neg h_exp] at hok
    push_neg at h_exp
    have h_ev : value.mOffset < s := h_exp
    have href_eq : STAmount.checked value.mNumericType kMinValue s value.negative .downward
        = .ok ⟨value.mNumericType, kMinValue, s, value.mIsNegative⟩ := by
      rw [hc.is_fractional]
      exact STAmount.checked_reference s value.mIsNegative .downward hs_lo hs_hi
    cases href : STAmount.checked value.mNumericType kMinValue s value.negative .downward with
    | error e => rw [href_eq] at href; exact absurd href (by simp)
    | ok referenceValue =>
      rw [href] at hok
      simp only [] at hok
      have hrefeq : referenceValue = ⟨value.mNumericType, kMinValue, s, value.mIsNegative⟩ := by
        rw [href_eq] at href; exact (Except.ok.inj href).symm
      subst hrefeq
      set refA : STAmount := ⟨value.mNumericType, kMinValue, s, value.mIsNegative⟩ with hrefA_def
      cases hsum : STAmount.operator_add value refA .downward with
      | error e => rw [hsum] at hok; exact absurd hok (by simp)
      | ok sum =>
        rw [hsum] at hok
        simp only [] at hok
        obtain ⟨k, hk_le, h_sum_asset, h_sum_mv, h_sum_off, h_sum_neg, _, _, _, _⟩ :=
          STAmount.roundToExponent_sum_spec value s .downward hc h_ev hs_lo hs_hi sum hsum
        have h_kMin_toNat : kMinValue.toNat = 10 ^ 15 := by decide
        have hc_sum : sum.IOUCanonical :=
          { is_fractional := by rw [h_sum_asset]; exact hc.is_fractional
            mant_lo := by rw [h_sum_mv]; omega
            mant_hi := by rw [h_sum_mv]; omega
            exp_lo := by rw [h_sum_off]; omega
            exp_hi := by rw [h_sum_off]; exact hs_hi }
        have hc_refA : refA.IOUCanonical :=
          { is_fractional := by rw [hrefA_def]; exact hc.is_fractional
            mant_lo := by rw [hrefA_def]; show 10 ^ 15 ≤ kMinValue.toNat; omega
            mant_hi := by rw [hrefA_def]; show kMinValue.toNat < 10 ^ 16; rw [h_kMin_toNat]; norm_num
            exp_lo := by rw [hrefA_def]; show (-96 : ℤ) ≤ s; omega
            exp_hi := by rw [hrefA_def]; exact hs_hi }
        have h_pow_s_pos : (0 : ℚ) < (10 : ℚ) ^ s := zpow_pos (by norm_num) _
        have hsum_val : sum.toRat = ((10 ^ 15 + k : ℕ) : ℚ) * 10 ^ s := by
          rw [STAmount.toRat_signed, h_sum_neg, hneg, h_sum_off, h_sum_mv]
          push_cast; ring
        have hrefA_val : refA.toRat = (10 ^ 15 : ℚ) * 10 ^ s := by
          rw [hrefA_def, STAmount.toRat_signed]
          show (if value.mIsNegative then (-1 : ℚ) else 1) * (kMinValue.toNat : ℚ) * 10 ^ s = _
          rw [hneg, h_kMin_toNat]; push_cast; ring
        have htruth : sum.toRat - refA.toRat = (k : ℚ) * 10 ^ s := by
          rw [hsum_val, hrefA_val]; push_cast; ring
        by_cases hrv : result.mValue = 0
        · rw [STAmount.toRat_signed, show result.mValue.toNat = 0 from by rw [hrv]; rfl]; simp
        · by_cases hk0 : k = 0
          · -- exact cancellation: `k = 0` forces `sum = refA`, so `operator_sub sum refA` is a
            -- self-difference and flushes to the canonical zero, contradicting `result.mValue ≠ 0`.
            exfalso
            have hmv_eq : sum.mValue = kMinValue :=
              UInt64.toNat_inj.mp (by rw [h_sum_mv, hk0, h_kMin_toNat, Nat.add_zero])
            have hsum_eq : sum = refA := by
              rw [hrefA_def]
              have hsum_eta : sum
                  = ⟨sum.mNumericType, sum.mValue, sum.mOffset, sum.mIsNegative⟩ := rfl
              rw [hsum_eta, h_sum_asset, hmv_eq, h_sum_off, h_sum_neg]
            rw [hsum_eq] at hok
            exact hrv (STAmount.operator_sub_self_zero refA result .downward hc_refA hok)
          · have hk1 : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr hk0
            have htruth_pos : 0 < sum.toRat - refA.toRat := by
              rw [htruth]
              have hkq : (1 : ℚ) ≤ (k : ℚ) := by exact_mod_cast hk1
              have : (0 : ℚ) < (k : ℚ) := by linarith
              positivity
            have hrw := STAmount.operator_sub_rounds_iou_downward sum refA result hc_sum hc_refA
              (ne_of_gt htruth_pos) hok hrv
            obtain ⟨_, hgap⟩ := hrw
            have hgap2 : (sum.toRat - refA.toRat) - result.toRat
                ≤ |sum.toRat - refA.toRat| * IOUAmount.εDirected := hgap
            rw [abs_of_pos htruth_pos] at hgap2
            have hεlt : IOUAmount.εDirected < 1 := by
              have h1 : (10 : ℚ) ^ (-15 : ℤ) = 1 / 10 ^ 15 := by
                rw [show ((-15) : ℤ) = -(15 : ℕ) from rfl, zpow_neg, zpow_natCast]; norm_num
              show 11 / (2 ^ 63 - 18 : ℚ) + (10 : ℚ) ^ (-15 : ℤ)
                + 11 / (2 ^ 63 - 18 : ℚ) * (10 : ℚ) ^ (-15 : ℤ) < 1
              rw [h1]; norm_num
            have hε1 : (0 : ℚ) < 1 - IOUAmount.εDirected := by linarith [hεlt]
            have hlb : (sum.toRat - refA.toRat) - (sum.toRat - refA.toRat) * IOUAmount.εDirected
                ≤ result.toRat := by linarith [hgap2]
            have hpos_lb : 0 < (sum.toRat - refA.toRat)
                - (sum.toRat - refA.toRat) * IOUAmount.εDirected := by
              nlinarith [mul_pos htruth_pos hε1]
            linarith [hlb, hpos_lb]

/-- **`roundToExponent` downward never raises the value.** The truncating
`.downward` pass keeps a nonnegative amount at or below its input: it rounds
`value.toRat` down onto the `10^s` grid (`⌊value/10^s⌋·10^s ≤ value`), and the
internal `reference + sub` rounds down again, so `result.toRat ≤ value.toRat`.
Works across the full `[-96, 80]` scale range (no `-81` grid-exactness needed). -/
theorem STAmount.roundToExponent_downward_le (value result : STAmount) (s : ℤ)
    (hc : value.IOUCanonical) (hs_lo : (-96 : ℤ) ≤ s) (hs_hi : s ≤ 80)
    (hnn : 0 ≤ value.toRat)
    (hok : STAmount.roundToExponent value s .downward = .ok result) :
    result.toRat ≤ value.toRat := by
  have h_int : value.integral = false := by
    unfold STAmount.integral; rw [hc.is_fractional]; rfl
  have h_mv_ne : value.mValue ≠ 0 := by
    intro h0; have h1 : value.mValue.toNat = 0 := by rw [h0]; rfl
    have := hc.mant_lo; omega
  have hpos : 0 < value.toRat :=
    lt_of_le_of_ne hnn (Ne.symm (STAmount.toRat_ne_zero value h_mv_ne))
  have hneg : value.mIsNegative = false := by
    rcases hb : value.mIsNegative with _ | _
    · rfl
    · exfalso
      have hsigned := STAmount.toRat_signed value
      rw [hb] at hsigned
      have hm : (0 : ℚ) ≤ (value.mValue.toNat : ℚ) * 10 ^ value.mOffset := by positivity
      rw [hsigned] at hpos
      simp only [if_true] at hpos
      nlinarith [hpos, hm]
  have h_notZero : ¬ value.isZero = true := by
    unfold STAmount.isZero; rw [beq_eq_false_iff_ne.mpr h_mv_ne]; exact Bool.false_ne_true
  unfold STAmount.roundToExponent at hok
  rw [if_neg (by rw [h_int]; exact Bool.false_ne_true), if_neg h_notZero] at hok
  by_cases h_exp : value.exponent ≥ s
  · rw [if_pos h_exp] at hok; rw [← Except.ok.inj hok]
  · rw [if_neg h_exp] at hok
    push_neg at h_exp
    have h_ev : value.mOffset < s := h_exp
    have href_eq : STAmount.checked value.mNumericType kMinValue s value.negative .downward
        = .ok ⟨value.mNumericType, kMinValue, s, value.mIsNegative⟩ := by
      rw [hc.is_fractional]
      exact STAmount.checked_reference s value.mIsNegative .downward hs_lo hs_hi
    cases href : STAmount.checked value.mNumericType kMinValue s value.negative .downward with
    | error e => rw [href_eq] at href; exact absurd href (by simp)
    | ok referenceValue =>
      rw [href] at hok
      simp only [] at hok
      have hrefeq : referenceValue = ⟨value.mNumericType, kMinValue, s, value.mIsNegative⟩ := by
        rw [href_eq] at href; exact (Except.ok.inj href).symm
      subst hrefeq
      set refA : STAmount := ⟨value.mNumericType, kMinValue, s, value.mIsNegative⟩ with hrefA_def
      cases hsum : STAmount.operator_add value refA .downward with
      | error e => rw [hsum] at hok; exact absurd hok (by simp)
      | ok sum =>
        rw [hsum] at hok
        simp only [] at hok
        obtain ⟨k, hk_le, h_sum_asset, h_sum_mv, h_sum_off, h_sum_neg, _, _, h_dw, _⟩ :=
          STAmount.roundToExponent_sum_spec value s .downward hc h_ev hs_lo hs_hi sum hsum
        have h_kMin_toNat : kMinValue.toNat = 10 ^ 15 := by decide
        have hc_sum : sum.IOUCanonical :=
          { is_fractional := by rw [h_sum_asset]; exact hc.is_fractional
            mant_lo := by rw [h_sum_mv]; omega
            mant_hi := by rw [h_sum_mv]; omega
            exp_lo := by rw [h_sum_off]; omega
            exp_hi := by rw [h_sum_off]; exact hs_hi }
        have hc_refA : refA.IOUCanonical :=
          { is_fractional := by rw [hrefA_def]; exact hc.is_fractional
            mant_lo := by rw [hrefA_def]; show 10 ^ 15 ≤ kMinValue.toNat; omega
            mant_hi := by rw [hrefA_def]; show kMinValue.toNat < 10 ^ 16; rw [h_kMin_toNat]; norm_num
            exp_lo := by rw [hrefA_def]; show (-96 : ℤ) ≤ s; omega
            exp_hi := by rw [hrefA_def]; exact hs_hi }
        have h_pow_s_pos : (0 : ℚ) < (10 : ℚ) ^ s := zpow_pos (by norm_num) _
        have hsum_val : sum.toRat = ((10 ^ 15 + k : ℕ) : ℚ) * 10 ^ s := by
          rw [STAmount.toRat_signed, h_sum_neg, hneg, h_sum_off, h_sum_mv]
          push_cast; ring
        have hrefA_val : refA.toRat = (10 ^ 15 : ℚ) * 10 ^ s := by
          rw [hrefA_def, STAmount.toRat_signed]
          show (if value.mIsNegative then (-1 : ℚ) else 1) * (kMinValue.toNat : ℚ) * 10 ^ s = _
          rw [hneg, h_kMin_toNat]; push_cast; ring
        have htruth : sum.toRat - refA.toRat = (k : ℚ) * 10 ^ s := by
          rw [hsum_val, hrefA_val]; push_cast; ring
        -- `k = ⌊value/10^s⌋`, so `sum - refA = ⌊value/10^s⌋·10^s ≤ value`
        have hkval : (k : ℤ) = ⌊value.toRat / 10 ^ s⌋ := by
          have hh := h_dw rfl
          rw [hneg, if_neg (by decide : ¬ (false = true)), abs_of_nonneg hnn] at hh
          exact hh
        have hsr_le : sum.toRat - refA.toRat ≤ value.toRat := by
          rw [htruth]
          have hfl : (k : ℚ) = (⌊value.toRat / 10 ^ s⌋ : ℚ) := by exact_mod_cast hkval
          rw [hfl]
          have hle : (⌊value.toRat / 10 ^ s⌋ : ℚ) ≤ value.toRat / 10 ^ s := Int.floor_le _
          calc (⌊value.toRat / 10 ^ s⌋ : ℚ) * 10 ^ s
              ≤ (value.toRat / 10 ^ s) * 10 ^ s :=
                mul_le_mul_of_nonneg_right hle (le_of_lt h_pow_s_pos)
            _ = value.toRat := by field_simp
        by_cases hrv : result.mValue = 0
        · have hr0 : result.toRat = 0 := by
            rw [STAmount.toRat_signed, show result.mValue.toNat = 0 from by rw [hrv]; rfl]; simp
          rw [hr0]; exact hnn
        · by_cases hk0 : k = 0
          · exfalso
            have hmv_eq : sum.mValue = kMinValue :=
              UInt64.toNat_inj.mp (by rw [h_sum_mv, hk0, h_kMin_toNat, Nat.add_zero])
            have hsum_eq : sum = refA := by
              rw [hrefA_def]
              have hsum_eta : sum
                  = ⟨sum.mNumericType, sum.mValue, sum.mOffset, sum.mIsNegative⟩ := rfl
              rw [hsum_eta, h_sum_asset, hmv_eq, h_sum_off, h_sum_neg]
            rw [hsum_eq] at hok
            exact hrv (STAmount.operator_sub_self_zero refA result .downward hc_refA hok)
          · have hk1 : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr hk0
            have htruth_pos : 0 < sum.toRat - refA.toRat := by
              rw [htruth]
              have hkq : (1 : ℚ) ≤ (k : ℚ) := by exact_mod_cast hk1
              have : (0 : ℚ) < (k : ℚ) := by linarith
              positivity
            have hrw := STAmount.operator_sub_rounds_iou_downward sum refA result hc_sum hc_refA
              (ne_of_gt htruth_pos) hok hrv
            have hle : result.toRat ≤ sum.toRat - refA.toRat := hrw.1
            linarith [hle, hsr_le]

/-- A nonzero fractional-canonical amount is `Canonical`. -/
lemma STAmount.Canonical.of_iou (s : STAmount) (h : s.IOUCanonical) : s.Canonical := by
  have hintf : s.integral = false := by
    unfold STAmount.integral; rw [h.is_fractional]; decide
  refine ⟨fun hi => ?_, fun _ => h⟩
  rw [hintf] at hi; exact absurd hi Bool.false_ne_true

end XRPL.Model.Protocol

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol

/-- **KEYSTONE.** The rounded deposit amount is stored canonically (or is zero)
whenever the raw `amountDeposit` is. Integral amounts pass through unchanged; a
fractional amount rounds via the `roundToExponent` pipeline, whose output is
`IOUCanonical`-or-zero. -/
theorem roundToVaultExponent_canonical_or_isZero (amountDeposit rounded : STAmount)
    (assetsTotal : Number) (hcanon : amountDeposit.Canonical)
    (hok : roundToVaultExponent amountDeposit assetsTotal = .ok rounded) :
    rounded.Canonical ∨ rounded.isZero = true := by
  by_cases hint : amountDeposit.integral = true
  · rw [roundToVaultExponent_integral amountDeposit assetsTotal hint] at hok
    left; rw [← Except.ok.inj hok]; exact hcanon
  · have hfr : amountDeposit.integral = false := by
      cases hb : amountDeposit.integral with
      | false => rfl
      | true => exact absurd hb hint
    have hcz : amountDeposit.FracCanonZero :=
      ⟨(hcanon.2 hfr).is_fractional, Or.inl (hcanon.2 hfr)⟩
    unfold roundToVaultExponent at hok
    rw [if_neg (by rw [hfr]; exact Bool.false_ne_true)] at hok
    obtain ⟨_, _, hok⟩ := bind_ok_peel _ _ _ hok
    obtain ⟨postScale, _, hrx⟩ := bind_ok_peel _ _ _ hok
    have hres := STAmount.roundToExponent_fczr amountDeposit rounded postScale .downward hcz hrx
    rcases hres.2 with hc | hzero
    · left; exact STAmount.Canonical.of_iou rounded hc
    · right; unfold STAmount.isZero; rw [hzero]; decide

/-- **`roundToVaultExponent` of a nonnegative amount is nonnegative.** The integral
pass is the identity; the fractional pass rounds down onto the post-deposit grid,
which never turns a nonnegative amount negative. The scale range `[-96, 80]` (or the
early-exit sentinel `-100`) is read off the packed exponent, and the truncation core
is `STAmount.roundToExponent_downward_nonneg`. -/
theorem RawVault.roundToVaultExponent_nonneg (amountDeposit result : STAmount) (assetsTotal : Number)
    (hc : amountDeposit.Canonical) (hnn : 0 ≤ amountDeposit.toRat)
    (hok : roundToVaultExponent amountDeposit assetsTotal = .ok result) :
    0 ≤ result.toRat := by
  by_cases hint : amountDeposit.integral = true
  · rw [roundToVaultExponent_integral amountDeposit assetsTotal hint] at hok
    rw [← Except.ok.inj hok]; exact hnn
  · have hfr : amountDeposit.integral = false := by
      cases hb : amountDeposit.integral with
      | false => rfl
      | true => exact absurd hb hint
    have hiou : amountDeposit.IOUCanonical := hc.2 hfr
    have h_mv_ne : amountDeposit.mValue ≠ 0 := by
      intro h0; have h1 : amountDeposit.mValue.toNat = 0 := by rw [h0]; rfl
      have := hiou.mant_lo; omega
    have h_notZero : ¬ amountDeposit.isZero = true := by
      unfold STAmount.isZero; rw [beq_eq_false_iff_ne.mpr h_mv_ne]; exact Bool.false_ne_true
    unfold roundToVaultExponent at hok
    rw [if_neg (by rw [hfr]; exact Bool.false_ne_true)] at hok
    obtain ⟨_, _, hok⟩ := bind_ok_peel _ _ _ hok
    obtain ⟨postScale, hpse, hrx⟩ := bind_ok_peel _ _ _ hok
    unfold postSumExponent at hpse
    obtain ⟨_, _, hpse⟩ := bind_ok_peel _ _ _ hpse
    obtain ⟨assetsTotal', _, hps⟩ := bind_ok_peel _ _ _ hpse
    have hps_nt : numberExponent assetsTotal' .fractional = .ok postScale := by
      rw [← hiou.is_fractional]; exact hps
    rcases exponent_fractional_offset assetsTotal' postScale hps_nt with h100 | ⟨hlo, hhi⟩
    · -- the sentinel `-100`: the amount's exponent already clears it, so the amount passes through
      subst h100
      have hge : amountDeposit.exponent ≥ (-100 : ℤ) := by
        have := hiou.exp_lo; show (-100 : ℤ) ≤ amountDeposit.mOffset; omega
      unfold STAmount.roundToExponent at hrx
      rw [if_neg (by rw [hfr]; exact Bool.false_ne_true), if_neg h_notZero, if_pos hge] at hrx
      rw [← Except.ok.inj hrx]; exact hnn
    · exact STAmount.roundToExponent_downward_nonneg amountDeposit result postScale hiou hlo hhi hnn hrx

/-- **`roundToVaultExponent` never raises a nonnegative amount.** The integral pass
is the identity; the fractional pass rounds down onto the post-deposit grid, which
never exceeds the input. So `result.toRat ≤ amountDeposit.toRat`, over the full
`Canonical` range (the deposit charge's conjunct-1 chain `charge ≤ rounded ≤ raw`). -/
theorem RawVault.roundToVaultExponent_le (amountDeposit result : STAmount) (assetsTotal : Number)
    (hc : amountDeposit.Canonical) (hnn : 0 ≤ amountDeposit.toRat)
    (hok : roundToVaultExponent amountDeposit assetsTotal = .ok result) :
    result.toRat ≤ amountDeposit.toRat := by
  by_cases hint : amountDeposit.integral = true
  · rw [roundToVaultExponent_integral amountDeposit assetsTotal hint] at hok
    rw [← Except.ok.inj hok]
  · have hfr : amountDeposit.integral = false := by
      cases hb : amountDeposit.integral with
      | false => rfl
      | true => exact absurd hb hint
    have hiou : amountDeposit.IOUCanonical := hc.2 hfr
    have h_mv_ne : amountDeposit.mValue ≠ 0 := by
      intro h0; have h1 : amountDeposit.mValue.toNat = 0 := by rw [h0]; rfl
      have := hiou.mant_lo; omega
    have h_notZero : ¬ amountDeposit.isZero = true := by
      unfold STAmount.isZero; rw [beq_eq_false_iff_ne.mpr h_mv_ne]; exact Bool.false_ne_true
    unfold roundToVaultExponent at hok
    rw [if_neg (by rw [hfr]; exact Bool.false_ne_true)] at hok
    obtain ⟨_, _, hok⟩ := bind_ok_peel _ _ _ hok
    obtain ⟨postScale, hpse, hrx⟩ := bind_ok_peel _ _ _ hok
    unfold postSumExponent at hpse
    obtain ⟨_, _, hpse⟩ := bind_ok_peel _ _ _ hpse
    obtain ⟨assetsTotal', _, hps⟩ := bind_ok_peel _ _ _ hpse
    have hps_nt : numberExponent assetsTotal' .fractional = .ok postScale := by
      rw [← hiou.is_fractional]; exact hps
    rcases exponent_fractional_offset assetsTotal' postScale hps_nt with h100 | ⟨hlo, hhi⟩
    · subst h100
      have hge : amountDeposit.exponent ≥ (-100 : ℤ) := by
        have := hiou.exp_lo; show (-100 : ℤ) ≤ amountDeposit.mOffset; omega
      unfold STAmount.roundToExponent at hrx
      rw [if_neg (by rw [hfr]; exact Bool.false_ne_true), if_neg h_notZero, if_pos hge] at hrx
      rw [← Except.ok.inj hrx]
    · exact STAmount.roundToExponent_downward_le amountDeposit result postScale hiou hlo hhi hnn hrx

/-- The rounded deposit amount from `roundedDepositAmount` is stored canonically
whenever the raw `amountDeposit` is: the `.rounded` outcome forbids the zero case. -/
theorem Vault.roundedDepositAmount_canonical (v : Vault) (amountDeposit roundedAmount : STAmount)
    (hcanon : amountDeposit.Canonical)
    (hrounded : v.roundedDepositAmount amountDeposit = .ok (.rounded roundedAmount)) :
    roundedAmount.Canonical := by
  obtain ⟨hround, hnz⟩ := roundedDepositAmount_rounded v amountDeposit roundedAmount hrounded
  rcases roundToVaultExponent_canonical_or_isZero amountDeposit roundedAmount v.assetsTotal
    hcanon hround with hc | hz
  · exact hc
  · rw [hz] at hnz; exact absurd hnz (by decide)


/-! ## Value bound for the post-sum clamp on a negative delta -/

/-- **The post-sum clamp never raises the magnitude of a negative delta.** A
withdrawal or clawback clamps `payout.operator_neg`, which takes the negative
branch: a plain downward `roundToExponent` of the magnitude. So the stored amount
is non-negative and at or below the priced one — every "never pays out more than
the shares are worth" bound transfers verbatim.

The post-sum exponent is either the flushed-to-zero `-100`, in which case the
`exponent ≥ scale` early exit makes the clamp the identity, or a clamped IOU
offset in `[-96, 80]`, where the directed `roundToExponent` lemmas apply. -/
lemma clampToSumExponent_neg_le (amount : Number) (a c : STAmount)
    (hc : a.IOUCanonical) (hnn : 0 ≤ a.toRat)
    (hok : clampToSumExponent amount a.operator_neg = .ok c) :
    0 ≤ c.toRat ∧ c.toRat ≤ a.toRat := by
  have hmv : a.mValue ≠ 0 := by
    intro h0
    have hlo := hc.mant_lo
    rw [h0] at hlo
    exact absurd hlo (by decide)
  have hsgn : a.mIsNegative = false := by
    by_contra hcn
    have hneg : a.mIsNegative = true := by simpa using hcn
    have hmag : (0 : ℚ) < (a.mValue.toNat : ℚ) * (10 : ℚ) ^ a.mOffset := by
      have h1 : 0 < a.mValue.toNat := by have := hc.mant_lo; omega
      have h1q : (0 : ℚ) < (a.mValue.toNat : ℚ) := by exact_mod_cast h1
      exact mul_pos h1q (zpow_pos (by norm_num) _)
    rw [STAmount.toRat_of_neg a hneg] at hnn
    linarith
  have hnegT : a.operator_neg.negative = true := by
    rw [STAmount.operator_neg_of_ne a hmv]
    show (!a.mIsNegative) = true
    rw [hsgn]; rfl
  have hintN : ¬ a.operator_neg.integral = true := by
    show ¬ a.operator_neg.mNumericType.isIntegral = true
    rw [STAmount.operator_neg_mNumericType, hc.is_fractional]; decide
  have hae : a.exponent = a.mOffset := rfl
  unfold clampToSumExponent at hok
  simp only [pure_bind] at hok
  rw [if_neg hintN] at hok
  obtain ⟨pe, hpe, hok⟩ := bind_ok_peel _ _ _ hok
  simp only [hnegT, if_true, STAmount.operator_neg_neg] at hok
  by_cases hge : a.exponent ≥ pe
  · -- the clamp is the identity: the grid is at or below the amount's own exponent
    have hzf : ¬ a.isZero = true := by
      show ¬ (a.mValue == 0) = true
      simpa using hmv
    have hintA : ¬ a.integral = true := by
      show ¬ a.mNumericType.isIntegral = true
      rw [hc.is_fractional]; decide
    unfold STAmount.roundToExponent at hok
    rw [if_neg hintA, if_neg hzf, if_pos hge] at hok
    rw [← Except.ok.inj hok]
    exact ⟨hnn, le_refl _⟩
  · push_neg at hge
    have hrange : pe = -100 ∨ ((-96 : ℤ) ≤ pe ∧ pe ≤ 80) := by
      unfold postSumExponent at hpe
      simp only [] at hpe
      obtain ⟨dn, -, hpe⟩ := bind_ok_peel _ _ _ hpe
      obtain ⟨sum, -, hpe⟩ := bind_ok_peel _ _ _ hpe
      refine exponent_fractional_offset sum pe ?_
      rw [show a.operator_neg.numericType = NumericType.fractional from by
        show a.operator_neg.mNumericType = NumericType.fractional
        rw [STAmount.operator_neg_mNumericType]; exact hc.is_fractional] at hpe
      exact hpe
    have hlo : (-96 : ℤ) ≤ pe := by
      have := hc.exp_lo; omega
    have hhi : pe ≤ 80 := by
      rcases hrange with h | ⟨-, h⟩
      · exfalso; rw [h] at hge; have := hc.exp_lo; omega
      · exact h
    exact ⟨STAmount.roundToExponent_downward_nonneg a c pe hc hlo hhi hnn hok,
      STAmount.roundToExponent_downward_le a c pe hc hlo hhi hnn hok⟩

/-- **The post-sum clamp of a negative delta loses less than one grid step.** The
negative branch floors the magnitude onto the post-sum grid `10 ^ pe`, so a
nonzero stored payout sits strictly within one step of the priced one. Paired
with `clampToSumExponent_neg_le` (`c ≤ a`) this brackets the clamp; bounding
`10 ^ pe` against the stored total then turns it into a `clampε` statement.

The zero-output case is excluded by hypothesis, which costs nothing: every
consumer of the under-pay direction is already guarded by `assets'.isZero = false`. -/
lemma clampToSumExponent_neg_ge_grid (amount : Number) (a c : STAmount) (pe : ℤ)
    (hc : a.IOUCanonical) (hnn : 0 ≤ a.toRat) (hnz : c.mValue ≠ 0)
    (hpe : postSumExponent amount a.operator_neg = .ok pe)
    (hok : clampToSumExponent amount a.operator_neg = .ok c) :
    a.toRat - (10 : ℚ) ^ pe < c.toRat := by
  have hpow_pos : (0 : ℚ) < (10 : ℚ) ^ pe := zpow_pos (by norm_num) _
  have hmv : a.mValue ≠ 0 := by
    intro h0
    have hlo := hc.mant_lo
    rw [h0] at hlo
    exact absurd hlo (by decide)
  have hsgn : a.mIsNegative = false := by
    by_contra hcn
    have hneg : a.mIsNegative = true := by simpa using hcn
    have hmag : (0 : ℚ) < (a.mValue.toNat : ℚ) * (10 : ℚ) ^ a.mOffset := by
      have h1 : 0 < a.mValue.toNat := by have := hc.mant_lo; omega
      have h1q : (0 : ℚ) < (a.mValue.toNat : ℚ) := by exact_mod_cast h1
      exact mul_pos h1q (zpow_pos (by norm_num) _)
    rw [STAmount.toRat_of_neg a hneg] at hnn
    linarith
  have hnegT : a.operator_neg.negative = true := by
    rw [STAmount.operator_neg_of_ne a hmv]
    show (!a.mIsNegative) = true
    rw [hsgn]; rfl
  have hintN : ¬ a.operator_neg.integral = true := by
    show ¬ a.operator_neg.mNumericType.isIntegral = true
    rw [STAmount.operator_neg_mNumericType, hc.is_fractional]; decide
  unfold clampToSumExponent at hok
  simp only [pure_bind] at hok
  rw [if_neg hintN] at hok
  obtain ⟨pe', hpe', hok⟩ := bind_ok_peel _ _ _ hok
  rw [show pe' = pe from Except.ok.inj (hpe'.symm.trans hpe)] at hok
  simp only [hnegT, if_true, STAmount.operator_neg_neg] at hok
  by_cases hge : a.exponent ≥ pe
  · -- the clamp is the identity: nothing is lost at all
    have hzf : ¬ a.isZero = true := by
      show ¬ (a.mValue == 0) = true
      simpa using hmv
    have hintA : ¬ a.integral = true := by
      show ¬ a.mNumericType.isIntegral = true
      rw [hc.is_fractional]; decide
    unfold STAmount.roundToExponent at hok
    rw [if_neg hintA, if_neg hzf, if_pos hge] at hok
    rw [← Except.ok.inj hok]
    linarith
  · push_neg at hge
    have hae : a.exponent = a.mOffset := rfl
    have hrange : pe = -100 ∨ ((-96 : ℤ) ≤ pe ∧ pe ≤ 80) := by
      unfold postSumExponent at hpe
      simp only [] at hpe
      obtain ⟨dn, -, hpe⟩ := bind_ok_peel _ _ _ hpe
      obtain ⟨sum, -, hpe⟩ := bind_ok_peel _ _ _ hpe
      refine exponent_fractional_offset sum pe ?_
      rw [show a.operator_neg.numericType = NumericType.fractional from by
        show a.operator_neg.mNumericType = NumericType.fractional
        rw [STAmount.operator_neg_mNumericType]; exact hc.is_fractional] at hpe
      exact hpe
    have hlo : (-96 : ℤ) ≤ pe := by have := hc.exp_lo; omega
    have hhi : pe ≤ 80 := by
      rcases hrange with h | ⟨-, h⟩
      · exfalso; rw [h] at hge; have := hc.exp_lo; omega
      · exact h
    -- `.downward` floors the magnitude onto the grid
    have hgrid : c.toRat = (⌊a.toRat / (10 : ℚ) ^ pe⌋ : ℚ) * (10 : ℚ) ^ pe :=
      STAmount.roundToExponent_rounded a c pe .downward hc hlo hhi hnz hok
    have hcancel : a.toRat / (10 : ℚ) ^ pe * (10 : ℚ) ^ pe = a.toRat :=
      div_mul_cancel₀ _ (ne_of_gt hpow_pos)
    have hfl : a.toRat / (10 : ℚ) ^ pe - 1 < (⌊a.toRat / (10 : ℚ) ^ pe⌋ : ℚ) :=
      Int.sub_one_lt_floor _
    have hmul := mul_lt_mul_of_pos_right hfl hpow_pos
    rw [sub_mul, one_mul, hcancel] at hmul
    rw [hgrid]
    exact hmul

/-- **The post-sum clamp loses at most `assetsTotal * clampε` of a negative
delta.** Combines the grid bound `a - 10 ^ pe < c` with a bound on the grid step
itself: the post-sum amount is `IOUCanonical`, so `10 ^ pe ≤ |sum| / 10 ^ 15`,
and the sum is at most `amount`. The flushed case is excluded because it forces
`pe = -100`, below the `-96` floor of a canonical `a`. -/
lemma clampToSumExponent_neg_ge (amount : Number) (a c : STAmount)
    (hc : a.IOUCanonical) (hnn : 0 ≤ a.toRat) (hnz : c.mValue ≠ 0)
    (hA_norm : amount.isNormalized) (hle : a.toRat ≤ amount.toRat)
    (hok : clampToSumExponent amount a.operator_neg = .ok c) :
    a.toRat - amount.toRat * clampε ≤ c.toRat := by
  have hA_nn : 0 ≤ amount.toRat := le_trans hnn hle
  have hcε : 0 ≤ amount.toRat * clampε := mul_nonneg hA_nn clampε_nonneg
  have hae : a.exponent = a.mOffset := rfl
  have hmv : a.mValue ≠ 0 := by
    intro h0; have hlo := hc.mant_lo; rw [h0] at hlo; exact absurd hlo (by decide)
  have hsgn : a.mIsNegative = false := by
    by_contra hcn
    have hneg : a.mIsNegative = true := by simpa using hcn
    have hmag : (0 : ℚ) < (a.mValue.toNat : ℚ) * (10 : ℚ) ^ a.mOffset := by
      have h1 : 0 < a.mValue.toNat := by have := hc.mant_lo; omega
      have h1q : (0 : ℚ) < (a.mValue.toNat : ℚ) := by exact_mod_cast h1
      exact mul_pos h1q (zpow_pos (by norm_num) _)
    rw [STAmount.toRat_of_neg a hneg] at hnn
    linarith
  have hnegT : a.operator_neg.negative = true := by
    rw [STAmount.operator_neg_of_ne a hmv]
    show (!a.mIsNegative) = true
    rw [hsgn]; rfl
  have hintN : ¬ a.operator_neg.integral = true := by
    show ¬ a.operator_neg.mNumericType.isIntegral = true
    rw [STAmount.operator_neg_mNumericType, hc.is_fractional]; decide
  have hok0 := hok
  unfold clampToSumExponent at hok0
  simp only [pure_bind] at hok0
  rw [if_neg hintN] at hok0
  obtain ⟨pe, hpe, hok1⟩ := bind_ok_peel _ _ _ hok0
  simp only [hnegT, if_true, STAmount.operator_neg_neg] at hok1
  by_cases hge : a.exponent ≥ pe
  · have hzf : ¬ a.isZero = true := by
      show ¬ (a.mValue == 0) = true
      simpa using hmv
    have hintA : ¬ a.integral = true := by
      show ¬ a.mNumericType.isIntegral = true
      rw [hc.is_fractional]; decide
    unfold STAmount.roundToExponent at hok1
    rw [if_neg hintA, if_neg hzf, if_pos hge] at hok1
    rw [← Except.ok.inj hok1]
    linarith
  · push_neg at hge
    have hgrid := clampToSumExponent_neg_ge_grid amount a c pe hc hnn hnz hpe hok
    have hstep : (10 : ℚ) ^ pe ≤ amount.toRat * clampε := by
      unfold postSumExponent at hpe
      simp only [] at hpe
      obtain ⟨dn, hdn, hpe1⟩ := bind_ok_peel _ _ _ hpe
      obtain ⟨S, hS, hpe2⟩ := bind_ok_peel _ _ _ hpe1
      rw [show a.operator_neg.numericType = NumericType.fractional from by
        show a.operator_neg.mNumericType = NumericType.fractional
        rw [STAmount.operator_neg_mNumericType]; exact hc.is_fractional] at hpe2
      unfold numberExponent at hpe2
      obtain ⟨Asum, hAsum, hpe3⟩ := bind_ok_peel _ _ _ hpe2
      have hpe_off : Asum.mOffset = pe :=
        Except.ok.inj (show Except.ok Asum.exponent = Except.ok pe from hpe3)
      -- `dn` is the exact negation of `a`
      have hnegc : a.operator_neg.IOUCanonical :=
        { is_fractional := by rw [STAmount.operator_neg_mNumericType]; exact hc.is_fractional
          mant_lo := by rw [STAmount.operator_neg_mValue]; exact hc.mant_lo
          mant_hi := by rw [STAmount.operator_neg_mValue]; exact hc.mant_hi
          exp_lo := by rw [STAmount.operator_neg_mOffset]; exact hc.exp_lo
          exp_hi := by rw [STAmount.operator_neg_mOffset]; exact hc.exp_hi }
      obtain ⟨dn2, hdn2, hdn_val, hdn_norm⟩ :=
        STAmount.toNumber_exact_canonical a.operator_neg .to_nearest (Or.inl hnegc)
      have hdn_eq : dn2 = dn := Except.ok.inj (hdn2.symm.trans hdn)
      rw [hdn_eq] at hdn_val hdn_norm
      rw [STAmount.operator_neg_toRat] at hdn_val
      -- the sum is nonzero: a flushed sum would put the grid at `-100`
      have hS_ne : S.mantissa_ ≠ 0 := by
        intro h0
        have hSz : S = Number.zero :=
          Number.operator_add_zero_shape_sz amount dn S hA_norm hdn_norm hS h0
        rw [hSz, show STAmount.ofNumber .fractional Number.zero .to_nearest
          = .ok ⟨.fractional, 0, -100, false⟩ from rfl] at hAsum
        have hz : Asum.mOffset = -100 := by rw [← Except.ok.inj hAsum]
        rw [hz] at hpe_off
        have := hc.exp_lo
        omega
      have hS_norm : S.isNormalized :=
        operator_add_isNormalized_to_nearest amount dn S hA_norm hdn_norm hS hS_ne
      obtain ⟨hSm_lo, hSm_hi⟩ := hS_norm.mantissaBounds_nat hS_ne
      have hSexp_lo : minExponent ≤ S.exponent_ := by
        rcases hS_norm with hz | ⟨_, _, _, hlo, _⟩
        · exact absurd (show S.mantissa_ = 0 by rw [hz]; rfl) hS_ne
        · exact hlo
      have hAs_ne : Asum.mValue ≠ 0 := by
        intro hz
        have h100 := STAmount.ofNumber_iou_zero_offset S .to_nearest Asum hS_norm hAsum hz
        rw [h100] at hpe_off
        have := hc.exp_lo
        omega
      have hAs_c : Asum.IOUCanonical := by
        rcases STAmount.ofNumber_iou_canonical_or_zero S .to_nearest Asum
          hSm_lo hSm_hi hSexp_lo hAsum with h | h
        · exact h
        · exact absurd h hAs_ne
      -- the sum sits in `[0, amount]`
      have hS_nn : 0 ≤ S.toRat :=
        operator_add_nonneg amount dn S hA_norm hdn_norm hS (by rw [hdn_val]; linarith)
      have hS_le : S.toRat ≤ amount.toRat :=
        operator_add_le_of_le_normalized amount dn S amount hA_norm hdn_norm hS hA_norm
          (by rw [hdn_val]; linarith)
      -- the packing moves the sum by at most one 16-digit step
      have hexp4 : S.exponent_ + 4 ≤ maxExponent :=
        STAmount.ofNumber_iou_success_exp_range S .to_nearest Asum hSm_lo hSm_hi hSexp_lo
          hAsum hAs_ne
      obtain ⟨hulp, -⟩ := STAmount.ofNumber_iou_within_ulp .fractional S .to_nearest Asum rfl
        hSm_lo hSm_hi hSexp_lo hexp4 hAsum hAs_ne
      -- `10 ^ (S.exponent_ + 3) ≤ S.toRat * 10 ^ (-15)`
      have hSval : S.toRat = (S.mantissa_.toNat : ℚ) * (10 : ℚ) ^ S.exponent_ := by
        rcases hsn : S.negative_ with _ | _
        · exact Number.toRat_of_nonneg S hsn
        · exfalso
          rw [Number.toRat_of_neg S hsn] at hS_nn
          have h1 : 0 < S.mantissa_.toNat := by omega
          have h1q : (0 : ℚ) < (S.mantissa_.toNat : ℚ) := by exact_mod_cast h1
          have := mul_pos h1q (zpow_pos (show (0:ℚ) < 10 by norm_num) S.exponent_)
          linarith
      have hulp_small : (10 : ℚ) ^ (S.exponent_ + 3) * (10 : ℚ) ^ (15 : ℕ) ≤ S.toRat := by
        rw [hSval]
        have h1 : (10 : ℚ) ^ (18 : ℕ) ≤ (S.mantissa_.toNat : ℚ) := by exact_mod_cast hSm_lo
        have hsplit : (10 : ℚ) ^ (S.exponent_ + 3) * (10 : ℚ) ^ (15 : ℕ)
            = (10 : ℚ) ^ (18 : ℕ) * (10 : ℚ) ^ S.exponent_ := by
          rw [show ((10 : ℚ) ^ (15 : ℕ)) = (10 : ℚ) ^ ((15 : ℤ)) from by norm_num,
            show ((10 : ℚ) ^ (18 : ℕ)) = (10 : ℚ) ^ ((18 : ℤ)) from by norm_num,
            ← zpow_add₀ (by norm_num : (10 : ℚ) ≠ 0),
            ← zpow_add₀ (by norm_num : (10 : ℚ) ≠ 0)]
          congr 1
          try omega
        rw [hsplit]
        exact mul_le_mul_of_nonneg_right h1 (le_of_lt (zpow_pos (by norm_num) _))
      -- assemble: `10 ^ pe * 10 ^ 15 ≤ |Asum| ≤ S + 10 ^ (S.exp+3) ≤ amount * 10`
      have hAs_abs : |Asum.toRat| = (Asum.mValue.toNat : ℚ) * (10 : ℚ) ^ Asum.mOffset :=
        STAmount.abs_toRat Asum
      have hlow : (10 : ℚ) ^ pe * (10 : ℚ) ^ (15 : ℕ) ≤ |Asum.toRat| := by
        rw [hAs_abs, ← hpe_off]
        have h1 : (10 : ℚ) ^ (15 : ℕ) ≤ (Asum.mValue.toNat : ℚ) := by
          have := hAs_c.mant_lo; exact_mod_cast this
        calc (10 : ℚ) ^ Asum.mOffset * (10 : ℚ) ^ (15 : ℕ)
            ≤ (10 : ℚ) ^ Asum.mOffset * (Asum.mValue.toNat : ℚ) :=
              mul_le_mul_of_nonneg_left h1 (le_of_lt (zpow_pos (by norm_num) _))
          _ = (Asum.mValue.toNat : ℚ) * (10 : ℚ) ^ Asum.mOffset := by ring
      have habs_le : |Asum.toRat| ≤ S.toRat + (10 : ℚ) ^ (S.exponent_ + 3) := by
        have := abs_le.mp hulp
        have h2 : Asum.toRat ≤ S.toRat + (10 : ℚ) ^ (S.exponent_ + 3) := by linarith [this.2]
        have h3 : -(S.toRat + (10 : ℚ) ^ (S.exponent_ + 3)) ≤ Asum.toRat := by
          have hp : (0 : ℚ) < (10 : ℚ) ^ (S.exponent_ + 3) := zpow_pos (by norm_num) _
          linarith [this.1]
        exact abs_le.mpr ⟨h3, h2⟩
      have h15 : (10 : ℚ) ^ (15 : ℕ) = 1000000000000000 := by norm_num
      rw [h15] at hlow hulp_small
      rw [clampε_eq]
      linarith
    linarith

end XRPL.Model.SingleAssetVault
