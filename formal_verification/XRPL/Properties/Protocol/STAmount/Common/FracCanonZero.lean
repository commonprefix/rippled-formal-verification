import XRPL.Properties.Protocol.STAmount.Common.RoundToScalePlumbing
import XRPL.Properties.Protocol.STAmount.Div.Common.IOU
import XRPL.Properties.Protocol.STAmount.Add.Common.Integral
import XRPL.Properties.Protocol.STAmount.Common.OfNumberBoundary

/-! # Canonical-or-zero fractional amounts

A fractional `STAmount` that `canonicalize` produced is either stored canonically
(`IOUCanonical`) or zero. `operator_add`, `operator_sub` and `roundToExponent`
keep that, and `toNumber` of the zero amount is the exact zero. `canonicalize` and
`ofNumber` keep the numeric type. -/

namespace XRPL.Model.Protocol

set_option maxRecDepth 4000

/-- A successful `IOUAmount.normalize` output is a canonical 16-digit amount
(`InRange16`) or the zero amount. The offset clamps that a `.ok` passed pin the
exponent to `[-96, 80]`. -/
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

/-- **`IOUAmount.normalize` keeps a nonnegative mantissa nonnegative.** Each stage
carries the cleared sign into its output. Unlike the `RoundsWithin` facts it
needs no magnitude bound. -/
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
          exact hsign.1 hvneg

/-- **`canonicalize` of a sign-cleared fractional source is nonnegative.** It
needs only that the stored magnitude fits `Int64`, so it also covers small
mantissas. -/
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

/-- A fractional amount that is stored canonically or zero. The fractional
rounding pipeline preserves this. -/
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

/-- `ofIOUAmount` canonicalizes a fractional record, so its output is
`FracCanonZero`. -/
lemma STAmount.ofIOUAmount_fczr (a : IOUAmount) (mode : rounding_mode) (result : STAmount)
    (hok : STAmount.ofIOUAmount a mode = .ok result) : result.FracCanonZero := by
  unfold STAmount.ofIOUAmount at hok
  exact STAmount.canonicalize_fczr _ result mode rfl hok

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

/-- A fractional `ofNumber` result is `FracCanonZero`: it packs through `checked`,
which canonicalizes the fractional record. -/
lemma STAmount.ofNumber_fractional_fczr (n : Number) (mode : rounding_mode) (result : STAmount)
    (hok : STAmount.ofNumber .fractional n mode = .ok result) : result.FracCanonZero := by
  rw [STAmount.ofNumber] at hok
  split at hok
  · exact absurd ‹NumericType.fractional.isIntegral = true› (by decide)
  · split at hok
    · exact absurd hok (by simp)
    · rw [STAmount.checked] at hok
      exact STAmount.canonicalize_fczr _ result mode rfl hok

/-- `roundToExponent` keeps `FracCanonZero`. The early exits return the value, and
the general path adds and then subtracts a fractional reference, which both keep
it. -/
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

/-- **`toNumber` of a zero-magnitude fractional amount is the exact zero.** The IOU
lift short-circuits: `signedDrops = 0`, `ofMantissaExp` returns `IOUAmount.zero`,
whose `from_rep` normalizes a zero mantissa to `Number.zero`. -/
lemma STAmount.toNumber_zero_fractional (s : STAmount) (mode : rounding_mode)
    (hfr : s.integral = false) (hz : s.mValue = 0) :
    s.toNumber mode = .ok Number.zero := by
  unfold STAmount.toNumber
  rw [if_neg (by rw [hfr]; decide)]
  have hsd : s.signedDrops.toInt64 = 0 := by
    have h0 : s.signedDrops = 0 := by unfold STAmount.signedDrops; rw [hz]; simp
    rw [h0]; rfl
  have hiou : s.iou mode = .ok IOUAmount.zero := by
    unfold STAmount.iou IOUAmount.ofMantissaExp
    rw [if_neg (by rw [hfr]; decide), hsd]
    show IOUAmount.normalize ⟨0, s.mOffset⟩ mode = .ok IOUAmount.zero
    unfold IOUAmount.normalize
    rw [if_pos (show (((⟨0, s.mOffset⟩ : IOUAmount)).mantissa_ == 0) = true from rfl)]
  rw [hiou]
  show IOUAmount.toNumber IOUAmount.zero mode = .ok Number.zero
  unfold IOUAmount.toNumber IOUAmount.zero Number.from_rep Number.normalized Number.normalize
  rw [show doNormalize
        (Number.unchecked ((0 : Int64) < 0) (0 : Int64).toInt.natAbs.toUInt64 (-100)).negative_
        (Number.unchecked ((0 : Int64) < 0) (0 : Int64).toInt.natAbs.toUInt64 (-100)).mantissa_
        (Number.unchecked ((0 : Int64) < 0) (0 : Int64).toInt.natAbs.toUInt64 (-100)).exponent_
        largeRange.min largeRange.max mode
      = doNormalize false 0 (-100) largeRange.min largeRange.max mode from rfl]
  unfold doNormalize
  rw [if_pos (by decide)]

/-- `canonicalize` preserves the numeric type: every success branch returns the
input record with only the magnitude/offset/sign fields rewritten. -/
lemma STAmount.canonicalize_mNumericType (s result : STAmount) (mode : rounding_mode)
    (hok : s.canonicalize mode = .ok result) : result.mNumericType = s.mNumericType := by
  rw [STAmount.canonicalize] at hok
  by_cases hint : s.integral = true
  · rw [if_pos hint] at hok
    by_cases hz : (s.mValue == 0 || decide (s.mOffset ≤ -20)) = true
    · rw [if_pos hz] at hok; rw [← Except.ok.inj hok]
    · rw [if_neg hz] at hok
      by_cases hmoff : s.mOffset > s.mNumericType.maxOffset
      · rw [if_pos hmoff] at hok; exact absurd hok (by simp)
      · rw [if_neg hmoff] at hok
        simp only [IntAmount.ofNumber] at hok
        cases hr : (Number.unchecked s.mIsNegative s.mValue s.mOffset).to_rep mode with
        | error e => rw [hr] at hok; exact absurd hok (by simp)
        | ok r =>
          rw [hr] at hok; simp only [] at hok
          by_cases hrng : r.toInt.natAbs.toUInt64 > s.mNumericType.maxValue
          · rw [if_pos hrng] at hok; exact absurd hok (by simp)
          · rw [if_neg hrng] at hok; rw [← Except.ok.inj hok]
  · rw [if_neg hint] at hok
    cases hi : s.iou mode with
    | error e => rw [hi] at hok; exact absurd hok (by simp)
    | ok i => rw [hi] at hok; simp only [] at hok; rw [← Except.ok.inj hok]

/-- `ofNumber` produces an amount of the requested numeric type (it packs through
`checked`, which preserves the type). -/
lemma STAmount.ofNumber_mNumericType (nt : NumericType) (n : Number) (mode : rounding_mode)
    (result : STAmount) (hok : STAmount.ofNumber nt n mode = .ok result) :
    result.mNumericType = nt := by
  rw [STAmount.ofNumber] at hok
  split at hok
  · split at hok
    · exact absurd hok (by simp)
    · rw [STAmount.checked] at hok
      exact STAmount.canonicalize_mNumericType _ result mode hok
  · split at hok
    · exact absurd hok (by simp)
    · rw [STAmount.checked] at hok
      exact STAmount.canonicalize_mNumericType _ result mode hok

end XRPL.Model.Protocol
