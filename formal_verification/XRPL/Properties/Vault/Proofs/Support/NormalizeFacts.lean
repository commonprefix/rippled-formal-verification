import XRPL.Properties.Protocol.Common.AmountArith
import XRPL.Properties.Vault.Proofs.Support.NumberFacts
import XRPL.Properties.Protocol.STAmount.Common.FracCanonZero
import XRPL.Properties.Protocol.STAmount.Common.OfNumberBoundary
-- Re-exported for the files that import this one
import XRPL.Properties.Protocol.STAmount.Common.OfNumberFacts
import XRPL.Properties.Protocol.STAmount.Common.OfNumberTotality

/-! # Normalization facts

Facts about `Number` normalization: `doNormalize`, `normalizeToRange`, the guard, and
`IOUAmount.normalize`. -/

namespace XRPL.Model.Protocol

/-- Normalizing a nonpositive mantissa gives a nonpositive mantissa. -/
lemma IOUAmount.normalize_mantissa_nonpos (m : Int64) (e : Int) (mode : rounding_mode)
    (i : IOUAmount) (hm : m.toInt ≤ 0)
    (hok : IOUAmount.normalize ⟨m, e⟩ mode = .ok i) :
    i.mantissa_.toInt ≤ 0 := by
  by_cases hi0 : i.mantissa_ = 0
  · rw [hi0]; decide
  unfold IOUAmount.normalize at hok
  by_cases hma : m = 0
  · rw [if_pos (show ((⟨m, e⟩ : IOUAmount).mantissa_ == 0) = true from beq_iff_eq.mpr hma)] at hok
    rw [← Except.ok.inj hok] at hi0; exact absurd rfl hi0
  · have hm_toInt : m.toInt ≠ 0 := fun h => hma (Int64.toInt_inj.mp (by rw [h]; decide))
    have hmlt : decide (m < 0) = true := by
      rw [decide_eq_true_iff, Int64.lt_iff_toInt_lt]
      have h0 : (0 : Int64).toInt = 0 := by decide
      omega
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
      have hv_exp_lo : minExponent ≤ v.exponent_ := Number.exponent_ge_min v hv_norm hv_ne
      have hvneg : v.negative_ = true := by
        obtain ⟨m3, e3, g3, res, hrup, hres_eq, -, -, -, -⟩ :=
          normalize_doRoundUp_stage _ v mode hun_ne hfr' hv_ne
        have hres_ne : res.mantissa_ ≠ 0 := by rw [hres_eq] at hv_ne; exact hv_ne
        have hsg := doRoundUp_negative_of_mant_ne g3 _ m3 e3 largeRange.min largeRange.max mode
          .normalize2 res hrup hres_ne
        rw [hres_eq]
        show res.negative_ = true
        rw [hsg]; exact hmlt
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
          exact hsign.2 hvneg

/-- Every `IOUAmount.normalize` output is either the zero sentinel (exponent
`-100`) or sits inside the IOU exponent window. -/
lemma IOUAmount.normalize_exp_range (a : IOUAmount) (mode : rounding_mode) (i : IOUAmount)
    (hok : IOUAmount.normalize a mode = .ok i) :
    (i.mantissa_ = 0 ∧ i.exponent_ = -100) ∨
      ((-96 : ℤ) ≤ i.exponent_ ∧ i.exponent_ ≤ 80) := by
  unfold IOUAmount.normalize at hok
  by_cases hz : (a.mantissa_ == 0) = true
  · rw [if_pos hz] at hok
    rw [← Except.ok.inj hok]; exact Or.inl ⟨rfl, rfl⟩
  · rw [if_neg hz] at hok
    cases hfr : Number.from_rep a.mantissa_ a.exponent_ largeRange.min largeRange.max mode with
    | error e => rw [hfr] at hok; exact absurd hok (by simp)
    | ok v =>
      rw [hfr] at hok
      simp only [] at hok
      cases hfn : IOUAmount.fromNumber v mode with
      | error e => rw [hfn] at hok; exact absurd hok (by simp)
      | ok r =>
        rw [hfn] at hok
        simp only [] at hok
        by_cases hhi : r.exponent_ > cMaxOffset
        · rw [if_pos hhi] at hok; exact absurd hok (by simp)
        · rw [if_neg hhi] at hok
          by_cases hlo : r.exponent_ < cMinOffset
          · rw [if_pos hlo] at hok
            rw [← Except.ok.inj hok]; exact Or.inl ⟨rfl, rfl⟩
          · rw [if_neg hlo] at hok
            rw [← Except.ok.inj hok]
            refine Or.inr ⟨?_, ?_⟩
            · have : cMinOffset = (-96 : ℤ) := rfl
              omega
            · have : cMaxOffset = (80 : ℤ) := rfl
              omega

/-- A zero result of `IOUAmount.normalize` is the `-100` zero sentinel: a nonzero source always packs to a nonzero
16-digit mantissa. -/
lemma IOUAmount.normalize_zero_exp (a : IOUAmount) (mode : rounding_mode) (i : IOUAmount)
    (hok : IOUAmount.normalize a mode = .ok i) (hz : i.mantissa_ = 0) : i.exponent_ = -100 := by
  unfold IOUAmount.normalize at hok
  by_cases hma : (a.mantissa_ == 0) = true
  · rw [if_pos hma] at hok; rw [← Except.ok.inj hok]; rfl
  · rw [if_neg hma] at hok
    have hane : a.mantissa_ ≠ 0 := by simpa using hma
    cases hfr : Number.from_rep a.mantissa_ a.exponent_ largeRange.min largeRange.max mode with
    | error e => rw [hfr] at hok; exact absurd hok (by simp)
    | ok v =>
      rw [hfr] at hok
      simp only [] at hok
      cases hfn : IOUAmount.fromNumber v mode with
      | error e => rw [hfn] at hok; exact absurd hok (by simp)
      | ok r =>
        rw [hfn] at hok
        simp only [] at hok
        by_cases hhi : r.exponent_ > cMaxOffset
        · rw [if_pos hhi] at hok; exact absurd hok (by simp)
        rw [if_neg hhi] at hok
        by_cases hlo : r.exponent_ < cMinOffset
        · rw [if_pos hlo] at hok; rw [← Except.ok.inj hok]; rfl
        rw [if_neg hlo] at hok
        -- the general exit: a nonzero source packs to a nonzero 16-digit mantissa
        exfalso
        have hir : i = r := (Except.ok.inj hok).symm
        rw [hir] at hz
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
          have hmi : a.mantissa_.toInt ≠ 0 := fun h =>
            hane (Int64.toInt_inj.mp (by rw [h]; decide))
          intro h; rw [h] at heq; simp at heq; omega
        unfold IOUAmount.fromNumber at hfn
        cases hnr : v.normalizeToRange cMinValue cMaxValue mode with
        | error e => rw [hnr] at hfn; exact absurd hfn (by simp)
        | ok me =>
          obtain ⟨mm, ee⟩ := me
          rw [hnr] at hfn
          simp only [] at hfn
          have hrmm : r = ⟨mm, ee⟩ := (Except.ok.inj hfn).symm
          by_cases hv0 : v.mantissa_ = 0
          · -- the 19-digit lift flushed to zero, so its exponent sits far below `cMinOffset`,
            -- so the underflow branch would have fired before this one
            have hnr' : v.normalizeToRange cMinValue cMaxValue mode
                = .ok ((if Number.zero.negative_ then -Number.zero.mantissa_.toInt64
                        else Number.zero.mantissa_.toInt64), Number.zero.exponent_) := by
              unfold Number.normalizeToRange
              rw [show doNormalize v.negative_ v.mantissa_ v.exponent_ cMinValue cMaxValue mode
                    = .ok Number.zero from by
                  unfold doNormalize; rw [if_pos (by simpa using hv0)]]
              ntr_tail
            have hpair := Except.ok.inj (hnr.symm.trans hnr')
            have hee : ee = Number.zero.exponent_ := congrArg Prod.snd hpair
            apply hlo
            rw [hrmm]
            show ee < cMinOffset
            rw [hee]
            decide
          · have hfr' : (Number.unchecked (a.mantissa_ < 0) a.mantissa_.toInt.natAbs.toUInt64
                a.exponent_).normalize largeRange.min largeRange.max mode = .ok v := hfr
            have hv_norm : v.isNormalized :=
              normalize_result_isNormalized _ v mode hun_ne hfr' hv0
            obtain ⟨hvm_lo, hvm_hi⟩ := hv_norm.mantissaBounds_nat hv0
            have hv_exp_lo : minExponent ≤ v.exponent_ := Number.exponent_ge_min v hv_norm hv0
            have hexp3 : v.exponent_ + 3 ≤ maxExponent :=
              normalizeToRange_iou_exp_hi v mode mm ee hvm_lo hvm_hi hnr
            obtain ⟨⟨hmlo, -⟩, -, -⟩ :=
              normalizeToRange_iou_ok_facts v mode mm ee hvm_lo hvm_hi (by omega) hexp3 hnr
            have hcm : cMinValue.toNat = 10 ^ 15 := by decide
            rw [hrmm] at hz
            have hmm0 : mm.toInt.natAbs = 0 := by
              have : mm = 0 := hz
              rw [this]; decide
            omega

end XRPL.Model.Protocol
