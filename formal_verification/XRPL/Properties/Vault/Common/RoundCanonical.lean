import XRPL.Properties.Vault.Common.OfNumberBoundary
import XRPL.Properties.Vault.Common.Reduction
import XRPL.Properties.Protocol.STAmount.Div.Common.IOU

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
    obtain ⟨_, _, hok⟩ := bind_ok_peel _ _ _ hok
    obtain ⟨_, _, hok⟩ := bind_ok_peel _ _ _ hok
    obtain ⟨postScale, _, hok⟩ := bind_ok_peel _ _ _ hok
    obtain ⟨rounded', hrx, hlast⟩ := bind_ok_peel _ _ _ hok
    have hlast' : rounded' = rounded :=
      Except.ok.inj (show Except.ok rounded' = .ok rounded from hlast)
    rw [hlast'] at hrx
    have hres := STAmount.roundToExponent_fczr amountDeposit rounded postScale .downward hcz hrx
    rcases hres.2 with hc | hzero
    · left; exact STAmount.Canonical.of_iou rounded hc
    · right; unfold STAmount.isZero; rw [hzero]; decide

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

end XRPL.Model.SingleAssetVault
