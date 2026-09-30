import XRPL.Properties.Vault.Proofs.Support.STAmountFacts

/-! # Fractional canonical amounts

`STAmount.FracCanonZero` (fractional, canonical or zero) and its preservation by the amount
operators. -/

set_option maxRecDepth 4000

namespace XRPL.Model.Protocol

/-- A deposit-ready fractional amount: fractional type and stored canonically or
zero. The `roundToVaultExponent` fractional pipeline preserves this. -/
def STAmount.FracCanonZero (s : STAmount) : Prop :=
  s.mNumericType = .fractional ∧ (s.IOUCanonical ∨ s.mValue = 0)

/-- `canonicalize` on a fractional record yields a `FracCanonZero` result: the IOU
branch routes `iou → ofMantissaExp → normalize`, whose output is `InRange16`-or-zero
(`normalize_InRange16_or_zero`), and the packed record keeps the fractional type. -/
lemma STAmount.canonicalize_fczr (s result : STAmount) (mode : rounding_mode)
    (hfr : s.mNumericType = .fractional) (hok : s.canonicalize mode = .ok result) :
    (STAmount.FracCanonZero result) := by
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
    (hok : STAmount.ofIOUAmount a mode = .ok result) : (STAmount.FracCanonZero result) := by
  unfold STAmount.ofIOUAmount at hok
  exact STAmount.canonicalize_fczr _ result mode rfl hok

/-- `operator_add` of a `FracCanonZero` first operand is `FracCanonZero`: the
`v2 = 0` branch returns the operand, and both other reachable branches
(`v1 = 0` and the IOU add) canonicalize a fractional record. -/
lemma STAmount.operator_add_fczr (v1 v2 result : STAmount) (mode : rounding_mode)
    (h1 : (STAmount.FracCanonZero v1)) (hok : STAmount.operator_add v1 v2 mode = .ok result) :
    (STAmount.FracCanonZero result) := by
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
    (h1 : (STAmount.FracCanonZero v1)) (hok : STAmount.operator_sub v1 v2 mode = .ok result) :
    (STAmount.FracCanonZero result) := by
  unfold STAmount.operator_sub at hok
  exact STAmount.operator_add_fczr v1 v2.operator_neg result mode h1 hok

/-- `roundToExponent` of a `FracCanonZero` value is `FracCanonZero`: the three
early exits pass the value through, and the general path is
`operator_sub (operator_add value reference) reference`, each preserving the
predicate (the reference is a fractional `checked`). -/
lemma STAmount.roundToExponent_fczr (value result : STAmount) (scale : Int)
    (rounding : rounding_mode) (h : (STAmount.FracCanonZero value))
    (hok : STAmount.roundToExponent value scale rounding = .ok result) :
    (STAmount.FracCanonZero result) := by
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
          have hsum_fczr : (STAmount.FracCanonZero sum) :=
            STAmount.operator_add_fczr value referenceValue sum rounding ⟨hnt, hcz⟩ hsum
          exact STAmount.operator_sub_fczr sum referenceValue result rounding hsum_fczr hok

/-- A fractional `ofNumber` on a normalized source lands canonical-or-zero. -/
lemma STAmount.ofNumber_frac_fczr (n : Number) (mode : rounding_mode)
    (result : STAmount) (hn : n.mantissa_ ≠ 0 → n.isNormalized)
    (hok : STAmount.ofNumber .fractional n mode = .ok result) :
    STAmount.FracCanonZero result := by
  refine ⟨STAmount.ofNumber_mNumericType _ _ _ _ hok, ?_⟩
  by_cases hm : n.mantissa_ = 0
  · refine Or.inr ?_
    by_contra h
    exact (XRPL.Model.Protocol.STAmount.ofNumber_iou_mantissa_ne_zero .fractional n mode result rfl
      hok h) hm
  · have hn := hn hm
    obtain ⟨hlo19, hhi19⟩ := hn.mantissaBounds_nat hm
    have hexp_lo : minExponent ≤ n.exponent_ := by
      rcases hn with h0 | ⟨_, _, _, hlo, _⟩
      · exact absurd (show n.mantissa_ = 0 by rw [h0]; rfl) hm
      · exact hlo
    exact STAmount.ofNumber_iou_canonical_or_zero n mode result hlo19 hhi19 hexp_lo hok

/-- Negation preserves `FracCanonZero`: it flips only the sign flag (or is the
identity on zero), leaving the type, magnitude, and exponent untouched. -/
lemma STAmount.operator_neg_fczr (s : STAmount) (h : STAmount.FracCanonZero s) :
    STAmount.FracCanonZero (s.operator_neg) := by
  obtain ⟨hnt, hcz⟩ := h
  unfold STAmount.operator_neg
  by_cases hz : s.mValue = 0
  · rw [if_pos (beq_iff_eq.mpr hz)]; exact ⟨hnt, hcz⟩
  · rw [if_neg (fun hb => hz (beq_iff_eq.mp hb))]
    refine ⟨hnt, ?_⟩
    rcases hcz with hc | hcv
    · exact Or.inl ⟨hnt, hc.mant_lo, hc.mant_hi, hc.exp_lo, hc.exp_hi⟩
    · exact Or.inr hcv

end XRPL.Model.Protocol
