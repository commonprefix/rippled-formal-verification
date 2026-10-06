import XRPL.Properties.Protocol.STAmount.Sub.Common.Neg
import XRPL.Properties.Vault.Common.CmpFaithfulCanonical
import XRPL.Properties.Vault.Common.Reduction

/-! # Shapes of the withdraw clamp `clampToSumExponent T (−priced)` -/

namespace XRPL.Model.SingleAssetVault.WdMono

open XRPL.Model.Protocol

/-- A nonzero non-negative amount is positive. -/
lemma pos_of_nonneg (p : STAmount) (h0 : 0 ≤ p.toRat) (hz : p.mValue ≠ 0) : 0 < p.toRat := by
  have habs := STAmount.abs_toRat p
  have hm : (0 : ℚ) < (p.mValue.toNat : ℚ) := by
    have : p.mValue.toNat ≠ 0 := fun h => hz (UInt64.toNat_inj.mp (by rw [h]; rfl))
    exact_mod_cast Nat.pos_of_ne_zero this
  have hp : (0 : ℚ) < (p.mValue.toNat : ℚ) * 10 ^ p.mOffset := by positivity
  rw [← habs, abs_of_nonneg h0] at hp
  exact hp

lemma operator_add_frac_nt (v1 v2 r : STAmount) (mode : rounding_mode)
    (h1 : v1.mNumericType = .fractional)
    (hok : v1.operator_add v2 mode = .ok r) : r.mNumericType = .fractional := by
  have hint : ¬ v1.integral = true := by
    show ¬ v1.mNumericType.isIntegral = true; rw [h1]; decide
  unfold STAmount.operator_add at hok
  by_cases hcmp : (!STAmount.areComparable v1 v2) = true
  · rw [if_pos hcmp] at hok; exact absurd hok (by simp)
  rw [if_neg hcmp] at hok
  by_cases h2z : (v2.mValue == 0) = true
  · rw [if_pos h2z] at hok; rw [← Except.ok.inj hok]; exact h1
  rw [if_neg h2z] at hok
  by_cases h1z : (v1.mValue == 0) = true
  · rw [if_pos h1z] at hok
    unfold STAmount.checked at hok
    rw [STAmount.canonicalize_mNumericType _ r mode hok]
    exact h1
  rw [if_neg h1z] at hok
  rw [if_neg hint] at hok
  cases h1i : v1.iou mode with
  | error e => rw [h1i] at hok; exact absurd hok (by simp)
  | ok i1 =>
    rw [h1i] at hok
    simp only [] at hok
    cases h2i : v2.iou mode with
    | error e => rw [h2i] at hok; exact absurd hok (by simp)
    | ok i2 =>
      rw [h2i] at hok
      simp only [] at hok
      cases hs : IOUAmount.operator_add i1 i2 mode with
      | error e => rw [hs] at hok; exact absurd hok (by simp)
      | ok sumI =>
        rw [hs] at hok
        simp only [] at hok
        unfold STAmount.ofIOUAmount at hok
        rw [STAmount.canonicalize_mNumericType _ r mode hok]
        rfl

lemma roundToExponent_frac_nt (value result : STAmount) (s : ℤ) (mode : rounding_mode)
    (h : value.mNumericType = .fractional)
    (hok : STAmount.roundToExponent value s mode = .ok result) :
    result.mNumericType = .fractional := by
  have hint : ¬ value.integral = true := by
    show ¬ value.mNumericType.isIntegral = true; rw [h]; decide
  unfold STAmount.roundToExponent at hok
  rw [if_neg hint] at hok
  by_cases hz : value.isZero = true
  · rw [if_pos hz] at hok; rw [← Except.ok.inj hok]; exact h
  rw [if_neg hz] at hok
  by_cases hge : value.exponent ≥ s
  · rw [if_pos hge] at hok; rw [← Except.ok.inj hok]; exact h
  rw [if_neg hge] at hok
  cases hc : STAmount.checked value.mNumericType kMinValue s value.negative mode with
  | error e => rw [hc] at hok; exact absurd hok (by simp)
  | ok ref =>
    rw [hc] at hok
    simp only [] at hok
    cases ha : STAmount.operator_add value ref mode with
    | error e => rw [ha] at hok; exact absurd hok (by simp)
    | ok sum =>
      rw [ha] at hok
      simp only [] at hok
      have hsum : sum.mNumericType = .fractional :=
        operator_add_frac_nt value ref sum mode h ha
      unfold STAmount.operator_sub at hok
      exact operator_add_frac_nt sum ref.operator_neg result mode hsum hok

/-- A fractional zero amount is reported non-positive. -/
lemma fnp_zero (a : STAmount) (ht : a.mNumericType = .fractional) (hz : a.mValue = 0) :
    a.isFractionalNonPositive = .ok true := by
  unfold STAmount.isFractionalNonPositive
  have hint : ¬ a.integral = true := by
    show ¬ a.mNumericType.isIntegral = true; rw [ht]; decide
  rw [if_neg hint]
  have hz0 : STAmount.zero a.numericType = ⟨.fractional, 0, -100, false⟩ := by
    show STAmount.zero a.mNumericType = _; rw [ht]; rfl
  rw [hz0]
  unfold STAmount.operator_le STAmount.operator_lt STAmount.areComparable
  rcases hn : a.mIsNegative <;> simp [ht, hz]

/-- On an integral asset the clamp returns the (non-negative) price itself. -/
lemma clampToSumExponent_neg_int_toRat (T : Number) (p a : STAmount) (hint : p.integral = true) (hnn : 0 ≤ p.toRat)
    (hcl : clampToSumExponent T p.operator_neg = .ok a) : a.toRat = p.toRat := by
  have hint' : p.operator_neg.integral = true := by
    unfold STAmount.integral at hint ⊢; rw [STAmount.operator_neg_mNumericType]; exact hint
  unfold clampToSumExponent at hcl
  simp only [hint', if_true, pure, Except.pure] at hcl
  rw [← Except.ok.inj hcl]
  by_cases hz : p.mValue = 0
  · have hid : p.operator_neg = p := by unfold STAmount.operator_neg; simp [hz]
    split <;> simp only [hid]
  · rw [STAmount.operator_neg_of_ne p hz]
    by_cases hneg : p.mIsNegative = true
    · exfalso
      have := STAmount.toRat_of_neg p hneg
      have := pos_of_nonneg p hnn hz
      have h2 : (0 : ℚ) < (p.mValue.toNat : ℚ) * 10 ^ p.mOffset := by
        have : p.mValue.toNat ≠ 0 := fun h => hz (UInt64.toNat_inj.mp (by rw [h]; rfl))
        have : (0 : ℚ) < (p.mValue.toNat : ℚ) := by exact_mod_cast Nat.pos_of_ne_zero this
        positivity
      linarith
    · have hn : p.mIsNegative = false := by simpa using hneg
      simp only [STAmount.negative, hn, Bool.not_false, if_true]
      rw [STAmount.operator_neg_of_ne _ (by simpa using hz)]
      rcases p with ⟨nt, mv, mo, mn⟩
      simp only at hn ⊢
      subst hn
      rfl

/-- On a positive canonical fractional price the clamp rounds the price down onto
the exponent of the rounded post-sum total. -/
lemma clamp_neg_frac (T : Number) (p a : STAmount) (hc : p.IOUCanonical) (hpos : 0 < p.toRat)
    (hcl : clampToSumExponent T p.operator_neg = .ok a) :
    ∃ dn s pe, p.operator_neg.toNumber .to_nearest = .ok dn ∧
      T.operator_add dn .to_nearest = .ok s ∧ numberExponent s .fractional = .ok pe ∧
      STAmount.roundToExponent p pe .downward = .ok a := by
  have hz : p.mValue ≠ 0 := by
    intro h; have := hc.mant_lo; rw [h] at this; simp at this
  have hn : p.mIsNegative = false := by
    by_contra h
    have h1 := STAmount.toRat_of_neg p (by simpa using h)
    have : (0 : ℚ) ≤ (p.mValue.toNat : ℚ) * 10 ^ p.mOffset := by positivity
    linarith
  have hqn : p.operator_neg.negative = true := by
    rw [STAmount.operator_neg_of_ne p hz]; simp [STAmount.negative, hn]
  have hqi : ¬ p.operator_neg.integral = true := by
    unfold STAmount.integral; rw [STAmount.operator_neg_mNumericType, hc.is_fractional]; decide
  have hqq : p.operator_neg.operator_neg = p := by
    rw [STAmount.operator_neg_of_ne p hz, STAmount.operator_neg_of_ne _ (by simpa using hz)]
    rcases p with ⟨nt, mv, mo, mn⟩
    simp only at hn ⊢
    subst hn
    rfl
  have hqt : p.operator_neg.numericType = .fractional := by
    show p.operator_neg.mNumericType = _; rw [STAmount.operator_neg_mNumericType]; exact hc.is_fractional
  unfold clampToSumExponent at hcl
  simp only [hqn, hqq, if_true, pure_bind] at hcl
  rw [if_neg hqi] at hcl
  obtain ⟨pe, hpe, hcl⟩ := bind_ok_peel _ _ _ hcl
  unfold postSumExponent at hpe
  obtain ⟨dn, hdn, hpe⟩ := bind_ok_peel _ _ _ hpe
  obtain ⟨s, hs, hpe⟩ := bind_ok_peel _ _ _ hpe
  rw [hqt] at hpe
  exact ⟨dn, s, pe, hdn, hs, hpe, hcl⟩

end XRPL.Model.SingleAssetVault.WdMono
