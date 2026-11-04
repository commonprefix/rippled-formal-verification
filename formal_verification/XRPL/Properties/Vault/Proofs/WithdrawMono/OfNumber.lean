import XRPL.Properties.Protocol.STAmount.Sub.Common.Neg
import XRPL.Properties.Vault.Proofs.Support.Integral
import XRPL.Properties.Vault.Proofs.Support.IntegralFacts
import XRPL.Properties.Vault.Proofs.WithdrawMono.Exponent

/-! # `.to_nearest` `ofNumber` on a non-negative source: shape and monotonicity -/

namespace XRPL.Model.SingleAssetVault.WdMono

open XRPL.Model.Protocol

/-- A nonzero fractional pack of a positive source is canonical, positive, within
half a unit of its own exponent, at exponent `k+3` or `k+4`. -/
lemma frac_pack (n : Number) (r : STAmount) (hn : n.isNormalized)
    (hneg : n.negative_ = false) (hnz : n.mantissa_ ≠ 0)
    (hok : STAmount.ofNumber .fractional n .to_nearest = .ok r) (hr : r.mValue ≠ 0) :
    r.IOUCanonical ∧ r.mIsNegative = false ∧
    |r.toRat - n.toRat| ≤ (1 / 2 : ℚ) * 10 ^ r.exponent ∧
    n.exponent_ + 3 ≤ r.exponent ∧ r.exponent ≤ n.exponent_ + 4 := by
  obtain ⟨hr_lo, hr_hi⟩ := hn.mantissaBounds_nat hnz
  have hre_lo : minExponent ≤ n.exponent_ := by
    rcases hn with h0 | ⟨_, _, _, hlo, _⟩
    · exact absurd (show n.mantissa_ = 0 by rw [h0]; rfl) hnz
    · exact hlo
  have hneg_dec : decide (n.signum < 0) = false := by rw [Number.signum_neg_decide]; exact hneg
  unfold STAmount.ofNumber at hok
  rw [if_neg (by decide : ¬ (NumericType.fractional.isIntegral = true)), hneg_dec] at hok
  simp only [Bool.false_eq_true, if_false] at hok
  cases hnorm : n.normalizeToRange kMinValue kMaxValue .to_nearest with
  | error e => rw [hnorm] at hok; exact absurd hok (by simp)
  | ok me =>
    obtain ⟨mant, exp⟩ := me
    rw [hnorm] at hok
    simp only at hok
    have hnorm' : n.normalizeToRange cMinValue cMaxValue .to_nearest = .ok (mant, exp) := hnorm
    obtain ⟨hexp, ⟨hmlo, hmhi⟩, hsgn, hexp_le⟩ :=
      ntr_tn_exp n mant exp hr_lo hr_hi (by omega) hnorm'
    have hmant_pos : 0 ≤ mant.toInt := hsgn hneg
    have hmant_natAbs : mant.toInt.natAbs = mant.toUInt64.toNat := by
      have := toUInt64_toNat_of_nonneg mant hmant_pos; omega
    have hexp_lo3 : minExponent + 3 ≤ exp := by rcases hexp with ⟨h, _⟩ | ⟨h, _⟩ <;> omega
    obtain ⟨hlo96, hhi80, hres⟩ := STAmount.checked_iou_cases .fractional mant.toUInt64 exp false
      .to_nearest rfl (by rw [← hmant_natAbs]; exact hmlo) (by rw [← hmant_natAbs]; exact hmhi)
      hexp_lo3 hexp_le r hok hr
    have hk3 : n.exponent_ + 3 ≤ exp := by rcases hexp with ⟨h, _⟩ | ⟨h, _⟩ <;> omega
    have hk4 : exp ≤ n.exponent_ + 4 := by rcases hexp with ⟨h, _⟩ | ⟨h, _⟩ <;> omega
    have hhalf := normalizeToRange_16_within_half_ulp n mant exp hr_lo hr_hi (by omega)
      (by have : maxExponent = 32768 := rfl; omega) hnorm'
    have hval : r.toRat = (mant.toInt : ℚ) * 10 ^ exp := by
      rw [hres, STAmount.toRat_of_nonneg _ rfl]
      show ((mant.toUInt64.toNat : ℕ) : ℚ) * 10 ^ exp = _
      have : ((mant.toUInt64.toNat : ℕ) : ℤ) = mant.toInt := toUInt64_toNat_of_nonneg mant hmant_pos
      rw [← this]; push_cast; ring
    have hre : r.exponent = exp := by rw [hres]; rfl
    refine ⟨?_, by rw [hres], ?_, by omega, by omega⟩
    · rw [hres]
      exact ⟨rfl, by rw [← hmant_natAbs]; exact hmlo, by rw [← hmant_natAbs]; exact hmhi,
        hlo96, hhi80⟩
    · rw [hval, hre]
      refine le_trans hhalf ?_
      have : (10 : ℚ) ^ (n.exponent_ + 3) ≤ 10 ^ exp := zpow_le_zpow_right₀ (by norm_num) hk3
      linarith

/-- An integral `.to_nearest` pack of a non-negative source is the nearest integer. -/
lemma int_pack (nt : NumericType) (hint : nt.isIntegral = true) (n : Number) (r : STAmount)
    (hn : n.isNormalized) (hnn : 0 ≤ n.toRat)
    (hok : STAmount.ofNumber nt n .to_nearest = .ok r) :
    ∃ z : ℤ, r.toRat = z ∧ 0 ≤ z ∧ |(z : ℚ) - n.toRat| ≤ 1 / 2 ∧
      r.mOffset = 0 ∧ r.mValue.toNat ≤ maxRep.toNat ∧ r.mNumericType = nt := by
  have hneg := Number.negative_false_of_nonneg n hn hnn
  have hneg_dec : decide (n.signum < 0) = false := by rw [Number.signum_neg_decide]; exact hneg
  obtain ⟨hnt, hoff, hmax⟩ := STAmount.ofNumber_integral_facts nt n .to_nearest r hint hok
  unfold STAmount.ofNumber at hok
  rw [if_pos hint, hneg_dec] at hok
  simp only [Bool.false_eq_true, if_false] at hok
  cases hr : n.to_rep .to_nearest with
  | error e => rw [hr] at hok; exact absurd hok (by simp)
  | ok iv =>
    rw [hr] at hok
    simp only [] at hok
    obtain ⟨hnn', hle⟩ := Number.to_rep_nonneg_range n .to_nearest iv hneg hr
    have hval : iv.toUInt64.toNat ≤ maxRep.toNat := toUInt64_toNat_le_maxRep iv hnn' hle
    have hint' : (STAmount.unchecked nt iv.toUInt64 0 false).integral = true := hint
    obtain ⟨_, _, _, htr⟩ := STAmount.canonicalize_integral_facts
      (STAmount.unchecked nt iv.toUInt64 0 false) r .to_nearest hint' rfl hval hok
    refine ⟨iv.toInt, ?_, hnn', Number.to_rep_to_nearest_within_half n iv hn hneg hr, hoff,
      hmax, hnt⟩
    rw [htr, STAmount.toRat_of_nonneg _ rfl]
    show ((iv.toUInt64.toNat : ℕ) : ℚ) * 10 ^ (0 : ℤ) = _
    rw [zpow_zero, mul_one]
    exact_mod_cast toUInt64_toNat_of_nonneg iv hnn'

/-- A `.to_nearest` pack of a non-negative source is non-negative. -/
lemma ofNumber_nonneg (nt : NumericType) (n : Number) (r : STAmount) (hn : n.isNormalized)
    (hnn : 0 ≤ n.toRat) (hok : STAmount.ofNumber nt n .to_nearest = .ok r) : 0 ≤ r.toRat := by
  by_cases hint : nt.isIntegral = true
  · obtain ⟨z, hz, hz0, -, -, -, -⟩ := int_pack nt hint n r hn hnn hok
    rw [hz]; exact_mod_cast hz0
  have hfr := NumericType.eq_fractional_of_not_integral (by simpa using hint)
  subst hfr
  by_cases hr : r.mValue = 0
  · rw [STAmount.toRat_eq_zero_of_mValue_zero r hr]
  by_cases hnz : n.mantissa_ = 0
  · rw [Number.eq_zero_of_mantissa_zero n hn hnz] at hok
    rw [zero_frac_eq r hok] at hr; exact absurd rfl hr
  have hneg := Number.negative_false_of_nonneg n hn hnn
  obtain ⟨-, hrneg, -, -, -⟩ := frac_pack n r hn hneg hnz hok hr
  rw [STAmount.toRat_of_nonneg r hrneg]; positivity

/-- `.to_nearest` `ofNumber` is monotone on non-negative sources. -/
lemma ofNumber_mono (nt : NumericType) (n₁ n₂ : Number) (r₁ r₂ : STAmount)
    (hn₁ : n₁.isNormalized) (hn₂ : n₂.isNormalized) (h0 : 0 ≤ n₁.toRat)
    (hle : n₁.toRat ≤ n₂.toRat)
    (hok₁ : STAmount.ofNumber nt n₁ .to_nearest = .ok r₁)
    (hok₂ : STAmount.ofNumber nt n₂ .to_nearest = .ok r₂) :
    r₁.toRat ≤ r₂.toRat := by
  have h0₂ : 0 ≤ n₂.toRat := le_trans h0 hle
  have hdet : n₁.toRat = n₂.toRat → r₁.toRat = r₂.toRat := fun heq => by
    have := Number.isNormalized.toRat_inj hn₁ hn₂ heq
    subst this
    rw [Except.ok.inj (hok₁.symm.trans hok₂)]
  by_contra hlt
  push Not at hlt
  by_cases hint : nt.isIntegral = true
  · obtain ⟨z₁, hz₁, -, hh₁, -⟩ := int_pack nt hint n₁ r₁ hn₁ h0 hok₁
    obtain ⟨z₂, hz₂, -, hh₂, -⟩ := int_pack nt hint n₂ r₂ hn₂ h0₂ hok₂
    rw [hz₁, hz₂] at hlt
    have hzz : z₂ + 1 ≤ z₁ := by exact_mod_cast (show z₂ < z₁ by exact_mod_cast hlt)
    have hq : (z₂ : ℚ) + 1 ≤ z₁ := by exact_mod_cast hzz
    have h1 := (abs_le.mp hh₁).2
    have h2 := (abs_le.mp hh₂).1
    have heq : n₁.toRat = n₂.toRat := by linarith
    have := hdet heq
    linarith
  have hfr := NumericType.eq_fractional_of_not_integral (by simpa using hint)
  subst hfr
  have hr₂nn := ofNumber_nonneg .fractional n₂ r₂ hn₂ h0₂ hok₂
  by_cases hr₁ : r₁.mValue = 0
  · rw [STAmount.toRat_eq_zero_of_mValue_zero r₁ hr₁] at hlt; linarith
  have hnz₁ : n₁.mantissa_ ≠ 0 := by
    intro h; rw [Number.eq_zero_of_mantissa_zero n₁ hn₁ h] at hok₁
    rw [zero_frac_eq r₁ hok₁] at hr₁; exact hr₁ rfl
  have hneg₁ := Number.negative_false_of_nonneg n₁ hn₁ h0
  obtain ⟨hc₁, hs₁, hh₁, _, _⟩ := frac_pack n₁ r₁ hn₁ hneg₁ hnz₁ hok₁ hr₁
  -- exponents are ordered
  set j := r₁.exponent - 4 with hj
  have hj0 : -100 ≤ j := by have := hc₁.exp_lo; unfold STAmount.exponent at hj; omega
  have hC := (exp_ge_iff n₁ r₁ hn₁ h0 hok₁ j hj0).mp (by omega)
  have hE := (exp_ge_iff n₂ r₂ hn₂ h0₂ hok₂ j hj0).mpr (le_trans hC hle)
  have hnz₂ : n₂.mantissa_ ≠ 0 := by
    intro h; rw [Number.eq_zero_of_mantissa_zero n₂ hn₂ h] at hok₂
    rw [zero_frac_eq r₂ hok₂] at hE; unfold STAmount.exponent at hE; simp at hE; omega
  have hneg₂ := Number.negative_false_of_nonneg n₂ hn₂ h0₂
  have hr₂ : r₂.mValue ≠ 0 := by
    intro hz
    obtain ⟨exp, _, hres⟩ := ofNumber_frac_tn_exp n₂ r₂ hn₂ hneg₂ hnz₂ hok₂
    rcases hres with ⟨_, _, he⟩ | ⟨_, h, _⟩
    · omega
    · exact h hz
  obtain ⟨hc₂, hs₂, hh₂, _, _⟩ := frac_pack n₂ r₂ hn₂ hneg₂ hnz₂ hok₂ hr₂
  have hv₁ := STAmount.toRat_of_nonneg r₁ hs₁
  have hv₂ := STAmount.toRat_of_nonneg r₂ hs₂
  have hE₁ : r₁.exponent = r₁.mOffset := rfl
  have hE₂ : r₂.exponent = r₂.mOffset := rfl
  rcases lt_or_eq_of_le (show r₁.mOffset ≤ r₂.mOffset by omega) with hlt' | heq'
  · -- a larger exponent dominates
    have hm₁ : (r₁.mValue.toNat : ℚ) < 10 ^ 16 := by exact_mod_cast hc₁.mant_hi
    have hm₂ : (10 : ℚ) ^ 15 ≤ (r₂.mValue.toNat : ℚ) := by exact_mod_cast hc₂.mant_lo
    have hp : (10 : ℚ) ^ (r₁.mOffset + 1) ≤ 10 ^ r₂.mOffset :=
      zpow_le_zpow_right₀ (by norm_num) (by omega)
    rw [zpow_add₀ (by norm_num), zpow_one] at hp
    have hp0 : (0 : ℚ) < 10 ^ r₁.mOffset := zpow_pos (by norm_num) _
    have : r₁.toRat < r₂.toRat := by
      rw [hv₁, hv₂]
      calc (r₁.mValue.toNat : ℚ) * 10 ^ r₁.mOffset < 10 ^ 16 * 10 ^ r₁.mOffset := by
            exact mul_lt_mul_of_pos_right hm₁ hp0
        _ = 10 ^ 15 * (10 ^ r₁.mOffset * 10) := by ring
        _ ≤ (r₂.mValue.toNat : ℚ) * 10 ^ r₂.mOffset := by
            apply mul_le_mul hm₂ hp (by positivity) (by positivity)
    linarith
  · -- same grid: an inversion needs both sources at the shared midpoint
    rw [hv₁, hv₂, ← heq'] at hlt
    have hp0 : (0 : ℚ) < 10 ^ r₁.mOffset := zpow_pos (by norm_num) _
    have hmm : r₂.mValue.toNat < r₁.mValue.toNat := by
      have := lt_of_mul_lt_mul_right hlt (le_of_lt hp0)
      exact_mod_cast this
    have hq : ((r₂.mValue.toNat : ℚ) + 1) * 10 ^ r₁.mOffset ≤
        (r₁.mValue.toNat : ℚ) * 10 ^ r₁.mOffset := by
      have : (r₂.mValue.toNat : ℚ) + 1 ≤ r₁.mValue.toNat := by exact_mod_cast hmm
      nlinarith
    rw [hE₁] at hh₁; rw [hE₂, ← heq'] at hh₂
    rw [hv₁] at hh₁; rw [hv₂, ← heq'] at hh₂
    have h1 := (abs_le.mp hh₁).2
    have h2 := (abs_le.mp hh₂).1
    have heq : n₁.toRat = n₂.toRat := by nlinarith
    have hd := hdet heq
    rw [hv₁, hv₂, ← heq'] at hd
    linarith

end XRPL.Model.SingleAssetVault.WdMono
