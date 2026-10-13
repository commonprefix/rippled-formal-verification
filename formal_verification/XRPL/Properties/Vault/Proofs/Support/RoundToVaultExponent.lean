import XRPL.Properties.Vault.Proofs.Support.ClampFacts

/-! # `roundToVaultExponent`

Facts about `RawVault.roundToVaultExponent`, the rounding of a deposit onto the vault's grid. -/

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol

/-- `roundToVaultExponent` is the identity on integral amounts. -/
lemma roundToVaultExponent_integral (amountDeposit : STAmount) (assetsTotal : Number)
    (hint : amountDeposit.integral = true) :
    roundToVaultExponent amountDeposit assetsTotal = .ok amountDeposit := by
  unfold roundToVaultExponent
  rw [if_pos hint]
  rfl

/-- **KEYSTONE.** The rounded deposit amount is stored canonically (or is zero)
whenever the raw `amountDeposit` is. Integral amounts pass through unchanged; a
fractional amount rounds via the `roundToExponent` pipeline, whose output is
`IOUCanonical`-or-zero. -/
lemma roundToVaultExponent_canonical_or_isZero (amountDeposit rounded : STAmount)
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
    have hcz : (STAmount.FracCanonZero amountDeposit) :=
      ⟨(hcanon.2 hfr).is_fractional, Or.inl (hcanon.2 hfr)⟩
    unfold roundToVaultExponent at hok
    rw [if_neg (by rw [hfr]; exact Bool.false_ne_true)] at hok
    simp only [pure_bind] at hok
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
lemma RawVault.roundToVaultExponent_nonneg (amountDeposit result : STAmount) (assetsTotal : Number)
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
    simp only [pure_bind] at hok
    obtain ⟨postScale, hps, hrx⟩ := bind_ok_peel _ _ _ hok
    unfold postSumExponent at hps
    obtain ⟨_, -, hps⟩ := bind_ok_peel _ _ _ hps
    obtain ⟨assetsTotal', -, hps⟩ := bind_ok_peel _ _ _ hps
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

end XRPL.Model.SingleAssetVault
