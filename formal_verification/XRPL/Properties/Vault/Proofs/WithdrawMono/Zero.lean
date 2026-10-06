import XRPL.Properties.Vault.Proofs.Support.FracCanon
import XRPL.Properties.Vault.Proofs.Support.Integral
import XRPL.Properties.Vault.Proofs.WithdrawMono.Clamp
import XRPL.Properties.Vault.Proofs.WithdrawMono.Exponent
import XRPL.Properties.Vault.Proofs.WithdrawMono.Grid

/-! # A zero fractional price is reported non-positive

With a zero price the clamp takes its sum branch: every step from `assetsTotal`
back to the recovered post-sum total rounds down, so the reported difference is
non-positive, which the withdrawal rejects. -/

namespace XRPL.Model.SingleAssetVault.WdMono

open XRPL.Model.Protocol

/-- The downward 16-digit pack of a positive 19-digit mantissa truncates. -/
lemma ntr_dn (n : Number) (h_lo : 10 ^ 18 ≤ n.mantissa_.toNat) (h_hi : n.mantissa_.toNat < 10 ^ 19)
    (hneg : n.negative_ = false)
    (he_lo : minExponent ≤ n.exponent_ + 3) (he_hi : n.exponent_ + 3 ≤ maxExponent) :
    n.normalizeToRange cMinValue cMaxValue .downward
      = .ok ((n.mantissa_ / 10 / 10 / 10).toInt64, n.exponent_ + 3) := by
  obtain ⟨g, _, hsbit, _, h_red⟩ :=
    doNormalize_small_facts n.negative_ n.mantissa_ n.exponent_ .downward h_lo h_hi he_lo he_hi
  have hm3 : (n.mantissa_ / 10 / 10 / 10).toNat = n.mantissa_.toNat / 1000 :=
    m_div_thousand_toNat n.mantissa_
  have hb : (g.round .downward == 1 ||
      (g.round .downward == 0 && (n.mantissa_ / 10 / 10 / 10) % 2 == 1)) = false := by
    have : g.round .downward = -1 ∨ g.round .downward = -2 := by
      unfold Guard.round
      rw [hsbit, hneg]
      split_ifs <;> simp_all
    rcases this with h | h <;> rw [h] <;> rfl
  unfold Number.normalizeToRange
  rw [h_red, doRoundUp_small_truncate g n.negative_ _ (n.exponent_ + 3) .downward .normalize2 hb
    (by rw [cMinValue_val, hm3]; omega) (by rw [cMaxValue_val, hm3]; omega) (by omega) (by omega)]
  simp [RoundResult.toNumber, hneg]

/-- The downward fractional pack of a non-negative amount stays below it and is
canonical or zero. -/
lemma ofNumber_dn (n : Number) (s2 : STAmount) (hn : n.isNormalized) (hnn : 0 ≤ n.toRat)
    (hk : n.exponent_ + 4 ≤ maxExponent)
    (hok : STAmount.ofNumber .fractional n .downward = .ok s2) :
    0 ≤ s2.toRat ∧ s2.toRat ≤ n.toRat ∧ STAmount.FracCanonZero s2 := by
  by_cases hnz : n.mantissa_ = 0
  · have hn0 : n = Number.zero := by
      rcases hn with h0 | ⟨hlo, _⟩
      · exact h0
      · exfalso; rw [hnz] at hlo; exact absurd hlo (by decide)
    subst hn0
    have h : STAmount.ofNumber .fractional Number.zero .downward
        = .ok ⟨.fractional, 0, -100, false⟩ := by rfl
    rw [h] at hok
    rw [← Except.ok.inj hok]
    exact ⟨le_refl _, by rw [Number.toRat_zero]; rfl, rfl, Or.inr rfl⟩
  have hpos : 0 < n.toRat :=
    lt_of_le_of_ne hnn (Ne.symm (Number.toRat_ne_zero_of_mantissa_ne_zero n hnz))
  have hneg : n.negative_ = false := by
    by_contra h
    have := Number.toRat_nonpos_of_negative n (by simpa using h)
    linarith
  obtain ⟨hr_lo, hr_hi⟩ := hn.mantissaBounds_nat hnz
  have hre_lo : minExponent ≤ n.exponent_ := by
    rcases hn with h0 | ⟨_, _, _, hlo, _⟩
    · exact absurd (show n.mantissa_ = 0 by rw [h0]; rfl) hnz
    · exact hlo
  have hneg_dec : decide (n.signum < 0) = false := by rw [Number.signum_neg_decide]; exact hneg
  have hm3 : (n.mantissa_ / 10 / 10 / 10).toNat = n.mantissa_.toNat / 1000 :=
    m_div_thousand_toNat n.mantissa_
  unfold STAmount.ofNumber at hok
  rw [if_neg (by decide : ¬ (NumericType.fractional.isIntegral = true)), hneg_dec] at hok
  simp only [Bool.false_eq_true, if_false] at hok
  rw [show n.normalizeToRange kMinValue kMaxValue .downward
      = .ok ((n.mantissa_ / 10 / 10 / 10).toInt64, n.exponent_ + 3) from
    ntr_dn n hr_lo hr_hi hneg (by omega) (by omega)] at hok
  simp only [] at hok
  have hX : (n.mantissa_ / 10 / 10 / 10).toInt64.toUInt64 = n.mantissa_ / 10 / 10 / 10 := by simp
  rw [hX] at hok
  by_cases hz : s2.mValue = 0
  · rw [STAmount.toRat_eq_zero_of_mValue_zero s2 hz]
    exact ⟨le_refl _, hnn, STAmount.canonicalize_fczr _ s2 .downward rfl hok⟩
  · obtain ⟨_, _, hres⟩ := STAmount.checked_iou_cases .fractional _ _ false .downward rfl
      (by rw [hm3]; omega) (by rw [hm3]; omega) (by omega) (by omega) s2 hok hz
    refine ⟨by rw [hres, STAmount.toRat_of_nonneg _ rfl]; positivity, ?_,
      STAmount.canonicalize_fczr _ s2 .downward rfl hok⟩
    rw [hres, STAmount.toRat_of_nonneg _ rfl, Number.toRat_of_nonneg n hneg]
    show ((n.mantissa_ / 10 / 10 / 10).toNat : ℚ) * 10 ^ (n.exponent_ + 3) ≤ _
    rw [hm3, zpow_add₀ (by norm_num)]
    have hk0 : (0 : ℚ) < 10 ^ n.exponent_ := zpow_pos (by norm_num) _
    have hdm : ((n.mantissa_.toNat / 1000 : ℕ) : ℚ) * 1000 ≤ (n.mantissa_.toNat : ℚ) := by
      exact_mod_cast Nat.div_mul_le_self _ _
    have : (10 : ℚ) ^ (3 : ℤ) = 1000 := by norm_num
    rw [this]
    nlinarith

/-- The fractional `.to_nearest` pack of a non-positive amount is zero or negative. -/
lemma ofNumber_nonpos (d : Number) (a : STAmount) (hd : d.isNormalized) (hdn : d.toRat ≤ 0)
    (hok : STAmount.ofNumber .fractional d .to_nearest = .ok a) :
    a.mValue = 0 ∨ a.mIsNegative = true := by
  by_cases hnz : d.mantissa_ = 0
  · have hn0 : d = Number.zero := by
      rcases hd with h0 | ⟨hlo, _⟩
      · exact h0
      · exfalso; rw [hnz] at hlo; exact absurd hlo (by decide)
    subst hn0
    have h : STAmount.ofNumber .fractional Number.zero .to_nearest
        = .ok ⟨.fractional, 0, -100, false⟩ := by rfl
    rw [h] at hok
    rw [← Except.ok.inj hok]
    exact Or.inl rfl
  have hneg : d.negative_ = true := by
    by_contra h
    have h1 := Number.toRat_nonneg_of_nonnegative d (by simpa using h)
    have := Number.toRat_ne_zero_of_mantissa_ne_zero d hnz
    exact this (le_antisymm hdn h1)
  set w := d.operator_neg with hw
  have hwn : w.isNormalized := Number.operator_neg_isNormalized d hd
  have hwm : w.mantissa_ = d.mantissa_ := Number.operator_neg_mantissa_of_ne d hnz
  have hwe : w.exponent_ = d.exponent_ := by
    rw [hw]; unfold Number.operator_neg; rw [if_neg (by simpa using hnz)]
  have hwneg : w.negative_ = false := by
    rw [hw, Number.operator_neg_negative_of_ne d hnz, hneg]; rfl
  obtain ⟨hr_lo, hr_hi⟩ := hd.mantissaBounds_nat hnz
  have hre_lo : minExponent ≤ d.exponent_ := by
    rcases hd with h0 | ⟨_, _, _, hlo, _⟩
    · exact absurd (show d.mantissa_ = 0 by rw [h0]; rfl) hnz
    · exact hlo
  have hneg_dec : decide (d.signum < 0) = true := by rw [Number.signum_neg_decide]; exact hneg
  unfold STAmount.ofNumber at hok
  rw [if_neg (by decide : ¬ (NumericType.fractional.isIntegral = true)), hneg_dec] at hok
  simp only [if_true] at hok
  rw [← hw] at hok
  cases hnorm : w.normalizeToRange kMinValue kMaxValue .to_nearest with
  | error e => rw [hnorm] at hok; exact absurd hok (by simp)
  | ok me =>
    obtain ⟨mant, exp⟩ := me
    rw [hnorm] at hok
    simp only at hok
    obtain ⟨hexp, ⟨hmlo, hmhi⟩, hsgn, hexp_le⟩ :=
      ntr_tn_exp w mant exp (by rw [hwm]; exact hr_lo) (by rw [hwm]; exact hr_hi)
        (by rw [hwe]; omega) hnorm
    have hmant_pos : 0 ≤ mant.toInt := hsgn hwneg
    have hmant_natAbs : mant.toInt.natAbs = mant.toUInt64.toNat := by
      have := toUInt64_toNat_of_nonneg mant hmant_pos; omega
    have hexp_lo3 : minExponent + 3 ≤ exp := by
      rw [hwe] at hexp; rcases hexp with ⟨h, _⟩ | ⟨h, _⟩ <;> omega
    by_cases hz : a.mValue = 0
    · exact Or.inl hz
    · obtain ⟨_, _, hres⟩ := STAmount.checked_iou_cases .fractional mant.toUInt64 exp true
        .to_nearest rfl (by rw [← hmant_natAbs]; exact hmlo) (by rw [← hmant_natAbs]; exact hmhi)
        hexp_lo3 hexp_le a hok hz
      right; rw [hres]

/-- A fractional amount that is zero or negative is reported non-positive. -/
lemma fnp_nonpos (a : STAmount) (ht : a.mNumericType = .fractional)
    (h : a.mValue = 0 ∨ a.mIsNegative = true) :
    a.isFractionalNonPositive = .ok true := by
  unfold STAmount.isFractionalNonPositive
  have hint : ¬ a.integral = true := by
    show ¬ a.mNumericType.isIntegral = true; rw [ht]; decide
  rw [if_neg hint]
  have hz0 : STAmount.zero a.numericType = ⟨.fractional, 0, -100, false⟩ := by
    show STAmount.zero a.mNumericType = _; rw [ht]; rfl
  rw [hz0]
  unfold STAmount.operator_le STAmount.operator_lt STAmount.areComparable
  rcases h with h | h
  · rcases hn : a.mIsNegative <;> simp [ht, h]
  · simp [ht, h]

/-- A post-sum exponent is at most `80`. -/
lemma pe_le (s : Number) (pe : ℤ) (h : numberExponent s .fractional = .ok pe) : pe ≤ 80 := by
  unfold numberExponent at h
  cases hr : STAmount.ofNumber .fractional s .to_nearest with
  | error err => rw [hr] at h; exact absurd h (by simp [bind, Except.bind])
  | ok r =>
    rw [hr] at h
    have he : r.exponent = pe := Except.ok.inj h
    rcases exp_cases s r hr with h1 | ⟨_, h2⟩ <;> omega

/-- A successful fractional pack of the total bounds its exponent. -/
lemma total_exp_le (T : Number) (atr : STAmount) (hTn : T.isNormalized) (hT0 : 0 ≤ T.toRat)
    (hatr : STAmount.ofNumber .fractional T .to_nearest = .ok atr) :
    T.exponent_ + 4 ≤ maxExponent := by
  by_cases hnz : T.mantissa_ = 0
  · have hn0 : T = Number.zero := by
      rcases hTn with h0 | ⟨hlo, _⟩
      · exact h0
      · exfalso; rw [hnz] at hlo; exact absurd hlo (by decide)
    subst hn0; decide
  have hpos : 0 < T.toRat :=
    lt_of_le_of_ne hT0 (Ne.symm (Number.toRat_ne_zero_of_mantissa_ne_zero T hnz))
  have hneg : T.negative_ = false := by
    by_contra h
    have := Number.toRat_nonpos_of_negative T (by simpa using h)
    linarith
  obtain ⟨exp, hexp, hres⟩ := ofNumber_frac_tn_exp T atr hTn hneg hnz hatr
  have h80 := exp_cases T atr hatr
  have hme : maxExponent = 32768 := rfl
  rcases hres with ⟨hlt, _, _⟩ | ⟨_, _, he⟩ <;> rcases hexp with ⟨h, _⟩ | ⟨h, _⟩ <;> omega

open private sumAndRoundToExponent from XRPL.Model.Protocol.Rounding in
/-- **A zero fractional price is reported non-positive.** -/
lemma clamp_zero_frac (T : Number) (p a atr : STAmount) (hTn : T.isNormalized)
    (hT0 : 0 ≤ T.toRat) (hfrac : p.mNumericType = .fractional) (hz : p.mValue = 0)
    (hatr : STAmount.ofNumber .fractional T .to_nearest = .ok atr)
    (hcl : clampToSumExponent T p.operator_neg = .ok a) :
    a.isFractionalNonPositive = .ok true := by
  have hid : p.operator_neg = p := by unfold STAmount.operator_neg; simp [hz]
  rw [hid] at hcl
  have hpi : ¬ p.integral = true := by
    show ¬ p.mNumericType.isIntegral = true; rw [hfrac]; decide
  have hpt : p.numericType = .fractional := hfrac
  unfold clampToSumExponent at hcl
  simp only [hid, ite_self, pure_bind] at hcl
  rw [if_neg hpi] at hcl
  obtain ⟨pe, hpe, hcl⟩ := bind_ok_peel _ _ _ hcl
  have hpe80 : pe ≤ 80 := by
    unfold postSumExponent at hpe
    obtain ⟨dn, _, hpe⟩ := bind_ok_peel _ _ _ hpe
    obtain ⟨s, _, hpe⟩ := bind_ok_peel _ _ _ hpe
    rw [hpt] at hpe
    exact pe_le s pe hpe
  by_cases hneg : p.negative = true
  · rw [if_pos hneg] at hcl
    have hpz : p.isZero = true := by unfold STAmount.isZero; simp [hz]
    unfold STAmount.roundToExponent at hcl
    rw [if_neg hpi, if_pos hpz] at hcl
    rw [← Except.ok.inj hcl]
    exact fnp_zero p hfrac hz
  · rw [if_neg hneg] at hcl
    obtain ⟨sum, hsum, hcl⟩ := bind_ok_peel _ _ _ hcl
    obtain ⟨d, hd, hcl⟩ := bind_ok_peel _ _ _ hcl
    unfold sumAndRoundToExponent at hsum
    obtain ⟨dn, hdn, hsum⟩ := bind_ok_peel _ _ _ hsum
    obtain ⟨s1, hs1, hsum⟩ := bind_ok_peel _ _ _ hsum
    obtain ⟨s2, hs2, hsum⟩ := bind_ok_peel _ _ _ hsum
    obtain ⟨s3, hs3, hsum⟩ := bind_ok_peel _ _ _ hsum
    have hdn0 : dn = Number.zero := by
      rw [STAmount.toNumber_zero_fractional p .downward (by simpa using hpi) hz] at hdn
      exact (Except.ok.inj hdn).symm
    have hs1T : s1 = T := by
      rw [hdn0] at hs1
      unfold Number.operator_add at hs1
      rw [if_pos (by decide)] at hs1
      exact (Except.ok.inj hs1).symm
    rw [hs1T, hpt] at hs2
    obtain ⟨hs2nn, hs2T, hs2nt, hs2c⟩ :=
      ofNumber_dn T s2 hTn hT0 (total_exp_le T atr hTn hT0 hatr) hs2
    -- the rounded post-sum total stays below the stored one
    have hs3le : s3.toRat ≤ s2.toRat := by
      rcases hs2c with hc | h0
      · have hs2pos : 0 < s2.toRat := pos_of_nonneg s2 hs2nn (by
          intro h; have := hc.mant_lo; rw [h] at this; simp at this)
        exact (rte_facts s2 s3 pe hc hs2pos hpe80 hs3).2.1
      · have hs2i : ¬ s2.integral = true := by
          show ¬ s2.mNumericType.isIntegral = true; rw [hs2nt]; decide
        unfold STAmount.roundToExponent at hs3
        rw [if_neg hs2i, if_pos (by unfold STAmount.isZero; simp [h0])] at hs3
        rw [← Except.ok.inj hs3]
    obtain ⟨hs3nt, hs3c⟩ := STAmount.roundToExponent_fczr s2 s3 pe .downward ⟨hs2nt, hs2c⟩ hs3
    have hsumv : sum.toRat = s3.toRat ∧ sum.isNormalized := by
      rcases hs3c with hc | h0
      · obtain ⟨sn, hsn, hval, hnorm⟩ := STAmount.toNumber_iou_exact s3 .downward hc
        rw [Except.ok.inj (hsum.symm.trans hsn)]; exact ⟨hval, hnorm⟩
      · have hs3i : s3.integral = false := by
          show s3.mNumericType.isIntegral = false; rw [hs3nt]; rfl
        rw [STAmount.toNumber_zero_fractional s3 .downward hs3i h0] at hsum
        rw [← Except.ok.inj hsum, Number.toRat_zero, STAmount.toRat_eq_zero_of_mValue_zero s3 h0]
        exact ⟨rfl, Or.inl rfl⟩
    have hdn : d.toRat ≤ 0 := by
      have := operator_sub_le_of_le_normalized sum T d Number.zero hsumv.2 hTn hd (Or.inl rfl)
        (by rw [Number.toRat_zero]; linarith [hsumv.1])
      rwa [Number.toRat_zero] at this
    have hdnorm : d.isNormalized := operator_sub_isNormalized_to_nearest' sum T d hsumv.2 hTn hd
    rw [hpt] at hcl
    exact fnp_nonpos a (STAmount.ofNumber_mNumericType _ _ _ a hcl)
      (ofNumber_nonpos d a hdnorm hdn hcl)

end XRPL.Model.SingleAssetVault.WdMono
