import XRPL.Properties.Vault.Proofs.WithdrawAccuracy.Pipe

/-! # The lower bound on a final withdrawal's payout -/

namespace XRPL.Model.SingleAssetVault.WdAcc

open XRPL.Model.Protocol

/-- A nonzero fractional-canonical amount is at least `10 ^ (-81)` in magnitude. -/
lemma iou_abs_ge (s : STAmount) (hc : s.IOUCanonical) : (10 : ℚ) ^ (-81 : ℤ) ≤ |s.toRat| := by
  rw [STAmount.abs_toRat]
  have h1 : ((10 ^ 15 : ℕ) : ℚ) ≤ (s.mValue.toNat : ℚ) := by exact_mod_cast hc.mant_lo
  have h2 : (10 : ℚ) ^ (-96 : ℤ) ≤ 10 ^ s.mOffset := zpow_le_zpow_right₀ (by norm_num) hc.exp_lo
  calc (10 : ℚ) ^ (-81 : ℤ) = ((10 ^ 15 : ℕ) : ℚ) * 10 ^ (-96 : ℤ) := by norm_num
    _ ≤ (s.mValue.toNat : ℚ) * 10 ^ s.mOffset :=
        mul_le_mul h1 h2 (by positivity) (by positivity)

/-- Between two nonnegative fractional-canonical amounts, the smaller one never has
the larger exponent. -/
lemma iou_offset_le (a b : STAmount) (ha : a.IOUCanonical) (hb : b.IOUCanonical)
    (ha0 : 0 ≤ a.toRat) (hle : a.toRat ≤ b.toRat) : a.mOffset ≤ b.mOffset := by
  by_contra h
  push_neg at h
  have := STAmount.abs_lt_of_offset_lt b a ⟨hb.mant_lo, hb.mant_hi⟩ ⟨ha.mant_lo, ha.mant_hi⟩ h
  rw [abs_of_nonneg (le_trans ha0 hle), abs_of_nonneg ha0] at this
  linarith

/-- A payout priced from `sh` that passed the funds guard sits under
`assetsAvailable`, so `assetsAvailable` is at least the shares' worth less the
stage error and two grid steps of its own packed form `aa`. -/
lemma final_payout_lower (v : Vault) (sh p aa : STAmount) (w : Bool) (an : Number)
    (hc : sh.Canonical) (hnav : v.WithdrawNavExact w)
    (hp : v.sharesToAssetsWithdraw sh w = .ok p)
    (han : p.toNumber .to_nearest = .ok an)
    (hlt : v.assetsAvailable.operator_lt an = false)
    (haa : STAmount.ofNumber v.numericType v.assetsAvailable .to_nearest = .ok aa)
    (haav : aa.toRat = v.assetsAvailable.toRat) (hpos : 0 < v.assetsAvailable.toRat) :
    v.idealAssetsWithdraw w sh.toRat * (1 - depositε) - 2 * (10 : ℚ) ^ aa.exponent ≤
      v.assetsAvailable.toRat := by
  set I := v.idealAssetsWithdraw w sh.toRat with hIdef
  set AA := v.assetsAvailable.toRat with hAA
  have hε : depositε < 1 := by rw [depositε_val]; norm_num
  have hε0 : 0 ≤ depositε := by rw [depositε_val]; norm_num
  have hpow : (0 : ℚ) < 10 ^ aa.exponent := by positivity
  by_cases hsmall : I * (1 - depositε) ≤ AA
  · linarith
  push_neg at hsmall
  have hAAn := v.wf.assetsAvailable_norm
  have hAAm : v.assetsAvailable.mantissa_ ≠ 0 :=
    Number.mantissa_ne_zero_of_toRat_ne_zero hpos.ne'
  -- the funds guard: the priced payout's `toNumber` is at most `assetsAvailable`
  have hguard : an.isNormalized → an.toRat ≤ AA := fun hann => by
    by_contra hc'
    push_neg at hc'
    have := (operator_lt_iff _ _ hAAn hann).mpr hc'
    rw [this] at hlt; exact absurd hlt (by decide)
  have hIpos : AA < I := by nlinarith [mul_nonneg (le_of_lt (lt_trans hpos hsmall)) hε0]
  rcases hnt : v.numericType with ⟨mv, mo, ms, msh⟩ | _
  · -- integral
    have hint : v.numericType.isIntegral = true := by rw [hnt]; rfl
    rw [hnt] at haa
    obtain ⟨-, haoff, -⟩ := STAmount.ofNumber_integral_facts _ _ _ _ rfl haa
    have hAA1 : 1 ≤ AA := by
      rw [← haav, STAmount.toRat_of_offset_zero aa haoff]
      have h0 : (0 : ℚ) < (aa.signedDrops : ℚ) := by
        rw [← STAmount.toRat_of_offset_zero aa haoff, haav]; exact hpos
      have : (0 : ℤ) < aa.signedDrops := by exact_mod_cast h0
      have : (1 : ℤ) ≤ aa.signedDrops := this
      exact_mod_cast this
    obtain ⟨an0, hof, hann, hanneg, -, hlo⟩ := price_an_lower v sh p w hc hnav hp
      (by
        have : (10 : ℚ) ^ (-82 : ℤ) ≤ 1 := by norm_num
        linarith)
    have h1 := STAmount.ofNumber_integral_within_one _ _ _ _ hint hann hanneg hof
    obtain ⟨-, hpoff, hpmv⟩ := price_integral_shape v sh p w hint hp
    obtain ⟨hpnt, -, -⟩ := price_integral_shape v sh p w hint hp
    obtain ⟨sn, hsn, hsnv, hsnn, -⟩ := STAmount.toNumber_integral_exact' p .to_nearest
      (by rw [hpnt]; exact hint) hpoff hpmv
    obtain rfl : sn = an := Except.ok.inj (hsn.symm.trans han)
    have hple : p.toRat ≤ AA := hsnv ▸ hguard hsnn
    have hae : aa.exponent = 0 := haoff
    rw [hae, zpow_zero]
    have := (abs_lt.mp h1).1
    linarith
  · -- fractional
    rw [hnt] at haa
    obtain ⟨hr_lo, hr_hi⟩ := hAAn.mantissaBounds_nat hAAm
    have hre_lo : minExponent ≤ v.assetsAvailable.exponent_ := by
      rcases hAAn with h0 | ⟨_, _, _, hlo, _⟩
      · exact absurd (show v.assetsAvailable.mantissa_ = 0 by rw [h0]; rfl) hAAm
      · exact hlo
    have haac : aa.IOUCanonical := by
      rcases STAmount.ofNumber_iou_canonical_or_zero _ _ _ hr_lo hr_hi hre_lo haa with h | h
      · exact h
      · exfalso
        have : aa.toRat = 0 := (STAmount.toRat_eq_zero_iff aa).mpr h
        linarith
    have hAAge : (10 : ℚ) ^ (-81 : ℤ) ≤ AA := by
      have := iou_abs_ge aa haac; rwa [abs_of_pos (by linarith), haav] at this
    obtain ⟨an0, hof, hann, hanneg, han0, hlo⟩ := price_an_lower v sh p w hc hnav hp
      (by
        have : (10 : ℚ) ^ (-82 : ℤ) ≤ 10 ^ (-81 : ℤ) := zpow_le_zpow_right₀ (by norm_num) (by norm_num)
        linarith)
    rw [hnt] at hof
    have han0m : an0.mantissa_ ≠ 0 := Number.mantissa_ne_zero_of_toRat_ne_zero han0.ne'
    by_cases hpz : p.mValue = 0
    · have := STAmount.ofNumber_fractional_zero_below_min .fractional an0 p .to_nearest (by decide)
        hann hanneg han0m hof hpz
      linarith
    obtain ⟨a_lo, a_hi⟩ := hann.mantissaBounds_nat han0m
    have ae_lo : minExponent ≤ an0.exponent_ := by
      rcases hann with h0 | ⟨_, _, _, hlo', _⟩
      · exact absurd (show an0.mantissa_ = 0 by rw [h0]; rfl) han0m
      · exact hlo'
    obtain ⟨hpc, hexp4⟩ := STAmount.ofNumber_iou_ok_facts an0 .to_nearest p a_lo a_hi ae_lo hof hpz
    obtain ⟨hhalf, hexp⟩ := STAmount.ofNumber_iou_within_half_ulp .fractional an0 p rfl a_lo a_hi
      ae_lo hexp4 hof hpz
    obtain ⟨sn, hsn, hsnv, hsnn⟩ := STAmount.toNumber_iou_exact p .to_nearest hpc
    obtain rfl : sn = an := Except.ok.inj (hsn.symm.trans han)
    have hple : p.toRat ≤ AA := hsnv ▸ hguard hsnn
    have hbase : (10 : ℚ) ^ an0.exponent_ * 10 ^ 18 ≤ an0.toRat := by
      rw [Number.toRat_of_nonneg an0 hanneg, mul_comm]
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact_mod_cast a_lo
    have h3 : (10 : ℚ) ^ (an0.exponent_ + 3) = 10 ^ an0.exponent_ * 1000 := by
      rw [zpow_add₀ (by norm_num)]; norm_num
    have he0 : (0 : ℚ) < 10 ^ an0.exponent_ := by positivity
    obtain ⟨hh1, -⟩ := abs_le.mp hhalf
    have hp0 : 0 ≤ p.toRat := by rw [h3] at hh1; nlinarith
    have hoff := iou_offset_le p aa hpc haac hp0 (haav ▸ hple)
    have hpe1 : (10 : ℚ) ^ (an0.exponent_ + 3) ≤ 10 ^ p.exponent :=
      zpow_le_zpow_right₀ (by norm_num) hexp
    have hpe2 : (10 : ℚ) ^ p.exponent ≤ 10 ^ aa.exponent :=
      zpow_le_zpow_right₀ (by norm_num) hoff
    linarith

/-- A non-final burn of a positive canonical `int64` amount never zeroes the share total. -/
lemma nonfinal_st_ne_zero (v : Vault) (sta sb : STAmount) (sbn st' : Number)
    (hpos : 0 < sb.toRat) (hc : sb.Canonical) (hSnt : sb.mNumericType = .int64)
    (hst : STAmount.ofNumber .int64 v.sharesTotal .to_nearest = .ok sta)
    (hf : sb.operator_eq sta = false)
    (hsbn : sb.toNumber .to_nearest = .ok sbn)
    (hsub : v.sharesTotal.operator_sub sbn .to_nearest = .ok st') : st' ≠ Number.zero := by
  intro h0
  have hS := v.wf
  have hex := sub_burn_exact v.sharesTotal sbn st' sb hS.sharesTotal_norm
    hS.sharesTotal_nonneg hS.sharesTotal_int
    (ofNumber_int64_fit _ _ _ hS.sharesTotal_norm hS.sharesTotal_nonneg hS.sharesTotal_int hst)
    hpos.le hc hSnt hsbn hsub
  rw [h0, Number.toRat_zero] at hex
  have := (burn_eq_iff v.sharesTotal sb sta hS.sharesTotal_norm hS.sharesTotal_nonneg
    hS.sharesTotal_int hst hpos hc hSnt).mpr (by linarith)
  rw [this] at hf; exact absurd hf (by decide)

end XRPL.Model.SingleAssetVault.WdAcc
