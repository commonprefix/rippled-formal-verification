import XRPL.Properties.Vault.Common.ClawbackDefs
import XRPL.Properties.Vault.VaultValid
import XRPL.Properties.Vault.Common.ClawbackReduction
import XRPL.Properties.Vault.Common.WithdrawAccuracy
import XRPL.Properties.Vault.Common.WithdrawBounds
import XRPL.Properties.Vault.Common.OfNumberBoundary
import XRPL.Properties.Vault.Common.SubZeroShape
import XRPL.Properties.Vault.Common.ExchangeShared

/-! # `Vault.clawback` accuracy proofs

Proof bodies behind the accuracy headlines in `VaultClawback.lean`. -/

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol

/-- A normalized non-negative `Number` has a clear sign bit. -/
lemma Number.negative_false_of_norm_nonneg (n : Number) (hn : n.isNormalized)
    (h0 : 0 ≤ n.toRat) : n.negative_ = false := by
  rcases hb : n.negative_ with _ | _
  · rfl
  · exfalso
    have hle := Number.toRat_nonpos_of_negative n hb
    have hm0 : n.mantissa_ = 0 := Number.toRat_eq_zero_iff.mp (le_antisymm hle h0)
    exact Number.mantissa_ne_zero_of_negative n hn hb hm0

/-! ## `assetsToSharesWithdraw` accuracy (shares side) -/

/-- **`assetsToSharesWithdraw` prices `assets` into shares within `depositε`.** For
a lawful vault with exact withdraw NAV, a positive exchange-ready `assets` (given
by its exact `toNumber` witness `hanexact` and magnitude floor `hfloor`), and a
nonzero result, there is a `q` (the pre-conversion share `Number`) within
`depositε` of `idealSharesClawback assets`, of which the packed result is either
the floor (`truncateShares`) or a to-nearest whole share. -/
lemma assetsToSharesWithdraw_spec (v : Vault) (assets shares : STAmount)
    (truncateShares : Bool)
    (hnav : v.WithdrawNavExact false)
    (hnn : 0 ≤ assets.toRat)
    (hanexact : ∃ an : Number, assets.toNumber .to_nearest = .ok an ∧
      an.toRat = assets.toRat ∧ an.isNormalized)
    (hfloornz : assets.mValue ≠ 0 → (10 : ℚ) ^ (-81 : ℤ) ≤ |assets.toRat|)
    (hok : assetsToSharesWithdraw v assets truncateShares false = .ok shares)
    (hnz : shares.isZero = false) :
    ∃ q : ℚ, 0 < v.idealSharesClawback assets.toRat ∧
      |q - v.idealSharesClawback assets.toRat|
        ≤ v.idealSharesClawback assets.toRat * depositε ∧
      (match truncateShares with
        | true => shares.toRat = (⌊q⌋ : ℚ)
        | false => |shares.toRat - q| ≤ 1 / 2) ∧
      shares.toRat.den = 1 ∧ 0 ≤ shares.toRat := by
  have hmv : shares.mValue ≠ 0 := ne_of_beq_false (show (shares.mValue == 0) = false from hnz)
  obtain ⟨nav2, hsub, hcase⟩ :=
    assetsToSharesWithdraw_ok_reduces v assets shares truncateShares false hok
  obtain ⟨netAssetValue, hs, hnavval⟩ := hnav
  have hnav2eq : nav2 = netAssetValue := Except.ok.inj (hsub.symm.trans hs)
  have hnav2val : nav2.toRat = v.withdrawNav := by rw [hnav2eq]; exact hnavval
  rcases hcase with ⟨hzm, hzero⟩ | ⟨hnz2, assetsNumber, sharesAssets, sharesNumber, sharesNumber',
      han, hmul, hdiv, htrunc, hofn⟩
  · exfalso; rw [hzero, STAmount.zero_mValue] at hmv; exact hmv rfl
  have hnav_nn : (0 : ℚ) ≤ v.withdrawNav := by
    unfold RawVault.withdrawNav; exact v.exact.withdraw_nav_nonneg
  have hnav2_pos : 0 < nav2.toRat := by
    have hne : nav2.toRat ≠ 0 := Number.toRat_ne_zero_of_mantissa_ne_zero nav2 hnz2
    rw [hnav2val] at hne
    rw [hnav2val]; exact lt_of_le_of_ne hnav_nn (Ne.symm hne)
  have hnav_pos : 0 < v.withdrawNav := by rw [← hnav2val]; exact hnav2_pos
  have hS_pos : 0 < v.sharesTotal.toRat := by
    rcases lt_or_eq_of_le v.wf.sharesTotal_nonneg with h | h
    · exact h
    · exfalso
      have hz : v.toExact.sharesTotal = 0 := by
        show v.sharesTotal.toRat.num.toNat = 0
        rw [← h]; rfl
      obtain ⟨hAT, hAA⟩ := v.exact.empty_shares hz
      have hle0 : v.withdrawNav ≤ 0 := by
        unfold RawVault.withdrawNav
        rw [hAT]
        have hl := v.exact.lossUnrealized_nonneg
        linarith
      linarith [hnav_pos]
  have hS_one : 1 ≤ v.sharesTotal.toRat := by
    have hnum_pos : 0 < v.sharesTotal.toRat.num := Rat.num_pos.mpr hS_pos
    have hcast : v.sharesTotal.toRat = (v.sharesTotal.toRat.num : ℚ) := by
      conv_lhs => rw [← Rat.num_div_den v.sharesTotal.toRat]
      rw [v.wf.sharesTotal_int]; simp
    rw [hcast]; exact_mod_cast hnum_pos
  have hSm : v.sharesTotal.mantissa_ ≠ 0 := Number.mantissa_ne_zero_of_toRat_ne_zero hS_pos.ne'
  obtain ⟨an', han', hanval, hannorm⟩ := hanexact
  have haneq : an' = assetsNumber := by rw [han'] at han; exact Except.ok.inj han
  rw [haneq] at hanval hannorm
  have hnav2norm : nav2.isNormalized :=
    operator_sub_isNormalized_to_nearest_sz v.assetsTotal v.lossUnrealized nav2
      v.wf.assetsTotal_norm v.wf.lossUnrealized_norm hsub
  have hQm : sharesNumber.mantissa_ ≠ 0 := by
    have hsn' : sharesNumber'.mantissa_ ≠ 0 :=
      STAmount.ofNumber_integral_source_ne_zero .int64 sharesNumber' .to_nearest shares
        (by decide) hofn hmv
    cases truncateShares with
    | true => exact Number.truncate_source_ne_zero sharesNumber sharesNumber' htrunc hsn'
    | false =>
      have hpure : sharesNumber' = sharesNumber :=
        (Except.ok.inj (show (pure sharesNumber : Except Error Number) = .ok sharesNumber'
          from htrunc)).symm
      rw [hpure] at hsn'; exact hsn'
  -- positivity: a zero input would collapse the product and quotient to zero,
  -- contradicting the nonzero pre-conversion `sharesNumber`
  have hmv0 : assets.mValue ≠ 0 := by
    intro h0
    have habs0 : |assets.toRat| = 0 := by rw [STAmount.abs_toRat, h0]; simp
    have haz : assets.toRat = 0 := abs_eq_zero.mp habs0
    have hanm0 : assetsNumber.mantissa_ = 0 := by
      by_contra hne
      exact Number.toRat_ne_zero_of_mantissa_ne_zero assetsNumber hne (by rw [hanval]; exact haz)
    have hanzero : assetsNumber = Number.zero :=
      Number.eq_zero_of_mantissa_zero assetsNumber hannorm hanm0
    have hSAzero : sharesAssets = Number.zero := by
      rw [hanzero] at hmul
      unfold Number.operator_mul at hmul
      rw [if_neg (Number.not_operator_eq_zero_of_mantissa_ne hSm),
          if_pos (show Number.zero.operator_eq Number.zero = true from by decide)] at hmul
      simpa using (Except.ok.inj hmul).symm
    have hSNzero : sharesNumber = Number.zero := by
      rw [hSAzero] at hdiv
      unfold Number.operator_div at hdiv
      rw [if_neg (Number.not_operator_eq_zero_of_mantissa_ne hnz2),
          if_pos (show Number.zero.operator_eq Number.zero = true from by decide)] at hdiv
      simpa using (Except.ok.inj hdiv).symm
    rw [hSNzero] at hQm
    exact hQm rfl
  have hfloor : (10 : ℚ) ^ (-81 : ℤ) ≤ |assets.toRat| := hfloornz hmv0
  have hpos : 0 < assets.toRat := by
    have hne : assets.toRat ≠ 0 := by
      intro h; rw [h, abs_zero] at hfloor; exact absurd hfloor (by norm_num)
    exact lt_of_le_of_ne hnn (Ne.symm hne)
  have hApos : 0 < assetsNumber.toRat := by rw [hanval]; exact hpos
  have hAm : assetsNumber.mantissa_ ≠ 0 := Number.mantissa_ne_zero_of_toRat_ne_zero hApos.ne'
  have hPm : sharesAssets.mantissa_ ≠ 0 := by
    intro h0
    have hsmall := operator_mul_underflow_truth_small v.sharesTotal assetsNumber sharesAssets
      .to_nearest v.wf.sharesTotal_norm hannorm hSm hAm hmul h0
    have hcombo : (10 : ℚ) ^ (18 : ℕ) * (10 : ℚ) ^ (minExponent : ℤ)
        = (10 : ℚ) ^ (-32750 : ℤ) := by
      rw [← zpow_natCast (10 : ℚ) 18, ← zpow_add₀ (by norm_num : (10 : ℚ) ≠ 0)]
      norm_num [minExponent]
    rw [hcombo] at hsmall
    have hge : (10 : ℚ) ^ (-81 : ℤ) ≤ |v.sharesTotal.toRat * assetsNumber.toRat| := by
      rw [abs_mul]
      have hh1 : (1 : ℚ) ≤ |v.sharesTotal.toRat| := by rw [abs_of_pos hS_pos]; exact hS_one
      have hh2 : (10 : ℚ) ^ (-81 : ℤ) ≤ |assetsNumber.toRat| := by rw [hanval]; exact hfloor
      nlinarith [abs_nonneg assetsNumber.toRat, abs_nonneg v.sharesTotal.toRat]
    have hmono : (10 : ℚ) ^ (-32750 : ℤ) ≤ (10 : ℚ) ^ (-81 : ℤ) :=
      zpow_le_zpow_right₀ (by norm_num) (by norm_num)
    linarith
  obtain ⟨hQnorm, hQpos, hQbound⟩ :=
    RawVault.exchange_pipeline_within v.sharesTotal assetsNumber nav2 sharesAssets sharesNumber
      v.wf.sharesTotal_norm hannorm hnav2norm hS_pos hApos hnav2_pos hmul hdiv hPm hQm
  have hideal_eq : v.sharesTotal.toRat * assetsNumber.toRat / nav2.toRat
      = v.idealSharesClawback assets.toRat := by
    unfold RawVault.idealSharesClawback
    rw [RawVault.WF.toExact_sharesTotal v.toRawVault v.wf, hanval, hnav2val]
  have hideal_pos : 0 < v.idealSharesClawback assets.toRat := by rw [← hideal_eq]; positivity
  rw [hideal_eq] at hQbound
  refine ⟨sharesNumber.toRat, hideal_pos, hQbound, ?_⟩
  have hsnneg : sharesNumber.negative_ = false := Number.negative_false_of_pos sharesNumber hQpos
  cases truncateShares with
  | true =>
    have htr : sharesNumber.truncate = .ok sharesNumber' := htrunc
    obtain ⟨htval, htnorm⟩ := Number.truncate_floor sharesNumber sharesNumber' hQnorm hsnneg htr
    have hsn'm : sharesNumber'.mantissa_ ≠ 0 :=
      STAmount.ofNumber_integral_source_ne_zero .int64 sharesNumber' .to_nearest shares
        (by decide) hofn hmv
    have hshval : shares.toRat = sharesNumber'.toRat :=
      STAmount.ofNumber_integral_exact .int64 sharesNumber' .to_nearest shares (by decide)
        (htnorm hsn'm) (by rw [htval]; exact Rat.den_intCast _) hofn
    refine ⟨?_, ?_, ?_⟩
    · show shares.toRat = (⌊sharesNumber.toRat⌋ : ℚ)
      rw [hshval, htval]
    · rw [hshval, htval]; exact Rat.den_intCast _
    · rw [hshval, htval]
      exact_mod_cast Int.floor_nonneg.mpr (le_of_lt hQpos)
  | false =>
    have hpure : sharesNumber' = sharesNumber :=
      (Except.ok.inj (show (pure sharesNumber : Except Error Number) = .ok sharesNumber'
        from htrunc)).symm
    have hofn' : STAmount.ofNumber .int64 sharesNumber .to_nearest = .ok shares := by
      rw [← hpure]; exact hofn
    obtain ⟨hwithin, hden, hnn⟩ :=
      STAmount.ofNumber_int64_to_nearest_within_half sharesNumber shares hQnorm hsnneg hofn'
    exact ⟨hwithin, hden, hnn⟩

/-- **Proof body of `clawback_sharesDestroyed`.** The computed recovery fits under
`assetsAvailable`, so the destroyed shares are priced directly from `assets`. -/
theorem Vault.clawback_sharesDestroyed_proof (v : Vault)
    (assets holderShares sharesDestroyed assetsRecovered : STAmount)
    (assetsRecoveredNumber : Number) (r : ClawbackResult)
    (hnav : v.WithdrawNavExact false) (hc : assets.Canonical)
    (hshares : assetsToSharesWithdraw v assets false false = .ok sharesDestroyed)
    (hassets : v.sharesToAssetsWithdraw sharesDestroyed false = .ok assetsRecovered)
    (hnum : assetsRecovered.toNumber .to_nearest = .ok assetsRecoveredNumber)
    (hle : assetsRecoveredNumber.operator_gt v.assetsAvailable = false)
    (hznz : assets.isZero = false)
    (hok : v.clawback assets holderShares = .ok r) (herr : r.error = none) :
    r.sharesDestroyed.toRat.den = 1 ∧ 0 ≤ r.sharesDestroyed.toRat ∧
    |r.sharesDestroyed.toRat - v.idealSharesClawback assets.toRat| ≤
      v.idealSharesClawback assets.toRat * depositε + 1 / 2 := by
  obtain ⟨cr, hcomp, herr2, hcrnz, -, hsd_eq, -⟩ :=
    Vault.clawback_success_reduces v assets holderShares r hok herr
  obtain ⟨hnegf, sd, ar, arn2, hsd', has', hnum2, hcase⟩ :=
    computeClawback_none_reduces v assets holderShares cr hznz hcomp herr2
  have hsd_det : sd = sharesDestroyed := by rw [hshares] at hsd'; exact (Except.ok.inj hsd').symm
  have har_det : ar = assetsRecovered := by rw [hsd_det, hassets] at has'; exact (Except.ok.inj has').symm
  have harn_det : arn2 = assetsRecoveredNumber := by
    rw [har_det, hnum] at hnum2; exact (Except.ok.inj hnum2).symm
  rcases hcase with ⟨-, -, hcrs⟩ | ⟨hgt', -⟩
  · have hrsd : r.sharesDestroyed = sharesDestroyed := by rw [hsd_eq, hcrs, hsd_det]
    have hsdnz : sharesDestroyed.isZero = false := by rw [← hsd_det, ← hcrs]; exact hcrnz
    have hnn : 0 ≤ assets.toRat := by
      rw [STAmount.toRat_of_nonneg assets (show assets.mIsNegative = false from hnegf)]; positivity
    obtain ⟨q, -, hqbound, hmatch, hden, hnn2⟩ :=
      assetsToSharesWithdraw_spec v assets sharesDestroyed false hnav hnn
        (STAmount.toNumber_canonical_exact assets .to_nearest hc)
        (fun hmv => STAmount.Canonical.abs_toRat_ge assets hc hmv) hshares hsdnz
    have hm2 : |sharesDestroyed.toRat - q| ≤ 1 / 2 := hmatch
    refine ⟨by rw [hrsd]; exact hden, by rw [hrsd]; exact hnn2, ?_⟩
    rw [hrsd]
    calc |sharesDestroyed.toRat - v.idealSharesClawback assets.toRat|
        ≤ |sharesDestroyed.toRat - q| + |q - v.idealSharesClawback assets.toRat| :=
          abs_sub_le _ _ _
      _ ≤ 1 / 2 + v.idealSharesClawback assets.toRat * depositε := by linarith [hm2, hqbound]
      _ = v.idealSharesClawback assets.toRat * depositε + 1 / 2 := by ring
  · rw [harn_det, hle] at hgt'; exact absurd hgt' (by simp)

/-- **Proof body of `clawback_sharesDestroyed_clamped`.** The first computed
recovery exceeds `assetsAvailable`, so the run reprices the truncated share value
of the clamped amount `assetsRecovered' = ofNumber assetsAvailable`, which is a
canonical (nonzero-or-zero) `ofNumber` output priced through the shares side. -/
theorem Vault.clawback_sharesDestroyed_clamped_proof (v : Vault)
    (assets holderShares sharesDestroyed assetsRecovered assetsRecovered' : STAmount)
    (assetsRecoveredNumber : Number) (r : ClawbackResult)
    (hnav : v.WithdrawNavExact false)
    (hshares : assetsToSharesWithdraw v assets false false = .ok sharesDestroyed)
    (hassets : v.sharesToAssetsWithdraw sharesDestroyed false = .ok assetsRecovered)
    (hnum : assetsRecovered.toNumber .to_nearest = .ok assetsRecoveredNumber)
    (hgt : assetsRecoveredNumber.operator_gt v.assetsAvailable = true)
    (hclamped : STAmount.ofNumber v.numericType v.assetsAvailable .to_nearest = .ok assetsRecovered')
    (hznz : assets.isZero = false)
    (hok : v.clawback assets holderShares = .ok r) (herr : r.error = none) :
    r.sharesDestroyed.toRat.den = 1 ∧ 0 ≤ r.sharesDestroyed.toRat ∧
    v.idealSharesClawback assetsRecovered'.toRat * (1 - depositε) - 1 <
      r.sharesDestroyed.toRat ∧
    r.sharesDestroyed.toRat ≤
      v.idealSharesClawback assetsRecovered'.toRat * (1 + depositε) := by
  obtain ⟨cr, hcomp, herr2, hcrnz, -, hsd_eq, -⟩ :=
    Vault.clawback_success_reduces v assets holderShares r hok herr
  obtain ⟨-, sd, ar, arn2, hsd', has', hnum2, hcase⟩ :=
    computeClawback_none_reduces v assets holderShares cr hznz hcomp herr2
  have hsd_det : sd = sharesDestroyed := by rw [hshares] at hsd'; exact (Except.ok.inj hsd').symm
  have har_det : ar = assetsRecovered := by rw [hsd_det, hassets] at has'; exact (Except.ok.inj has').symm
  have harn_det : arn2 = assetsRecoveredNumber := by
    rw [har_det, hnum] at hnum2; exact (Except.ok.inj hnum2).symm
  rcases hcase with ⟨hgt', -, -⟩ |
      ⟨-, clamped, sd', ar', arn', hclamp', hshareT, -, -, -, -, hcrsd⟩
  · rw [harn_det, hgt] at hgt'; exact absurd hgt' (by simp)
  · have hclamp_det : clamped = assetsRecovered' := by
      rw [hclamped] at hclamp'; exact (Except.ok.inj hclamp').symm
    rw [hclamp_det] at hshareT
    have hrsd : r.sharesDestroyed = sd' := by rw [hsd_eq, hcrsd]
    have hsdnz : sd'.isZero = false := by rw [← hcrsd]; exact hcrnz
    have hAA_neg : v.assetsAvailable.negative_ = false :=
      Number.negative_false_of_norm_nonneg v.assetsAvailable v.wf.assetsAvailable_norm
        v.exact.assetsAvailable_nonneg
    obtain ⟨hnn, hexact, hfloor⟩ :=
      STAmount.ofNumber_input_spec v.numericType v.assetsAvailable .to_nearest assetsRecovered'
        v.wf.assetsAvailable_norm hAA_neg hclamped
    obtain ⟨q, hideal_pos, hqbound, hmatch, hden, hnn2⟩ :=
      assetsToSharesWithdraw_spec v assetsRecovered' sd' true hnav hnn hexact hfloor hshareT hsdnz
    have hqfloor : sd'.toRat = (⌊q⌋ : ℚ) := hmatch
    set ideal : ℚ := v.idealSharesClawback assetsRecovered'.toRat with hideal_def
    obtain ⟨hlo_b, hhi_b⟩ := abs_le.mp hqbound
    have hexpand : ideal * (1 - depositε) = ideal - ideal * depositε := by ring
    have hexpand' : ideal * (1 + depositε) = ideal + ideal * depositε := by ring
    refine ⟨by rw [hrsd]; exact hden, by rw [hrsd]; exact hnn2, ?_, ?_⟩
    · rw [hrsd, hqfloor]
      have hfl : q - 1 < (⌊q⌋ : ℚ) := Int.sub_one_lt_floor q
      linarith [hlo_b, hexpand, hfl]
    · rw [hrsd, hqfloor]
      have hfl : (⌊q⌋ : ℚ) ≤ q := Int.floor_le q
      linarith [hhi_b, hexpand', hfl]

/-- **Proof body of `clawback_vault_updates_integral`.** -/
theorem Vault.clawback_vault_updates_integral_proof (v : Vault) (assets holderShares : STAmount)
    (r : ClawbackResult)
    (hint : v.numericType.isIntegral = true)
    (hznz : assets.isZero = false)
    (hok : v.clawback assets holderShares = .ok r) (herr : r.error = none)
    (hnn : 0 ≤ r.assetsRecovered.toRat)
    (hsz : v.toExact.assetsTotal ≤ 2 ^ 63 - 1) :
    r.vault'.assetsTotal.toRat = v.toExact.assetsTotal - r.assetsRecovered.toRat ∧
    r.vault'.assetsAvailable.toRat = v.toExact.assetsAvailable - r.assetsRecovered.toRat := by
  obtain ⟨cr, hcomp, herr2, -, hra, -, sbn, arn, at', st', av', atr, atr',
      -, harn, hat, -, -, -, -, hav, hr⟩ :=
    Vault.clawback_success_reduces v assets holderShares r hok herr
  -- the recovered amount came from `sharesToAssetsWithdraw` and passed the
  -- `assetsAvailable` cap
  obtain ⟨-, sd, ar, arn2, -, has, hnum2, hcase⟩ :=
    computeClawback_none_reduces v assets holderShares cr hznz hcomp herr2
  have hrec : ∃ sd' : STAmount, v.sharesToAssetsWithdraw sd' false = .ok cr.assetsRecovered := by
    rcases hcase with ⟨-, hval, -⟩ | ⟨-, clamped, sd', ar', arn', -, -, hshareA, -, -, hval, -⟩
    · exact ⟨sd, by rw [hval]; exact has⟩
    · exact ⟨sd', by rw [hval]; exact hshareA⟩
  obtain ⟨sd0, hsd0⟩ := hrec
  obtain ⟨hshape_nt, hshape_off, hshape_val⟩ :=
    Vault.sharesToAssetsWithdraw_integral_shape v sd0 cr.assetsRecovered false hint hsd0
  obtain ⟨sn, hsn_ok, hsn_val, hsn_norm, hsn_den⟩ :=
    STAmount.toNumber_integral_exact' cr.assetsRecovered .to_nearest
      (by rw [hshape_nt]; exact hint) hshape_off hshape_val
  have harn_eq : arn = sn := by
    rw [hsn_ok] at harn
    exact (Except.ok.inj harn).symm
  rw [harn_eq] at hat hav
  set k : ℚ := cr.assetsRecovered.toRat with hk_def
  have hknn : 0 ≤ k := by rw [hk_def, ← hra]; exact hnn
  -- the cap: the recovered value never exceeds `assetsAvailable`
  have hk_le_AA : k ≤ v.assetsAvailable.toRat := by
    have hgt : sn.operator_gt v.assetsAvailable = false := by
      rcases hcase with ⟨hgt', hvalA, -⟩ |
          ⟨-, clamped, sd', ar', arn', -, -, -, hnum', hgt', hvalA, -⟩
      · rw [← hvalA, hsn_ok] at hnum2
        rw [show arn2 = sn from (Except.ok.inj hnum2).symm] at hgt'
        exact hgt'
      · rw [← hvalA, hsn_ok] at hnum'
        rw [show arn' = sn from (Except.ok.inj hnum').symm] at hgt'
        exact hgt'
    have hbridge := operator_gt_iff sn v.assetsAvailable hsn_norm v.wf.assetsAvailable_norm
    by_contra hc
    push_neg at hc
    have : sn.operator_gt v.assetsAvailable = true := by
      rw [hbridge, hsn_val]
      exact hc
    rw [this] at hgt
    exact absurd hgt (by simp)
  have hAA_le_A : v.assetsAvailable.toRat ≤ v.assetsTotal.toRat :=
    v.exact.assetsAvailable_le
  have hsz' : v.assetsTotal.toRat ≤ 2 ^ 63 - 1 := hsz
  have hat_exact : at'.toRat = v.assetsTotal.toRat - k :=
    operator_sub_exact_int_le v.assetsTotal sn at' k v.wf.assetsTotal_norm hsz'
      hsn_norm (by rw [hsn_val]) hsn_den hknn (le_trans hk_le_AA hAA_le_A) hat
  have hav_exact : av'.toRat = v.assetsAvailable.toRat - k :=
    operator_sub_exact_int_le v.assetsAvailable sn av' k v.wf.assetsAvailable_norm
      (le_trans hAA_le_A hsz') hsn_norm (by rw [hsn_val]) hsn_den hknn hk_le_AA hav
  constructor
  · rw [hr, hra]
    show at'.toRat = v.toExact.assetsTotal - cr.assetsRecovered.toRat
    exact hat_exact
  · rw [hr, hra]
    show av'.toRat = v.toExact.assetsAvailable - cr.assetsRecovered.toRat
    exact hav_exact

/-! ## `clawback_assetsRecovered` / `clawback_vault_updates` support -/

/-- **Proof body of `idealAssetsClawback_idealSharesClawback`.** -/
theorem RawVault.idealAssetsClawback_idealSharesClawback_proof (rv : RawVault) (assets : ℚ)
    (hnav : rv.withdrawNav ≠ 0) (hsh : rv.toExact.sharesTotal ≠ 0) :
    rv.idealAssetsClawback (rv.idealSharesClawback assets) = assets := by
  unfold RawVault.idealAssetsClawback RawVault.idealSharesClawback
  have hsh' : ((rv.toExact.sharesTotal : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hsh
  field_simp

/-- The clawback recovery ideal coincides with the withdraw ideal at
`waiveUnrealizedLoss = false`: both price shares at `withdrawNav`. -/
lemma RawVault.idealAssetsClawback_eq_withdraw (rv : RawVault) (shares : ℚ) :
    rv.idealAssetsClawback shares = rv.idealAssetsWithdraw false shares := by
  unfold RawVault.idealAssetsClawback RawVault.idealAssetsWithdraw
  rw [if_neg (by decide : ¬ ((false : Bool) = true))]

/-- **A priced recovery whose `to_nearest` lift did not exceed `assetsAvailable`
lands at or below `assetsAvailable`.** The `operator_gt = false` guard (the run did
not take the second-excess `tecINTERNAL` branch) bridges to `≤` through the payout's
exact `toNumber` value; a zero payout is trivially below the nonnegative
`assetsAvailable`. -/
lemma Vault.sharesToAssetsWithdraw_le_assetsAvailable (v : Vault)
    (shares assets : STAmount) (arn : Number) (hc : shares.Canonical)
    (hprice : v.sharesToAssetsWithdraw shares false = .ok assets)
    (hnum : assets.toNumber .to_nearest = .ok arn)
    (hgt : arn.operator_gt v.assetsAvailable = false) :
    assets.toRat ≤ v.assetsAvailable.toRat := by
  have hAA_nn : (0 : ℚ) ≤ v.assetsAvailable.toRat := v.exact.assetsAvailable_nonneg
  by_cases hz : assets.mValue = 0
  · rw [STAmount.toRat_signed, hz]; simpa using hAA_nn
  · obtain ⟨an, hnum', hval, hnorm⟩ :=
      Vault.sharesToAssetsWithdraw_toNumber_exact_of_ne v shares assets false hc hprice hz
    have han_eq : an = arn := Except.ok.inj (hnum'.symm.trans hnum)
    have harn_val : arn.toRat = assets.toRat := by rw [← han_eq]; exact hval
    rw [← harn_val]
    by_contra hlt
    push_neg at hlt
    have hbridge := operator_gt_iff arn v.assetsAvailable (han_eq ▸ hnorm) v.wf.assetsAvailable_norm
    have : arn.operator_gt v.assetsAvailable = true := hbridge.mpr hlt
    rw [this] at hgt; exact absurd hgt (by decide)

/-- **Common recovery facts of a successful clawback.** The destroyed shares are a
nonnegative `Canonical` `int64` amount that prices the recovery through
`sharesToAssetsWithdraw`, and the recovery never exceeds `assetsAvailable` (the run
would otherwise have failed with `tecINTERNAL`). Covers both the direct and the
recompute-from-`assetsAvailable` branches uniformly. -/
lemma Vault.clawback_recovery_priced (v : Vault) (assets holderShares : STAmount)
    (r : ClawbackResult)
    (hnav : v.WithdrawNavExact false) (hc : assets.Canonical)
    (hznz : assets.isZero = false)
    (hok : v.clawback assets holderShares = .ok r) (herr : r.error = none) :
    0 ≤ r.sharesDestroyed.toRat ∧ r.sharesDestroyed.Canonical ∧
    v.sharesToAssetsWithdraw r.sharesDestroyed false = .ok r.assetsRecovered ∧
    r.assetsRecovered.toRat ≤ v.assetsAvailable.toRat ∧
    r.sharesDestroyed.isZero = false ∧ 0 < v.withdrawNav := by
  obtain ⟨cr, hcomp, herr2, hcrnz, hra_eq, hsd_eq, -⟩ :=
    Vault.clawback_success_reduces v assets holderShares r hok herr
  obtain ⟨hnegf, sd, ar, arn2, hshares, hprice, hnum2, hcase⟩ :=
    computeClawback_none_reduces v assets holderShares cr hznz hcomp herr2
  -- `withdrawNav > 0`: the shares priced positively (`0 < idealSharesClawback`).
  -- `ideal = sharesTotal · X / withdrawNav`, nonneg numerator, so a nonpositive
  -- divisor would make it nonpositive.
  have hnavpos_of_q : ∀ X : STAmount, 0 ≤ X.toRat →
      0 < v.idealSharesClawback X.toRat → 0 < v.withdrawNav := by
    intro X hXnn hq
    by_contra h; push_neg at h
    have hnum_nn : 0 ≤ v.sharesTotal.toRat * X.toRat :=
      mul_nonneg v.wf.sharesTotal_nonneg hXnn
    have : v.idealSharesClawback X.toRat ≤ 0 := by
      unfold RawVault.idealSharesClawback
      rw [RawVault.WF.toExact_sharesTotal v.toRawVault v.wf]
      exact div_nonpos_of_nonneg_of_nonpos hnum_nn h
    linarith
  have hmain :
      0 ≤ cr.sharesDestroyed.toRat ∧ cr.sharesDestroyed.Canonical ∧
      v.sharesToAssetsWithdraw cr.sharesDestroyed false = .ok cr.assetsRecovered ∧
      cr.assetsRecovered.toRat ≤ v.assetsAvailable.toRat ∧ 0 < v.withdrawNav := by
    rcases hcase with ⟨hgtF, hcr_ar, hcr_sd⟩ |
        ⟨-, clamped, sd', ar', arn', hclamp, hshareT, hprice', hnum', hgtF, hcr_ar, hcr_sd⟩
    · -- direct branch: shares priced from `assets`
      have hsdnz : cr.sharesDestroyed.isZero = false := hcrnz
      have hsdnz' : sd.isZero = false := by rw [← hcr_sd]; exact hsdnz
      have hnn_assets : 0 ≤ assets.toRat := by
        rw [STAmount.toRat_of_nonneg assets (show assets.mIsNegative = false from hnegf)]; positivity
      obtain ⟨_, hq_pos, _, _, _, hnn_sd⟩ :=
        assetsToSharesWithdraw_spec v assets sd false hnav hnn_assets
          (STAmount.toNumber_canonical_exact assets .to_nearest hc)
          (fun hmv => STAmount.Canonical.abs_toRat_ge assets hc hmv) hshares hsdnz'
      have hnav_pos : 0 < v.withdrawNav := hnavpos_of_q assets hnn_assets hq_pos
      have hcanon_sd : sd.Canonical :=
        assetsToSharesWithdraw_shares_canonical v assets sd false false hshares hsdnz'
      have hprice_cr : v.sharesToAssetsWithdraw cr.sharesDestroyed false = .ok cr.assetsRecovered := by
        rw [hcr_sd, hcr_ar]; exact hprice
      have hle : cr.assetsRecovered.toRat ≤ v.assetsAvailable.toRat := by
        rw [hcr_ar]
        exact Vault.sharesToAssetsWithdraw_le_assetsAvailable v sd ar arn2
          hcanon_sd hprice hnum2 hgtF
      exact ⟨by rw [hcr_sd]; exact hnn_sd, by rw [hcr_sd]; exact hcanon_sd, hprice_cr, hle, hnav_pos⟩
    · -- recompute branch: shares priced from the clamped `assetsAvailable`
      have hsdnz : cr.sharesDestroyed.isZero = false := hcrnz
      have hsdnz' : sd'.isZero = false := by rw [← hcr_sd]; exact hsdnz
      have hAA_neg : v.assetsAvailable.negative_ = false :=
        Number.negative_false_of_norm_nonneg v.assetsAvailable v.wf.assetsAvailable_norm
          v.exact.assetsAvailable_nonneg
      obtain ⟨hnn_cl, hexact_cl, hfloor_cl⟩ :=
        STAmount.ofNumber_input_spec v.numericType v.assetsAvailable .to_nearest clamped
          v.wf.assetsAvailable_norm hAA_neg hclamp
      obtain ⟨_, hq_pos, _, _, _, hnn_sd⟩ :=
        assetsToSharesWithdraw_spec v clamped sd' true hnav hnn_cl hexact_cl hfloor_cl hshareT hsdnz'
      have hnav_pos : 0 < v.withdrawNav := hnavpos_of_q clamped hnn_cl hq_pos
      have hcanon_sd : sd'.Canonical :=
        assetsToSharesWithdraw_shares_canonical v clamped sd' true false hshareT hsdnz'
      have hprice_cr : v.sharesToAssetsWithdraw cr.sharesDestroyed false = .ok cr.assetsRecovered := by
        rw [hcr_sd, hcr_ar]; exact hprice'
      have hle : cr.assetsRecovered.toRat ≤ v.assetsAvailable.toRat := by
        rw [hcr_ar]
        exact Vault.sharesToAssetsWithdraw_le_assetsAvailable v sd' ar' arn'
          hcanon_sd hprice' hnum' hgtF
      exact ⟨by rw [hcr_sd]; exact hnn_sd, by rw [hcr_sd]; exact hcanon_sd, hprice_cr, hle, hnav_pos⟩
  obtain ⟨h1, h2, h3, h4, h5⟩ := hmain
  exact ⟨by rw [hsd_eq]; exact h1, by rw [hsd_eq]; exact h2, by rw [hsd_eq, hra_eq]; exact h3,
    by rw [hra_eq]; exact h4, by rw [hsd_eq]; exact hcrnz, h5⟩

/-- **Recovery facts of a successful zero-amount clawback.** The zero amount
destroys the holder's shares directly, so the holder balance side conditions
(canonical, nonnegative) replace the nonzero amount pricing facts. No positive
NAV: a zero amount can claw a worthless holding whose recovery prices to zero. -/
lemma Vault.clawback_recovery_priced_zero (v : Vault) (assets holderShares : STAmount)
    (r : ClawbackResult)
    (hnav : v.WithdrawNavExact false)
    (hz : assets.isZero = true)
    (hSc : holderShares.Canonical) (hSnn : holderShares.negative = false)
    (hok : v.clawback assets holderShares = .ok r) (herr : r.error = none) :
    0 ≤ r.sharesDestroyed.toRat ∧ r.sharesDestroyed.Canonical ∧
    v.sharesToAssetsWithdraw r.sharesDestroyed false = .ok r.assetsRecovered ∧
    r.assetsRecovered.toRat ≤ v.assetsAvailable.toRat ∧
    r.sharesDestroyed.isZero = false := by
  obtain ⟨cr, hcomp, herr2, hcrnz, hra_eq, hsd_eq, -⟩ :=
    Vault.clawback_success_reduces v assets holderShares r hok herr
  obtain ⟨-, ar, arn2, hprice, hnum2, hcase⟩ :=
    computeClawback_none_reduces_zero v assets holderShares cr hz hcomp herr2
  have hmain :
      0 ≤ cr.sharesDestroyed.toRat ∧ cr.sharesDestroyed.Canonical ∧
      v.sharesToAssetsWithdraw cr.sharesDestroyed false = .ok cr.assetsRecovered ∧
      cr.assetsRecovered.toRat ≤ v.assetsAvailable.toRat := by
    rcases hcase with ⟨hgtF, hcr_ar, hcr_sd⟩ |
        ⟨-, clamped, sd', ar', arn', hclamp, hshareT, hprice', hnum', hgtF, hcr_ar, hcr_sd⟩
    · -- direct branch: the destroyed shares are the holder's balance
      have hnn_sd : 0 ≤ holderShares.toRat := by
        rw [STAmount.toRat_of_nonneg holderShares
          (show holderShares.mIsNegative = false from hSnn)]
        positivity
      have hprice_cr : v.sharesToAssetsWithdraw cr.sharesDestroyed false
          = .ok cr.assetsRecovered := by
        rw [hcr_sd, hcr_ar]; exact hprice
      have hle : cr.assetsRecovered.toRat ≤ v.assetsAvailable.toRat := by
        rw [hcr_ar]
        exact Vault.sharesToAssetsWithdraw_le_assetsAvailable v holderShares ar arn2
          hSc hprice hnum2 hgtF
      exact ⟨by rw [hcr_sd]; exact hnn_sd, by rw [hcr_sd]; exact hSc, hprice_cr, hle⟩
    · -- recompute branch: shares priced from the clamped `assetsAvailable`,
      -- identical to the nonzero-amount clamp arm
      have hsdnz : cr.sharesDestroyed.isZero = false := hcrnz
      have hsdnz' : sd'.isZero = false := by rw [← hcr_sd]; exact hsdnz
      have hAA_neg : v.assetsAvailable.negative_ = false :=
        Number.negative_false_of_norm_nonneg v.assetsAvailable v.wf.assetsAvailable_norm
          v.exact.assetsAvailable_nonneg
      obtain ⟨hnn_cl, hexact_cl, hfloor_cl⟩ :=
        STAmount.ofNumber_input_spec v.numericType v.assetsAvailable .to_nearest clamped
          v.wf.assetsAvailable_norm hAA_neg hclamp
      obtain ⟨_, hq_pos, _, _, _, hnn_sd⟩ :=
        assetsToSharesWithdraw_spec v clamped sd' true hnav hnn_cl hexact_cl hfloor_cl
          hshareT hsdnz'
      have hcanon_sd : sd'.Canonical :=
        assetsToSharesWithdraw_shares_canonical v clamped sd' true false hshareT hsdnz'
      have hprice_cr : v.sharesToAssetsWithdraw cr.sharesDestroyed false
          = .ok cr.assetsRecovered := by
        rw [hcr_sd, hcr_ar]; exact hprice'
      have hle : cr.assetsRecovered.toRat ≤ v.assetsAvailable.toRat := by
        rw [hcr_ar]
        exact Vault.sharesToAssetsWithdraw_le_assetsAvailable v sd' ar' arn'
          hcanon_sd hprice' hnum' hgtF
      exact ⟨by rw [hcr_sd]; exact hnn_sd, by rw [hcr_sd]; exact hcanon_sd, hprice_cr, hle⟩
  obtain ⟨h1, h2, h3, h4⟩ := hmain
  exact ⟨by rw [hsd_eq]; exact h1, by rw [hsd_eq]; exact h2, by rw [hsd_eq, hra_eq]; exact h3,
    by rw [hra_eq]; exact h4, by rw [hsd_eq]; exact hcrnz⟩

/-- **Zero-capable recovery facts.** `clawback_recovery_priced` without the
nonzero amount hypothesis: the holder balance side conditions carry the zero
arm, and the positive NAV conjunct is dropped (it fails on the zero arm). -/
lemma Vault.clawback_recovery_priced' (v : Vault) (assets holderShares : STAmount)
    (r : ClawbackResult)
    (hnav : v.WithdrawNavExact false) (hc : assets.Canonical)
    (hSc : holderShares.Canonical) (hSnn : holderShares.negative = false)
    (hok : v.clawback assets holderShares = .ok r) (herr : r.error = none) :
    0 ≤ r.sharesDestroyed.toRat ∧ r.sharesDestroyed.Canonical ∧
    v.sharesToAssetsWithdraw r.sharesDestroyed false = .ok r.assetsRecovered ∧
    r.assetsRecovered.toRat ≤ v.assetsAvailable.toRat ∧
    r.sharesDestroyed.isZero = false := by
  by_cases hz : assets.isZero = true
  · exact Vault.clawback_recovery_priced_zero v assets holderShares r hnav hz hSc hSnn
      hok herr
  · obtain ⟨h1, h2, h3, h4, h5, -⟩ :=
      Vault.clawback_recovery_priced v assets holderShares r hnav hc (by simpa using hz)
        hok herr
    exact ⟨h1, h2, h3, h4, h5⟩

/-- **Proof body of `clawback_assetsRecovered`.** The recovery is nonnegative, never
exceeds `assetsAvailable`, and prices the destroyed shares at most `depositε`
relatively above their ideal worth. The shortfall from the destroyed shares' ideal
worth splits on the payout:
* a nonzero payout falls short by at most the interior stage error plus `2·10^exponent`;
* a payout that underflows to the canonical zero forces the ideal itself below the
  smallest positive representable of the vault's numeric type — one whole unit for an
  integral asset, `10⁻⁸¹` for a fractional one, with `idealAssetsClawback · (1 - depositε)`
  under that grid minimum. The lawful vault `assetsTotal = assetsAvailable = 0.8·10⁻⁸¹`,
  `sharesTotal = 1`, fractional, clawing the canonical `assets = 10⁻⁸¹` attains the zero
  branch: `sharesDestroyed = 1`, `assetsRecovered = 0`, and the ideal
  `withdrawNav = 0.8·10⁻⁸¹` sits below the grid minimum `10⁻⁸¹`. -/
theorem Vault.clawback_assetsRecovered_proof (v : Vault) (assets holderShares : STAmount)
    (r : ClawbackResult)
    (hnav : v.WithdrawNavExact false) (hc : assets.Canonical)
    (hznz : assets.isZero = false)
    (hok : v.clawback assets holderShares = .ok r) (herr : r.error = none) :
    r.assetsRecovered.toRat ≤ v.toExact.assetsAvailable ∧
    0 ≤ r.assetsRecovered.toRat ∧
    r.assetsRecovered.toRat ≤
      v.idealAssetsClawback r.sharesDestroyed.toRat * (1 + depositε) ∧
    (r.assetsRecovered.isZero = false →
      v.idealAssetsClawback r.sharesDestroyed.toRat - r.assetsRecovered.toRat ≤
        v.idealAssetsClawback r.sharesDestroyed.toRat * depositε +
          2 * (10 : ℚ) ^ r.assetsRecovered.exponent) ∧
    (r.assetsRecovered.isZero = true →
      v.idealAssetsClawback r.sharesDestroyed.toRat * (1 - depositε) <
        if v.numericType.isIntegral then 1 else (10 : ℚ) ^ (-81 : ℤ)) := by
  obtain ⟨hnn_sd, hcanon_sd, hprice, hle_AA, hsdnz, hnav_pos⟩ :=
    Vault.clawback_recovery_priced v assets holderShares r hnav hc hznz hok herr
  obtain ⟨hrec_nn, hrec_le, hrec_shortfall⟩ :=
    Vault.sharesToAssetsWithdraw_bounds_proof v r.sharesDestroyed r.assetsRecovered false
      hnn_sd hcanon_sd hnav hprice
  refine ⟨hle_AA, hrec_nn, ?_, ?_, ?_⟩
  · rw [RawVault.idealAssetsClawback_eq_withdraw]; exact hrec_le
  · -- nonzero payout: the interior stage error plus 2 ULP
    intro hrz
    rw [RawVault.idealAssetsClawback_eq_withdraw]
    exact hrec_shortfall hrz
  · -- zero payout: the ideal is below the smallest positive representable of the type
    intro hrz
    rw [RawVault.idealAssetsClawback_eq_withdraw]
    set ideal : ℚ := v.idealAssetsWithdraw false r.sharesDestroyed.toRat with hideal_def
    have hmv : r.sharesDestroyed.mValue ≠ 0 := ne_of_beq_false hsdnz
    have hshpos : 0 < r.sharesDestroyed.toRat := by
      have hfloor := STAmount.Canonical.abs_toRat_ge r.sharesDestroyed hcanon_sd hmv
      rcases lt_or_eq_of_le hnn_sd with h | h
      · exact h
      · exfalso; rw [← h, abs_zero] at hfloor
        linarith [show (0:ℚ) < 10 ^ (-81:ℤ) from zpow_pos (by norm_num) _]
    have hεnn : (0 : ℚ) ≤ depositε := by rw [depositε_eq]; norm_num
    have hideal_nn : 0 ≤ ideal :=
      (Vault.sharesToAssetsWithdraw_spec v r.sharesDestroyed r.assetsRecovered false
        hnn_sd hcanon_sd hnav hprice).2.1
    have hzmv : r.assetsRecovered.mValue = 0 := by
      have := hrz; rw [STAmount.isZero] at this; exact beq_iff_eq.mp this
    obtain ⟨aN, hof, hnzcase, hzcase⟩ :=
      Vault.recovery_pipeline_bound v r.sharesDestroyed r.assetsRecovered hnav hcanon_sd
        hnav_pos hshpos hprice
    by_cases haN0 : aN.mantissa_ = 0
    · -- the `Number` pipeline underflowed: the ideal is `Number`-tiny, below either grid step
      have hidsmall := hzcase haN0
      have hC_big : (10:ℚ)^(-32700:ℤ) <
          if v.numericType.isIntegral then (1:ℚ) else (10:ℚ)^(-81:ℤ) := by
        by_cases hint : v.numericType.isIntegral = true
        · rw [if_pos hint]
          calc (10:ℚ)^(-32700:ℤ) < (10:ℚ)^(0:ℤ) :=
                zpow_lt_zpow_right₀ (by norm_num) (by norm_num)
            _ = 1 := by norm_num
        · rw [if_neg hint]
          exact zpow_lt_zpow_right₀ (by norm_num) (by norm_num)
      nlinarith [hidsmall, hC_big, mul_nonneg hideal_nn hεnn]
    · -- the `ofNumber` snap floored a nonzero `aN` to zero: `aN` below the grid minimum
      obtain ⟨haNnorm, haNneg, hbound⟩ := hnzcase haN0
      by_cases hint : v.numericType.isIntegral = true
      · rw [if_pos hint]
        have haN1 : aN.toRat < 1 :=
          STAmount.ofNumber_integral_zero_floor v.numericType aN r.assetsRecovered hint
            haNnorm haNneg hof hzmv
        nlinarith [hbound, haN1]
      · rw [if_neg hint]
        have hint' : v.numericType.isIntegral = false := by
          cases h : v.numericType.isIntegral with
          | true => exact absurd h hint
          | false => rfl
        have haN81 : aN.toRat < (10:ℚ)^(-81:ℤ) :=
          STAmount.ofNumber_fractional_zero_below_min v.numericType aN r.assetsRecovered hint'
            haNnorm haNneg haN0 hof hzmv
        nlinarith [hbound, haN81]

/-- **Proof body of `clawback_assetsRecovered_integral`.** -/
theorem Vault.clawback_assetsRecovered_integral_proof (v : Vault) (assets holderShares : STAmount)
    (r : ClawbackResult)
    (hnav : v.WithdrawNavExact false) (hint : v.numericType.isIntegral = true)
    (hc : assets.Canonical) (hznz : assets.isZero = false)
    (hok : v.clawback assets holderShares = .ok r) (herr : r.error = none) :
    v.idealAssetsClawback r.sharesDestroyed.toRat - r.assetsRecovered.toRat ≤
      1 + v.idealAssetsClawback r.sharesDestroyed.toRat * depositε := by
  obtain ⟨hnn_sd, hcanon_sd, hprice, hle_AA, hsdnz, hnav_pos⟩ :=
    Vault.clawback_recovery_priced v assets holderShares r hnav hc hznz hok herr
  rw [RawVault.idealAssetsClawback_eq_withdraw]
  set ideal : ℚ := v.idealAssetsWithdraw false r.sharesDestroyed.toRat with hideal_def
  have hmv : r.sharesDestroyed.mValue ≠ 0 := ne_of_beq_false hsdnz
  have hshpos : 0 < r.sharesDestroyed.toRat := by
    have hfloor := STAmount.Canonical.abs_toRat_ge r.sharesDestroyed hcanon_sd hmv
    rcases lt_or_eq_of_le hnn_sd with h | h
    · exact h
    · exfalso; rw [← h, abs_zero] at hfloor
      linarith [show (0:ℚ) < 10 ^ (-81:ℤ) from zpow_pos (by norm_num) _]
  have hεnn : (0 : ℚ) ≤ depositε := by rw [depositε_eq]; norm_num
  have hideal_nn : 0 ≤ ideal :=
    (Vault.sharesToAssetsWithdraw_spec v r.sharesDestroyed r.assetsRecovered false
      hnn_sd hcanon_sd hnav hprice).2.1
  by_cases hrz : r.assetsRecovered.isZero = false
  · -- nonzero payout: the `.downward` floor within one integral ULP (`10^0 = 1`)
    obtain ⟨-, -, -, h4⟩ :=
      Vault.sharesToAssetsWithdraw_spec v r.sharesDestroyed r.assetsRecovered false
        hnn_sd hcanon_sd hnav hprice
    obtain ⟨-, hexp0, -⟩ :=
      Vault.sharesToAssetsWithdraw_integral_shape v r.sharesDestroyed r.assetsRecovered false hint hprice
    have hb := h4 hrz
    rw [show r.assetsRecovered.exponent = (0 : ℤ) from hexp0, zpow_zero] at hb
    linarith [hb]
  · -- zero payout: the ideal is below one whole unit (integral floor `< 1`)
    have hzmv : r.assetsRecovered.mValue = 0 := by
      by_contra hne; exact hrz (by simp [STAmount.isZero, hne])
    have hrec0 : r.assetsRecovered.toRat = 0 := by rw [STAmount.toRat_signed, hzmv]; simp
    obtain ⟨aN, hof, hnzcase, hzcase⟩ :=
      Vault.recovery_pipeline_bound v r.sharesDestroyed r.assetsRecovered hnav hcanon_sd
        hnav_pos hshpos hprice
    by_cases haN0 : aN.mantissa_ = 0
    · have hidsmall := hzcase haN0
      have hle1 : (10:ℚ) ^ (-32700:ℤ) ≤ 1 := by
        calc (10:ℚ) ^ (-32700:ℤ) ≤ (10:ℚ) ^ (0:ℤ) :=
              zpow_le_zpow_right₀ (by norm_num) (by norm_num)
          _ = 1 := by norm_num
      rw [hrec0]
      nlinarith [hidsmall, hle1, mul_nonneg hideal_nn hεnn]
    · obtain ⟨haNnorm, haNneg, hbound⟩ := hnzcase haN0
      have haN1 : aN.toRat < 1 :=
        STAmount.ofNumber_integral_zero_floor v.numericType aN r.assetsRecovered hint
          haNnorm haNneg hof hzmv
      rw [hrec0]; linarith [hbound, haN1]

/-! ## `clawback_vault_updates` support -/

/-- A den-`1` rational equals its integer numerator, cast back to `ℚ`. -/
lemma eq_intCast_of_den_one {q : ℚ} (h : q.den = 1) : q = (q.num : ℚ) := by
  conv_lhs => rw [← Rat.num_div_den q]
  rw [h]; simp

/-- **A normalized `Number` whose magnitude clears `10⁻⁸¹` has exponent `≥ -99`.**
The mantissa stays below `10¹⁹`, so `10⁻⁸¹ ≤ mantissa · 10^e < 10^(19+e)` forces
`-81 < 19 + e`. -/
lemma Number.exponent_ge_of_abs_toRat_ge (n : Number) (hn : n.isNormalized)
    (hne : n.mantissa_ ≠ 0) (h : (10 : ℚ) ^ (-81 : ℤ) ≤ |n.toRat|) :
    (-99 : ℤ) ≤ n.exponent_ := by
  obtain ⟨-, hhi⟩ := hn.mantissaBounds_nat hne
  have hmlt : (n.mantissa_.toNat : ℚ) < (10 : ℚ) ^ (19 : ℕ) := by exact_mod_cast hhi
  have hpe_pos : (0 : ℚ) < (10 : ℚ) ^ n.exponent_ := zpow_pos (by norm_num) _
  have hstep : (n.mantissa_.toNat : ℚ) * (10 : ℚ) ^ n.exponent_
      < (10 : ℚ) ^ (19 : ℕ) * (10 : ℚ) ^ n.exponent_ :=
    mul_lt_mul_of_pos_right hmlt hpe_pos
  have hcombine : (10 : ℚ) ^ (-81 : ℤ) < (10 : ℚ) ^ (19 : ℕ) * (10 : ℚ) ^ n.exponent_ := by
    have heq : |n.toRat| = (n.mantissa_.toNat : ℚ) * 10 ^ n.exponent_ := abs_toRat_eq n
    rw [heq] at h; linarith [hstep]
  rw [← zpow_natCast (10 : ℚ) 19, ← zpow_add₀ (by norm_num : (10 : ℚ) ≠ 0)] at hcombine
  have hlt : (-81 : ℤ) < ((19 : ℕ) : ℤ) + n.exponent_ :=
    (zpow_lt_zpow_iff_right₀ (by norm_num : (1 : ℚ) < 10)).mp hcombine
  omega

/-- **The destroyed shares of a successful clawback are an `int64`-canonical
record.** Both `computeClawback` branches pack the shares through `ofNumber .int64`,
so the nonzero output is `IntegralCanonical`. -/
lemma Vault.clawback_shares_intCanonical (v : Vault) (assets holderShares : STAmount)
    (r : ClawbackResult) (hznz : assets.isZero = false)
    (hok : v.clawback assets holderShares = .ok r) (herr : r.error = none) :
    r.sharesDestroyed.IntegralCanonical := by
  obtain ⟨cr, hcomp, herr2, hcrnz, -, hsd_eq, -⟩ :=
    Vault.clawback_success_reduces v assets holderShares r hok herr
  obtain ⟨-, sd, ar, arn2, hshares, hprice, hnum2, hcase⟩ :=
    computeClawback_none_reduces v assets holderShares cr hznz hcomp herr2
  rw [hsd_eq]
  rcases hcase with ⟨-, -, hcr_sd⟩ | ⟨-, clamped, sd', ar', arn', -, hshareT, -, -, -, -, hcr_sd⟩
  · have hnz : sd.isZero = false := by rw [← hcr_sd]; exact hcrnz
    rw [hcr_sd]
    exact (assetsToSharesWithdraw_int64_canonical v assets sd false false hshares hnz).1
  · have hnz : sd'.isZero = false := by rw [← hcr_sd]; exact hcrnz
    rw [hcr_sd]
    exact (assetsToSharesWithdraw_int64_canonical v clamped sd' true false hshareT hnz).1

/-- **Zero-capable variant of `clawback_shares_intCanonical`.** On the zero-amount
direct branch the destroyed shares are the holder's balance, whose side condition
carries the claim. Every other branch packs through `ofNumber .int64` as before. -/
lemma Vault.clawback_shares_intCanonical' (v : Vault) (assets holderShares : STAmount)
    (r : ClawbackResult) (hSic : holderShares.IntegralCanonical)
    (hok : v.clawback assets holderShares = .ok r) (herr : r.error = none) :
    r.sharesDestroyed.IntegralCanonical := by
  by_cases hz : assets.isZero = true
  · obtain ⟨cr, hcomp, herr2, hcrnz, -, hsd_eq, -⟩ :=
      Vault.clawback_success_reduces v assets holderShares r hok herr
    obtain ⟨-, ar, arn2, -, -, hcase⟩ :=
      computeClawback_none_reduces_zero v assets holderShares cr hz hcomp herr2
    rw [hsd_eq]
    rcases hcase with ⟨-, -, hcr_sd⟩ | ⟨-, clamped, sd', ar', arn', -, hshareT, -, -, -, -, hcr_sd⟩
    · rw [hcr_sd]; exact hSic
    · have hnz : sd'.isZero = false := by rw [← hcr_sd]; exact hcrnz
      rw [hcr_sd]
      exact (assetsToSharesWithdraw_int64_canonical v clamped sd' true false hshareT hnz).1
  · exact Vault.clawback_shares_intCanonical v assets holderShares r (by simpa using hz) hok herr

/-- Cast a `Number` back through `.toRat.num.toNat` when its value is an in-domain
integer difference `S - k` of two integer-valued rationals with `k ≤ S`. -/
lemma Number.natCast_num_toNat_of_int_sub (n : Number) (S k : ℚ)
    (hval : n.toRat = S - k) (hSden : S.den = 1) (hkden : k.den = 1) (hle : k ≤ S) :
    ((n.toRat.num.toNat : ℕ) : ℚ) = S - k := by
  have hnn : 0 ≤ n.toRat := by rw [hval]; linarith
  have hden1 : n.toRat.den = 1 := by
    rw [hval, eq_intCast_of_den_one hSden, eq_intCast_of_den_one hkden, ← Int.cast_sub]
    exact Rat.den_intCast _
  have hnum_nn : 0 ≤ n.toRat.num := Rat.num_nonneg.mpr hnn
  rw [← Int.cast_natCast, Int.toNat_of_nonneg hnum_nn, ← eq_intCast_of_den_one hden1, hval]

/-- **Shared core of the `clawback_vault_updates` proofs.** Works from the
recovery facts directly, so the nonzero-amount and the zero-amount (claw all
holder shares) routes both land here: `assetsTotal` and `assetsAvailable` are
the stored value minus the recovery within `depositε`, and the `sharesTotal`
update is the exact integer difference on the share domain. -/
theorem Vault.clawback_vault_updates_core (v : Vault) (assets holderShares : STAmount)
    (r : ClawbackResult)
    (hnav : v.WithdrawNavExact false)
    (hok : v.clawback assets holderShares = .ok r) (herr : r.error = none)
    (hnn_sd : 0 ≤ r.sharesDestroyed.toRat) (hcanon_sd : r.sharesDestroyed.Canonical)
    (hprice : v.sharesToAssetsWithdraw r.sharesDestroyed false = .ok r.assetsRecovered)
    (hle_AA : r.assetsRecovered.toRat ≤ v.assetsAvailable.toRat)
    (hsdnz : r.sharesDestroyed.isZero = false)
    (hint_sd : r.sharesDestroyed.IntegralCanonical) :
    RoundsWithin r.vault'.assetsTotal
      (v.toExact.assetsTotal - r.assetsRecovered.toRat) .to_nearest depositε ∧
    RoundsWithin r.vault'.assetsAvailable
      (v.toExact.assetsAvailable - r.assetsRecovered.toRat) .to_nearest depositε ∧
    (r.sharesDestroyed.toRat ≤ (v.toExact.sharesTotal : ℚ) ∧
        (v.toExact.sharesTotal : ℚ) ≤ 2 ^ 63 - 1 →
      (r.vault'.toExact.sharesTotal : ℚ) =
        (v.toExact.sharesTotal : ℚ) - r.sharesDestroyed.toRat) := by
  obtain ⟨cr, hcomp, herr2, hcrnz, hra_eq, hsd_eq, sbn, arn, at', st', av', atr, atr',
      hsbn, harn, hat, -, -, -, hst, hav, hr⟩ :=
    Vault.clawback_success_reduces v assets holderShares r hok herr
  -- the recovery `Number` `arn` is value-exact and normalized
  have hnum_r : r.assetsRecovered.toNumber .to_nearest = .ok arn := by rw [hra_eq]; exact harn
  obtain ⟨harn_val, harn_norm⟩ :=
    Vault.sharesToAssetsWithdraw_toNumber_facts v r.sharesDestroyed r.assetsRecovered false arn
      hcanon_sd hprice hnum_r
  have hrec_nn : 0 ≤ r.assetsRecovered.toRat :=
    (Vault.sharesToAssetsWithdraw_spec v r.sharesDestroyed r.assetsRecovered false
      hnn_sd hcanon_sd hnav hprice).1
  -- clean `ℚ` sign/order facts on the stored fields
  have hAT_nn : (0 : ℚ) ≤ v.assetsTotal.toRat := v.exact.assetsTotal_nonneg
  have hAA_nn : (0 : ℚ) ≤ v.assetsAvailable.toRat := v.exact.assetsAvailable_nonneg
  have hAA_le_AT : v.assetsAvailable.toRat ≤ v.assetsTotal.toRat := v.exact.assetsAvailable_le
  -- the destroyed shares clear the `10⁻⁸¹` magnitude floor, so are positive
  have hshpos : 0 < r.sharesDestroyed.toRat :=
    STAmount.Canonical.toRat_pos_of_nonneg r.sharesDestroyed hcanon_sd hnn_sd hsdnz
  have hmv_of : r.assetsRecovered.toRat ≠ 0 → r.assetsRecovered.mValue ≠ 0 := by
    intro hne hmv0; apply hne; rw [STAmount.toRat_signed, hmv0]; simp
  -- the recovery magnitude floor `10⁻⁸¹` for a positive payout
  have hfloor_rec : 0 < r.assetsRecovered.toRat →
      (10 : ℚ) ^ (-81 : ℤ) ≤ |r.assetsRecovered.toRat| := by
    intro hp_pos
    obtain ⟨-, -, hp_up, -⟩ :=
      Vault.sharesToAssetsWithdraw_spec_raw v r.sharesDestroyed r.assetsRecovered false
        hnn_sd hcanon_sd hnav hprice
    have hS_nn : (0 : ℚ) ≤ (v.toExact.sharesTotal : ℚ) := by exact_mod_cast Nat.zero_le _
    have hnav_pos : 0 < v.withdrawNav := by
      by_contra h
      push_neg at h
      have hideal_np : v.idealAssetsWithdraw false r.sharesDestroyed.toRat ≤ 0 := by
        unfold RawVault.idealAssetsWithdraw
        rw [if_neg (by decide : ¬((false : Bool) = true))]
        exact div_nonpos_iff.mpr (Or.inr ⟨mul_nonpos_iff.mpr (Or.inr ⟨h, hnn_sd⟩), hS_nn⟩)
      have hIc : v.idealAssetsWithdraw false r.sharesDestroyed.toRat
          * (1 + (12 / (2 ^ 63 - 3))) ≤ 0 :=
        mul_nonpos_iff.mpr (Or.inr ⟨hideal_np, by norm_num⟩)
      linarith [hp_up, hp_pos]
    obtain ⟨aN, hof, hnzcase, -⟩ :=
      Vault.recovery_pipeline_bound v r.sharesDestroyed r.assetsRecovered hnav hcanon_sd
        hnav_pos hshpos hprice
    have hmv : r.assetsRecovered.mValue ≠ 0 := hmv_of hp_pos.ne'
    have haNnz : aN.mantissa_ ≠ 0 :=
      STAmount.ofNumber_source_ne_zero v.numericType aN .downward r.assetsRecovered hof hmv
    obtain ⟨haNnorm, -, -⟩ := hnzcase haNnz
    exact STAmount.canonical_disj_abs_toRat_ge r.assetsRecovered
      (STAmount.ofNumber_disj_canonical v.numericType aN .downward r.assetsRecovered haNnorm hof
        hmv)
      hmv
  -- sign bits of the operands are clear
  have harn_neg : arn.negative_ = false :=
    Number.negative_false_of_norm_nonneg arn harn_norm (by rw [harn_val]; exact hrec_nn)
  have hAT_neg : v.assetsTotal.negative_ = false :=
    Number.negative_false_of_norm_nonneg v.assetsTotal v.wf.assetsTotal_norm hAT_nn
  have hAA_neg : v.assetsAvailable.negative_ = false :=
    Number.negative_false_of_norm_nonneg v.assetsAvailable v.wf.assetsAvailable_norm hAA_nn
  -- a nonzero recovery Number forces a positive payout, hence positive stored fields
  have hrec_pos_of : arn.mantissa_ ≠ 0 → 0 < r.assetsRecovered.toRat := by
    intro hm
    have hne : r.assetsRecovered.toRat ≠ 0 := by
      rw [← harn_val]; exact Number.toRat_ne_zero_of_mantissa_ne_zero arn hm
    exact lt_of_le_of_ne hrec_nn (Ne.symm hne)
  have hxm_AT : arn.mantissa_ ≠ 0 → v.assetsTotal.mantissa_ ≠ 0 := by
    intro hm
    have : 0 < v.assetsTotal.toRat := lt_of_lt_of_le (hrec_pos_of hm) (le_trans hle_AA hAA_le_AT)
    exact Number.mantissa_ne_zero_of_toRat_ne_zero this.ne'
  have hxm_AA : arn.mantissa_ ≠ 0 → v.assetsAvailable.mantissa_ ≠ 0 := by
    intro hm
    have : 0 < v.assetsAvailable.toRat := lt_of_lt_of_le (hrec_pos_of hm) hle_AA
    exact Number.mantissa_ne_zero_of_toRat_ne_zero this.ne'
  -- exponent floors: both operands stay `≥ 10⁻⁸¹`, so their exponents clear `-99`
  have hEarn_floor : arn.mantissa_ ≠ 0 → (-99 : ℤ) ≤ arn.exponent_ := by
    intro hm
    have hfloor : (10 : ℚ) ^ (-81 : ℤ) ≤ |arn.toRat| := by
      rw [harn_val]; exact hfloor_rec (hrec_pos_of hm)
    exact Number.exponent_ge_of_abs_toRat_ge arn harn_norm hm hfloor
  have hEAT_floor : arn.mantissa_ ≠ 0 → (-99 : ℤ) ≤ v.assetsTotal.exponent_ := by
    intro hm
    have hrec' := hfloor_rec (hrec_pos_of hm)
    rw [abs_of_nonneg hrec_nn] at hrec'
    have hAT_ge : (10 : ℚ) ^ (-81 : ℤ) ≤ |v.assetsTotal.toRat| := by
      rw [abs_of_nonneg hAT_nn]; linarith [le_trans hle_AA hAA_le_AT]
    exact Number.exponent_ge_of_abs_toRat_ge v.assetsTotal v.wf.assetsTotal_norm (hxm_AT hm) hAT_ge
  have hEAA_floor : arn.mantissa_ ≠ 0 → (-99 : ℤ) ≤ v.assetsAvailable.exponent_ := by
    intro hm
    have hrec' := hfloor_rec (hrec_pos_of hm)
    rw [abs_of_nonneg hrec_nn] at hrec'
    have hAA_ge : (10 : ℚ) ^ (-81 : ℤ) ≤ |v.assetsAvailable.toRat| := by
      rw [abs_of_nonneg hAA_nn]; linarith [hle_AA]
    exact Number.exponent_ge_of_abs_toRat_ge v.assetsAvailable v.wf.assetsAvailable_norm
      (hxm_AA hm) hAA_ge
  -- the two subtractions round within `depositε`
  have hround_AT : RoundsWithin at' (v.assetsTotal.toRat - arn.toRat) .to_nearest depositε :=
    Number.sub_recovery_rounds_within v.assetsTotal arn at' (-99)
      v.wf.assetsTotal_norm hAT_neg hxm_AT harn_norm harn_neg hEAT_floor hEarn_floor
      (by norm_num [minExponent]) hat
  have hround_AA : RoundsWithin av' (v.assetsAvailable.toRat - arn.toRat) .to_nearest depositε :=
    Number.sub_recovery_rounds_within v.assetsAvailable arn av' (-99)
      v.wf.assetsAvailable_norm hAA_neg hxm_AA harn_norm harn_neg hEAA_floor hEarn_floor
      (by norm_num [minExponent]) hav
  have hv'_AT : r.vault'.assetsTotal = at' := by rw [hr]
  have hv'_AA : r.vault'.assetsAvailable = av' := by rw [hr]
  refine ⟨?_, ?_, ?_⟩
  · rw [hv'_AT]; rw [harn_val] at hround_AT; exact hround_AT
  · rw [hv'_AA]; rw [harn_val] at hround_AA; exact hround_AA
  · rintro ⟨hk_le, hS_le⟩
    have hSeq : ((v.toExact.sharesTotal : ℕ) : ℚ) = v.sharesTotal.toRat :=
      RawVault.WF.toExact_sharesTotal v.toRawVault v.wf
    have hkle_S : r.sharesDestroyed.toRat ≤ v.sharesTotal.toRat := by rw [← hSeq]; exact hk_le
    have hS_bound : v.sharesTotal.toRat ≤ 2 ^ 63 - 1 := by rw [← hSeq]; exact hS_le
    -- shares `Number` `sbn` is value-exact, normalized, integer-valued
    have hnum_sbn : r.sharesDestroyed.toNumber .to_nearest = .ok sbn := by rw [hsd_eq]; exact hsbn
    obtain ⟨sbn0, hsbn0ok, hsbn0val, hsbn0norm⟩ :=
      STAmount.toNumber_canonical_exact r.sharesDestroyed .to_nearest hcanon_sd
    have hsbn_eqn : sbn0 = sbn := Except.ok.inj (hsbn0ok.symm.trans hnum_sbn)
    have hsbn_val_r : sbn.toRat = r.sharesDestroyed.toRat := by rw [← hsbn_eqn]; exact hsbn0val
    have hsbn_norm : sbn.isNormalized := by rw [← hsbn_eqn]; exact hsbn0norm
    have hkden : r.sharesDestroyed.toRat.den = 1 :=
      STAmount.IntegralCanonical.den_eq_one r.sharesDestroyed hint_sd
    have hst_val : st'.toRat = v.sharesTotal.toRat - r.sharesDestroyed.toRat :=
      operator_sub_exact_int_le v.sharesTotal sbn st' r.sharesDestroyed.toRat
        v.wf.sharesTotal_norm hS_bound hsbn_norm hsbn_val_r hkden hnn_sd hkle_S hst
    have hv'ST : r.vault'.sharesTotal = st' := by rw [hr]
    have hlhs : (r.vault'.toExact.sharesTotal : ℚ)
        = v.sharesTotal.toRat - r.sharesDestroyed.toRat := by
      show ((r.vault'.sharesTotal.toRat.num.toNat : ℕ) : ℚ)
        = v.sharesTotal.toRat - r.sharesDestroyed.toRat
      rw [hv'ST]
      exact Number.natCast_num_toNat_of_int_sub st' v.sharesTotal.toRat r.sharesDestroyed.toRat
        hst_val v.wf.sharesTotal_int hkden hkle_S
    rw [hlhs, hSeq]

/-- **Proof body of `clawback_vault_updates`.** `assetsTotal` and `assetsAvailable`
are the stored value minus the recovery within `depositε` (a `to_nearest`
subtraction of a nonnegative recovery that, when nonzero, sits `≥ 10⁻⁸¹` on a grid
that never underflows the difference to zero), and the `sharesTotal` update is the
exact integer difference on the share domain. -/
theorem Vault.clawback_vault_updates_proof (v : Vault) (assets holderShares : STAmount)
    (r : ClawbackResult)
    (hnav : v.WithdrawNavExact false) (hc : assets.Canonical)
    (hznz : assets.isZero = false)
    (hok : v.clawback assets holderShares = .ok r) (herr : r.error = none) :
    RoundsWithin r.vault'.assetsTotal
      (v.toExact.assetsTotal - r.assetsRecovered.toRat) .to_nearest depositε ∧
    RoundsWithin r.vault'.assetsAvailable
      (v.toExact.assetsAvailable - r.assetsRecovered.toRat) .to_nearest depositε ∧
    (r.sharesDestroyed.toRat ≤ (v.toExact.sharesTotal : ℚ) ∧
        (v.toExact.sharesTotal : ℚ) ≤ 2 ^ 63 - 1 →
      (r.vault'.toExact.sharesTotal : ℚ) =
        (v.toExact.sharesTotal : ℚ) - r.sharesDestroyed.toRat) := by
  obtain ⟨hnn_sd, hcanon_sd, hprice, hle_AA, hsdnz, -⟩ :=
    Vault.clawback_recovery_priced v assets holderShares r hnav hc hznz hok herr
  exact Vault.clawback_vault_updates_core v assets holderShares r hnav hok herr
    hnn_sd hcanon_sd hprice hle_AA hsdnz
    (Vault.clawback_shares_intCanonical v assets holderShares r hznz hok herr)

/-- **Zero-capable variant of `clawback_vault_updates_proof`.** The holder balance
side conditions carry the zero-amount (claw all holder shares) arm. -/
theorem Vault.clawback_vault_updates_proof' (v : Vault) (assets holderShares : STAmount)
    (r : ClawbackResult)
    (hnav : v.WithdrawNavExact false) (hc : assets.Canonical)
    (hSic : holderShares.IntegralCanonical) (hSc : holderShares.Canonical)
    (hSnn : holderShares.negative = false)
    (hok : v.clawback assets holderShares = .ok r) (herr : r.error = none) :
    RoundsWithin r.vault'.assetsTotal
      (v.toExact.assetsTotal - r.assetsRecovered.toRat) .to_nearest depositε ∧
    RoundsWithin r.vault'.assetsAvailable
      (v.toExact.assetsAvailable - r.assetsRecovered.toRat) .to_nearest depositε ∧
    (r.sharesDestroyed.toRat ≤ (v.toExact.sharesTotal : ℚ) ∧
        (v.toExact.sharesTotal : ℚ) ≤ 2 ^ 63 - 1 →
      (r.vault'.toExact.sharesTotal : ℚ) =
        (v.toExact.sharesTotal : ℚ) - r.sharesDestroyed.toRat) := by
  obtain ⟨hnn_sd, hcanon_sd, hprice, hle_AA, hsdnz⟩ :=
    Vault.clawback_recovery_priced' v assets holderShares r hnav hc hSc hSnn hok herr
  exact Vault.clawback_vault_updates_core v assets holderShares r hnav hok herr
    hnn_sd hcanon_sd hprice hle_AA hsdnz
    (Vault.clawback_shares_intCanonical' v assets holderShares r hSic hok herr)

end XRPL.Model.SingleAssetVault
