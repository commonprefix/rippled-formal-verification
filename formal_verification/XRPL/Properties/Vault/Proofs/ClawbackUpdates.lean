import XRPL.Properties.Vault.Proofs.ClawbackRecovery

/-! # The vault update a clawback makes

A clawback subtracts its recovery from the cash and its destroyed shares from the share total. The
share total is exact. On a reachable vault all the shares together are worth exactly the cash, so a
clawback of every share recovers all of it and empties the vault. -/

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol

/-- On a reachable vault all the shares together are worth exactly the cash. The vault prices at its
cash, and the 19-digit price of all the shares sits so close to it that the conversion rounds back to it. -/
lemma Vault.Reachable.sharesToAssetsWithdraw_all (v : Vault) (t0 : UInt32) (hr : Vault.Reachable v t0)
    (hmax : v.numericType.isIntegral = true → v.numericType.maxValue.toNat ≤ maxRep.toNat)
    (shares assets : STAmount) (waive : Bool) (hc : shares.Canonical)
    (hall : shares.toRat = v.toExact.sharesTotal)
    (hok : v.sharesToAssetsWithdraw shares waive = .ok assets) :
    assets.toRat = v.assetsAvailable.toRat := by
  have hcast := RawVault.WF.toExact_sharesTotal v.toRawVault v.wf
  have hs0 : 0 ≤ shares.toRat := by rw [hall]; exact Nat.cast_nonneg _
  have hle := Vault.Reachable.sharesToAssetsWithdraw_le_cash v t0 hr hmax shares assets waive hs0 hc hall.le hok
  have hp0 := Vault.sharesToAssetsWithdraw_nonneg v _ _ waive (Or.inl hc) hs0 hok
  have hAA0 : 0 ≤ v.assetsAvailable.toRat := v.exact.assetsAvailable_nonneg
  rcases eq_or_lt_of_le hAA0 with hAAz | hAApos
  · linarith
  -- the cash is at least one base step, at least `10⁻¹⁰`
  obtain ⟨hbk, hAA10⟩ := (Vault.Reachable.openZone_proof v t0 hr hmax).cash_ge hAApos
  -- the vault prices at its cash, and all the shares together are worth all of it
  obtain ⟨nav, hsub, hnavn, hcase⟩ := WdPrice.price_cases v _ _ waive hok
  have hnavv := Vault.Reachable.nav_eq_cash v t0 hr waive nav hsub
  rcases hcase with ⟨h0, -⟩ | ⟨-, sn, NS, an, hsn, hmul, hdiv, hof⟩
  · rw [Number.toRat_eq_zero_of_mantissa_zero nav h0] at hnavv
    linarith
  obtain ⟨sn0, hsn0, hsnv, hsnn⟩ := STAmount.toNumber_exact_canonical shares .to_nearest
    (STAmount.Canonical.exactCanonical _ hc)
  obtain rfl := Except.ok.inj (hsn0.symm.trans hsn)
  obtain ⟨hSTpos, hST1, -⟩ := Vault.sharesTotal_bounds_of_cash v hAApos
  have hT : nav.toRat * sn0.toRat / v.sharesTotal.toRat = v.assetsAvailable.toRat := by
    rw [hnavv, hsnv, hall, hcast]
    field_simp
  obtain ⟨hann, hanpos, hb⟩ := pipe_large nav sn0 NS an v.sharesTotal hnavn hsnn v.wf.sharesTotal_norm
    (by rw [hnavv]; exact hAA0) (by rw [hsnv]; exact hs0) hSTpos hST1
    (by rw [hT]; exact le_trans (zpow_le_zpow_right₀ (by norm_num) (by norm_num)) hAA10) hmul hdiv
  rw [hT] at hb
  have hδ : (sharesε : ℚ) ≤ 2 / 10 ^ 18 := by unfold sharesε; norm_num
  have hb2 : |an.toRat - v.assetsAvailable.toRat| ≤ v.assetsAvailable.toRat * (2 / 10 ^ 18) :=
    le_trans hb (mul_le_mul_of_nonneg_left hδ hAA0)
  obtain ⟨hb3, -⟩ := abs_le.mp hb2
  -- the cash, as an amount of the asset
  have hrd := (Vault.Reachable.openZone_proof v t0 hr hmax).cashExact
  obtain ⟨cash, hcash⟩ := STAmount.ofNumber_ok_of_isRounded_false _ _ hrd
  have hcv := Vault.final_payout_exact v cash hrd hmax hcash
  have hcm : cash.mValue ≠ 0 := fun h => by
    rw [(STAmount.toRat_eq_zero_iff _).mpr h] at hcv; linarith
  have hcE := STAmount.ofNumber_exactCanonical _ _ _ _ v.wf.assetsAvailable_norm hAA0 hcash hcm
  have hct : cash.mNumericType = v.numericType := STAmount.ofNumber_mNumericType _ _ _ _ hcash
  have hnear : |an.toRat - cash.toRat| < (1 / 2 : ℚ) * (10 : ℚ) ^ (cash.exponent - 1) := by
    rw [hcv]
    refine lt_of_le_of_lt hb2 ?_
    have hu : (1 / 2 : ℚ) * (10 : ℚ) ^ (cash.exponent - 1) = (10 : ℚ) ^ cash.exponent / 20 := by
      rw [zpow_sub₀ (by norm_num : (10 : ℚ) ≠ 0)]; ring
    rw [hu]
    rcases hcE with hiou | ⟨hic, -⟩
    · -- an IOU cash is below `10 ^ (exponent + 16)`
      obtain ⟨-, hhi⟩ := STAmount.IOUCanonical.toRat_bounds cash hiou (by rw [hcv]; exact hAApos)
      rw [hcv] at hhi
      have h16 : (10 : ℚ) ^ (cash.exponent + 16) = 10 ^ cash.exponent * 10 ^ 16 := by
        rw [zpow_add₀ (by norm_num)]; norm_num
      have hp : (0 : ℚ) < 10 ^ cash.exponent := zpow_pos (by norm_num) _
      nlinarith
    · -- an integral cash is a whole amount in the Open zone, below `9·10¹⁵`
      have hoff : cash.exponent = 0 := hic.offset_zero
      have hint : v.numericType.isIntegral = true := by rw [← hct]; exact hic.is_integral
      have hb0 := v.baseExponent_bounds.2.2 hint
      have hopen := (Vault.Reachable.openZone_proof v t0 hr hmax).assetsAvailable_le_openLimit
      rw [hb0] at hopen
      rw [hoff, zpow_zero]
      norm_num at hopen ⊢
      nlinarith
  -- the conversion does not round the price to zero
  have hpz : assets.mValue ≠ 0 := by
    intro h0
    by_cases hint : v.numericType.isIntegral = true
    · have hhalf := STAmount.ofNumber_integral_within_half _ an assets hint hann
        (Number.negative_false_of_pos an hanpos) hof
      rw [(STAmount.toRat_eq_zero_iff _).mpr h0, zero_sub, abs_neg, abs_of_pos hanpos] at hhalf
      have hb0 := v.baseExponent_bounds.2.2 hint
      rw [hb0, zpow_zero] at hbk
      linarith
    · have hvfr := NumericType.eq_fractional_of_not_integral (by simpa using hint)
      have hge : (10 : ℚ) ^ (-81 : ℤ) ≤ an.toRat := by
        have h1 : (10 : ℚ) ^ (-81 : ℤ) ≤ 10 ^ (-10 : ℤ) / 2 := by norm_num
        calc (10 : ℚ) ^ (-81 : ℤ) ≤ 10 ^ (-10 : ℤ) / 2 := h1
          _ ≤ v.assetsAvailable.toRat / 2 := div_le_div_of_nonneg_right hAA10 (by norm_num)
          _ ≤ an.toRat := by linarith
      exact STAmount.ofNumber_frac_ne_zero_of_ge an .to_nearest assets hann hge (hvfr ▸ hof) h0
  have heq := STAmount.ofNumber_to_nearest_eq_of_near_canonical _ an assets cash hann hanpos.le hcE hct
    (by rw [hcv]; exact hAApos) hnear hof hpz
  rw [heq, hcv]

/-- On a reachable vault a clawback of every share recovers all the cash: all the shares together are
worth the cash, which sits on the base grid the clamp floors onto. -/
lemma Vault.Reachable.computeClawback_final (v : Vault) (t0 : UInt32) (hr : Vault.Reachable v t0)
    (hmax : v.numericType.isIntegral = true → v.numericType.maxValue.toNat ≤ maxRep.toNat)
    (assets holderShares : STAmount) (waive : Bool) (hc : assets.CanonicalOrZero) (hnn : 0 ≤ assets.toRat)
    (hhs : holderShares.ShareBalance) (amounts : VaultAmounts)
    (hcomp : (computeClawback v assets holderShares waive).run = .ok (.ok amounts))
    (hall : amounts.shares.toRat = v.toExact.sharesTotal) :
    amounts.assets.toRat = v.assetsAvailable.toRat := by
  obtain ⟨rec, _, hpr, -, -, hrec⟩ := computeClawback_success_reduces v _ _ waive _ hcomp
  obtain ⟨hsic, hs64, -, hrc, hr0, hrle⟩ := hpr.form hc hnn hhs hmax
  obtain ⟨hs2a, -, -⟩ := hpr.recovered hmax
  have hsc : amounts.shares.Canonical := hsic.canonical (by rw [hs64]; decide)
  have hrv := Vault.Reachable.sharesToAssetsWithdraw_all v t0 hr hmax _ _ waive hsc hall hs2a
  rcases hrec with ⟨-, heq⟩ | ⟨-, hcl, hfnp⟩
  · rw [heq]; exact hrv
  have hpt := (Vault.sharesToAssetsWithdraw_form v _ _ waive hmax hs2a).2
  by_cases hint : v.numericType.isIntegral = true
  · -- an integral clamp keeps the worth
    have hni : rec.operator_neg.integral = true := by
      unfold STAmount.integral
      rw [(STAmount.operator_neg_fields rec).1, hpt]
      exact hint
    rw [clampToSumExponent_integral _ _ _ hni, Except.ok.injEq] at hcl
    obtain ⟨-, -, -, hrat⟩ := clamp_magnitude rec.operator_neg
    rw [hcl, STAmount.operator_neg_toRat, abs_neg, abs_of_nonneg hr0] at hrat
    rw [hrat, hrv]
  -- a fractional clamp floors the cash onto the base grid, where it already sits
  have hvfr := NumericType.eq_fractional_of_not_integral (by simpa using hint)
  have hat : amounts.assets.mNumericType = .fractional := by
    have h := (clampToSumExponent_canonicalOrZero _ _ _ _ hrc.operator_neg
      v.baseExponent_range.1 v.baseExponent_range.2 hcl).2.1
    rw [h, (STAmount.operator_neg_fields rec).1, hpt, hvfr]
  have hrm : amounts.assets.mValue ≠ 0 := fun h0 => by
    rw [STAmount.isFractionalNonPositive_zero _ hat h0] at hfnp
    exact absurd (Except.ok.inj hfnp) (by decide)
  have hfl := Vault.Reachable.clamp_base v t0 hr hmax rec amounts.assets hrc (by rw [hpt, hvfr]) hr0 hrle hrm hcl
  obtain ⟨k, -, hkv⟩ := (Vault.Reachable.openZone_proof v t0 hr hmax).cash
  have hbp : (0 : ℚ) < 10 ^ v.baseExponent := zpow_pos (by norm_num) _
  rw [hfl, hrv, hkv, mul_div_cancel_right₀ _ hbp.ne', Int.floor_natCast]
  push_cast
  ring

/-- Proof of the final clawback line of `Vault.clawback_exits`. -/
lemma Vault.clawback_final_proof (v : Vault) (assets holderShares : STAmount) (waive : Bool) (t0 : UInt32)
    (hnn : 0 ≤ assets.toRat) (hr : Vault.Reachable v t0) (hc : assets.CanonicalOrZero)
    (hhs : holderShares.ShareBalance)
    (hmax : v.numericType.isIntegral = true → v.numericType.maxValue.toNat ≤ maxRep.toNat)
    (r : VaultWithAmounts) (hok : (v.clawback assets holderShares waive hnn).run = .ok (.ok r))
    (hfinal : r.shares.toRat = v.toExact.sharesTotal) :
    r.assets.toRat = v.assetsAvailable.toRat ∧ r.vault'.assetsAvailable = Number.zero ∧
      r.vault'.sharesTotal = Number.zero := by
  obtain ⟨amounts, raw, hcomp, hadj, hraw, hras, hrsh⟩ :=
    Vault.clawback_ok_reduces v assets holderShares waive hnn r hok
  obtain ⟨hic, h64, -, hac, -⟩ := computeClawback_amounts_form v _ _ waive _ hc hnn hhs hmax hcomp
  rw [hrsh] at hfinal
  have hpay :=
    Vault.Reachable.computeClawback_final v t0 hr hmax assets holderShares waive hc hnn hhs _ hcomp hfinal
  obtain ⟨hAA, hST⟩ := Vault.adjustAssetsAndShares_burn_all v _ _ raw hac hpay hic h64 hfinal hadj
  refine ⟨by rw [hras]; exact hpay, ?_, ?_⟩
  · rw [show r.vault'.assetsAvailable = raw.assetsAvailable from congrArg RawVault.assetsAvailable hraw]
    exact hAA
  · rw [show r.vault'.sharesTotal = raw.sharesTotal from congrArg RawVault.sharesTotal hraw]
    exact hST

end XRPL.Model.SingleAssetVault
