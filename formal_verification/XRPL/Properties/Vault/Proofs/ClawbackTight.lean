import XRPL.Properties.Vault.Proofs.ClawbackTight.Reduce
import XRPL.Properties.Vault.Proofs.ClawbackTight.Shares
import XRPL.Properties.Vault.Proofs.ClawbackTight.Assets
import XRPL.Properties.Vault.Proofs.ClawbackTight.Lower

/-! # `Vault.clawback` accuracy, tight forms

Proof bodies of `clawback_sharesDestroyed`, `clawback_sharesDestroyed_clamped`,
`clawback_zero_all_shares` and `clawback_assetsRecovered`. -/

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol

lemma Vault.clawback_sharesDestroyed_proof (v : Vault)
    (assets holderShares sharesDestroyed assetsRecovered : STAmount)
    (assetsRecoveredNumber : Number) (r : ClawbackResult)
    (hnav : v.WithdrawNavExact false)
    (hc : assets.Canonical)
    (hshares : assetsToSharesWithdraw v assets true false = .ok sharesDestroyed)
    (hassets : v.sharesToAssetsWithdraw sharesDestroyed false = .ok assetsRecovered)
    (hnum : assetsRecovered.toNumber .to_nearest = .ok assetsRecoveredNumber)
    (hle : assetsRecoveredNumber.operator_gt v.assetsAvailable = false)
    (hznz : assets.isZero = false)
    (hnn : 0 ≤ assets.toRat)
    (hok : v.clawback assets holderShares hnn = .ok r) (herr : r.error = none) :
    r.sharesDestroyed.toRat.den = 1 ∧ 0 ≤ r.sharesDestroyed.toRat ∧
    v.idealSharesClawback assets.toRat * (1 - sharesε) - 1 < r.sharesDestroyed.toRat ∧
    r.sharesDestroyed.toRat ≤ v.idealSharesClawback assets.toRat * (1 + sharesε) := by
  obtain ⟨cr, hcomp, hcerr, hcnz, -, hsd⟩ := ClwTight.clawback_cr v assets holderShares r hnn hok herr
  obtain ⟨X, priced, arn, hX, -, -, -, -, -, hbr⟩ :=
    ClwTight.computeClawback_cases v assets holderShares cr hznz hcomp hcerr
  rcases hbr with rfl | ⟨sd0, p0, n0, h1, h2, h3, h4, -⟩
  · rw [hsd]
    exact ClwTight.shares_core v hnav X cr.sharesDestroyed (ClwTight.numExact_of_canonical X hc) hnn
      hX (by simpa [STAmount.isZero] using hcnz)
  · obtain rfl := Except.ok.inj (hshares.symm.trans h1)
    obtain rfl := Except.ok.inj (hassets.symm.trans h2)
    obtain rfl := Except.ok.inj (hnum.symm.trans h3)
    rw [hle] at h4; exact absurd h4 (by decide)

lemma Vault.clawback_sharesDestroyed_clamped_proof (v : Vault)
    (assets holderShares sharesDestroyed assetsRecovered assetsRecovered' : STAmount)
    (assetsRecoveredNumber : Number) (r : ClawbackResult)
    (hnav : v.WithdrawNavExact false)
    (hshares : assetsToSharesWithdraw v assets true false = .ok sharesDestroyed)
    (hassets : v.sharesToAssetsWithdraw sharesDestroyed false = .ok assetsRecovered)
    (hnum : assetsRecovered.toNumber .to_nearest = .ok assetsRecoveredNumber)
    (hgt : assetsRecoveredNumber.operator_gt v.assetsAvailable = true)
    (hclamped : STAmount.ofNumber v.numericType v.assetsAvailable .to_nearest =
      .ok assetsRecovered')
    (hznz : assets.isZero = false)
    (hnn : 0 ≤ assets.toRat)
    (hok : v.clawback assets holderShares hnn = .ok r) (herr : r.error = none) :
    r.sharesDestroyed.toRat.den = 1 ∧ 0 ≤ r.sharesDestroyed.toRat ∧
    v.idealSharesClawback assetsRecovered'.toRat * (1 - depositε) - 1 <
      r.sharesDestroyed.toRat ∧
    r.sharesDestroyed.toRat ≤
      v.idealSharesClawback assetsRecovered'.toRat * (1 + depositε) := by
  obtain ⟨cr, hcomp, hcerr, hcnz, -, hsd⟩ := ClwTight.clawback_cr v assets holderShares r hnn hok herr
  obtain ⟨X, priced, arn, hX, hpr, harn, hle, -, -, hbr⟩ :=
    ClwTight.computeClawback_cases v assets holderShares cr hznz hcomp hcerr
  have hAn := v.wf.assetsAvailable_norm
  have hA0 := v.exact.assetsAvailable_nonneg
  rcases hbr with rfl | ⟨sd0, p0, n0, h1, h2, h3, h4, h5⟩
  · obtain rfl := Except.ok.inj (hshares.symm.trans hX)
    obtain rfl := Except.ok.inj (hassets.symm.trans hpr)
    obtain rfl := Except.ok.inj (hnum.symm.trans harn)
    rw [hle] at hgt; exact absurd hgt (by decide)
  · obtain rfl := Except.ok.inj (hclamped.symm.trans h5)
    rw [hsd]
    exact ClwTight.shares_core_weak v hnav _ cr.sharesDestroyed
      (ClwTight.numExact_of_ofNumber _ _ _ _ hclamped)
      (STAmount.ofNumber_nonneg _ _ _ _ hAn
        (Number.negative_false_of_nonneg _ hAn hA0) hclamped)
      hX (by simpa [STAmount.isZero] using hcnz)

lemma Vault.clawback_zero_all_shares_proof (v : Vault)
    (assets holderShares assetsRecovered reported : STAmount)
    (assetsRecoveredNumber : Number) (r : ClawbackResult)
    (hz : assets.isZero = true)
    (hassets : v.sharesToAssetsWithdraw holderShares false = .ok assetsRecovered)
    (hnum : assetsRecovered.toNumber .to_nearest = .ok assetsRecoveredNumber)
    (hle : assetsRecoveredNumber.operator_gt v.assetsAvailable = false)
    (hclamp : clampToSumExponent v.assetsTotal assetsRecovered.operator_neg = .ok reported)
    (hnn : 0 ≤ assets.toRat)
    (hok : v.clawback assets holderShares hnn = .ok r) (herr : r.error = none) :
    r.sharesDestroyed = holderShares ∧ r.assetsRecovered = reported ∧
    holderShares.isZero = false := by
  obtain ⟨cr, hcomp, hcerr, hcnz, hra, hsd⟩ := ClwTight.clawback_cr v assets holderShares r hnn hok herr
  obtain ⟨priced, arn, hpr, harn, hbr⟩ :=
    ClwTight.computeClawback_zero v assets holderShares cr hz hcomp hcerr
  obtain rfl := Except.ok.inj (hassets.symm.trans hpr)
  obtain rfl := Except.ok.inj (hnum.symm.trans harn)
  rcases hbr with h | ⟨h1, h2⟩
  · rw [hle] at h; exact absurd h (by decide)
  · refine ⟨hsd.trans h1, hra.trans (Except.ok.inj (h2.symm.trans hclamp)), ?_⟩
    rw [← h1]; exact hcnz

lemma Vault.clawback_assetsRecovered_proof (v : Vault) (assets holderShares : STAmount)
    (r : ClawbackResult)
    (hnav : v.WithdrawNavExact false)
    (hc : assets.Canonical)
    (hznz : assets.isZero = false)
    (hnn : 0 ≤ assets.toRat)
    (hok : v.clawback assets holderShares hnn = .ok r) (herr : r.error = none) :
    r.assetsRecovered.toRat ≤ v.toExact.assetsAvailable ∧
    0 ≤ r.assetsRecovered.toRat ∧
    r.assetsRecovered.toRat ≤
      v.idealAssetsClawback r.sharesDestroyed.toRat * (1 + depositε) +
        1 / 2 * (10 : ℚ) ^ r.assetsRecovered.exponent ∧
    (∃ atr' : STAmount,
      STAmount.ofNumber v.numericType r.vault'.assetsTotal .to_nearest = .ok atr' ∧
      v.idealAssetsClawback r.sharesDestroyed.toRat - r.assetsRecovered.toRat ≤
        v.idealAssetsClawback r.sharesDestroyed.toRat * depositε +
          max (1 / 2 * (10 : ℚ) ^ r.assetsRecovered.exponent)
            ((10 : ℚ) ^ atr'.exponent - 1 / 2 * (10 : ℚ) ^ r.assetsRecovered.exponent)) ∧
    (r.assetsRecovered.isZero = true →
      v.numericType.isIntegral = true ∧
        v.idealAssetsClawback r.sharesDestroyed.toRat * (1 - depositε) ≤ 1 / 2) := by
  obtain ⟨an', at', atr', han', hat, hatr', hvt⟩ :=
    ClwTight.clawback_total v assets holderShares r hnn hok herr
  obtain ⟨cr, hcomp, hcerr, hcnz, hra, hsd⟩ := ClwTight.clawback_cr v assets holderShares r hnn hok herr
  obtain ⟨X, priced, arn, hX, hpr, harn, hle, hcl, hfnp, hbr⟩ :=
    ClwTight.computeClawback_cases v assets holderShares cr hznz hcomp hcerr
  have hAn := v.wf.assetsAvailable_norm
  have hA0 := v.exact.assetsAvailable_nonneg
  have hTn := v.wf.assetsTotal_norm
  have hT0 := v.exact.assetsTotal_nonneg
  have hAle := v.exact.assetsAvailable_le
  have hd0 : cr.sharesDestroyed.mValue ≠ 0 := by simpa [STAmount.isZero] using hcnz
  have hsd0 : 0 ≤ cr.sharesDestroyed.toRat := by
    rcases hbr with rfl | ⟨-, -, -, -, -, -, -, h5⟩
    · exact (ClwTight.shares_core v hnav X _ (ClwTight.numExact_of_canonical X hc) hnn hX hd0).2.1
    · exact (ClwTight.shares_core v hnav X _ (ClwTight.numExact_of_ofNumber _ _ _ _ h5)
        (STAmount.ofNumber_nonneg _ _ _ _ hAn
          (Number.negative_false_of_nonneg _ hAn hA0) h5) hX hd0).2.1
  obtain ⟨hst, hsoff, hsval⟩ := ClwAcc.shares_shape v X _ hX
  have hsdE : ClwTight.NumExact cr.sharesDestroyed :=
    ClwTight.numExact_of_integral _ (by rw [hst]; rfl) hsoff hsval
  rw [hvt]
  rw [hra] at han'
  rw [hra, hsd]
  show cr.assetsRecovered.toRat ≤ v.assetsAvailable.toRat ∧ _
  have hε : (0 : ℚ) ≤ depositε ∧ depositε ≤ 1 / 2 := by unfold depositε; norm_num
  have hpc := ClwTight.price_core v hnav _ priced hsdE hsd0 hpr
  have hpE : ClwTight.NumExact priced := by
    rcases hpc with ⟨hz, -⟩ | ⟨an, hann, -, -, -, -, hof⟩
    · exact ClwTight.numExact_of_zero _ hz
    · exact ClwTight.numExact_of_ofNumber _ _ _ _ hof
  have hple : priced.toRat ≤ v.assetsAvailable.toRat := by
    obtain ⟨harnn, harnv⟩ := hpE arn harn
    rw [← harnv]
    by_contra hc'
    replace hc' := not_le.mp hc'
    rw [(operator_gt_iff _ _ harnn hAn).mpr hc'] at hle
    exact absurd hle (by decide)
  have hptype := ClwTight.price_type v _ priced hpr
  set sd := cr.sharesDestroyed
  set rec := cr.assetsRecovered
  have hI0 : 0 ≤ v.idealAssetsClawback sd.toRat := by
    unfold RawVault.idealAssetsClawback
    exact div_nonneg (mul_nonneg v.exact.withdraw_nav_nonneg hsd0) (Nat.cast_nonneg _)
  by_cases hint : v.numericType.isIntegral = true
  · obtain ⟨-, hoff', -⟩ := STAmount.ofNumber_integral_facts _ _ _ _ hint hatr'
    have hx' : atr'.exponent = 0 := hoff'
    have hmx : (1 / 2 : ℚ) ≤ max (1 / 2 * (10 : ℚ) ^ (0 : ℤ)) ((10 : ℚ) ^ (0 : ℤ) - 1 / 2 * 10 ^ (0 : ℤ)) := by
      rw [zpow_zero, mul_one]; exact le_max_left _ _
    rcases hpc with ⟨hz, hIs⟩ | ⟨an, hann, ham, hanneg, hIpos, hb, hof⟩
    · have hp0 : priced.toRat = 0 := (STAmount.toRat_eq_zero_iff _).mpr hz
      obtain ⟨hrp, hre, -, hrm⟩ := ClwTight.integral_clamp_eq v hint sd priced rec hpr hp0.ge hcl
      refine ⟨by linarith, by linarith, ?_, ⟨atr', hatr', ?_⟩, fun _ => ⟨hint, ?_⟩⟩
      · have : (0 : ℚ) ≤ 1 / 2 * 10 ^ rec.exponent := by positivity
        nlinarith
      · rw [hre, hx']
        have : 0 ≤ v.idealAssetsClawback sd.toRat * depositε := mul_nonneg hI0 hε.1
        linarith
      · nlinarith
    · have hp0 := STAmount.ofNumber_nonneg _ _ _ _ hann hanneg hof
      obtain ⟨hrp, hre, hpe, hrm⟩ := ClwTight.integral_clamp_eq v hint sd priced rec hpr hp0 hcl
      obtain ⟨hh, -, -⟩ := ClwTight.ofNumber_half v.numericType an priced hann ham hanneg hof
        (fun h => absurd hint (by rw [h]; decide))
      rw [hpe, zpow_zero, mul_one] at hh
      obtain ⟨hb1, hb2⟩ := abs_le.mp hb
      obtain ⟨hh1, hh2⟩ := abs_le.mp hh
      refine ⟨by linarith, by linarith, ?_, ⟨atr', hatr', ?_⟩, fun hz => ⟨hint, ?_⟩⟩
      · rw [hre, zpow_zero, mul_one]; nlinarith
      · rw [hre, hx']; nlinarith
      · have hm0 : priced.mValue = 0 := by rw [← hrm]; simpa [STAmount.isZero] using hz
        rw [(STAmount.toRat_eq_zero_iff _).mpr hm0] at hh
        obtain ⟨hh1', -⟩ := abs_le.mp hh
        nlinarith
  · have hfr := ClwTight.fractional_of_not_integral _ hint
    rcases hpc with ⟨hz, -⟩ | ⟨an, hann, ham, hanneg, hIpos, hb, hof⟩
    · exact absurd (ClwTight.frac_zero_contra v.assetsTotal hTn hT0 priced rec hz
        (by rw [hptype, hfr]) hcl hfnp) (fun h => h)
    have hpm : priced.mValue ≠ 0 := fun hz =>
      ClwTight.frac_zero_contra v.assetsTotal hTn hT0 priced rec hz (by rw [hptype, hfr]) hcl hfnp
    obtain ⟨hh, -, hcan⟩ := ClwTight.ofNumber_half v.numericType an priced hann ham hanneg hof
      (fun _ => hpm)
    have hpcan := hcan (by rw [hfr]; rfl)
    have hp0 := STAmount.ofNumber_nonneg _ _ _ _ hann hanneg hof
    have hppos : 0 < priced.toRat :=
      lt_of_le_of_ne hp0 (fun h => hpm ((STAmount.toRat_eq_zero_iff _).mp h.symm))
    have hrfc := WdAcc.clamp_frac_shape v.assetsTotal priced.operator_neg rec
      (STAmount.operator_neg_fczr priced ⟨hpcan.is_fractional, Or.inl hpcan⟩) hcl
    have hrint : rec.integral = false := by
      show rec.mNumericType.isIntegral = false; rw [hrfc.1]; rfl
    obtain ⟨hrm, hrn⟩ := STAmount.fnp_false_pos rec hrint hfnp
    obtain ⟨-, hRle, hcase⟩ := ClwTight.clamp_frac v.assetsTotal hTn priced rec hpcan hppos
      (hple.trans hAle) hcl hrm
    have hr0 : 0 ≤ rec.toRat := STAmount.nonneg_of_fnp rec hrint hfnp
    obtain ⟨hb1, hb2⟩ := abs_le.mp hb
    obtain ⟨hh1, hh2⟩ := abs_le.mp hh
    have hrz : rec.isZero = false := by simpa [STAmount.isZero] using hrm
    have hup : (0 : ℚ) ≤ 1 / 2 * 10 ^ rec.exponent := by positivity
    rw [hfr] at hatr'
    refine ⟨by linarith, hr0, ?_, ⟨atr', by rw [hfr]; exact hatr', ?_⟩,
      fun h => absurd h (by rw [hrz]; decide)⟩
    · rcases hcase with ⟨hRP, hRe⟩ | ⟨hl, -⟩
      · rw [hRe]; nlinarith
      · have : (0 : ℚ) < 10 ^ priced.exponent := zpow_pos (by norm_num) _
        nlinarith
    · rcases ClwTight.frac_clamp_gap v.assetsTotal hTn priced rec hpcan hppos (hple.trans hAle)
        hcl hrm an' at' atr' han' hat hatr' with ⟨hRP, hRe⟩ | ⟨hRe, hgap⟩
      · refine le_trans ?_ (add_le_add le_rfl (le_max_left _ _))
        rw [hRe]; nlinarith
      · refine le_trans ?_ (add_le_add le_rfl (le_max_right _ _))
        have : (10 : ℚ) ^ rec.exponent ≤ 10 ^ priced.exponent :=
          zpow_le_zpow_right₀ (by norm_num) hRe
        nlinarith

end XRPL.Model.SingleAssetVault
