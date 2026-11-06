import XRPL.Properties.Vault.Proofs.ClawbackRecovery
import XRPL.Properties.Vault.Proofs.WithdrawTight.Shares
import XRPL.Properties.Protocol.Number.Mul.RoundsToRepresentable
import XRPL.Properties.Protocol.Number.Div.RoundsToRepresentable
import XRPL.Properties.Protocol.Number.Common.NumberBridge
import XRPL.Properties.Vault.Proofs.Reachable
import XRPL.Properties.Vault.Proofs.ShareWorth
import XRPL.Properties.Vault.Proofs.PricedWorth

/-! # Clawback shares and recovery against their ideals

On a reachable vault the capped recovery is the whole cash, whose ideal share count is the whole share total. A
recovery never exceeds a worth of whole base units, and falls short of the worth by less than one base unit. -/

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol

open private Vault.clawback_capped_shares Vault.Reachable.clawback_zero_recovery Vault.ClawbackPriced.shares_of_nonzero
  from XRPL.Properties.Vault.Proofs.ClawbackRecovery

/-- Proof of `Vault.clawback_assetsRecovered`. -/
lemma Vault.clawback_assetsRecovered_intended_proof (v : Vault) (assets holderShares : STAmount) (waive : Bool)
    (t0 : UInt32) (hr : Vault.Reachable v t0) (hc : assets.Canonical) (hznz : assets.isZero = false)
    (hnn : 0 ≤ assets.toRat)
    (hmax : v.numericType.isIntegral = true → v.numericType.maxValue.toNat ≤ maxRep.toNat)
    (r : VaultWithAmounts) (hok : (v.clawback assets holderShares waive hnn).run = .ok (.ok r)) :
    r.assets.toRat ≤ v.toExact.assetsAvailable ∧ 0 ≤ r.assets.toRat ∧
    ((∃ k : ℤ, v.idealAssetsClawback waive r.shares.toRat = k * 10 ^ v.baseExponent) →
      r.assets.toRat ≤ v.idealAssetsClawback waive r.shares.toRat) ∧
    v.idealAssetsClawback waive r.shares.toRat - r.assets.toRat < (10 : ℚ) ^ v.baseExponent ∧
    (r.assets.isZero = true → v.numericType.isIntegral = true ∧
      v.idealAssetsClawback waive r.shares.toRat * (1 - sharesε) ≤ 1 / 2) := by
  obtain ⟨hcash, hr0, -, hlo, hzero⟩ :=
    Vault.clawback_assetsRecovered_proof v assets holderShares waive t0 hr hc hznz hnn hmax r hok
  obtain ⟨rec, hcp, -, -⟩ := Vault.clawback_recovery_cases v assets holderShares waive hnn r hok
  obtain ⟨hsic, hs64, hs0⟩ := Vault.ClawbackPriced.shares_of_nonzero hmax hc hznz hnn hcp
  have hsc : r.shares.Canonical := hsic.canonical (by rw [hs64]; decide)
  obtain ⟨priced, hpr, hpcz, hp0, hple, -, hrle, -, -, hfrac, hintg⟩ :=
    Vault.clawback_recovery_le v assets holderShares waive hnn hmax r hok (Or.inl hsc) hs0
  set I := v.idealAssetsClawback waive r.shares.toRat with hIdef
  have hb : (0 : ℚ) < 10 ^ v.baseExponent := zpow_pos (by norm_num) _
  have hε : (0 : ℚ) ≤ sharesε := by unfold sharesε; norm_num
  have hz := Vault.Reachable.openZone_proof v t0 hr hmax
  have hlim := hz.assetsAvailable_le_openLimit
  have h9 : (9 : ℚ) * 10 ^ (15 + v.baseExponent) = 9 * 10 ^ 15 * 10 ^ v.baseExponent := by
    rw [zpow_add₀ (by norm_num)]; norm_num; ring
  refine ⟨hcash, hr0, fun hworth => ?_, ?_, hzero⟩
  · -- the recovery is at most the price, which is at most the worth
    exact le_trans hrle (hz.priced_le_worth hmax r.shares priced waive hs0 hsc hpr hple hworth)
  by_cases hzr : r.assets.isZero = true
  · -- nothing is recovered: an integral vault whose shares are worth at most half a unit
    obtain ⟨hint, hhalf⟩ := hzero hzr
    have hb0 : v.baseExponent = 0 := v.baseExponent_bounds.2.2 hint
    have h0 : r.assets.toRat = 0 := (STAmount.toRat_eq_zero_iff _).mpr (by simpa [STAmount.isZero] using hzr)
    rw [h0, hb0, zpow_zero, sub_zero]
    unfold sharesε at hhalf
    linarith
  -- one unit of the recovery's last digit, no coarser than the base grid, and the relative error below half of it
  have hrnz : r.assets.mValue ≠ 0 := by simpa [STAmount.isZero] using hzr
  have hrpos : 0 < r.assets.toRat := lt_of_le_of_ne hr0 (Ne.symm (STAmount.toRat_ne_zero _ hrnz))
  have hrv : r.assets.toRat = (r.assets.mValue.toNat : ℚ) * 10 ^ r.assets.exponent :=
    STAmount.toRat_of_nonneg _ (STAmount.mIsNegative_false_of_pos _ hrpos)
  have hu : (0 : ℚ) < 10 ^ r.assets.exponent := zpow_pos (by norm_num) _
  have hpnz : priced.isZero = false := by
    by_contra h
    have : priced.toRat = 0 := (STAmount.toRat_eq_zero_iff _).mpr (by simpa [STAmount.isZero] using h)
    linarith
  have key : (10 : ℚ) ^ r.assets.exponent ≤ 10 ^ v.baseExponent ∧
      I * sharesε < 1 / 2 * (10 : ℚ) ^ r.assets.exponent := by
    by_cases hint : v.numericType.isIntegral = true
    · obtain ⟨hval, hexp⟩ := hintg hpnz hint
      have hb0 : v.baseExponent = 0 := v.baseExponent_bounds.2.2 hint
      have hpt := (Vault.sharesToAssetsWithdraw_form v r.shares priced waive hmax hpr).2
      have hpm : priced.mValue ≠ 0 := by simpa [STAmount.isZero] using hpnz
      have hpcan : priced.Canonical := hpcz.resolve_right (by simpa [STAmount.isZero] using hpm)
      have hic : priced.IntegralCanonical := (hpcan.1 (by unfold STAmount.integral; rw [hpt]; exact hint)).1
      have he : r.assets.exponent = 0 := by rw [hexp]; exact hic.offset_zero
      rw [he, hb0, zpow_zero]
      refine ⟨le_rfl, ?_⟩
      rw [he, hb0] at hlo
      norm_num at hlo
      rw [hb0] at hlim h9
      have hI1 : I * (1 - sharesε) ≤ 9 * 10 ^ 15 + 1 / 2 := by
        have : r.assets.toRat ≤ 9 * 10 ^ 15 := by
          have := hcash; simp only [RawVault.toExact] at this; norm_num at hlim h9; linarith
        nlinarith
      unfold sharesε at *
      nlinarith
    obtain ⟨hRc, -, -, hcl⟩ := hfrac hpnz (by simpa using hint)
    have hmlo : (10 ^ 15 : ℚ) ≤ r.assets.mValue.toNat := by exact_mod_cast hRc.mant_lo
    have hmhi : (r.assets.mValue.toNat : ℚ) < 10 ^ 16 := by exact_mod_cast hRc.mant_hi
    have hbig : 10 ^ 15 * (10 : ℚ) ^ r.assets.exponent ≤ r.assets.toRat := by
      rw [hrv]; exact mul_le_mul_of_nonneg_right hmlo hu.le
    have hsmall : r.assets.toRat < 10 ^ 16 * (10 : ℚ) ^ r.assets.exponent := by
      rw [hrv]; exact mul_lt_mul_of_pos_right hmhi hu
    have hcashq : r.assets.toRat ≤ 9 * 10 ^ 15 * 10 ^ v.baseExponent := by
      have := hcash; simp only [RawVault.toExact] at this; linarith
    have heb : r.assets.exponent ≤ v.baseExponent := by
      by_contra h
      push Not at h
      have h1 : (10 : ℚ) ^ (v.baseExponent + 1) ≤ 10 ^ r.assets.exponent :=
        zpow_le_zpow_right₀ (by norm_num) (by omega)
      have h2 : (10 : ℚ) ^ (v.baseExponent + 1) = 10 * 10 ^ v.baseExponent := by
        rw [zpow_add_one₀ (by norm_num)]; ring
      nlinarith
    have hue : (10 : ℚ) ^ r.assets.exponent ≤ 10 ^ v.baseExponent := zpow_le_zpow_right₀ (by norm_num) heb
    -- a positive recovery floored onto the base grid is at least one base unit
    have hfl := Vault.Reachable.clamp_base v t0 hr hmax priced r.assets hpcz
      (by have := (Vault.sharesToAssetsWithdraw_form v r.shares priced waive hmax hpr).2
          rw [this]; exact NumericType.eq_fractional_of_not_integral (by simpa using hint)) hp0 hple hrnz hcl
    have hge : 10 ^ v.baseExponent ≤ r.assets.toRat := by
      have hq : (0 : ℚ) < ⌊priced.toRat / 10 ^ v.baseExponent⌋ := by
        by_contra h
        push Not at h
        rw [hfl] at hrpos
        nlinarith
      have hq1 : (1 : ℚ) ≤ ⌊priced.toRat / 10 ^ v.baseExponent⌋ := by
        have : (0 : ℤ) < ⌊priced.toRat / 10 ^ v.baseExponent⌋ := by exact_mod_cast hq
        exact_mod_cast this
      rw [hfl]; nlinarith
    refine ⟨hue, ?_⟩
    have hm : max (1 / 2 * (10 : ℚ) ^ r.assets.exponent) ((10 : ℚ) ^ v.baseExponent - 1 / 2 * 10 ^ r.assets.exponent)
        ≤ 10 ^ v.baseExponent := max_le (by linarith) (by linarith)
    have hI2 : I * (1 - sharesε) ≤ 2 * r.assets.toRat := by nlinarith
    unfold sharesε at *
    nlinarith
  obtain ⟨hue, hrel⟩ := key
  rcases le_total (1 / 2 * (10 : ℚ) ^ r.assets.exponent)
      ((10 : ℚ) ^ v.baseExponent - 1 / 2 * 10 ^ r.assets.exponent) with h | h
  · rw [max_eq_right h] at hlo; linarith
  · rw [max_eq_left h] at hlo; linarith

/-- Proof of the valid-vault line of `Vault.clawback_assetsRecovered`. -/
lemma Vault.clawback_assetsRecovered_intended_total_proof (v : Vault) (assets holderShares : STAmount)
    (waive : Bool) (nav : Number) (hnav : v.assetsTotalForWithdrawal waive = .ok nav)
    (hc : assets.CanonicalOrZero) (hhs : holderShares.ShareBalance) (hnn : 0 ≤ assets.toRat)
    (hmax : v.numericType.isIntegral = true → v.numericType.maxValue.toNat ≤ maxRep.toNat)
    (r : VaultWithAmounts) (hok : (v.clawback assets holderShares waive hnn).run = .ok (.ok r)) :
    r.assets.toRat ≤ v.toExact.assetsAvailable ∧ 0 ≤ r.assets.toRat ∧
    ((∃ k : ℤ, v.idealAssetsWithdrawAt nav.toRat r.shares.toRat = k * 10 ^ v.baseExponent) →
      v.idealAssetsWithdrawAt nav.toRat r.shares.toRat ≤ 9 * 10 ^ 15 * (10 : ℚ) ^ v.baseExponent →
      r.assets.toRat ≤ v.idealAssetsWithdrawAt nav.toRat r.shares.toRat) := by
  obtain ⟨rec, hcp, -, -⟩ := Vault.clawback_recovery_cases v assets holderShares waive hnn r hok
  obtain ⟨hsic, hs64, hs0, -⟩ := hcp.form hc hnn hhs hmax
  have hsc : r.shares.Canonical := hsic.canonical (by rw [hs64]; decide)
  obtain ⟨priced, hpr, -, -, hple, hr0, hrle, -⟩ :=
    Vault.clawback_recovery_le v assets holderShares waive hnn hmax r hok (Or.inl hsc) hs0
  exact ⟨le_trans hrle hple, hr0, fun hworth hsmall =>
    le_trans hrle (Vault.priced_le_worth_total v hmax r.shares priced waive nav hnav hs0 hsc hpr hsmall hworth)⟩

end XRPL.Model.SingleAssetVault
