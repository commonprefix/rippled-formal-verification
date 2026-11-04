import XRPL.Properties.Vault.Proofs.ClawbackRecovery
import XRPL.Properties.Vault.Proofs.ShareExact
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

/-- Proof of `Vault.clawback_sharesDestroyed_clamped`. -/
lemma Vault.clawback_sharesDestroyed_clamped_floor_proof (v : Vault)
    (assets holderShares sharesDestroyed assetsRecovered assetsRecovered' : STAmount) (waive : Bool)
    (assetsRecoveredNumber : Number) (t0 : UInt32) (hr : Vault.Reachable v t0)
    (hmax : v.numericType.isIntegral = true → v.numericType.maxValue.toNat ≤ maxRep.toNat)
    (hshares : assetsToSharesWithdraw v assets true waive = .ok sharesDestroyed)
    (hassets : v.sharesToAssetsWithdraw sharesDestroyed waive = .ok assetsRecovered)
    (hnum : assetsRecovered.toNumber .to_nearest = .ok assetsRecoveredNumber)
    (hgt : assetsRecoveredNumber.operator_gt v.assetsAvailable = true)
    (hclamped : STAmount.ofNumber v.numericType v.assetsAvailable .to_nearest = .ok assetsRecovered')
    (hznz : assets.isZero = false) (hnn : 0 ≤ assets.toRat) (r : VaultWithAmounts)
    (hok : (v.clawback assets holderShares waive hnn).run = .ok (.ok r)) :
    r.shares.toRat.den = 1 ∧ 0 ≤ r.shares.toRat ∧
    ((∃ p : Number, p.isNormalized ∧ p.toRat = v.sharesTotal.toRat * assetsRecovered'.toRat) →
      v.idealSharesClawback waive assetsRecovered'.toRat - 1 < r.shares.toRat) ∧
    r.shares.toRat ≤ v.idealSharesClawback waive assetsRecovered'.toRat := by
  obtain ⟨hden, h0, -, hup⟩ := Vault.clawback_sharesDestroyed_clamped_proof v assets holderShares sharesDestroyed
    assetsRecovered assetsRecovered' waive assetsRecoveredNumber t0 hr hmax hshares hassets hnum hgt hclamped
    hznz hnn r hok
  have hz := Vault.Reachable.openZone_proof v t0 hr hmax
  have hcash : assetsRecovered'.toRat = v.assetsAvailable.toRat :=
    Vault.final_payout_exact v assetsRecovered' hz.cashExact hmax hclamped
  set A := v.assetsAvailable.toRat with hA
  set S : ℚ := (v.toExact.sharesTotal : ℚ) with hS
  -- the ideal for the cash is the share total
  have hideal : v.idealSharesClawback waive assetsRecovered'.toRat = S * A / A := by
    unfold RawVault.idealSharesClawback RawVault.idealSharesWithdraw
    rw [hcash]
    cases waive <;> simp [hz.withdrawNav_eq, hz.depositNav_eq, ← hA, ← hS]
  -- the share total stays below `9·10^15`, so the relative pricing error is below one share
  have hS1 : S * sharesε < 1 := by
    have hle := Vault.Reachable.sharesTotal_le_cash_proof v t0 hr
    have hlim := hz.assetsAvailable_le_openLimit
    have hb : (0 : ℚ) < 10 ^ v.baseExponent := zpow_pos (by norm_num) _
    have h9 : (9 : ℚ) * 10 ^ (15 + v.baseExponent) = 9 * 10 ^ 15 * 10 ^ v.baseExponent := by
      rw [zpow_add₀ (by norm_num)]; norm_num; ring
    have hS9 : S ≤ 9 * 10 ^ 15 := by
      have : S * 10 ^ v.baseExponent ≤ 9 * 10 ^ 15 * 10 ^ v.baseExponent := by rw [← h9]; linarith
      exact le_of_mul_le_mul_right this hb
    unfold sharesε
    nlinarith
  have hkn : r.shares.toRat = (r.shares.toRat.num : ℚ) := (Rat.coe_int_num_of_den_eq_one hden).symm
  refine ⟨hden, h0, fun hprod => ?_, ?_⟩
  · -- the exact product gives the floor of the ideal at the computed net asset value
    obtain ⟨ha2s, hsnz⟩ := Vault.clawback_capped_shares v assets holderShares sharesDestroyed assetsRecovered
      assetsRecovered' waive assetsRecoveredNumber hshares hassets hnum hgt hclamped hznz hnn r hok
    obtain ⟨nav, hnavN⟩ : ∃ nav, v.assetsTotalForWithdrawal waive = .ok nav :=
      ⟨_, Vault.assetsTotalForWithdrawal_of_noLending v hz.assetsDeployed waive⟩
    have hnavv : nav.toRat = A := Vault.Reachable.nav_eq_cash v t0 hr waive nav hnavN
    have hcc := (STAmount.ofNumber_canonicalOrZero _ _ _ _ hmax hclamped).1
    have hc0 : assetsRecovered'.toRat ≠ 0 :=
      assetsToSharesWithdraw_amount_ne_zero v assetsRecovered' r.shares waive hcc ha2s hsnz
    have hA0 : A ≠ 0 := by rw [← hcash]; exact hc0
    have hApos : 0 < assetsRecovered'.toRat := lt_of_le_of_ne (by rw [hcash]; exact v.exact.assetsAvailable_nonneg)
      (Ne.symm hc0)
    have hcan : assetsRecovered'.Canonical := hcc.resolve_right (fun hzr => hc0 ((STAmount.toRat_eq_zero_iff _).mpr
      (by simpa [STAmount.isZero] using hzr)))
    have hquot : ∃ q : Number, q.isNormalized ∧
        q.toRat = v.sharesTotal.toRat * assetsRecovered'.toRat / nav.toRat :=
      ⟨v.sharesTotal, v.wf.sharesTotal_norm, by rw [hnavv, hcash]; field_simp⟩
    have hfl := WdTight.shares_exact v assetsRecovered' r.shares waive nav hnavN hApos hcan ha2s hsnz hprod hquot
    have hat : v.idealSharesWithdrawAt nav.toRat assetsRecovered'.toRat =
        v.idealSharesClawback waive assetsRecovered'.toRat := by
      rw [hideal]
      unfold RawVault.idealSharesWithdrawAt
      rw [hnavv, hcash]
    rw [hfl, hat]
    exact Int.sub_one_lt_floor _
  · -- the count is whole and less than one share above the whole share total
    rw [hideal] at hup ⊢
    by_cases hA0 : A = 0
    · rw [hA0, div_zero, zero_mul] at hup
      rw [hA0, div_zero]
      exact hup
    rw [mul_div_assoc, div_self hA0, mul_one] at hup ⊢
    have hSnn : (0 : ℚ) ≤ S := Nat.cast_nonneg _
    have hε0 : (0 : ℚ) ≤ sharesε := by unfold sharesε; norm_num
    have hlt : r.shares.toRat < S + 1 := by nlinarith
    rw [hkn] at hlt ⊢
    have hSn : S = ((v.toExact.sharesTotal : ℤ) : ℚ) := by rw [hS]; push_cast; ring
    rw [hSn] at hlt ⊢
    have : r.shares.toRat.num < (v.toExact.sharesTotal : ℤ) + 1 := by exact_mod_cast hlt
    exact_mod_cast (show r.shares.toRat.num ≤ (v.toExact.sharesTotal : ℤ) by omega)

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

/-- Proof of `Vault.clawback_assetsRecovered_integral`. An integral recovery is the destroyed shares' price, which an
exact 19-digit price rounds once to nearest. -/
lemma Vault.clawback_assetsRecovered_integral_proof (v : Vault) (assets holderShares : STAmount) (waive : Bool)
    (t0 : UInt32) (hr : Vault.Reachable v t0) (hint : v.numericType.isIntegral = true)
    (hznz : assets.isZero = false) (hc : assets.Canonical) (hnn : 0 ≤ assets.toRat)
    (r : VaultWithAmounts) (hok : (v.clawback assets holderShares waive hnn).run = .ok (.ok r))
    (hexact : (∃ q : Number, q.isNormalized ∧
        q.toRat = v.idealAssetsClawback waive r.shares.toRat * (v.toExact.sharesTotal : ℚ)) ∧
      ∃ q : Number, q.isNormalized ∧ q.toRat = v.idealAssetsClawback waive r.shares.toRat) :
    v.idealAssetsClawback waive r.shares.toRat - r.assets.toRat ≤ 1 / 2 := by
  have hmax := Vault.Reachable.maxValue_fits v t0 hr
    (Vault.Reachable.clawback_sharesTotal_pos_of_nonzero v t0 hr assets holderShares waive hznz hnn r hok)
  obtain ⟨rec, hcp, -, -⟩ := Vault.clawback_recovery_cases v assets holderShares waive hnn r hok
  obtain ⟨hsic, hs64, hs0⟩ := Vault.ClawbackPriced.shares_of_nonzero hmax hc hznz hnn hcp
  have hsc : r.shares.Canonical := hsic.canonical (by rw [hs64]; decide)
  obtain ⟨priced, hpr, -, hp0, -, hr0, hrle, -, -, -, hintg⟩ :=
    Vault.clawback_recovery_le v assets holderShares waive hnn hmax r hok (Or.inl hsc) hs0
  -- an integral recovery is the price itself, a zero price included
  have hrp : r.assets.toRat = priced.toRat := by
    by_cases hpz : priced.isZero = false
    · exact (hintg hpz hint).1
    · have : priced.toRat = 0 := (STAmount.toRat_eq_zero_iff _).mpr (by simpa [STAmount.isZero] using hpz)
      linarith
  -- the computed net asset value is the cash, and the worth at it is the exact worth
  have hnav := Vault.assetsTotalForWithdrawal_of_noLending v (Vault.Reachable.noLending_proof v t0 hr).1 waive
  have hI : v.idealAssetsWithdrawAt v.assetsAvailable.toRat r.shares.toRat =
      v.idealAssetsClawback waive r.shares.toRat := by
    rw [RawVault.idealAssetsClawback, Vault.Reachable.idealAssetsWithdraw_eq v t0 hr waive]; rfl
  rw [← hI] at hexact ⊢
  rw [hrp]
  linarith [(abs_le.mp (WdPrice.price_exact_integral v r.shares priced waive v.assetsAvailable hint hnav hs0 hsc
    hpr hexact)).1]

end XRPL.Model.SingleAssetVault
