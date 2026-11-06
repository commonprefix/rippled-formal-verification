import XRPL.Properties.Vault.Proofs.DepositCharge
import XRPL.Properties.Vault.Proofs.PricedWorth

/-! # A deposit charge against the issued shares' worth

The charge is the issued shares' worth priced to nearest, then floored onto the base grid for an IOU. When that
worth is a whole number of base units the to-nearest price lands on it, so an IOU charge stays at or below the worth
and an integral charge at or above it. -/

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault.DepTight

open private empty_charge_at frac_charge_floor from XRPL.Properties.Vault.Proofs.DepositTight.Charge

/-- A deposit charge against the worth `I` at the computed total, `I` below `9.9·10^15` base units: an IOU charge is
at most a whole worth, an integral one at least it, and an integral charge exceeds `I` by less than one unit. -/
lemma Vault.deposit_charge_worth (v : Vault) (amountDeposit : STAmount) (t : UInt32)
    (hcanon : amountDeposit.Canonical) (hpos : 0 < amountDeposit.toRat)
    (navN : Number) (hat : v.assetsTotal = .ok navN)
    (r : VaultWithAmounts) (hok : (v.deposit amountDeposit false t hpos).run = .ok (.ok r))
    (hsmall : v.idealChargeDepositAt navN.toRat r.shares.toRat ≤ 99 * 10 ^ 14 * (10 : ℚ) ^ v.baseExponent) :
    ((∃ k : ℤ, v.idealChargeDepositAt navN.toRat r.shares.toRat = k * 10 ^ v.baseExponent) →
      (v.numericType.isIntegral = false → r.assets.toRat ≤ v.idealChargeDepositAt navN.toRat r.shares.toRat) ∧
      (v.numericType.isIntegral = true → v.idealChargeDepositAt navN.toRat r.shares.toRat ≤ r.assets.toRat)) ∧
    (v.numericType.isIntegral = true → r.assets.toRat - v.idealChargeDepositAt navN.toRat r.shares.toRat < 1) := by
  obtain ⟨ra, priced, navN', hra, hrc, hrp, hats, hshz, hshc, hshnt, hshpos, hsad, -, hat', hcl, hfnp⟩ :=
    DepAcc.Vault.deposit_success_reduces v amountDeposit t hpos hcanon r hok
  rw [hat, Except.ok.injEq] at hat'
  subst hat'
  set I := v.idealChargeDepositAt navN.toRat r.shares.toRat with hIdef
  have hεnn : (0 : ℚ) ≤ sharesε := by unfold sharesε; norm_num
  have hb : (0 : ℚ) < 10 ^ v.baseExponent := zpow_pos (by norm_num) _
  have hpnn := sharesToAssetsDeposit_nonneg v r.shares priced hshc hshnt hshpos hsad
  have hpnt := sharesToAssetsDeposit_mNumericType v r.shares priced hsad
  have hcle := DepRnd.Vault.deposit_charge_le v r.shares priced r.assets navN hshc hshnt hshpos hsad hcl
  have hty := Vault.deposit_amount_numericType v amountDeposit t hpos hcanon r hok
  -- an integral charge is the priced amount, a whole number of units
  have hintc : v.numericType.isIntegral = true →
      r.assets = priced ∧ v.baseExponent = 0 ∧ r.assets.toRat = (r.assets.mValue.toNat : ℚ) := by
    intro hint
    have hcp : r.assets = priced :=
      clampToSumExponent_integral_nonneg navN priced r.assets v.baseExponent
        (by show priced.mNumericType.isIntegral = true; rw [hpnt]; exact hint) hpnn hcl
    have hic := (sharesToAssetsDeposit_integral_canonical v r.shares priced hint hsad).1
    have he : r.assets.exponent = 0 := by rw [hcp]; exact hic.offset_zero
    refine ⟨hcp, (Vault.baseExponent_bounds v).2.2 hint, ?_⟩
    by_cases hm : r.assets.mValue = 0
    · rw [(STAmount.toRat_eq_zero_iff _).mpr hm, hm]
      simp
    rw [STAmount.toRat_of_offset_zero _ he]
    unfold STAmount.signedDrops
    rw [STAmount.mIsNegative_false_of_nonneg _ (by rw [hcp]; exact hpnn) hm]
    simp
  by_cases hmz : navN.mantissa_ = 0
  · -- an empty vault prices the shares exactly
    have hIe : I = v.idealChargeDeposit r.shares.toRat := empty_charge_at v navN hat hmz _
    have hpI : priced.toRat = I := by
      rw [hIe]
      by_cases hint : v.numericType.isIntegral = true
      · exact (charge_empty_integral v r.shares priced hint hshc hshnt hshpos navN hat hmz hsad).1
      · obtain ⟨-, hra2, -⟩ := v.roundedDepositAmount_form amountDeposit ra hcanon hty hra
        exact empty_frac_charge_exact v ra r.shares priced (by simpa using hint) navN hat hmz hrc hrp
          (by rw [hra2]; exact NumericType.eq_fractional_of_not_integral (by simpa using hint)) hats hshz hsad
    refine ⟨fun _ => ⟨fun _ => by linarith, fun hint => ?_⟩, fun hint => ?_⟩
    · rw [(hintc hint).1, hpI]
    · rw [(hintc hint).1, hpI, sub_self]; norm_num
  obtain ⟨Q, hQc, hIpos, hQcases⟩ := charge_nonempty v r.shares priced hshc hshnt hshpos navN hat hmz hsad
  by_cases hint : v.numericType.isIntegral = true
  · obtain ⟨hcp, hb0, hcv⟩ := hintc hint
    rw [hb0, zpow_zero, mul_one] at hsmall
    -- the priced amount is within half a unit of a value within `sharesε` of the worth
    have hnear : |r.assets.toRat - I| ≤ 1 / 2 + I * sharesε := by
      rcases hQcases with ⟨-, hQn, hQneg, hQb⟩ | ⟨hQm, hIsmall⟩
      · have hh := abs_le.mp (STAmount.ofNumber_integral_within_half v.numericType Q priced hint hQn hQneg hQc)
        have hQb' := abs_le.mp hQb
        rw [hcp]
        exact abs_le.mpr ⟨by linarith, by linarith⟩
      · have hp0 : priced.toRat = 0 := by
          by_contra hne
          exact STAmount.ofNumber_integral_source_ne_zero v.numericType Q .to_nearest priced hint hQc
            (fun h => hne ((STAmount.toRat_eq_zero_iff priced).mpr h)) hQm
        have hI1 : I ≤ 1 / 2 := le_trans hIsmall (le_trans (zpow_le_zpow_right₀ (by norm_num)
          (by norm_num : (-32700 : ℤ) ≤ -1)) (by norm_num))
        rw [hcp, hp0, zero_sub, abs_neg, abs_of_pos hIpos]
        nlinarith
    have hrel : I * sharesε < 1 / 4 := by unfold sharesε; nlinarith
    obtain ⟨hn1, hn2⟩ := abs_le.mp hnear
    refine ⟨fun hworth => ⟨fun h => absurd hint (by simp [h]), fun _ => ?_⟩, fun _ => by linarith⟩
    obtain ⟨k, hk⟩ := hworth
    rw [hb0, zpow_zero, mul_one] at hk
    -- a whole charge less than one unit below a whole worth is at least the worth
    rw [hk, hcv]
    have hlt : (k : ℚ) - 1 < r.assets.mValue.toNat := by rw [← hcv, ← hk]; linarith
    have hlt' : k - 1 < (r.assets.mValue.toNat : ℤ) := by exact_mod_cast hlt
    exact_mod_cast (show k ≤ (r.assets.mValue.toNat : ℤ) by omega)
  -- fractional: the floored charge is at most a priced amount on a grid no coarser than the base grid
  refine ⟨fun hworth => ⟨fun _ => ?_, fun h => absurd h hint⟩, fun h => absurd h hint⟩
  have hop := Vault.deposit_open_bound v amountDeposit false t hpos hcanon hty navN hat r hok
  obtain ⟨hpiou, hpmv, hppos, -, -, hpexp, -, -⟩ := frac_charge_floor v navN hat r.shares priced r.assets
    (by simpa using hint) hshc hshnt hshpos hsad hcl hfnp hop
  have hvfr : v.numericType = .fractional := NumericType.eq_fractional_of_not_integral (by simpa using hint)
  rcases hQcases with ⟨hQm, hQn, -, hQb⟩ | ⟨hQm, -⟩
  · rw [hvfr] at hQc
    have hh := abs_le.mp (STAmount.ofNumber_iou_to_nearest_within_half Q priced hQn hQm hQc hpmv)
    have hQb' := abs_le.mp hQb
    have hpv : priced.toRat = (priced.mValue.toNat : ℚ) * 10 ^ priced.exponent :=
      STAmount.toRat_of_nonneg priced (STAmount.mIsNegative_false_of_pos priced hppos)
    have hu : (0 : ℚ) < 10 ^ priced.exponent := zpow_pos (by norm_num) _
    have hmhi : (priced.mValue.toNat : ℚ) < 10 ^ 16 := by exact_mod_cast hpiou.mant_hi
    have hsm : priced.toRat < 10 ^ 16 * (10 : ℚ) ^ priced.exponent := by
      rw [hpv]; exact mul_lt_mul_of_pos_right hmhi hu
    have hrel : I * sharesε < 1 / 4 * (10 : ℚ) ^ priced.exponent := by unfold sharesε at *; nlinarith
    obtain ⟨k, hk⟩ := hworth
    exact le_trans hcle (le_of_grid_lt _ k _ _ hpexp _ _ hpv hk (by linarith))
  · -- the priced number underflowed, so the charge is not a positive IOU amount
    exact absurd hQm (STAmount.ofNumber_source_ne_zero _ Q .to_nearest priced hQc hpmv)

/-- Proof of `Vault.deposit_charge`. -/
lemma Vault.deposit_charge_intended_total_proof (v : Vault) (amountDeposit : STAmount) (t : UInt32)
    (hcanon : amountDeposit.Canonical) (hpos : 0 < amountDeposit.toRat)
    (navN : Number) (hat : v.assetsTotal = .ok navN)
    (r : VaultWithAmounts) (hok : (v.deposit amountDeposit false t hpos).run = .ok (.ok r))
    (hsmall : v.idealChargeDepositAt navN.toRat r.shares.toRat ≤ 9 * 10 ^ 15 * (10 : ℚ) ^ v.baseExponent) :
    r.assets.toRat ≤ amountDeposit.toRat ∧
    v.idealChargeDepositAt navN.toRat r.shares.toRat - (10 : ℚ) ^ v.baseExponent < r.assets.toRat ∧
    (v.numericType.isIntegral = true → r.assets.toRat - v.idealChargeDepositAt navN.toRat r.shares.toRat < 1) ∧
    ((∃ k : ℤ, v.idealChargeDepositAt navN.toRat r.shares.toRat = k * 10 ^ v.baseExponent) →
      (v.numericType.isIntegral = false → r.assets.toRat ≤ v.idealChargeDepositAt navN.toRat r.shares.toRat) ∧
      (v.numericType.isIntegral = true → v.idealChargeDepositAt navN.toRat r.shares.toRat ≤ r.assets.toRat)) := by
  obtain ⟨h1, h2, -, -⟩ := Vault.deposit_charge_total_proof v amountDeposit t hcanon hpos navN hat r hok
  have hb : (0 : ℚ) < 10 ^ v.baseExponent := zpow_pos (by norm_num) _
  obtain ⟨hw, hu⟩ := Vault.deposit_charge_worth v amountDeposit t hcanon hpos navN hat r hok (by nlinarith)
  exact ⟨h1, h2, hu, hw⟩

end XRPL.Model.SingleAssetVault
