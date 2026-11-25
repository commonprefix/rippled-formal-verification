import XRPL.Properties.Vault.Proofs.WithdrawPricing.Core
import XRPL.Properties.Vault.Proofs.WithdrawAccuracy.Price

/-! # Accuracy of the `sharesToAssetsWithdraw` pricing

The payout is packed `.to_nearest`, so it can exceed the shares' worth by half a ULP of
the result on top of the interior stage error. -/

namespace XRPL.Model.SingleAssetVault.WdPrice

open XRPL.Model.Protocol

/-- An exact pricing value: the computed net asset value is the exact one. -/
lemma nav_exact (v : Vault) (w : Bool) (nav : Number) (hnav : v.WithdrawNavExact w)
    (hsub : v.assetsTotalForWithdrawal w = .ok nav) :
    nav.toRat = navQ v w := by
  obtain ⟨atot, nv, hat, hnv, hq⟩ := hnav
  simp only [Vault.assetsTotalForWithdrawal, bind, Except.bind, hat] at hsub
  rw [show nav = nv from Except.ok.inj (hsub.symm.trans hnv)]
  exact hq

/-- An exact pricing value computes: the net asset value the withdrawal reads exists. -/
lemma nav_exact_ok (v : Vault) (w : Bool) (hnav : v.WithdrawNavExact w) :
    ∃ nav : Number, v.assetsTotalForWithdrawal w = .ok nav ∧ nav.toRat = navQ v w := by
  obtain ⟨atot, nv, hat, hnv, hq⟩ := hnav
  refine ⟨nv, ?_, hq⟩
  simp only [Vault.assetsTotalForWithdrawal, bind, Except.bind, hat]
  exact hnv

end XRPL.Model.SingleAssetVault.WdPrice

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol WdPrice

/-- The assets priced for shares against the net asset value the model computes: within `sharesε` of the worth
at that value and half a unit of their last digit. -/
lemma Vault.sharesToAssetsWithdraw_total_proof (v : Vault) (shares assets : STAmount)
    (waiveUnrealizedLoss : Bool) (nav : Number)
    (hnav : v.assetsTotalForWithdrawal waiveUnrealizedLoss = .ok nav)
    (hnn : 0 ≤ shares.toRat) (hc : shares.Canonical)
    (hok : v.sharesToAssetsWithdraw shares waiveUnrealizedLoss = .ok assets) :
    0 ≤ assets.toRat ∧
    assets.toRat ≤ v.idealAssetsWithdrawAt nav.toRat shares.toRat * (1 + sharesε) +
      (1 / 2 : ℚ) * (10 : ℚ) ^ assets.exponent ∧
    (assets.isZero = false →
      v.idealAssetsWithdrawAt nav.toRat shares.toRat - assets.toRat ≤
        v.idealAssetsWithdrawAt nav.toRat shares.toRat * sharesε +
          (1 / 2 : ℚ) * (10 : ℚ) ^ assets.exponent) := by
  obtain ⟨nav', hsub, hN0, hpnn, hcase⟩ := price_spec v shares assets waiveUnrealizedLoss hnn hc hok
  rw [hnav, Except.ok.injEq] at hsub
  subst hsub
  have hAt : v.idealAssetsWithdrawAt nav.toRat shares.toRat = nav.toRat * shares.toRat / v.sharesTotal.toRat := by
    unfold RawVault.idealAssetsWithdrawAt
    rw [RawVault.WF.toExact_sharesTotal v.toRawVault v.wf]
  have hI0 : 0 ≤ v.idealAssetsWithdrawAt nav.toRat shares.toRat := by
    rw [hAt]; exact div_nonneg (mul_nonneg hN0 hnn) v.wf.sharesTotal_nonneg
  have hU : (0 : ℚ) < (10 : ℚ) ^ assets.exponent := zpow_pos (by norm_num) _
  refine ⟨hpnn, ?_⟩
  rcases hcase with hp0 | ⟨-, -, an, -, hb, hh, -⟩
  · rw [STAmount.toRat_eq_zero_of_mValue_zero _ hp0]
    have hε : (0 : ℚ) ≤ sharesε := by unfold sharesε; norm_num
    refine ⟨by nlinarith, fun hz => ?_⟩
    simp [STAmount.isZero, hp0] at hz
  rw [← hAt] at hb
  set I := v.idealAssetsWithdrawAt nav.toRat shares.toRat
  obtain ⟨hb1, hb2⟩ := abs_le.mp hb
  obtain ⟨hh1, hh2⟩ := abs_le.mp hh
  exact ⟨by nlinarith, fun _ => by nlinarith⟩

/-- The assets priced for shares when the pricing value is exact: within `sharesε` of the worth and half a unit
of their last digit. -/
lemma Vault.sharesToAssetsWithdraw_bounds_proof (v : Vault) (shares assets : STAmount)
    (waiveUnrealizedLoss : Bool)
    (hnn : 0 ≤ shares.toRat) (hc : shares.Canonical)
    (hnav : v.WithdrawNavExact waiveUnrealizedLoss)
    (hok : v.sharesToAssetsWithdraw shares waiveUnrealizedLoss = .ok assets) :
    0 ≤ assets.toRat ∧
    assets.toRat ≤ v.idealAssetsWithdraw waiveUnrealizedLoss shares.toRat * (1 + sharesε) +
      (1 / 2 : ℚ) * (10 : ℚ) ^ assets.exponent ∧
    (assets.isZero = false →
      v.idealAssetsWithdraw waiveUnrealizedLoss shares.toRat - assets.toRat ≤
        v.idealAssetsWithdraw waiveUnrealizedLoss shares.toRat * sharesε +
          (1 / 2 : ℚ) * (10 : ℚ) ^ assets.exponent) := by
  obtain ⟨nav, hnavN, hexact⟩ := nav_exact_ok v waiveUnrealizedLoss hnav
  have h := Vault.sharesToAssetsWithdraw_total_proof v shares assets waiveUnrealizedLoss nav hnavN hnn hc hok
  rwa [hexact] at h

end XRPL.Model.SingleAssetVault
