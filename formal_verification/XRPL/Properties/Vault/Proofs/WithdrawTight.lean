import XRPL.Properties.Vault.Proofs.WithdrawTight.Payout

/-! # Tight `Vault.withdraw` share and payout bounds

Proof bodies for the re-signed `withdraw_sharesBurned` and `withdraw_payout` rows. -/

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol

/-- Shares burned by a withdrawal by assets: a positive integer at most `sharesε`
above the ideal and less than one share plus `sharesε` below it. -/
lemma Vault.withdraw_sharesBurned_proof (v : Vault) (assets : STAmount)
    (waiveUnrealizedLoss : Bool) (r : WithdrawResult)
    (hpos : 0 < assets.toRat) (hc : assets.Canonical)
    (hnav : v.WithdrawNavExact waiveUnrealizedLoss)
    (hok : v.withdraw (.vaultAssets assets) waiveUnrealizedLoss hpos = .ok r)
    (herr : r.error = none) :
    r.sharesBurned.toRat.den = 1 ∧ 0 < r.sharesBurned.toRat ∧
    r.sharesBurned.toRat ≤
      v.idealSharesWithdraw waiveUnrealizedLoss assets.toRat * (1 + sharesε) ∧
    v.idealSharesWithdraw waiveUnrealizedLoss assets.toRat * (1 - sharesε) - 1 <
      r.sharesBurned.toRat := by
  obtain ⟨hs, hnz⟩ := WdTight.burned_of_assets v assets waiveUnrealizedLoss r hpos hok herr
  exact WdTight.shares_bounds v assets _ waiveUnrealizedLoss hnav hpos hc hs hnz

/-- Payout of a non-final withdrawal: at most half a unit of its own grid above the
burned shares' worth (plus `depositε`), and below it by at most half a unit or, when
the payout is floored onto the grid of the rounded post-withdrawal total `atr'`, by
less than one step of that grid (plus `depositε`). -/
lemma Vault.withdraw_payout_proof (v : Vault) (amount : WithdrawAmount)
    (waiveUnrealizedLoss : Bool) (sharesTotalAmount : STAmount) (r : WithdrawResult)
    (hnn : 0 ≤ r.sharesBurned.toRat) (hc : r.sharesBurned.Canonical)
    (hnav : v.WithdrawNavExact waiveUnrealizedLoss)
    (hpos : 0 < amount.amount.toRat)
    (hok : v.withdraw amount waiveUnrealizedLoss hpos = .ok r) (herr : r.error = none)
    (hst : STAmount.ofNumber .int64 v.sharesTotal .to_nearest = .ok sharesTotalAmount)
    (hfin : r.sharesBurned.operator_eq sharesTotalAmount = false) :
    0 ≤ r.assets'.toRat ∧
    r.assets'.toRat ≤
      v.idealAssetsWithdraw waiveUnrealizedLoss r.sharesBurned.toRat * (1 + depositε) +
        1 / 2 * (10 : ℚ) ^ r.assets'.exponent ∧
    ∃ atr' : STAmount,
      STAmount.ofNumber v.numericType r.vault'.assetsTotal .to_nearest = .ok atr' ∧
      v.idealAssetsWithdraw waiveUnrealizedLoss r.sharesBurned.toRat - r.assets'.toRat ≤
        v.idealAssetsWithdraw waiveUnrealizedLoss r.sharesBurned.toRat * depositε +
          max (1 / 2 * (10 : ℚ) ^ r.assets'.exponent)
            ((10 : ℚ) ^ atr'.exponent - 1 / 2 * (10 : ℚ) ^ r.assets'.exponent) :=
  WdTight.payout_bounds v amount waiveUnrealizedLoss sharesTotalAmount r hnn hc hnav hpos hok
    herr hst hfin

end XRPL.Model.SingleAssetVault
