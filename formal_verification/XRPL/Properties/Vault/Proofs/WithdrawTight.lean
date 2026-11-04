import XRPL.Properties.Vault.Proofs.WithdrawTight.Shares
import XRPL.Properties.Vault.Proofs.WithdrawPricing

/-! # Tight `Vault.withdraw` share bounds

Proof bodies behind the `withdraw_sharesBurned` headlines. -/

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol

/-- A successful withdrawal that names shares burns exactly the named amount. -/
lemma Vault.withdraw_sharesBurned_exact_proof (v : Vault) (shares : STAmount) (waive : Bool) (t : UInt32)
    (hpos : 0 < shares.toRat) (r : VaultWithAmounts)
    (hok : (v.withdraw (.vaultShares shares) waive t hpos).run = .ok (.ok r)) :
    r.shares = shares := by
  simp only [Vault.withdraw] at hok
  unfold_ter at hok
  walk_ok
  all_goals
    have hcomp : (computeWithdraw v (.vaultShares shares) waive).run = .ok (.ok _) := ‹_›
    have h := WdTight.computeWithdraw_vaultShares_shares v shares waive _ hcomp
    exact h

/-- Shares burned by a withdrawal by assets, priced at the net asset value the model computes: a positive
integer at most `sharesε` above the ideal at that value and less than one share plus `sharesε` below it. -/
lemma Vault.withdraw_sharesBurned_total_proof (v : Vault) (assets : STAmount) (waive : Bool) (t : UInt32)
    (nav : Number) (hnav : v.assetsTotalForWithdrawal waive = .ok nav)
    (hpos : 0 < assets.toRat) (hc : assets.Canonical)
    (r : VaultWithAmounts) (hok : (v.withdraw (.vaultAssets assets) waive t hpos).run = .ok (.ok r)) :
    r.shares.toRat.den = 1 ∧ 0 < r.shares.toRat ∧
    r.shares.toRat ≤ v.idealSharesWithdrawAt nav.toRat assets.toRat * (1 + sharesε) ∧
    v.idealSharesWithdrawAt nav.toRat assets.toRat * (1 - sharesε) - 1 < r.shares.toRat := by
  obtain ⟨hs, hnz⟩ := WdTight.burned_of_assets v assets waive t r hpos hok
  exact WdTight.shares_bounds v assets r.shares waive nav hnav hpos hc hs hnz

/-- Shares burned by a withdrawal by assets on a vault whose net asset value is exact. -/
lemma Vault.withdraw_sharesBurned_proof (v : Vault) (assets : STAmount) (waive : Bool) (t : UInt32)
    (hpos : 0 < assets.toRat) (hc : assets.Canonical) (hnav : v.WithdrawNavExact waive)
    (r : VaultWithAmounts) (hok : (v.withdraw (.vaultAssets assets) waive t hpos).run = .ok (.ok r)) :
    r.shares.toRat.den = 1 ∧ 0 < r.shares.toRat ∧
    r.shares.toRat ≤ v.idealSharesWithdraw waive assets.toRat * (1 + sharesε) ∧
    v.idealSharesWithdraw waive assets.toRat * (1 - sharesε) - 1 < r.shares.toRat := by
  obtain ⟨nav, hnavN, hexact⟩ := WdPrice.nav_exact_ok v waive hnav
  have h := Vault.withdraw_sharesBurned_total_proof v assets waive t nav hnavN hpos hc r hok
  have hAt : v.idealSharesWithdrawAt nav.toRat assets.toRat = v.idealSharesWithdraw waive assets.toRat := by
    unfold RawVault.idealSharesWithdrawAt RawVault.idealSharesWithdraw
    rw [hexact]
  rwa [hAt] at h

end XRPL.Model.SingleAssetVault
