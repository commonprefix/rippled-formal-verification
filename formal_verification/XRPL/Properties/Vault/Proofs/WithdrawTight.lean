import XRPL.Properties.Vault.Proofs.WithdrawTight.Shares
import XRPL.Properties.Vault.Proofs.WithdrawPricing

/-! # Tight `Vault.withdraw` share bounds

Proof bodies behind the `withdraw_sharesRedeemed` headlines. -/

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol

/-- A successful withdrawal that names shares burns exactly the named amount. -/
lemma Vault.withdraw_sharesRedeemed_exact_proof (v : Vault) (shares : STAmount) (waive : Bool) (t : UInt32)
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
lemma Vault.withdraw_sharesRedeemed_total_proof (v : Vault) (assets : STAmount) (waive : Bool) (t : UInt32)
    (nav : Number) (hnav : v.assetsTotalForWithdrawal waive = .ok nav)
    (hpos : 0 < assets.toRat) (hc : assets.Canonical)
    (r : VaultWithAmounts) (hok : (v.withdraw (.vaultAssets assets) waive t hpos).run = .ok (.ok r)) :
    r.shares.toRat.den = 1 ∧ 0 < r.shares.toRat ∧
    r.shares.toRat ≤ v.idealSharesWithdrawAt nav.toRat assets.toRat * (1 + sharesε) ∧
    v.idealSharesWithdrawAt nav.toRat assets.toRat * (1 - sharesε) - 1 < r.shares.toRat := by
  obtain ⟨hs, hnz⟩ := WdTight.burned_of_assets v assets waive t r hpos hok
  exact WdTight.shares_bounds v assets r.shares waive nav hnav hpos hc hs hnz

end XRPL.Model.SingleAssetVault
