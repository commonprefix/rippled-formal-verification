import XRPL.Properties.Vault.Common.ReachableDefs
import XRPL.Properties.Vault.Proofs.Frame

/-! # Reachability induction proofs

Induction on `Vault.Reachable`: the base case reads `Vault.create_lawful`, and each
step case uses the frame facts of `Frame.lean`. -/

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol

-- `Vault.create_lawful` is a tactic-mode definition; reducing its `toRawVault` in the
-- `create` base case needs a deeper reduction budget.
set_option maxRecDepth 4000

lemma Vault.Reachable.lossUnrealized_zero_proof (v : Vault) (hr : Vault.Reachable v) :
    v.toExact.lossUnrealized = 0 := by
  induction hr with
  | create => simp only [Vault.create_lawful_toRawVault, RawVault.toExact, Number.toRat_zero]
  | deposit u _ _ r _ _ hok _ _ ih =>
    show r.vault'.lossUnrealized.toRat = 0
    rw [Vault.deposit_lossUnrealized_frame u _ _ r _ hok]; exact ih
  | withdraw u _ _ r _ _ hok _ _ _ _ _ ih =>
    show r.vault'.lossUnrealized.toRat = 0
    rw [Vault.withdraw_lossUnrealized_frame u _ _ r _ hok]; exact ih
  | clawback u _ _ r _ _ hok _ _ _ _ _ _ ih =>
    show r.vault'.lossUnrealized.toRat = 0
    rw [Vault.clawback_lossUnrealized_frame u _ _ r _ hok]; exact ih
  | burnShares u _ _ u' _ _ _ _ _ _ hok ih =>
    show u'.lossUnrealized.toRat = 0
    rw [Vault.burnShares_lossUnrealized_frame u _ u' hok]; exact ih

lemma Vault.Reachable.asset_parity_proof (v : Vault) (hr : Vault.Reachable v) :
    v.assetsAvailable = v.assetsTotal := by
  induction hr with
  | create => simp only [Vault.create_lawful_toRawVault]
  | deposit u _ _ r _ _ hok _ _ ih => exact Vault.deposit_parity_frame u _ _ r _ hok ih
  | withdraw u _ _ r _ _ hok _ _ _ _ _ ih => exact Vault.withdraw_parity_frame u _ _ r _ hok ih
  | clawback u _ _ r _ _ hok _ _ _ _ _ _ ih => exact Vault.clawback_parity_frame u _ _ r _ hok ih
  | burnShares u _ _ u' _ _ _ _ _ _ hok ih => exact Vault.burnShares_parity_frame u _ u' hok ih

end XRPL.Model.SingleAssetVault
