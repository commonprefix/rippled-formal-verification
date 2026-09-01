import XRPL.Properties.Vault.Common.Preservation
import XRPL.Properties.Vault.Common.ReachableDefs

/-! # Reachability induction proofs

Proof bodies for the `LawfulVault.Reachable` corollaries in `Reachable.lean`. Each is an
induction on `LawfulVault.Reachable` (from `ReachableDefs.lean`, over `LawfulVault`): one
base case `create` and one step case per operation, discharged by the field
preservation theorems in `Preservation.lean`. Reachable states are lawful by
construction (the ops return `LawfulVault`), so no separate lawfulness proof is
needed: read `lv.wf`/`lv.exact` directly. -/

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol

-- `LawfulVault.create_lawful` is a tactic-mode definition; reducing its `toRawVault` in the
-- `create` base case needs a deeper reduction budget.
set_option maxRecDepth 4000

/-- No operation changes `lossUnrealized`. -/
theorem LawfulVault.Reachable.lossUnrealized_zero_proof (lv : LawfulVault) (hr : LawfulVault.Reachable lv) :
    lv.toExact.lossUnrealized = 0 := by
  induction hr with
  | create nt scale am hn hp hi hl =>
    simp only [LawfulVault.create_lawful_toRawVault, RawVault.toExact, Number.toRat_zero]
  | deposit lw amount isDonation r hrv hdep _ _ _ ih =>
    show r.vault'.lossUnrealized.toRat = 0
    rw [LawfulVault.deposit_preserves_unrealized lw amount isDonation r hdep]; exact ih
  | withdraw lw amount waive r hrv hwd _ _ _ _ _ ih =>
    show r.vault'.lossUnrealized.toRat = 0
    rw [LawfulVault.withdraw_preserves_unrealized lw amount waive r hwd]; exact ih
  | clawback lw assets holderShares r hrv hcb _ _ _ _ _ _ ih =>
    show r.vault'.lossUnrealized.toRat = 0
    rw [LawfulVault.clawback_preserves_unrealized lw assets holderShares r hcb]; exact ih
  | burnShares lw sharesDestroyed sharesTotalAmount lw' hrv hcan hcanon hnn hle hfit hburn ih =>
    show lw'.lossUnrealized.toRat = 0
    rw [LawfulVault.burnShares_preserves_unrealized lw sharesDestroyed lw' hburn]; exact ih

/-- Every operation writes both asset fields with the identical update, so
record-level asset parity holds on all reachable states. -/
theorem LawfulVault.Reachable.asset_parity_proof (lv : LawfulVault) (hr : LawfulVault.Reachable lv) :
    lv.assetsAvailable = lv.assetsTotal := by
  induction hr with
  | create nt scale am hn hp hi hl =>
    simp only [LawfulVault.create_lawful_toRawVault]
  | deposit lw amount isDonation r hrv hdep _ _ _ ih =>
    exact LawfulVault.deposit_asset_parity lw amount isDonation r ih hdep
  | withdraw lw amount waive r hrv hwd _ _ _ _ _ ih =>
    exact LawfulVault.withdraw_asset_parity lw amount waive r ih hwd
  | clawback lw assets holderShares r hrv hcb _ _ _ _ _ _ ih =>
    exact LawfulVault.clawback_asset_parity lw assets holderShares r ih hcb
  | burnShares lw sharesDestroyed sharesTotalAmount lw' hrv hcan hcanon hnn hle hfit hburn ih =>
    exact LawfulVault.burnShares_asset_parity lw sharesDestroyed lw' ih hburn

end XRPL.Model.SingleAssetVault
