import XRPL.Properties.Vault.Lawful
import XRPL.Properties.Vault.Common.Preservation
import XRPL.Properties.Vault.Common.ReachableDefs

/-! # Reachability induction proofs

Proof bodies for the `Vault.Reachable` headlines in `Reachable.lean`. Each is an
induction on `Vault.Reachable` (from `ReachableDefs.lean`): one base case
`create` and one step case per operation, discharged by the field-preservation
theorems in `Preservation.lean` and, for `lawful`, the `*_lawful` theorems in
`Lawful.lean`. -/

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol

/-- No operation changes `lossUnrealized`. -/
theorem Vault.Reachable.lossUnrealized_zero_proof (v : Vault) (hr : Vault.Reachable v) :
    v.toExact.lossUnrealized = 0 := by
  induction hr with
  | create nt scale am hn hp hi hl =>
    simp only [Vault.toExact, Vault.create, Number.toRat_zero]
  | deposit v amount isDonation r hrv hdep _ _ _ ih =>
    show r.vault'.lossUnrealized.toRat = 0
    rw [(Vault.deposit_preserves_unrealized v amount isDonation r hdep).1]; exact ih
  | withdraw v amount waive r hrv hwd _ _ _ _ _ ih =>
    show r.vault'.lossUnrealized.toRat = 0
    rw [(Vault.withdraw_preserves_unrealized v amount waive r hwd).1]; exact ih
  | clawback v assets r hrv hcb _ _ _ ih =>
    show r.vault'.lossUnrealized.toRat = 0
    rw [(Vault.clawback_preserves_unrealized v assets r hcb).1]; exact ih
  | burnShares v sharesDestroyed sharesTotalAmount v' hrv hcan hcanon hnn hle hfit hburn ih =>
    show v'.lossUnrealized.toRat = 0
    rw [(Vault.burnShares_preserves_unrealized v sharesDestroyed v' hburn).1]; exact ih

/-- No operation changes `interestUnrealized`. -/
theorem Vault.Reachable.interestUnrealized_zero_proof (v : Vault) (hr : Vault.Reachable v) :
    v.toExact.interestUnrealized = 0 := by
  induction hr with
  | create nt scale am hn hp hi hl =>
    simp only [Vault.toExact, Vault.create, Number.toRat_zero]
  | deposit v amount isDonation r hrv hdep _ _ _ ih =>
    show r.vault'.interestUnrealized.toRat = 0
    rw [(Vault.deposit_preserves_unrealized v amount isDonation r hdep).2]; exact ih
  | withdraw v amount waive r hrv hwd _ _ _ _ _ ih =>
    show r.vault'.interestUnrealized.toRat = 0
    rw [(Vault.withdraw_preserves_unrealized v amount waive r hwd).2]; exact ih
  | clawback v assets r hrv hcb _ _ _ ih =>
    show r.vault'.interestUnrealized.toRat = 0
    rw [(Vault.clawback_preserves_unrealized v assets r hcb).2]; exact ih
  | burnShares v sharesDestroyed sharesTotalAmount v' hrv hcan hcanon hnn hle hfit hburn ih =>
    show v'.interestUnrealized.toRat = 0
    rw [(Vault.burnShares_preserves_unrealized v sharesDestroyed v' hburn).2]; exact ih

/-- Every operation writes both asset fields with the identical update, so
record-level asset parity holds on all reachable states. -/
theorem Vault.Reachable.asset_parity_proof (v : Vault) (hr : Vault.Reachable v) :
    v.assetsAvailable = v.assetsTotal := by
  induction hr with
  | create nt scale am hn hp hi hl => rfl
  | deposit v amount isDonation r hrv hdep _ _ _ ih =>
    exact Vault.deposit_asset_parity v amount isDonation r ih hdep
  | withdraw v amount waive r hrv hwd _ _ _ _ _ ih =>
    exact Vault.withdraw_asset_parity v amount waive r ih hwd
  | clawback v assets r hrv hcb _ _ _ ih =>
    exact Vault.clawback_asset_parity v assets r ih hcb
  | burnShares v sharesDestroyed sharesTotalAmount v' hrv hcan hcanon hnn hle hfit hburn ih =>
    exact Vault.burnShares_asset_parity v sharesDestroyed v' ih hburn

/-- All reachable states are lawful. Base case `create` is `Vault.create_lawful`;
each operation case is the matching preservation theorem applied to the
induction hypothesis (the prior state is lawful) and the reachability
corollaries (both unrealized fields zero, asset parity). -/
theorem Vault.Reachable.lawful_proof (v : Vault) (hr : Vault.Reachable v) : v.Lawful := by
  induction hr with
  | create nt scale am hn hp hi hl =>
    exact Vault.create_lawful nt scale am hn hp hi hl
  | deposit v amount isDonation r hrv hdep hcanon hnn hSsz ih =>
    exact Vault.deposit_lawful v amount isDonation ih
      (Vault.Reachable.interestUnrealized_zero_proof v hrv)
      (Vault.Reachable.lossUnrealized_zero_proof v hrv)
      (Vault.Reachable.asset_parity_proof v hrv) hcanon hnn r hdep hSsz
  | withdraw v amount waive r hrv hwd hSc hSnt hSnn hsle hfit ih =>
    exact Vault.withdraw_lawful v amount waive ih
      (Vault.Reachable.interestUnrealized_zero_proof v hrv)
      (Vault.Reachable.lossUnrealized_zero_proof v hrv)
      (Vault.Reachable.asset_parity_proof v hrv) r hwd hSc hSnt hSnn hsle hfit
  | clawback v assets r hrv hcb hcanon hslt hfit ih =>
    exact Vault.clawback_lawful v assets ih
      (Vault.Reachable.interestUnrealized_zero_proof v hrv)
      (Vault.Reachable.lossUnrealized_zero_proof v hrv)
      (Vault.Reachable.asset_parity_proof v hrv) hcanon r hcb hslt hfit
  | burnShares v sharesDestroyed sharesTotalAmount v' hrv hcan hcanon hnn hle hfit hburn ih =>
    exact Vault.burnShares_lawful v sharesDestroyed sharesTotalAmount v' ih hcan hcanon hnn
      hle hfit hburn

end XRPL.Model.SingleAssetVault
