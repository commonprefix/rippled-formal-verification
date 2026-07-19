import XRPL.Properties.Vault.Lawful
import XRPL.Properties.Vault.Common.Preservation

/-! # Vault reachability (statement sketch)

`Vault.Reachable v` holds when `v` is the result of `Vault.create` with parameters
satisfying the creation hypotheses, or the result of a `deposit`, `withdraw`,
`clawback`, or `burnShares` that ran without a throw on a vault that is itself
reachable, with the operation's amounts satisfying the canonical-storage and
sign side conditions of the matching preservation theorem. The constructors do
not require the operation to succeed. A rejected operation returns the starting
vault unchanged (the theorems in `Unchanged.lean`), so admitting rejected
results does not enlarge the set of states. `create` is the only constructor
that does not require a prior reachability proof, so every proof of
`Vault.Reachable` starts with a creation. Induction on `Vault.Reachable`
therefore has exactly one base case, `create`, and one step case per operation,
which is how `Reachable.lawful` covers every possible history: `create_lawful`
discharges the creation case and the preservation theorems discharge the
operation cases. The two zero-corollaries and the asset-parity corollary supply
the state hypotheses those preservation theorems take.
-/

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol

/-- States reachable from `VaultCreate` under all operations. -/
inductive Vault.Reachable : Vault → Prop where
  | create (nt : NumericType) (scale : UInt8) (assetsMaximum : Option Number)
      (hmax_norm : ∀ m ∈ assetsMaximum, m.isNormalized)
      (hmax_pos : ∀ m ∈ assetsMaximum, 0 < m.toRat)
      (hscale_int : nt.isIntegral = true → scale = 0) (hscale_le : scale.toNat ≤ 18) :
      Vault.Reachable (Vault.create nt scale assetsMaximum)
  | deposit (v : Vault) (amount : STAmount) (isDonation : Bool) (r : DepositResult) :
      Vault.Reachable v → v.deposit amount isDonation = .ok r →
      r.amountDeposit'.ExactCanonical → -- the taken amount is stored canonically
      0 ≤ r.amountDeposit'.toRat → -- and is not negative
      r.sharesIssued.IntegralCanonical → -- the issued shares are canonical integral
      0 ≤ r.sharesIssued.toRat → -- and not negative
      (v.toExact.sharesTotal : ℚ) + r.sharesIssued.toRat ≤ 2 ^ 63 - 1 → -- share domain
      Vault.Reachable r.vault'
  | withdraw (v : Vault) (amount : WithdrawAmount) (waive : Bool) (r : WithdrawResult) :
      Vault.Reachable v → v.withdraw amount waive = .ok r →
      r.assets'.ExactCanonical → -- the paid amount is stored canonically
      0 ≤ r.assets'.toRat → -- and is not negative
      r.sharesBurned.IntegralCanonical → -- the burned shares are canonical int64
      r.sharesBurned.mNumericType = .int64 →
      r.sharesBurned.negative = false →
      r.sharesBurned.toRat ≤ (v.toExact.sharesTotal : ℚ) → -- within the share total
      (v.toExact.sharesTotal : ℚ) ≤ 2 ^ 63 - 1 → -- share domain
      Vault.Reachable r.vault'
  | clawback (v : Vault) (assets : STAmount) (r : ClawbackResult) :
      Vault.Reachable v → v.clawback assets = .ok r →
      r.assetsRecovered.ExactCanonical → -- the recovered amount is stored canonically
      0 ≤ r.assetsRecovered.toRat → -- and is not negative
      r.assetsRecovered.toRat ≤ v.toExact.assetsAvailable → -- covered by the balance
      r.sharesDestroyed.IntegralCanonical → -- the destroyed shares are canonical integral
      r.sharesDestroyed.negative = false →
      r.sharesDestroyed.toRat < (v.toExact.sharesTotal : ℚ) → -- strictly partial
      (v.toExact.sharesTotal : ℚ) ≤ 2 ^ 63 - 1 → -- share domain
      Vault.Reachable r.vault'
  | burnShares (v : Vault) (sharesDestroyed sharesTotalAmount : STAmount) (v' : Vault) :
      Vault.Reachable v →
      v.canBurnShares = .ok (.assets sharesTotalAmount) → -- the burn permission guard passed
      sharesDestroyed.IntegralCanonical → -- stored as a plain integral amount
      sharesDestroyed.negative = false →
      sharesDestroyed.toRat ≤ sharesTotalAmount.toRat → -- a holder cannot burn more than exists
      (v.toExact.sharesTotal : ℚ) ≤ 2 ^ 63 - 1 → -- share domain
      v.burnShares sharesDestroyed = .ok v' →
      Vault.Reachable v'

/-- No operation changes `lossUnrealized`. -/
theorem Vault.Reachable.lossUnrealized_zero (v : Vault) (hr : Vault.Reachable v) :
    v.toExact.lossUnrealized = 0 := by
  induction hr with
  | create nt scale am hn hp hi hl =>
    simp only [Vault.toExact, Vault.create, Number.toRat_zero]
  | deposit v amount isDonation r hrv hdep _ _ _ _ _ ih =>
    show r.vault'.lossUnrealized.toRat = 0
    rw [(Vault.deposit_preserves_unrealized v amount isDonation r hdep).1]; exact ih
  | withdraw v amount waive r hrv hwd _ _ _ _ _ _ _ ih =>
    show r.vault'.lossUnrealized.toRat = 0
    rw [(Vault.withdraw_preserves_unrealized v amount waive r hwd).1]; exact ih
  | clawback v assets r hrv hcb _ _ _ _ _ _ _ ih =>
    show r.vault'.lossUnrealized.toRat = 0
    rw [(Vault.clawback_preserves_unrealized v assets r hcb).1]; exact ih
  | burnShares v sharesDestroyed sharesTotalAmount v' hrv hcan hcanon hnn hle hfit hburn ih =>
    show v'.lossUnrealized.toRat = 0
    rw [(Vault.burnShares_preserves_unrealized v sharesDestroyed v' hburn).1]; exact ih

/-- No operation changes `interestUnrealized`. -/
theorem Vault.Reachable.interestUnrealized_zero (v : Vault) (hr : Vault.Reachable v) :
    v.toExact.interestUnrealized = 0 := by
  induction hr with
  | create nt scale am hn hp hi hl =>
    simp only [Vault.toExact, Vault.create, Number.toRat_zero]
  | deposit v amount isDonation r hrv hdep _ _ _ _ _ ih =>
    show r.vault'.interestUnrealized.toRat = 0
    rw [(Vault.deposit_preserves_unrealized v amount isDonation r hdep).2]; exact ih
  | withdraw v amount waive r hrv hwd _ _ _ _ _ _ _ ih =>
    show r.vault'.interestUnrealized.toRat = 0
    rw [(Vault.withdraw_preserves_unrealized v amount waive r hwd).2]; exact ih
  | clawback v assets r hrv hcb _ _ _ _ _ _ _ ih =>
    show r.vault'.interestUnrealized.toRat = 0
    rw [(Vault.clawback_preserves_unrealized v assets r hcb).2]; exact ih
  | burnShares v sharesDestroyed sharesTotalAmount v' hrv hcan hcanon hnn hle hfit hburn ih =>
    show v'.interestUnrealized.toRat = 0
    rw [(Vault.burnShares_preserves_unrealized v sharesDestroyed v' hburn).2]; exact ih

/-- Every operation writes both asset fields with the identical update, so
record-level asset parity holds on all reachable states. -/
theorem Vault.Reachable.asset_parity (v : Vault) (hr : Vault.Reachable v) :
    v.assetsAvailable = v.assetsTotal := by
  induction hr with
  | create nt scale am hn hp hi hl => rfl
  | deposit v amount isDonation r hrv hdep _ _ _ _ _ ih =>
    exact Vault.deposit_asset_parity v amount isDonation r ih hdep
  | withdraw v amount waive r hrv hwd _ _ _ _ _ _ _ ih =>
    exact Vault.withdraw_asset_parity v amount waive r ih hwd
  | clawback v assets r hrv hcb _ _ _ _ _ _ _ ih =>
    exact Vault.clawback_asset_parity v assets r ih hcb
  | burnShares v sharesDestroyed sharesTotalAmount v' hrv hcan hcanon hnn hle hfit hburn ih =>
    exact Vault.burnShares_asset_parity v sharesDestroyed v' ih hburn

/-- All reachable states are lawful. Base case `create` is `Vault.create_lawful`;
each operation case is the matching preservation theorem applied to the
induction hypothesis (the prior state is lawful) and the reachability
corollaries (both unrealized fields zero, asset parity). -/
theorem Vault.Reachable.lawful (v : Vault) (hr : Vault.Reachable v) : v.Lawful := by
  induction hr with
  | create nt scale am hn hp hi hl =>
    exact Vault.create_lawful nt scale am hn hp hi hl
  | deposit v amount isDonation r hrv hdep hDc hDnn hSc hSnn hSsz ih =>
    exact Vault.deposit_lawful v amount isDonation ih
      (Vault.Reachable.interestUnrealized_zero v hrv)
      (Vault.Reachable.lossUnrealized_zero v hrv)
      (Vault.Reachable.asset_parity v hrv) r hdep hDc hDnn hSc hSnn hSsz
  | withdraw v amount waive r hrv hwd hDc hDnn hSc hSnt hSnn hsle hfit ih =>
    exact Vault.withdraw_lawful v amount waive ih
      (Vault.Reachable.interestUnrealized_zero v hrv)
      (Vault.Reachable.lossUnrealized_zero v hrv)
      (Vault.Reachable.asset_parity v hrv) r hwd hDc hDnn hSc hSnt hSnn hsle hfit
  | clawback v assets r hrv hcb hDc hDnn hDle hSc hSnn hslt hfit ih =>
    exact Vault.clawback_lawful v assets ih
      (Vault.Reachable.interestUnrealized_zero v hrv)
      (Vault.Reachable.lossUnrealized_zero v hrv)
      (Vault.Reachable.asset_parity v hrv) r hcb hDc hDnn hDle hSc hSnn hslt hfit
  | burnShares v sharesDestroyed sharesTotalAmount v' hrv hcan hcanon hnn hle hfit hburn ih =>
    exact Vault.burnShares_lawful v sharesDestroyed sharesTotalAmount v' ih hcan hcanon hnn
      hle hfit hburn

end XRPL.Model.SingleAssetVault
