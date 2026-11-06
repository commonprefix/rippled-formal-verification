import XRPL.Properties.Lending.Ledger.Common.ReachableProofs

/-! # Runs that add up what the payments collect

`LendingLedger.ReachableFromIn start txs l extraInterest` says the transactions `txs` take `start` to `l`, each
one succeeding, and the payments among them collect `extraInterest` beyond the schedule. -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol

/-- A vault is coarsened once AssetsAvailable + AssetsDeployed reaches `10^16` base units. Only an IOU amount
coarsens, but the bound applies to XRP and MPT vaults too. -/
def LendingLedger.NotCoarsened (l : LendingLedger) : Prop :=
  l.vault.assetsAvailable.toRat + l.vault.assetsDeployed.toRat < 10 ^ 16 * (10 : ℚ) ^ l.vault.baseExponent

/-- The Open limit of the ledger's vault, `9·10^15` base units. -/
def LendingLedger.openLimit (l : LendingLedger) : ℚ := 9 * 10 ^ 15 * (10 : ℚ) ^ l.vault.baseExponent

/-- The interest a transaction collects beyond the schedule. For a payment it is the AssetsTotal it adds beyond
the YieldUnrealized it releases, when positive, and zero for every other transaction. -/
def LendingLedger.extraInterest (l : LendingLedger) (tx : LendingTx) (l' : LendingLedger) : ℚ :=
  match tx with
  | .loanPay .. => max 0 ((l'.vault.toRawVault.toExact.assetsTotal - l.vault.toRawVault.toExact.assetsTotal) -
      (l.vault.yieldUnrealized.toRat - l'.vault.yieldUnrealized.toRat))
  | _ => 0

/-- A transaction that can take assets out of the vault: a default, a VaultWithdraw or a VaultClawback. -/
def LendingTx.isOutflow : LendingTx → Bool
  | .loanManage _ .default | .vaultWithdraw .. | .vaultClawback .. => true
  | _ => false

/-- `ReachableFromIn start txs l extraInterest`: applying `txs` in order to `start` succeeds at every step and
ends in `l`, and the payments among them collect `extraInterest` beyond the schedule. -/
inductive LendingLedger.ReachableFromIn (start : LendingLedger) : List LendingTx → LendingLedger → ℚ → Prop where
  | refl : LendingLedger.ReachableFromIn start [] start 0
  | step {txs : List LendingTx} {l l' : LendingLedger} {x : ℚ} (tx : LendingTx) :
      LendingLedger.ReachableFromIn start txs l x → (l.apply tx).run = .ok (.ok l') →
      LendingLedger.ReachableFromIn start (txs ++ [tx]) l' (x + l.extraInterest tx l')

/-- A transaction collects at least zero beyond the schedule. -/
lemma LendingLedger.extraInterest_nonneg (l : LendingLedger) (tx : LendingTx) (l' : LendingLedger) :
    0 ≤ l.extraInterest tx l' := by
  unfold LendingLedger.extraInterest
  split
  · exact le_max_left _ _
  · exact le_refl _

/-- A run collects at least zero beyond the schedule. -/
lemma LendingLedger.ReachableFromIn.extraInterest_nonneg {start l : LendingLedger} {txs : List LendingTx} {x : ℚ}
    (h : start.ReachableFromIn txs l x) : 0 ≤ x := by
  induction h with
  | refl => exact le_refl _
  | @step _ l₀ l₁ _ tx _ _ ih => linarith [LendingLedger.extraInterest_nonneg l₀ tx l₁]

/-- A run is a sequence of successful transactions. -/
lemma LendingLedger.ReachableFromIn.reaches {start l : LendingLedger} {txs : List LendingTx} {x : ℚ}
    (h : start.ReachableFromIn txs l x) : LendingLedger.Reaches start txs l := by
  induction h with
  | refl => exact .refl
  | step tx _ hok ih => exact .step tx ih hok

/-- A run from a new vault ends in a reachable ledger. -/
lemma LendingLedger.ReachableFromIn.reachable {start l : LendingLedger} {txs : List LendingTx} {x : ℚ}
    (hg : start.Genesis) (h : start.ReachableFromIn txs l x) : l.Reachable :=
  ⟨start, txs, hg, h.reaches, fun _ _ => trivial⟩

/-- A run from a reachable ledger ends in a reachable ledger. -/
lemma LendingLedger.ReachableFromIn.reachable_of {start l : LendingLedger} {txs : List LendingTx} {x : ℚ}
    (hr : start.Reachable) (h : start.ReachableFromIn txs l x) : l.Reachable := by
  obtain ⟨g, txs₀, hg, hreach, -⟩ := hr
  exact ⟨g, txs₀ ++ txs, hg, hreach.trans h.reaches, fun _ _ => trivial⟩

/-- A successful transaction in front of a run is a longer run. -/
lemma LendingLedger.ReachableFromIn.cons {l l' l'' : LendingLedger} {tx : LendingTx} {txs : List LendingTx} {x : ℚ}
    (hok : (l.apply tx).run = .ok (.ok l')) (h : l'.ReachableFromIn txs l'' x) :
    l.ReachableFromIn (tx :: txs) l'' (l.extraInterest tx l' + x) := by
  induction h with
  | refl =>
    have := LendingLedger.ReachableFromIn.step tx (LendingLedger.ReachableFromIn.refl (start := l)) hok
    simpa using this
  | @step txs₀ l₀ l₁ x₀ tx' _ hok' ih =>
    have := LendingLedger.ReachableFromIn.step tx' ih hok'
    rw [show l.extraInterest tx l' + (x₀ + l₀.extraInterest tx' l₁) =
      l.extraInterest tx l' + x₀ + l₀.extraInterest tx' l₁ by ring]
    exact this

end XRPL.Model.Lending
