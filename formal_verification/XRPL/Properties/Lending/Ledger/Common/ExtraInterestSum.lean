import XRPL.Properties.Lending.Ledger.Common.RunSums

/-! # Interest collected beyond the schedule over a sequence

`l.extraInterestPaid txs` adds up what the payments among `txs` collect beyond the schedule. A sequence of
transactions is exactly a run that collects that sum. -/

namespace XRPL.Model.Lending

/-- The interest the transaction `tx` collects beyond the schedule when it runs on `l`. -/
def LendingLedger.extraInterestOf (l : LendingLedger) (tx : LendingTx) : ℚ :=
  match (l.apply tx).run with
  | .ok (.ok l') => l.extraInterest tx l'
  | _ => 0

/-- Σ extraInterest over the transactions `txs` applied in order from `l`. -/
def LendingLedger.extraInterestPaid (l : LendingLedger) (txs : List LendingTx) : ℚ :=
  l.runSum LendingLedger.extraInterestOf txs

/-- A sequence of transactions is a run that collects Σ extraInterest beyond the schedule. -/
lemma LendingLedger.Reaches.reachableFromIn_sum {start l : LendingLedger} {txs : List LendingTx}
    (h : LendingLedger.Reaches start txs l) : start.ReachableFromIn txs l (start.extraInterestPaid txs) := by
  induction h with
  | refl => exact LendingLedger.ReachableFromIn.refl
  | @step txs₀ l₀ l₁ tx hprev hok ih =>
    have hstep := LendingLedger.ReachableFromIn.step tx ih hok
    unfold LendingLedger.extraInterestPaid at hstep ⊢
    rw [LendingLedger.runSum_snoc hprev hok]
    simpa only [LendingLedger.extraInterestOf, hok] using hstep

/-- A run is a sequence of transactions that collects Σ extraInterest beyond the schedule. -/
lemma LendingLedger.ReachableFromIn.reaches_sum {start l : LendingLedger} {txs : List LendingTx} {x : ℚ}
    (h : start.ReachableFromIn txs l x) : LendingLedger.Reaches start txs l ∧ x = start.extraInterestPaid txs := by
  induction h with
  | refl => exact ⟨.refl, rfl⟩
  | @step txs₀ l₀ l₁ x₀ tx _ hok ih =>
    obtain ⟨hr, hx⟩ := ih
    refine ⟨.step tx hr hok, ?_⟩
    unfold LendingLedger.extraInterestPaid at hx ⊢
    rw [LendingLedger.runSum_snoc hr hok, hx]
    simp only [LendingLedger.extraInterestOf, hok]

end XRPL.Model.Lending
