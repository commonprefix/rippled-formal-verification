import XRPL.Properties.Lending.Ledger.Common.CoarsenedVault
import XRPL.Properties.Lending.Ledger.Common.CoverOpenZone

/-! # A run that takes a cover past the Open zone

Broker 1 deposits a cover of exactly the Open limit, late interest coarsens the vault, and defaulting loan B pays the
vault a negative cover of −0.9. The cover ends 0.9 above the Open limit, with no fee paid into it. -/

set_option linter.style.nativeDecide false

namespace XRPL.Model.Lending

open XRPL.Model.Protocol

/-- Apply the transactions in order and add up what the payments collect beyond the schedule, or `none` when one
of them does not succeed. -/
private def LendingLedger.runIn' (l : LendingLedger) : List LendingTx → Option (LendingLedger × ℚ)
  | [] => some (l, 0)
  | tx :: txs =>
    match (l.apply tx).run with
    | .ok (.ok l') => (l'.runIn' txs).map fun p => (p.1, l.extraInterest tx l' + p.2)
    | _ => none

/-- A run that succeeds at every step is a `ReachableFromIn` run. -/
private lemma LendingLedger.runIn'_reachableFromIn {l l' : LendingLedger} {txs : List LendingTx} {x : ℚ}
    (h : l.runIn' txs = some (l', x)) : l.ReachableFromIn txs l' x := by
  induction txs generalizing l l' x with
  | nil =>
    simp only [LendingLedger.runIn', Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact .refl
  | cons tx txs ih =>
    unfold LendingLedger.runIn' at h
    split at h
    · rename_i l₁ hl₁
      obtain ⟨⟨l₂, x₂⟩, h₂, heq⟩ := Option.map_eq_some_iff.mp h
      simp only [Prod.mk.injEq] at heq
      obtain ⟨rfl, rfl⟩ := heq
      exact LendingLedger.ReachableFromIn.cons hl₁ (ih h₂)
    · cases h

/-- The run of `CoarsenedVault.lean` with broker 1's cover at the Open limit, ending in the default of loan B. -/
private def cvTxs : List LendingTx :=
  (cwTxs.set 4 (.loanBrokerCoverDeposit 1 (cwAmount 9000000000000000 (-1)))) ++ [.loanManage 1 .default]

/-- Every step succeeds and broker 1's cover ends above the Open limit plus the fees paid into it. -/
private def cvCheck : Bool :=
  match cwGenesis.runIn' cvTxs with
  | some (l, _) =>
    match l.broker? 1 with
    | some b => decide (l.openLimit + cwGenesis.coverFees 1 cvTxs < b.coverAvailable.toRat)
    | none => false
  | none => false

private lemma cvCheck_true : cvCheck = true := by native_decide

/-- A run from a new vault can take a broker's cover past the Open zone. The default on the coarsened vault pays
the vault a cover of −0.9, which C++ rejects with tecINTERNAL (FV_M4_27). -/
lemma LendingLedger.cover_within_open_zone_witness :
    ∃ (genesis l : LendingLedger) (txs : List LendingTx) (x : ℚ) (j : Nat) (b : LoanBroker), genesis.Genesis ∧
      genesis.ReachableFromIn txs l x ∧ l.broker? j = some b ∧
      ¬ b.coverAvailable.toRat ≤ l.openLimit + genesis.coverFees j txs := by
  have h := cvCheck_true
  unfold cvCheck at h
  split at h
  · rename_i l x hrun
    split at h
    · rename_i b hb
      exact ⟨cwGenesis, l, cvTxs, x, 1, b, cwGenesis_genesis, LendingLedger.runIn'_reachableFromIn hrun, hb,
        not_le.mpr (of_decide_eq_true h)⟩
    · cases h
  · cases h

end XRPL.Model.Lending
