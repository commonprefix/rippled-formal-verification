import Batteries.Tactic.OpenPrivate
import XRPL.Properties.Lending.Ledger.Common.CoverWitness

/-! # A full clawback that leaves CoverAvailable below the minimum cover

A full cover clawback past `10^16` base units rounds up and leaves CoverAvailable below the minimum cover (FV_M3_2). -/

set_option linter.style.native false

namespace XRPL.Model.Lending

open XRPL.Model.Protocol

open private rcGenesis rcTxs rcGenesis_genesis from XRPL.Properties.Lending.Ledger.Common.CoverWitness

/-- A full clawback of broker 0's cover at the end of the run succeeds and leaves it below the minimum cover. -/
private def ccCheck : Bool :=
  match rcGenesis.run rcTxs with
  | .ok l =>
    match l.broker? 0, (l.apply (.loanBrokerCoverClawback 0 none)).run with
    | some b, .ok (.ok l') =>
      match l'.broker? 0, (b.coverClawback l.vault none).run,
          minimumBrokerCover b.numericType b.debtTotal b.coverRateMinimum l.vault.baseExponent with
      | some b', .ok (.ok _), .ok m => decide (b'.coverAvailable.toRat < m.toRat)
      | _, _, _ => false
    | _, _ => false
  | .error _ => false

private lemma ccCheck_true : ccCheck = true := by native_decide

/-- Proof body of `Lending.coverClawback_minimum_attained`. -/
lemma LendingLedger.coverClawback_minimum_witness :
    ∃ (l l' : LendingLedger) (j : Nat) (amount : Option STAmount) (b b' : LoanBroker) (r : LoanBrokerCoverResult)
      (m : Number), l.Reachable ∧ (l.apply (.loanBrokerCoverClawback j amount)).run = .ok (.ok l') ∧
      l.broker? j = some b ∧ l'.broker? j = some b' ∧ (b.coverClawback l.vault amount).run = .ok (.ok r) ∧
      minimumBrokerCover b.numericType b.debtTotal b.coverRateMinimum l.vault.baseExponent = .ok m ∧
      (amount = none ∨ ∃ a, amount = some a ∧ a.isZero = true) ∧ b'.coverAvailable.toRat < m.toRat := by
  have h := ccCheck_true
  unfold ccCheck at h
  split at h
  · rename_i l hl
    split at h
    · rename_i b l' hb hl'
      split at h
      · rename_i b' r m hb' hr hm
        exact ⟨l, l', 0, none, b, b', r, m, LendingLedger.Reachable.of_run rcGenesis_genesis hl, hl', hb, hb', hr,
          hm, Or.inl rfl, of_decide_eq_true h⟩
      · cases h
    · cases h
  · cases h

end XRPL.Model.Lending
