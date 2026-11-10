import XRPL.Properties.Lending.Ledger.Common.CoarsenedVault

/-! # A LoanAccept from a broker below minCover

A default of an active loan takes the cover a pending loan of the same broker was checked against, and the pending
loan is then accepted with the broker below minCover. -/

set_option linter.style.nativeDecide false

namespace XRPL.Model.Lending

open XRPL.Model.Protocol

/-- A deposit of 10000, a broker at 10% minimum cover and 100% liquidation with 100 of cover, an active loan A of 600,
a pending loan B of 400 that starts 10 days later, a close past the grace period of A and the default of A. -/
private def acTxs : List LendingTx :=
  [.vaultDeposit 0 (cwAmount 1000000000000000 (-11)) false,
   .close 1001,
   .loanBrokerCreate ⟨none, none, some 10000, some 100000⟩,
   .loanBrokerCoverDeposit 0 (cwAmount 1000000000000000 (-13)),
   .loanSet 0 ⟨false, 6000000000000000000, -16⟩ (cwRates 0) cwFees (some 86400) (some 1) (some 60) 0 false false,
   .loanSet 0 ⟨false, 4000000000000000000, -16⟩ (cwRates 0) cwFees (some 86400) (some 1) (some 60) 865001 true
     false,
   .close 100000,
   .loanManage 0 .default]

/-- The loan at `i` on `l`, read with its broker, has a broker below minCover. -/
private def belowCheck (l : LendingLedger) (i : Nat) : Bool :=
  match l.loan? i with
  | some e =>
    match l.broker? e.brokerIndex with
    | some b =>
      match e.loan.withBroker b with
      | .ok loan =>
        match loan.broker.hasMinimumCover l.vault.baseExponent with
        | .ok covered => !covered
        | .error _ => false
      | .error _ => false
    | none => false
  | none => false

private lemma below_of_check {l : LendingLedger} {i : Nat} (h : belowCheck l i = true) :
    ∃ loan, l.LoanAt i loan ∧ loan.broker.hasMinimumCover l.vault.baseExponent = .ok false := by
  unfold belowCheck at h
  split at h
  case h_2 => cases h
  rename_i e he
  split at h
  case h_2 => cases h
  rename_i b hb
  split at h
  case h_2 => cases h
  rename_i loan hw
  split at h
  case h_2 => cases h
  rename_i covered hc
  simp only [Bool.not_eq_eq_eq_not, Bool.not_true] at h
  exact ⟨loan, ⟨e, b, he, hb, hw⟩, h ▸ hc⟩

/-- The LoanAccept of loan B succeeds, and its broker is below minCover before and after it. -/
private def acCheck : Bool :=
  match cwGenesis.run acTxs with
  | .ok l =>
    match (l.apply (.loanAccept 1)).run with
    | .ok (.ok l') => belowCheck l 1 && belowCheck l' 1
    | _ => false
  | .error _ => false

private lemma acCheck_true : acCheck = true := by native_decide

/-- Proof body of `accept_keeps_minimum_cover_attained`. -/
lemma LendingLedger.accept_keeps_minimum_cover_witness :
    ∃ (l l' : LendingLedger) (i : Nat) (loan loan' : Loan),
      l.Reachable ∧ (l.apply (.loanAccept i)).run = .ok (.ok l') ∧ l.LoanAt i loan ∧ l'.LoanAt i loan' ∧
      loan.broker.hasMinimumCover l.vault.baseExponent = .ok false ∧
      loan'.broker.hasMinimumCover l'.vault.baseExponent = .ok false := by
  have h := acCheck_true
  unfold acCheck at h
  split at h
  case h_2 => cases h
  rename_i l hl
  split at h
  case h_2 => cases h
  rename_i l' hl'
  simp only [Bool.and_eq_true] at h
  obtain ⟨loan, hat, hc⟩ := below_of_check h.1
  obtain ⟨loan', hat', hc'⟩ := below_of_check h.2
  exact ⟨l, l', 1, loan, loan', LendingLedger.Reachable.of_run cwGenesis_genesis hl, hl', hat, hat', hc, hc'⟩

end XRPL.Model.Lending
