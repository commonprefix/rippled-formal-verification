import XRPL.Properties.Lending.Loan.Common.DeleteWitness

/-! # A LoanDelete of a pending loan on a coarsened vault

On the coarsened run of `DeleteWitness.lean` a LoanDelete of the pending loan E of 0.6 credits AssetsAvailable
with 1. -/

set_option linter.style.nativeDecide false

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault (Vault)

open private dwTxs from XRPL.Properties.Lending.Loan.Common.DeleteWitness

/-- The LoanDelete of pending loan E succeeds and moves AssetsAvailable by other than its principal. -/
private def adDeleteCheck : Bool :=
  match cwGenesis.run dwTxs with
  | .ok l =>
    match (l.apply (.loanDelete 3)).run, l.loan? 3 with
    | .ok (.ok l'), some e =>
      match l.broker? e.brokerIndex with
      | some b =>
        match e.loan.withBroker b with
        | .ok loan => loan.isPending && decide (l'.vault.assetsAvailable.toRat - l.vault.assetsAvailable.toRat ≠
            loan.principalOutstanding.toRat)
        | .error _ => false
      | none => false
    | _, _ => false
  | .error _ => false

private lemma adDeleteCheck_true : adDeleteCheck = true := by native_decide

/-- Proof body of `deletePending_principal_attained`. -/
lemma LendingLedger.deletePending_principal_witness :
    ∃ (l l' : LendingLedger) (i : Nat) (loan : Loan),
      l.Reachable ∧ (l.apply (.loanDelete i)).run = .ok (.ok l') ∧ l.LoanAt i loan ∧ loan.isPending = true ∧
      l'.vault.assetsAvailable.toRat - l.vault.assetsAvailable.toRat ≠ loan.principalOutstanding.toRat := by
  have h := adDeleteCheck_true
  unfold adDeleteCheck at h
  split at h
  case h_2 => cases h
  rename_i l hl
  split at h
  case h_2 => cases h
  rename_i l' e hl' he
  split at h
  case h_2 => cases h
  rename_i b hb
  split at h
  case h_2 => cases h
  rename_i loan hw
  simp only [Bool.and_eq_true] at h
  exact ⟨l, l', 3, loan, LendingLedger.Reachable.of_run cwGenesis_genesis hl, hl', ⟨e, b, he, hb, hw⟩, h.1,
    of_decide_eq_true h.2⟩

end XRPL.Model.Lending
