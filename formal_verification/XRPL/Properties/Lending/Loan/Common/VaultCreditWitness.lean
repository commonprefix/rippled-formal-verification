import XRPL.Properties.Lending.Loan.Common.PayLedgerWitness

/-! # Witness for what a regular payment credits a coarsened vault

The coarsened run of `PayLedgerWitness`, then loan D's final regular payment, checked by `native_decide`. -/

set_option linter.style.nativeDecide false

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault (Vault)

open private plYieldTxs plPay plPay_spec from XRPL.Properties.Lending.Loan.Common.PayLedgerWitness

/-- Loan D's regular payment of 1.9 takes 1.9 off TotalValueOutstanding and nothing off ManagementFeeOutstanding,
but the coarsened vault gets only 1. -/
private def vcCoarsenedCheck : Bool :=
  match cwGenesis.run plYieldTxs with
  | .ok l =>
    match plPay l 3 .regular ⟨false, 1900000000000000000, -18⟩ with
    | some (loan, l', loan', _) =>
      decide (l'.vault.assetsAvailable.toRat - l.vault.assetsAvailable.toRat <
        (loan.totalValueOutstanding.toRat - loan'.totalValueOutstanding.toRat) -
          (loan.managementFeeOutstanding.toRat - loan'.managementFeeOutstanding.toRat))
    | none => false
  | .error _ => false

private lemma vcCoarsenedCheck_true : vcCoarsenedCheck = true := by native_decide

/-- A regular LoanPay on a reachable coarsened vault can credit it less than the loan's books drop. Loan D's
instalment of 1.9 is credited as 1. -/
lemma LendingLedger.payment_vault_credit_coarsened_witness :
    ∃ (l l' : LendingLedger) (i : Nat) (amount : Number) (loan loan' : Loan),
      l.Reachable ∧ (l.apply (.loanPay i .regular amount)).run = .ok (.ok l') ∧ l.LoanAt i loan ∧
      l'.LoanAt i loan' ∧
      l'.vault.assetsAvailable.toRat - l.vault.assetsAvailable.toRat <
        (loan.totalValueOutstanding.toRat - loan'.totalValueOutstanding.toRat) -
          (loan.managementFeeOutstanding.toRat - loan'.managementFeeOutstanding.toRat) := by
  have h := vcCoarsenedCheck_true
  unfold vcCoarsenedCheck at h
  split at h
  · rename_i l hl
    split at h
    · rename_i loan l' loan' p hpay
      obtain ⟨hap, hat, hat', -⟩ := plPay_spec hpay
      exact ⟨l, l', 3, _, loan, loan', LendingLedger.Reachable.of_run cwGenesis_genesis hl, hap, hat, hat',
        of_decide_eq_true h⟩
    · cases h
  · cases h

end XRPL.Model.Lending
