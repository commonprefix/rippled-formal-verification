import XRPL.Properties.Lending.Ledger.Common.LoanPayoff
import XRPL.Properties.Lending.Ledger.Common.ShareValueWitness

/-! # Payments of loan D on the coarsened vault

The run `svTxs` coarsens the vault after loan D of 3 is created. Each instalment of 1.5 without interest is
credited on the coarser grid as 1, so the share value falls and the payoff returns 2 of the 3. -/

set_option linter.style.nativeDecide false

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault (Vault RawVault)

/-- `1.5`. -/
private def pwInstalment : Number := ⟨false, 1500000000000000000, -18⟩

/-- Loan D's late instalment of 1.5 on the coarsened run lowers the share value. -/
private def paymentCheck : Bool :=
  match cwGenesis.run svTxs with
  | .ok l =>
    match l.loan? 3 with
    | some e =>
      match l.broker? e.brokerIndex with
      | some b =>
        match e.loan.withBroker b with
        | .ok loan =>
          match (loan.payInstalments l.vault .late pwInstalment l.now).run,
              (l.apply (.loanPay 3 .late pwInstalment)).run with
          | .ok (.ok _), .ok (.ok l') => decide (l'.vault.toRawVault.shareValue < l.vault.toRawVault.shareValue)
          | _, _ => false
        | .error _ => false
      | none => false
    | none => false
  | .error _ => false

private lemma paymentCheck_true : paymentCheck = true := by native_decide

/-- A payment on a reachable coarsened vault can lower the share value. Loan D's instalment of 1.5 is credited
as 1. -/
lemma LendingLedger.payment_share_value_falls_reachable :
    ∃ (l l' : LendingLedger) (i : Nat) (paymentType : LoanPaymentType) (amount : Number) (loan : Loan)
      (payment : UnsettledPayment Vault),
      l.Reachable ∧ (l.apply (.loanPay i paymentType amount)).run = .ok (.ok l') ∧ l.LoanAt i loan ∧
      (loan.payInstalments l.vault paymentType amount l.now).run = .ok (.ok payment) ∧
      l'.vault.toRawVault.shareValue < l.vault.toRawVault.shareValue := by
  have h := paymentCheck_true
  unfold paymentCheck at h
  split at h
  case h_2 => cases h
  rename_i l hl
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
  rename_i payment l' hpay hl'
  exact ⟨l, l', 3, .late, pwInstalment, loan, payment, LendingLedger.Reachable.of_run cwGenesis_genesis hl, hl',
    ⟨e, b, he, hb, hw⟩, hpay, of_decide_eq_true h⟩

/-- Loan D's two instalments of 1.5 on the coarsened run pay it off but add only 2 to AssetsAvailable. -/
private def payoffCheck : Bool :=
  match cwGenesis.run svTxs with
  | .ok l₀ =>
    match l₀.loan? 3 with
    | some e =>
      match l₀.broker? e.brokerIndex with
      | some b =>
        match e.loan.withBroker b with
        | .ok loan₀ =>
          match (l₀.apply (.loanPay 3 .late pwInstalment)).run with
          | .ok (.ok l₁) =>
            match (l₁.apply (.loanPay 3 .regular pwInstalment)).run with
            | .ok (.ok l₂) =>
              (match l₂.loan? 3 with | some e₂ => e₂.loan.paymentRemaining == 0 | none => false) &&
                decide (0 + (l₁.vault.assetsAvailable.toRat - l₀.vault.assetsAvailable.toRat) +
                  (l₂.vault.assetsAvailable.toRat - l₁.vault.assetsAvailable.toRat) <
                    loan₀.principalOutstanding.toRat)
            | _ => false
          | _ => false
        | .error _ => false
      | none => false
    | none => false
  | .error _ => false

private lemma payoffCheck_true : payoffCheck = true := by native_decide

/-- A loan on a reachable coarsened vault whose payoff returns less than its principal. Loan D of 3 is paid off
by two instalments of 1.5, each credited as 1. -/
lemma LendingLedger.payoff_short_run_reachable :
    ∃ (l₀ : LendingLedger) (i : Nat) (loan₀ : Loan) (l : LendingLedger) (paid : ℚ),
      l₀.Reachable ∧ l₀.LoanAt i loan₀ ∧ l₀.PaysLoan i (fun _ _ _ => True) l paid ∧
      (∃ e, l.loan? i = some e ∧ e.loan.paymentRemaining = 0) ∧ paid < loan₀.principalOutstanding.toRat := by
  have h := payoffCheck_true
  unfold payoffCheck at h
  split at h
  case h_2 => cases h
  rename_i l₀ hl₀
  split at h
  case h_2 => cases h
  rename_i e he
  split at h
  case h_2 => cases h
  rename_i b hb
  split at h
  case h_2 => cases h
  rename_i loan₀ hw
  split at h
  case h_2 => cases h
  rename_i l₁ hl₁
  split at h
  case h_2 => cases h
  rename_i l₂ hl₂
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨hpaid, hsum⟩ := h
  refine ⟨l₀, 3, loan₀, l₂, _, LendingLedger.Reachable.of_run cwGenesis_genesis hl₀, ⟨e, b, he, hb, hw⟩,
    .pay .regular pwInstalment (.pay .late pwInstalment .refl trivial hl₁) trivial hl₂, ?_, hsum⟩
  split at hpaid
  · rename_i e₂ he₂; exact ⟨e₂, he₂, by simpa using hpaid⟩
  · cases hpaid

end XRPL.Model.Lending
