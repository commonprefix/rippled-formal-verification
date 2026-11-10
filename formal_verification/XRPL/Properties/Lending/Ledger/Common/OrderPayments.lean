import XRPL.Properties.Lending.Ledger.Common.OrderWitness

/-! # Witness for the order of two payments

A payment sends the management fee to the broker's cover while the cover is below its minimum, read from the
DebtTotal before the payment. Paying the larger loan first drops the minimum, so the other fee goes to the
owner. Checked by `native_decide`. -/

set_option linter.style.nativeDecide false

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault (Vault RawVault)

/-- A loan of one payment of TotalValueOutstanding with no interest and the given management fee, due at
1060. -/
private def opLoan (broker : LoanBroker) (principal fee total : Number) : RawLoan :=
  { broker := broker
    rates := { interestRate := 0, lateInterestRate := 0, closeInterestRate := 0, overpaymentInterestRate := 0
               overpaymentFee := 0 }
    fees := { originationFee := Number.zero, serviceFee := Number.zero, latePaymentFee := Number.zero
              closePaymentFee := Number.zero }
    schedule := { paymentInterval := 60, paymentTotal := 1, gracePeriod := 60, startDate := 1000 }
    paymentRemaining := 1, periodicPayment := total, principalOutstanding := principal
    totalValueOutstanding := total, managementFeeOutstanding := fee, loanScale := 0
    previousPaymentDueDate := 0, nextPaymentDueDate := 1060
    isPending := false, isImpaired := false, isDefault := false, allowsOverpayment := false }

/-- AssetsAvailable 9000 and 1000 lent out, at scale `10^0`. -/
private def opVault : Vault :=
  ⟨owVault 0 ⟨false, 9000000000000000000, -15⟩ ⟨false, 1000000000000000000, -15⟩ Number.zero,
    by native_decide, by native_decide⟩

/-- DebtTotal 1000 and cover 50, below the minimum 100 of a 10% CoverRateMinimum. -/
private def opBroker : LoanBroker :=
  ⟨owBroker 10000 10000 ⟨false, 1000000000000000000, -15⟩ ⟨false, 5000000000000000000, -17⟩ 2,
    by native_decide, by native_decide⟩

/-- A loan of 100 with a management fee of 10. -/
private def opLoanA : Loan :=
  ⟨opLoan opBroker ⟨false, 1000000000000000000, -16⟩ ⟨false, 1000000000000000000, -17⟩
    ⟨false, 1100000000000000000, -16⟩, by native_decide, by native_decide⟩

/-- A loan of 900 with a management fee of 10. -/
private def opLoanB : Loan :=
  ⟨opLoan opBroker ⟨false, 9000000000000000000, -16⟩ ⟨false, 1000000000000000000, -17⟩
    ⟨false, 9100000000000000000, -16⟩, by native_decide, by native_decide⟩

/-- Both loans on broker 0, before their due date at close time 1030. -/
private def opLedger : LendingLedger :=
  { vault := opVault, shares := [⟨false, 1000000000000000000, -15⟩], brokers := [some opBroker]
    loans := [some ⟨0, opLoanA⟩, some ⟨0, opLoanB⟩], now := 1030 }

/-- The payment of loan A, 110. -/
private def opAmountA : Number := ⟨false, 1100000000000000000, -16⟩

/-- The payment of loan B, 910. -/
private def opAmountB : Number := ⟨false, 9100000000000000000, -16⟩

/-- The broker's CoverAvailable after the two payments differs between the orders. -/
private def paymentsCheck : Bool :=
  match (opLedger.apply (.loanPay 0 .regular opAmountA)).run, (opLedger.apply (.loanPay 1 .regular opAmountB)).run with
  | .ok (.ok la), .ok (.ok lb) =>
    match (la.apply (.loanPay 1 .regular opAmountB)).run, (lb.apply (.loanPay 0 .regular opAmountA)).run with
    | .ok (.ok lab), .ok (.ok lba) =>
      match lab.broker? 0, lba.broker? 0 with
      | some b, some b' => decide (b.coverAvailable.toRat ≠ b'.coverAvailable.toRat)
      | _, _ => false
    | _, _ => false
  | _, _ => false

private lemma paymentsCheck_true : paymentsCheck = true := by native_decide

/-- Payments of loans 100 and 900 on one broker with DebtTotal 1000, cover 50 and a 10% CoverRateMinimum. Paying
A first leaves the minimum at 90, so both fees go to cover (70). Paying B first drops it to 10, so cover ends at 60. -/
lemma LendingLedger.payments_comm_witness :
    ∃ (l la lb lab lba : LendingLedger) (i j : Nat) (a a' : Number) (k : Nat) (b b' : LoanBroker), i ≠ j ∧
      (l.apply (.loanPay i .regular a)).run = .ok (.ok la) ∧ (la.apply (.loanPay j .regular a')).run = .ok (.ok lab) ∧
      (l.apply (.loanPay j .regular a')).run = .ok (.ok lb) ∧ (lb.apply (.loanPay i .regular a)).run = .ok (.ok lba) ∧
      lab.broker? k = some b ∧ lba.broker? k = some b' ∧ b.coverAvailable.toRat ≠ b'.coverAvailable.toRat := by
  have h := paymentsCheck_true
  unfold paymentsCheck at h
  split at h
  · rename_i la lb ha hb
    split at h
    · rename_i lab lba hab hba
      split at h
      · rename_i b b' hb₁ hb₂
        exact ⟨_, la, lb, lab, lba, 0, 1, _, _, 0, b, b', by decide, ha, hab, hb, hba, hb₁, hb₂,
          of_decide_eq_true h⟩
      · exact absurd h (by decide)
    · exact absurd h (by decide)
  · exact absurd h (by decide)

end XRPL.Model.Lending
