import XRPL.Properties.Lending.Ledger.Common.CoarsenedVault

/-! # A full payment before StartDate pays no interest

A run from a new IOU vault at Scale 1, checked by `native_decide`. A two-step loan of 100 at 10% is accepted on day
0 with StartDate on day 30, so LoanAccept pays the principal out at once. On day 29 a full payment pays it off with
no interest, since the interest accrues only from StartDate. -/

set_option linter.style.nativeDecide false

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault (Vault)

/-- 10% yearly interest and no other rate. -/
private def fsRates : LoanRates :=
  { interestRate := 10000, lateInterestRate := 0, closeInterestRate := 0, overpaymentInterestRate := 0,
    overpaymentFee := 0 }

/-- A deposit of 1000, a broker, at time 1001 a two-step loan of 100 in 12 payments 30 days apart with StartDate
30 days later, its LoanAccept at time 1001, then a close 29 days later. -/
private def fsTxs : List LendingTx :=
  [.vaultDeposit 0 (cwAmount 1000000000000000 (-12)) false,
   .close 1001,
   .loanBrokerCreate ⟨none, none, none, none⟩,
   .loanSet 0 ⟨false, 1000000000000000000, -16⟩ fsRates cwFees (some 2592000) (some 12) (some 60)
     (1001 + 2592000) true false,
   .loanAccept 0,
   .close (1001 + 2505600)]

/-- More than the loan's value, `200`. -/
private def fsAmount : Number := ⟨false, 2000000000000000000, -16⟩

/-- The full payment of loan 0 after `fsTxs`: the loan has an InterestRate and principal, now is before StartDate,
and the payment pays no interest. -/
private def fsCheck : Bool :=
  match cwGenesis.run fsTxs with
  | .ok l =>
    match l.loan? 0 with
    | some e =>
      match l.broker? e.brokerIndex with
      | some b =>
        match e.loan.withBroker b with
        | .ok loan =>
          match (l.apply (.loanPay 0 .full fsAmount)).run, (loan.payInstalments l.vault .full fsAmount l.now).run with
          | .ok (.ok _), .ok (.ok payment) =>
            decide (loan.rates.interestRate ≠ 0) && decide (0 < loan.principalOutstanding.toRat) &&
              decide (l.now < loan.schedule.startDate) && decide (payment.amounts.interestPaid.toRat = 0)
          | _, _ => false
        | .error _ => false
      | none => false
    | none => false
  | .error _ => false

private lemma fsCheck_true : fsCheck = true := by native_decide

/-- A reachable full payment before StartDate on a loan with an InterestRate and principal that pays no interest. -/
lemma LendingLedger.fullPayment_before_start_witness :
    ∃ (l l' : LendingLedger) (i : Nat) (amount : Number) (loan : Loan) (payment : UnsettledPayment Vault),
      l.Reachable ∧ (l.apply (.loanPay i .full amount)).run = .ok (.ok l') ∧ l.LoanAt i loan ∧
      (loan.payInstalments l.vault .full amount l.now).run = .ok (.ok payment) ∧
      loan.rates.interestRate ≠ 0 ∧ 0 < loan.principalOutstanding.toRat ∧ l.now < loan.schedule.startDate ∧
      payment.amounts.interestPaid.toRat = 0 := by
  have h := fsCheck_true
  unfold fsCheck at h
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
  rename_i l' payment hl' hpay
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨hrate, hprin⟩, hstart⟩, hint⟩ := h
  exact ⟨l, l', 0, fsAmount, loan, payment, LendingLedger.Reachable.of_run cwGenesis_genesis hl, hl',
    ⟨e, b, he, hb, hw⟩, hpay, hrate, hprin, hstart, hint⟩

end XRPL.Model.Lending
