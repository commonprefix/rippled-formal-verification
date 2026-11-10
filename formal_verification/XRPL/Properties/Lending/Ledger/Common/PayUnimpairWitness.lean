import XRPL.Properties.Lending.Ledger.Common.CoarsenedVault

/-! # A late payment on an impaired loan three instalments behind

A run from a new IOU vault at Scale 1, checked by `native_decide`. The loan is impaired with three instalments
overdue, and one late payment clears the impairment while the loan stays two instalments behind. -/

set_option linter.style.nativeDecide false

namespace XRPL.Model.Lending

open XRPL.Model.Protocol

/-- 10% yearly interest and no late interest. -/
private def puRates : LoanRates :=
  { interestRate := 10000, lateInterestRate := 0, closeInterestRate := 0, overpaymentInterestRate := 0,
    overpaymentFee := 0 }

/-- A deposit of 1000, a broker, a loan of 100 with 5 payments 30 days apart from time 1001, a close at 7800000
past three due dates, then the impairment. -/
private def puTxs : List LendingTx :=
  [.vaultDeposit 0 (cwAmount 1000000000000000 (-12)) false,
   .close 1001,
   .loanBrokerCreate ⟨none, none, none, none⟩,
   .loanSet 0 ⟨false, 1000000000000000000, -16⟩ puRates cwFees (some 2592000) (some 5) (some 60) 0 false false,
   .close 7800000,
   .loanManage 0 .impair]

/-- One instalment, `20.5`. -/
private def puAmount : Number := ⟨false, 2050000000000000000, -17⟩

/-- The late payment of loan 0 after `puTxs`: the loan before is impaired three instalments behind, and the loan
after has payments left, is not impaired and is still late. -/
private def puCheck : Bool :=
  match cwGenesis.run puTxs with
  | .ok l =>
    match l.loan? 0 with
    | some e =>
      match l.broker? e.brokerIndex with
      | some b =>
        match e.loan.withBroker b with
        | .ok loan =>
          match (l.apply (.loanPay 0 .late puAmount)).run with
          | .ok (.ok l') =>
            match l'.loan? 0 with
            | some e' =>
              match l'.broker? e'.brokerIndex with
              | some b' =>
                match e'.loan.withBroker b' with
                | .ok loan' =>
                  loan.isImpaired && decide (loan'.paymentRemaining ≠ 0) &&
                    decide (loan.nextPaymentDueDate.toNat + 2 * loan.schedule.paymentInterval.toNat <
                      l.now.toNat) &&
                    !loan'.isImpaired && loan'.isPaymentLate l'.now
                | .error _ => false
              | none => false
            | none => false
          | _ => false
        | .error _ => false
      | none => false
    | none => false
  | .error _ => false

private lemma puCheck_true : puCheck = true := by native_decide

/-- A reachable late payment on an impaired loan three instalments behind that leaves it not impaired but late. -/
lemma LendingLedger.pay_unimpairs_only_current_witness :
    ∃ (l l' : LendingLedger) (i : Nat) (paymentType : LoanPaymentType) (amount : Number) (loan loan' : Loan),
      l.Reachable ∧ (l.apply (.loanPay i paymentType amount)).run = .ok (.ok l') ∧ l.LoanAt i loan ∧
      l'.LoanAt i loan' ∧ loan.isImpaired = true ∧ loan'.paymentRemaining ≠ 0 ∧
      loan.nextPaymentDueDate.toNat + 2 * loan.schedule.paymentInterval.toNat < l.now.toNat ∧
      loan'.isImpaired = false ∧ loan'.isPaymentLate l'.now = true := by
  have h := puCheck_true
  unfold puCheck at h
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
  rename_i l' hl'
  split at h
  case h_2 => cases h
  rename_i e' he'
  split at h
  case h_2 => cases h
  rename_i b' hb'
  split at h
  case h_2 => cases h
  rename_i loan' hw'
  simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨himp, hrem⟩, hbehind⟩, himp'⟩, hlate⟩ := h
  exact ⟨l, l', 0, .late, puAmount, loan, loan', LendingLedger.Reachable.of_run cwGenesis_genesis hl, hl',
    ⟨e, b, he, hb, hw⟩, ⟨e', b', he', hb', hw'⟩, himp, hrem, hbehind, himp', hlate⟩

end XRPL.Model.Lending
