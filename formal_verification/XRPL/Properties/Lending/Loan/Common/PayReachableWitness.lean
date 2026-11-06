import XRPL.Properties.Lending.Ledger.Common.CoarsenedVault
import XRPL.Properties.Lending.Loan.Common.PayDefs

/-! # Witnesses for the LoanPay bounds on a reachable ledger

Runs from a new IOU vault at Scale 1, checked by `native_decide`. A loan of `603946999675283.3` paid 32 years late
takes AssetsAvailable and a broker's cover past `10^16` base units. -/

set_option linter.style.nativeDecide false

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault (Vault RawVault)

/-- The loan at `i` read with its broker's ledger copy, as every loan transaction reads it. -/
private def LendingLedger.loanAt? (l : LendingLedger) (i : Nat) : Option Loan :=
  match l.loan? i with
  | some e =>
    match l.broker? e.brokerIndex with
    | some b =>
      match e.loan.withBroker b with
      | .ok loan => some loan
      | .error _ => none
    | none => none
  | none => none

private lemma LendingLedger.loanAt?_spec {l : LendingLedger} {i : Nat} {loan : Loan} (h : l.loanAt? i = some loan) :
    l.LoanAt i loan := by
  unfold LendingLedger.loanAt? at h
  split at h
  · rename_i e he
    split at h
    · rename_i b hb
      split at h
      · rename_i loan' hw
        obtain rfl := Option.some.inj h
        exact ⟨e, b, he, hb, hw⟩
      · cases h
    · cases h
  · cases h

/-- The payment of exactly the first instalment's totalDue at the ledger's close time, with its instalments and
its result. -/
private def LendingLedger.payDue (l : LendingLedger) (loan : Loan) (pt : LoanPaymentType) :
    Option (Number × UnsettledPayment Vault × LoanWithAmounts Vault) :=
  match loan.paymentComponents pt l.now with
  | .ok pc =>
    match pc.totalDue with
    | .ok due =>
      match (loan.payInstalments l.vault pt due l.now).run, (loan.pay l.vault pt due l.now).run with
      | .ok (.ok payment), .ok (.ok r) => some (due, payment, r)
      | _, _ => none
    | .error _ => none
  | .error _ => none

private lemma LendingLedger.payDue_spec {l : LendingLedger} {loan : Loan} {pt : LoanPaymentType} {due : Number}
    {payment : UnsettledPayment Vault} {r : LoanWithAmounts Vault} (h : l.payDue loan pt = some (due, payment, r)) :
    (loan.payInstalments l.vault pt due l.now).run = .ok (.ok payment) ∧
      (loan.pay l.vault pt due l.now).run = .ok (.ok r) := by
  unfold LendingLedger.payDue at h
  split at h
  · split at h
    · split at h
      · rename_i payment' r' hp hr
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        exact ⟨hp, hr⟩
      · cases h
    · cases h
  · cases h

/-- The given InterestRate and LateInterestRate, and no other rate. -/
private def pwRates (interestRate lateInterestRate : TenthBips32) : LoanRates :=
  { interestRate := interestRate, lateInterestRate := lateInterestRate, closeInterestRate := 0,
    overpaymentInterestRate := 0, overpaymentFee := 0 }

/-- A deposit of `603953705712463.7`, a broker with no fee and no cover, and the loan of `603946999675283.3` at
0.964% over 7 monthly payments with a 100% late rate, at close time `1001`. AssetsAvailable is left `6706037180.4`. -/
private def pwLoanTxs : List LendingTx :=
  [.vaultDeposit 0 (cwAmount 6039537057124637 (-1)) false,
   .close 1001,
   .loanBrokerCreate ⟨none, none, none, none⟩,
   .loanSet 0 ⟨false, 6039469996752833000, -4⟩ (pwRates 964 100000) cwFees (some 2592000) (some 7) (some 60) 0
     false false]

/-- The first due date of the loan. -/
private def pwDue : UInt32 := 1001 + 2592000

/-- At the first due date, the first instalment credits the vault exactly principalPaid + interestPaid. -/
private def pwEqualCheck : Bool :=
  match cwGenesis.run (pwLoanTxs ++ [.close pwDue]) with
  | .ok l =>
    match l.loanAt? 0 with
    | some loan =>
      match l.payDue loan .regular with
      | some (_, payment, r) =>
        match payment.amounts.principalPaid.operator_add payment.amounts.interestPaid .to_nearest with
        | .ok w =>
          decide w.isNormalized &&
            decide (w.toRat = payment.amounts.principalPaid.toRat + payment.amounts.interestPaid.toRat) &&
            decide ((r.pool'.assetsAvailable.toRat - l.vault.assetsAvailable.toRat) -
              (payment.amounts.principalPaid.toRat + payment.amounts.interestPaid.toRat) = 0) &&
            decide (r.pool'.toExact.assetsTotal -
              (l.vault.toExact.assetsTotal + payment.amounts.interestPaid.toRat) = 0)
        | .error _ => false
      | none => false
    | none => false
  | .error _ => false

private lemma pwEqualCheck_true : pwEqualCheck = true := by native_decide

private lemma pwEqual :
    ∃ (l : LendingLedger) (i : Nat) (loan : Loan) (paymentType : LoanPaymentType) (amount : Number)
      (r : LoanWithAmounts Vault) (payment : UnsettledPayment Vault),
      l.Reachable ∧ l.LoanAt i loan ∧
      (loan.payInstalments l.vault paymentType amount l.now).run = .ok (.ok payment) ∧
      (loan.pay l.vault paymentType amount l.now).run = .ok (.ok r) ∧
      (∃ w : Number, w.isNormalized ∧
        w.toRat = payment.amounts.principalPaid.toRat + payment.amounts.interestPaid.toRat) ∧
      (r.pool'.assetsAvailable.toRat - l.vault.assetsAvailable.toRat) -
        (payment.amounts.principalPaid.toRat + payment.amounts.interestPaid.toRat) = 0 ∧
      r.pool'.toExact.assetsTotal - (l.vault.toExact.assetsTotal + payment.amounts.interestPaid.toRat) = 0 := by
  have h := pwEqualCheck_true
  unfold pwEqualCheck at h
  split at h
  · rename_i l hl
    split at h
    · rename_i loan hloan
      split at h
      · rename_i due payment r hpd
        split at h
        · rename_i w _
          simp only [Bool.and_eq_true, decide_eq_true_eq] at h
          obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
          obtain ⟨hp, hr⟩ := LendingLedger.payDue_spec hpd
          exact ⟨l, 0, loan, .regular, due, r, payment, LendingLedger.Reachable.of_run cwGenesis_genesis hl,
            LendingLedger.loanAt?_spec hloan, hp, hr, ⟨w, h1, h2⟩, h3, h4⟩
        · cases h
      · cases h
    · cases h
  · cases h

/-- A payment on a reachable ledger can credit the vault exactly principalPaid + interestPaid. The first
instalment of the loan of `603946999675283.3`, paid at its due date. -/
lemma Loan.payment_vault_upper_bound_witness :
    ∃ (l : LendingLedger) (i : Nat) (loan : Loan) (paymentType : LoanPaymentType) (amount : Number)
      (r : LoanWithAmounts Vault) (payment : UnsettledPayment Vault),
      l.Reachable ∧ l.LoanAt i loan ∧
      (loan.payInstalments l.vault paymentType amount l.now).run = .ok (.ok payment) ∧
      (loan.pay l.vault paymentType amount l.now).run = .ok (.ok r) ∧
      (∃ w : Number, w.isNormalized ∧
        w.toRat = payment.amounts.principalPaid.toRat + payment.amounts.interestPaid.toRat) ∧
      (r.pool'.assetsAvailable.toRat - l.vault.assetsAvailable.toRat) -
        (payment.amounts.principalPaid.toRat + payment.amounts.interestPaid.toRat) = 0 := by
  obtain ⟨l, i, loan, pt, amount, r, payment, h1, h2, h3, h4, h5, h6, -⟩ := pwEqual
  exact ⟨l, i, loan, pt, amount, r, payment, h1, h2, h3, h4, h5, h6⟩

/-- About 32 years after the first due date. -/
private def pwLate : UInt32 := pwDue + 1014453797

/-- A deposit of `603963705712463.7`, a broker with a 10% management fee that needs 0.001% cover, a cover of
`6039569997.2`, the large loan and a loan of `10^10`. The default of the second loan leaves the cover at `0.5`. -/
private def pwCoverTxs : List LendingTx :=
  [.vaultDeposit 0 (cwAmount 6039637057124637 (-1)) false,
   .close 1001,
   .loanBrokerCreate ⟨none, some 10000, some 1, some 100000⟩,
   .loanBrokerCoverDeposit 0 (cwAmount 6039569997200000 (-6)),
   .loanSet 0 ⟨false, 6039469996752833000, -4⟩ (pwRates 964 100000) cwFees (some 2592000) (some 7) (some 60) 0
     false false,
   .loanSet 0 ⟨false, 1000000000000000000, -8⟩ (pwRates 0 0) cwFees (some 2592000) (some 1) (some 60) 0
     false false,
   .close (pwDue + 61),
   .loanManage 1 .default]

end XRPL.Model.Lending
