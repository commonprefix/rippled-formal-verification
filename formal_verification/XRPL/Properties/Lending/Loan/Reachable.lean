import XRPL.Properties.Lending.Loan.Common.LifetimeLedger
import XRPL.Properties.Lending.Loan.Common.LifetimeWitness
import XRPL.Properties.Lending.Loan.Common.RegularPayoffLedger

/-! # Loan reachability

Every loan a ledger holds keeps the terms it was created with. `LendingLedger.Reaches l txs l'` is a
run of the transactions `txs` from `l` to `l'`, and the loan at slot `i` is read before the run in `l` and after it
in `l'`. -/

namespace XRPL.Model

open XRPL.Model.Protocol
open XRPL.Model.Lending
open XRPL.Model.SingleAssetVault (Vault)

/-- After create -> rates, fees, the schedule terms, LoanScale and the overpayment flag never change, and
PaymentRemaining and the outstanding amounts never increase. -/
theorem Lending.Reachable.loan_lifetime (l l' : LendingLedger) (txs : List LendingTx) (i : Nat) (loan loan' : Loan)
    (hrun : LendingLedger.Reaches l txs l') (hat : l.LoanAt i loan) (hat' : l'.LoanAt i loan') :
    (loan'.rates = loan.rates ∧ loan'.fees = loan.fees ∧ loan'.schedule.startDate = loan.schedule.startDate ∧
      loan'.schedule.paymentInterval = loan.schedule.paymentInterval ∧
      loan'.schedule.paymentTotal = loan.schedule.paymentTotal ∧
      loan'.schedule.gracePeriod = loan.schedule.gracePeriod ∧ loan'.loanScale = loan.loanScale ∧
      loan'.allowsOverpayment = loan.allowsOverpayment) ∧
    (loan'.paymentRemaining.toNat ≤ loan.paymentRemaining.toNat ∧
      loan'.principalOutstanding.toRat ≤ loan.principalOutstanding.toRat ∧
      loan'.totalValueOutstanding.toRat ≤ loan.totalValueOutstanding.toRat ∧
      loan'.managementFeeOutstanding.toRat ≤ loan.managementFeeOutstanding.toRat) :=
  ⟨LendingLedger.fixed_terms_proof l l' txs i loan loan' hrun hat hat',
    LendingLedger.outstanding_monotone_proof l l' txs i loan loan' hrun hat hat'⟩

/-- Any sequence of transactions from a reachable ledger -> a loan's interestDue never increases, where interestDue =
TotalValueOutstanding − PrincipalOutstanding − ManagementFeeOutstanding. -/
theorem Lending.Reachable.interest_monotone (l l' : LendingLedger) (txs : List LendingTx) (i : Nat) (loan loan' : Loan)
    (hr : l.Reachable) (hrun : LendingLedger.Reaches l txs l') (hat : l.LoanAt i loan) (hat' : l'.LoanAt i loan')
    -- in the run, a late payment with late interest takes nonnegative interest off the loan (FV_M4_30)
    (hlate : ∀ (pre : List LendingTx) (l₁ l₂ : LendingLedger) (amount : Number) (loan₁ : Loan)
      (pc : PaymentComponents) (d : Number), pre ++ [.loanPay i .late amount] <+: txs →
      LendingLedger.Reaches l pre l₁ → (l₁.apply (.loanPay i .late amount)).run = .ok (.ok l₂) →
      l₁.LoanAt i loan₁ → loan₁.rates.lateInterestRate ≠ 0 → loan₁.paymentComponents .late l₁.now = .ok pc →
      pc.interestDelta = .ok d → 0 ≤ d.toRat)
    -- in the run, the scheduled part of an overpayment with overpayment interest takes nonnegative interest off the
    -- loan (FV_M4_30)
    (hover : ∀ (pre : List LendingTx) (l₁ l₂ : LendingLedger) (amount : Number) (loan₁ : Loan)
      (p : UnsettledPayment Vault), pre ++ [.loanPay i .overpayment amount] <+: txs →
      LendingLedger.Reaches l pre l₁ → (l₁.apply (.loanPay i .overpayment amount)).run = .ok (.ok l₂) →
      l₁.LoanAt i loan₁ → loan₁.rates.overpaymentInterestRate ≠ 0 →
      (loan₁.payInstalments l₁.vault .regular amount l₁.now).run = .ok (.ok p) → 0 ≤ p.amounts.interestPaid.toRat) :
    loan'.toExact.interestDue ≤ loan.toExact.interestDue :=
  LendingLedger.interest_monotone_proof l l' txs i loan loan' hr hrun hat hat' hlate hover

/-- Witness: a run where interestDue rises without `hlate`. A late payment at a 100% LateInterestRate covers
the interest part of −3.24 of the third instalment, so interestDue rises by 3.24. -/
theorem Lending.Reachable.interest_monotone_late_attained :
    ∃ (l l' : LendingLedger) (txs : List LendingTx) (i : Nat) (loan loan' : Loan), l.Reachable ∧
      LendingLedger.Reaches l txs l' ∧ l.LoanAt i loan ∧ l'.LoanAt i loan' ∧
      (∀ (pre : List LendingTx) (l₁ l₂ : LendingLedger) (amount : Number) (loan₁ : Loan)
        (p : UnsettledPayment Vault), pre ++ [.loanPay i .overpayment amount] <+: txs →
        LendingLedger.Reaches l pre l₁ → (l₁.apply (.loanPay i .overpayment amount)).run = .ok (.ok l₂) →
        l₁.LoanAt i loan₁ → loan₁.rates.overpaymentInterestRate ≠ 0 →
        (loan₁.payInstalments l₁.vault .regular amount l₁.now).run = .ok (.ok p) →
        0 ≤ p.amounts.interestPaid.toRat) ∧
      loan.toExact.interestDue < loan'.toExact.interestDue :=
  LendingLedger.interest_monotone_late_witness

/-- Witness: a run where interestDue rises without `hover`. An overpayment at a 50% OverpaymentInterestRate
covers the interest part of −3.24 of the third instalment, so interestDue rises by 3.24. -/
theorem Lending.Reachable.interest_monotone_overpayment_attained :
    ∃ (l l' : LendingLedger) (txs : List LendingTx) (i : Nat) (loan loan' : Loan), l.Reachable ∧
      LendingLedger.Reaches l txs l' ∧ l.LoanAt i loan ∧ l'.LoanAt i loan' ∧
      (∀ (pre : List LendingTx) (l₁ l₂ : LendingLedger) (amount : Number) (loan₁ : Loan)
        (pc : PaymentComponents) (d : Number), pre ++ [.loanPay i .late amount] <+: txs →
        LendingLedger.Reaches l pre l₁ → (l₁.apply (.loanPay i .late amount)).run = .ok (.ok l₂) →
        l₁.LoanAt i loan₁ → loan₁.rates.lateInterestRate ≠ 0 → loan₁.paymentComponents .late l₁.now = .ok pc →
        pc.interestDelta = .ok d → 0 ≤ d.toRat) ∧
      loan.toExact.interestDue < loan'.toExact.interestDue :=
  LendingLedger.interest_monotone_overpayment_witness

/-- Regular payoff -> the cost and what the vault and the broker receive follow from the loan at create. From any
reachable loan, with PaymentRemaining for PaymentTotal. -/
theorem Lending.Reachable.regularPayoff (l l' : LendingLedger) (i : Nat) (loan loan' : Loan) (cost toVault toBroker : ℚ)
    (hr : l.Reachable) (hat : l.LoanAt i loan)
    (hrun : l.RegularPayoff i (fun _ _ _ => True) l' cost toVault toBroker) (hat' : l'.LoanAt i loan')
    (hpaid : loan'.paymentRemaining = 0) :
    -- the schedule's sum stays below `10^16` LoanScale units
    (loan.totalValueOutstanding.toRat + loan.fees.serviceFee.toRat * loan.paymentRemaining.toNat <
        10 ^ 16 * 10 ^ loan.loanScale →
      cost = loan.totalValueOutstanding.toRat + loan.fees.serviceFee.toRat * loan.paymentRemaining.toNat) ∧
    -- the same run, where no payment coarsens the vault
    (l.RegularPayoff i LendingLedger.PaysVaultUncoarsened l' cost toVault toBroker →
      toVault = loan.totalValueOutstanding.toRat - loan.managementFeeOutstanding.toRat) ∧
    -- the same run, where no payment coarsens the cover, and the schedule's sum stays below `10^16` LoanScale units
    (l.RegularPayoff i LendingLedger.PaysCoverUncoarsened l' cost toVault toBroker →
      loan.totalValueOutstanding.toRat + loan.fees.serviceFee.toRat * loan.paymentRemaining.toNat <
        10 ^ 16 * 10 ^ loan.loanScale →
      toBroker = loan.managementFeeOutstanding.toRat + loan.fees.serviceFee.toRat * loan.paymentRemaining.toNat) :=
  ⟨LendingLedger.regularPayoff_cost_proof l l' i loan loan' cost toVault toBroker hr hat hrun hat' hpaid,
    fun hv => LendingLedger.regularPayoff_vault_proof l l' i loan loan' cost toVault toBroker hr hat hv hat' hpaid,
    fun hc => LendingLedger.regularPayoff_broker_proof l l' i loan loan' cost toVault toBroker hr hat hc hat' hpaid⟩

/-- Witness: a run where the cost is less. A LoanServiceFee of `10^30` drops the loan's value from the 19-digit
charge. -/
theorem Lending.Reachable.regularPayoff_cost_attained :
    ∃ (l l' : LendingLedger) (i : Nat) (loan loan' : Loan) (cost toVault toBroker : ℚ), l.Reachable ∧
      l.LoanAt i loan ∧ l.RegularPayoff i (fun _ _ _ => True) l' cost toVault toBroker ∧ l'.LoanAt i loan' ∧
      loan'.paymentRemaining = 0 ∧
      cost < loan.totalValueOutstanding.toRat + loan.fees.serviceFee.toRat * loan.paymentRemaining.toNat :=
  LendingLedger.regularPayoff_cost_witness

/-- Witness: a run where the vault receives less. On a reachable coarsened vault a payoff of 1.5 is credited as 1. -/
theorem Lending.Reachable.regularPayoff_vault_attained :
    ∃ (l l' : LendingLedger) (i : Nat) (loan loan' : Loan) (cost toVault toBroker : ℚ), l.Reachable ∧
      l.LoanAt i loan ∧ l.RegularPayoff i (fun _ _ _ => True) l' cost toVault toBroker ∧ l'.LoanAt i loan' ∧
      loan'.paymentRemaining = 0 ∧
      toVault < loan.totalValueOutstanding.toRat - loan.managementFeeOutstanding.toRat :=
  LendingLedger.regularPayoff_vault_witness

/-- Witness: a run where the broker receives less. A LoanServiceFee of `10^30` drops the management fee from the
19-digit fee. -/
theorem Lending.Reachable.regularPayoff_broker_attained :
    ∃ (l l' : LendingLedger) (i : Nat) (loan loan' : Loan) (cost toVault toBroker : ℚ), l.Reachable ∧
      l.LoanAt i loan ∧ l.RegularPayoff i LendingLedger.PaysCoverUncoarsened l' cost toVault toBroker ∧
      l'.LoanAt i loan' ∧ loan'.paymentRemaining = 0 ∧
      toBroker < loan.managementFeeOutstanding.toRat + loan.fees.serviceFee.toRat * loan.paymentRemaining.toNat :=
  LendingLedger.regularPayoff_broker_witness

end XRPL.Model
