import XRPL.Properties.Lending.LoanBroker.Common.ReachableProofs

/-! # Loan broker reachability

Every reachable broker is lawful and keeps the numeric type, debt, loan count and rates it
was created with. -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol

variable (lb : LoanBroker)

/-- Every reachable broker is lawful: it is well formed and valid. Each operation
re-checks the new broker and returns a `LoanBroker`, which carries both proofs. -/
theorem LoanBroker.Reachable.lawful (_hr : lb.Reachable) :
    lb.toRawLoanBroker.WF ∧ lb.toRawLoanBroker.Valid :=
  ⟨lb.wf, lb.valid⟩

/-- No operation changes `debtTotal`, so every reachable broker has none. -/
theorem LoanBroker.Reachable.debtTotal_zero (hr : lb.Reachable) :
    lb.debtTotal = Number.zero :=
  LoanBroker.Reachable.debtTotal_zero_proof lb hr

/-- No operation changes `loanCount`, so every reachable broker has no loans. -/
theorem LoanBroker.Reachable.loanCount_zero (hr : lb.Reachable) :
    lb.loanCount = 0 :=
  LoanBroker.Reachable.loanCount_zero_proof lb hr

/-- A broker keeps the rates it was created with: `managementFeeRate`,
`coverRateMinimum` and `coverRateLiquidation` never change after `create`. -/
theorem LoanBroker.ReachableFrom.creation_rates (tx : LoanBrokerSetCreate) (nt : NumericType)
    (start lb : LoanBroker)
    (hc : LoanBroker.create tx nt = .ok start)
    (hr : LoanBroker.ReachableFrom start lb) :
    lb.managementFeeRate = tx.managementFeeRate.getD 0 ∧
      lb.coverRateMinimum = tx.coverRateMinimum.getD 0 ∧
      lb.coverRateLiquidation = tx.coverRateLiquidation.getD 0 :=
  LoanBroker.ReachableFrom.creation_rates_proof tx nt start lb hc hr

end XRPL.Model.Lending
