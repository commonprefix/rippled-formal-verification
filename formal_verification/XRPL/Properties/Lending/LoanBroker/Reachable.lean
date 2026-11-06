import XRPL.Properties.Lending.LoanBroker.Common.ReachableProofs
import XRPL.Properties.Lending.LoanBroker.Common.OpenZone
import XRPL.Properties.Lending.LoanBroker.Common.MaxValueFits

/-! # Loan broker reachability

Every reachable broker is lawful and keeps the debt, loan count and rates it was created with. Its CoverAvailable is
whole base units within the Open limit and its DebtMaximum is on the base grid. -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol

variable (lb : LoanBroker)

/-- Every broker reachable from creation by a sequence of broker transactions is lawful, as every broker is by
construction. -/
theorem LoanBroker.Reachable.lawful (base : Int) (_hr : lb.Reachable base) :
    lb.toRawLoanBroker.WF ∧ lb.toRawLoanBroker.Valid :=
  ⟨lb.wf, lb.valid⟩

/-- Every reachable broker -> no debt and no loans, its rates fixed at create, CoverAvailable and DebtMaximum on the
base grid. -/
theorem LoanBroker.Reachable.broker_fields (base : Int) :
    (lb.Reachable base → lb.debtTotal = Number.zero) ∧
    (lb.Reachable base → lb.loanCount = 0) ∧
    (∀ (tx : LoanBrokerSetCreate) (nt : NumericType) (start : LoanBroker), LoanBroker.create tx nt = .ok start →
      LoanBroker.ReachableFrom base start lb →
      lb.managementFeeRate = tx.managementFeeRate.getD 0 ∧ lb.coverRateMinimum = tx.coverRateMinimum.getD 0 ∧
        lb.coverRateLiquidation = tx.coverRateLiquidation.getD 0) ∧
    (lb.Reachable base → ∃ k : ℕ, k ≤ 9 * 10 ^ 15 ∧ lb.toExact.coverAvailable = (k : ℚ) * (10 : ℚ) ^ base) ∧
    (lb.Reachable base → lb.debtMaximum.isOnExponentGrid base lb.numericType = .ok true) :=
  ⟨LoanBroker.Reachable.debtTotal_zero_proof lb base, LoanBroker.Reachable.loanCount_zero_proof lb base,
    fun tx nt start hc hrf => LoanBroker.ReachableFrom.creation_rates_proof tx nt base start lb hc hrf,
    fun hr =>
      have hz := LoanBroker.Reachable.openZone lb base hr
      Number.OnGrid.units_le _ _ hz.cover lb.exact.coverAvailable_nonneg hz.coverLimit,
    fun hr => (LoanBroker.Reachable.openZone lb base hr).debtMaximum⟩

end XRPL.Model.Lending
