import XRPL.Properties.Lending.LoanBroker.Common.Create

/-! # `LoanBroker.create` and `LoanBroker.update`

A broker created with in-range parameters is lawful and starts with no debt, no cover and no
loans. An update changes only `debtMaximum`. -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol

variable (lb : LoanBroker)

/-- LoanBrokerSet create -> with valid fields a lawful broker with no exposure is created, and a DebtMaximum that
passes the checks is stored without rounding. -/
theorem LoanBroker.create_success (nt : NumericType) :
    -- ManagementFeeRate at most 10%, each cover rate at most 100%, and both cover rates set or neither
    (∀ tx : LoanBrokerSetCreate, (∀ dm ∈ tx.debtMaximum, dm.isNormalized ∧ Number.zero.operator_le dm = true ∧
        dm.operator_le debtMaximumCap = true) →
      tx.managementFeeRate.getD 0 ≤ maxManagementFeeRate → tx.coverRateMinimum.getD 0 ≤ maxCoverRate →
      tx.coverRateLiquidation.getD 0 ≤ maxCoverRate →
      (tx.coverRateMinimum.getD 0 = 0 ↔ tx.coverRateLiquidation.getD 0 = 0) →
      ∃ lb, LoanBroker.create tx nt = .ok lb ∧ lb.toRawLoanBroker = LoanBroker.createRaw tx nt) ∧
    (∀ (tx : LoanBrokerSetCreate) (lb : LoanBroker), LoanBroker.create tx nt = .ok lb →
      lb.debtTotal = Number.zero ∧ lb.coverAvailable = Number.zero ∧ lb.loanCount = 0) ∧
    ∀ {α : Type} [AssetPool α] (pool : α) (dm : Number),
      LoanBroker.canCreate pool (some dm) nt = .ok .tesSUCCESS → STAmount.isRounded nt dm = false :=
  ⟨fun tx => LoanBroker.create_success_proof tx nt, fun tx => LoanBroker.create_no_exposure_proof tx nt,
    fun pool dm hcan => LoanBroker.canCreate_debtMaximum_not_rounded_proof pool dm nt hcan⟩

/-- LoanBrokerSet update -> a valid DebtMaximum gives a lawful broker where only DebtMaximum changes, a DebtMaximum
that passes the checks is stored without rounding, and no DebtMaximum changes nothing. -/
theorem LoanBroker.update_success :
    (∀ dm : Number, dm.isNormalized → Number.zero.operator_le dm = true → dm.operator_le debtMaximumCap = true →
      (dm ≠ Number.zero → lb.debtTotal.operator_le dm = true) →
      ∃ lb', lb.update (some dm) = .ok lb' ∧ lb'.toRawLoanBroker = { lb.toRawLoanBroker with debtMaximum := dm }) ∧
    (∀ {α : Type} [AssetPool α] (pool : α) (dm : Number), lb.canUpdate pool (some dm) = .ok .tesSUCCESS →
      STAmount.isRounded lb.numericType dm = false) ∧
    lb.update none = .ok lb :=
  ⟨LoanBroker.update_success_proof lb,
    fun pool dm hcan => LoanBroker.canUpdate_debtMaximum_not_rounded_proof lb pool dm hcan,
    LoanBroker.update_none_proof lb⟩

end XRPL.Model.Lending
