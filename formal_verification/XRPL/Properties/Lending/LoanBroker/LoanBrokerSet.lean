import XRPL.Properties.Lending.LoanBroker.Common.Create

/-! # `LoanBroker.create` and `LoanBroker.update`

A broker created with in-range parameters is lawful and starts with no debt, no cover and no
loans. An update changes only `debtMaximum`. -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol

variable (lb : LoanBroker)

/-- A new loan broker -> with every field in range and consistent with the others a lawful broker is created, with
DebtTotal = CoverAvailable = LoanCount = 0, and a DebtMaximum that passes the checks is stored exactly. -/
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

/-- Loan broker update -> a new DebtMaximum in range gives a lawful broker where no other field changes, one that
passes the checks is stored exactly, and no DebtMaximum changes nothing. -/
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
