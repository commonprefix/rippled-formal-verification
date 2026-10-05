import XRPL.Properties.Lending.LoanBroker.Common.Create

/-! # `LoanBroker.create` and `LoanBroker.update`

A broker created with in-range parameters is lawful and starts with no debt, no
cover and no loans. An update writes `debtMaximum` and nothing else. -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol

variable (lb : LoanBroker)

/-- In-range parameters create a lawful broker holding exactly the requested
values. -/
theorem LoanBroker.create_success (tx : LoanBrokerSetCreate) (nt : NumericType)
    (hdm : ∀ dm ∈ tx.debtMaximum, dm.isNormalized ∧ Number.zero.operator_le dm = true ∧
      dm.operator_le debtMaximumCap = true)
    (hfee : tx.managementFeeRate.getD 0 ≤ maxManagementFeeRate) -- at most 10%
    (hmin : tx.coverRateMinimum.getD 0 ≤ maxCoverRate) -- at most 100%
    (hliq : tx.coverRateLiquidation.getD 0 ≤ maxCoverRate) -- at most 100%
    -- both cover rates are set or neither is
    (hcoupled : tx.coverRateMinimum.getD 0 = 0 ↔ tx.coverRateLiquidation.getD 0 = 0) :
    ∃ lb, LoanBroker.create tx nt = .ok lb ∧ lb.toRawLoanBroker = LoanBroker.createRaw tx nt :=
  LoanBroker.create_success_proof tx nt hdm hfee hmin hliq hcoupled

/-- A new broker has no exposure: `debtTotal`, `coverAvailable` and `loanCount`
are all zero. -/
theorem LoanBroker.create_no_exposure (tx : LoanBrokerSetCreate) (nt : NumericType)
    (lb : LoanBroker) (hok : LoanBroker.create tx nt = .ok lb) :
    lb.debtTotal = Number.zero ∧ lb.coverAvailable = Number.zero ∧ lb.loanCount = 0 :=
  LoanBroker.create_no_exposure_proof tx nt lb hok

/-- A `debtMaximum` that passed the create checks is on the STAmount grid of the vault
asset, so C++ `associateAsset` stores it without rounding. -/
theorem LoanBroker.canCreate_debtMaximum_not_rounded (dm : Number) (nt : NumericType)
    (hcan : LoanBroker.canCreate (some dm) nt = .ok .tesSUCCESS) :
    STAmount.isRounded nt dm = false :=
  LoanBroker.canCreate_debtMaximum_not_rounded_proof dm nt hcan

/-- An in-range new `debtMaximum` that is zero or not below the debt gives a
lawful broker that differs from the old one only in `debtMaximum`. -/
theorem LoanBroker.update_success (dm : Number)
    (hnorm : dm.isNormalized) (hnn : Number.zero.operator_le dm = true)
    (hcap : dm.operator_le debtMaximumCap = true)
    (hdebt : dm ≠ Number.zero → lb.debtTotal.operator_le dm = true) :
    ∃ lb', lb.update (some dm) = .ok lb' ∧
      lb'.toRawLoanBroker = { lb.toRawLoanBroker with debtMaximum := dm } :=
  LoanBroker.update_success_proof lb dm hnorm hnn hcap hdebt

/-- A `debtMaximum` that passed the update checks is on the STAmount grid of the vault
asset, so C++ `associateAsset` stores it without rounding. -/
theorem LoanBroker.canUpdate_debtMaximum_not_rounded (dm : Number)
    (hcan : lb.canUpdate (some dm) = .ok .tesSUCCESS) :
    STAmount.isRounded lb.numericType dm = false :=
  LoanBroker.canUpdate_debtMaximum_not_rounded_proof lb dm hcan

/-- An update with no `debtMaximum` returns the broker unchanged. -/
theorem LoanBroker.update_none : lb.update none = .ok lb :=
  LoanBroker.update_none_proof lb

end XRPL.Model.Lending
