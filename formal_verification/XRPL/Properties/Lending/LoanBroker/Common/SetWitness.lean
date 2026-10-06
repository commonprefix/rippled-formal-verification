import XRPL.Model.Lending.LoanBroker.LoanBrokerSet

/-! # Witnesses for the `LoanBrokerSet` checks

An XRP `debtMaximum` above the XRP maximum, checked by `native_decide`. -/

set_option linter.style.nativeDecide false

namespace XRPL.Model.Lending

open XRPL.Model.Protocol

/-- `10^18` drops: inside `[0, 2^63 - 1]`, above the XRP maximum `10^17`. -/
def wdXrpAboveMax : Number := ⟨false, 1000000000000000000, 0⟩

/-- An XRP broker with no debt, no cover and no loans. -/
def wbXrp : RawLoanBroker :=
  { numericType := .native, managementFeeRate := 0, coverRateMinimum := 0
  , coverRateLiquidation := 0, debtTotal := Number.zero, debtMaximum := Number.zero
  , coverAvailable := Number.zero, loanCount := 0 }

def wbXrpL : LoanBroker := ⟨wbXrp, by native_decide, by native_decide⟩

/-- On an XRP vault the create check throws for an in-range `debtMaximum` above `10^17`. -/
lemma LoanBroker.canCreate_error_codes_witness :
    ∃ dm : Number, dm.isNormalized ∧ Number.zero.operator_le dm = true ∧
      dm.operator_le debtMaximumCap = true ∧ LoanBroker.canCreate (some dm) .native = .error .outOfRange :=
  ⟨wdXrpAboveMax, by native_decide⟩

/-- On an XRP broker the update check throws for an in-range `debtMaximum` above `10^17`. -/
lemma LoanBroker.canUpdate_error_codes_witness :
    ∃ (lb : LoanBroker) (dm : Number), lb.numericType = .native ∧ dm.isNormalized ∧
      Number.zero.operator_le dm = true ∧ dm.operator_le debtMaximumCap = true ∧
      lb.canUpdate (some dm) = .error .outOfRange :=
  ⟨wbXrpL, wdXrpAboveMax, by native_decide⟩

end XRPL.Model.Lending
