import XRPL.Properties.Lending.LoanBroker.Common.GuardProofs

/-! # `LoanBroker.canDelete` exits

The exits of `canDelete`. Its debt check never fires on a lawful broker, because no loans
means no debt. -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol

variable {α : Type} [AssetPool α]

variable (lb : LoanBroker)

/-- When the loan broker LoanCount ≠ 0 -> tecHAS_OBLIGATIONS. -/
theorem LoanBroker.canDelete_has_loans (pool : α)
    (hloans : lb.loanCount ≠ 0) :
    lb.canDelete pool = .ok .tecHAS_OBLIGATIONS :=
  LoanBroker.canDelete_has_loans_proof lb pool hloans

/-- When the loan broker DebtTotal ≠ 0 -> tecHAS_OBLIGATIONS. On a lawful broker debt means loans,
so the rounding check is never reached. -/
theorem LoanBroker.canDelete_has_debt (pool : α)
    (hdebt : lb.debtTotal.signum ≠ 0) :
    lb.canDelete pool = .ok .tecHAS_OBLIGATIONS :=
  LoanBroker.canDelete_has_debt_proof lb pool hdebt

/-- Otherwise -> success. -/
theorem LoanBroker.canDelete_success (pool : α)
    (hloans : lb.loanCount = 0) :
    lb.canDelete pool = .ok .tesSUCCESS :=
  LoanBroker.canDelete_success_proof lb pool hloans

/-- Error codes: success or tecHAS_OBLIGATIONS. -/
theorem LoanBroker.canDelete_error_codes (pool : α) (ter : TER)
    (hok : lb.canDelete pool = .ok ter) : ter = .tesSUCCESS ∨ ter = .tecHAS_OBLIGATIONS :=
  LoanBroker.canDelete_error_codes_proof lb pool ter hok

/-- Success ⟺ the broker has no loans. -/
theorem LoanBroker.lawful_canDelete_iff (pool : α) :
    lb.canDelete pool = .ok .tesSUCCESS ↔ lb.loanCount = 0 :=
  LoanBroker.lawful_canDelete_iff_proof lb pool

end XRPL.Model.Lending
