import XRPL.Properties.Lending.LoanBroker.Common.GuardProofs

/-! # `LoanBroker.canDelete` exits

On a lawful broker `loanCount = 0` forces `debtTotal = 0` (`empty_broker`), so
the `debtTotal` check never fires on its own. It is a defensive check. -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol

variable {α : Type} [AssetPool α]

variable (lb : LoanBroker)

/-- A broker with outstanding loans: `tecHAS_OBLIGATIONS`. -/
theorem LoanBroker.canDelete_has_loans (pool : α)
    (hloans : lb.loanCount ≠ 0) : -- the broker still has loans
    lb.canDelete pool = .ok .tecHAS_OBLIGATIONS :=
  LoanBroker.canDelete_has_loans_proof lb pool hloans

/-- A broker with debt: `tecHAS_OBLIGATIONS`. On a lawful broker debt means loans,
so the rounding step of the defensive check is never reached. -/
theorem LoanBroker.canDelete_has_debt (pool : α)
    (hdebt : lb.debtTotal.signum ≠ 0) : -- the broker has debt
    lb.canDelete pool = .ok .tecHAS_OBLIGATIONS :=
  LoanBroker.canDelete_has_debt_proof lb pool hdebt

/-- A broker with no loans passes. -/
theorem LoanBroker.canDelete_success (pool : α)
    (hloans : lb.loanCount = 0) : -- the broker has no loans
    lb.canDelete pool = .ok .tesSUCCESS :=
  LoanBroker.canDelete_success_proof lb pool hloans

/-- Every outcome of the check: `tecHAS_OBLIGATIONS` is the only rejection
`canDelete` can return. -/
theorem LoanBroker.canDelete_error_codes (pool : α) (ter : TER)
    (hok : lb.canDelete pool = .ok ter) : ter = .tesSUCCESS ∨ ter = .tecHAS_OBLIGATIONS :=
  LoanBroker.canDelete_error_codes_proof lb pool ter hok

/-- On a lawful broker, deletion passes exactly when the broker has no loans. -/
theorem LoanBroker.lawful_canDelete_iff (pool : α) :
    lb.canDelete pool = .ok .tesSUCCESS ↔ lb.loanCount = 0 :=
  LoanBroker.lawful_canDelete_iff_proof lb pool

end XRPL.Model.Lending
