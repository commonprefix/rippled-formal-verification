import XRPL.Properties.Lending.LoanBroker.Common.GuardProofs

/-! # `LoanBroker.canDelete` exits

The exits of `canDelete`. Its debt check never fires on a lawful broker, because no loans
means no debt. -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol

variable {α : Type} [AssetPool α]

variable (lb : LoanBroker)

/-- The exits of `canDelete`, in the order it runs its checks. Each line assumes the checks before it passed. -/
theorem LoanBroker.canDelete_exits (pool : α) :
    (lb.loanCount ≠ 0 → lb.canDelete pool = .ok .tecHAS_OBLIGATIONS) ∧
    (lb.debtTotal.signum ≠ 0 → lb.canDelete pool = .ok .tecHAS_OBLIGATIONS) ∧
    (lb.loanCount = 0 → lb.canDelete pool = .ok .tesSUCCESS) :=
  ⟨LoanBroker.canDelete_has_loans_proof lb pool, LoanBroker.canDelete_has_debt_proof lb pool,
    LoanBroker.canDelete_success_proof lb pool⟩

/-- Error codes: success or tecHAS_OBLIGATIONS. -/
theorem LoanBroker.canDelete_error_codes (pool : α) (ter : TER)
    (hok : lb.canDelete pool = .ok ter) : ter = .tesSUCCESS ∨ ter = .tecHAS_OBLIGATIONS :=
  LoanBroker.canDelete_error_codes_proof lb pool ter hok

/-- Success ⟺ the broker has no loans. -/
theorem LoanBroker.canDelete_lawful_iff (pool : α) :
    lb.canDelete pool = .ok .tesSUCCESS ↔ lb.loanCount = 0 :=
  LoanBroker.canDelete_lawful_iff_proof lb pool

end XRPL.Model.Lending
