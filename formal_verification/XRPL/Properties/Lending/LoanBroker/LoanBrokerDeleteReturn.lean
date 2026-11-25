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
    (lb.loanCount = 0 → lb.canDelete pool = .ok .tesSUCCESS) := by
  sorry

/-- Error codes: success or tecHAS_OBLIGATIONS. -/
theorem LoanBroker.canDelete_error_codes (pool : α) (ter : TER)
    (hok : lb.canDelete pool = .ok ter) : ter = .tesSUCCESS ∨ ter = .tecHAS_OBLIGATIONS := by
  sorry

/-- Success ⟺ the broker has no loans. -/
theorem LoanBroker.canDelete_lawful_iff (pool : α) :
    lb.canDelete pool = .ok .tesSUCCESS ↔ lb.loanCount = 0 := by
  sorry

end XRPL.Model.Lending
