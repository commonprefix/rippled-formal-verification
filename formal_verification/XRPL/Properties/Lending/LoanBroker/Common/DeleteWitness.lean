import XRPL.Properties.Lending.LoanBroker.Common.DeleteAccuracy

/-! # Witness for the `LoanBroker.roundedCoverAvailable` bound

A cover one digit longer than an IOU amount holds, checked by `native_decide`. -/

set_option linter.style.nativeDecide false

namespace XRPL.Model.Lending

open XRPL.Model.Protocol

/-- An IOU broker holding `1000000000000000.5` of cover, 17 significant digits. -/
private def wbHalfCover : LoanBroker :=
  ⟨{ numericType := .fractional, managementFeeRate := 0, coverRateMinimum := 0
   , coverRateLiquidation := 0, debtTotal := Number.zero, debtMaximum := Number.zero
   , coverAvailable := ⟨false, 1000000000000000500, -3⟩, loanCount := 0 },
   by native_decide, by native_decide⟩

/-- The amount returned on deleting `wbHalfCover`. -/
private def wsHalf : STAmount :=
  match wbHalfCover.roundedCoverAvailable with
  | .ok s => s
  | .error _ => STAmount.unchecked .fractional 0 0 false

/-- The amount returned on deletion can be a full half unit away from `coverAvailable`. -/
lemma LoanBroker.roundedCoverAvailable_bounds_witness :
    ∃ (lb : LoanBroker) (s : STAmount), lb.roundedCoverAvailable = .ok s ∧ s.mValue ≠ 0 ∧
      |s.toRat - lb.toExact.coverAvailable| = (1 / 2 : ℚ) * (10 : ℚ) ^ s.exponent :=
  ⟨wbHalfCover, wsHalf, by native_decide, by native_decide, by native_decide⟩

end XRPL.Model.Lending
