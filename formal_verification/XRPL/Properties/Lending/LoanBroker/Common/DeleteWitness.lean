import XRPL.Properties.Lending.LoanBroker.Common.DeleteAccuracy

/-! # Witness for the `LoanBroker.roundedCoverAvailable` bound

A cover one digit longer than an IOU amount holds, checked by `native_decide`. -/

set_option linter.style.nativeDecide false

namespace XRPL.Model.Lending

open XRPL.Model.Protocol

/-- An IOU broker holding `1000000000000000.5` of cover, 17 significant digits. -/
def wbHalfCover : RawLoanBroker :=
  { numericType := .fractional, managementFeeRate := 0, coverRateMinimum := 0
  , coverRateLiquidation := 0, debtTotal := Number.zero, debtMaximum := Number.zero
  , coverAvailable := ⟨false, 1000000000000000500, -3⟩, loanCount := 0 }

def wbHalfCoverL : LoanBroker := ⟨wbHalfCover, by native_decide, by native_decide⟩

/-- The returned amount is nonzero and exactly half a unit away from `coverAvailable`. -/
def roundsByHalf (lb : LoanBroker) : Bool :=
  match lb.roundedCoverAvailable with
  | .ok s =>
    s.mValue != 0 && decide (|s.toRat - lb.coverAvailable.toRat| = (1 / 2 : ℚ) * (10 : ℚ) ^ s.exponent)
  | _ => false

private lemma roundsByHalf_witness : roundsByHalf wbHalfCoverL = true := by native_decide

/-- The amount returned on deletion can be a full half unit away from `coverAvailable`. -/
lemma LoanBroker.roundedCoverAvailable_bounds_witness :
    ∃ (lb : LoanBroker) (s : STAmount), lb.roundedCoverAvailable = .ok s ∧ s.mValue ≠ 0 ∧
      |s.toRat - lb.toExact.coverAvailable| = (1 / 2 : ℚ) * (10 : ℚ) ^ s.exponent := by
  have h := roundsByHalf_witness
  unfold roundsByHalf at h
  split at h
  · rename_i s hs
    rw [Bool.and_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq] at h
    exact ⟨_, s, hs, h.1, h.2⟩
  · exact absurd h (by decide)

end XRPL.Model.Lending
