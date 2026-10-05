import XRPL.Properties.Lending.LoanBroker.Defs

/-! # Witness for the cover floor at two vault scales

An IOU broker with `debtTotal` `12.34567890123`, `coverRateMinimum` `10%` and
`coverAvailable` `1.3`, checked by `native_decide`. The debt times the rate is
`1.234567890123`. At vault scale `10^-13` the minimum cover keeps that value and
the cover floor holds. At vault scale `10^0` it rounds up to `2` and the floor
fails. -/

set_option linter.style.nativeDecide false

namespace XRPL.Model.Lending

open XRPL.Model.Protocol

/-- An IOU broker with one loan, `debtTotal` `12.34567890123`, `coverRateMinimum`
`10%` and `coverAvailable` `1.3`. -/
def wbFloor : RawLoanBroker :=
  { numericType := .fractional, managementFeeRate := 0, coverRateMinimum := 10000
  , coverRateLiquidation := 10000, debtTotal := ⟨false, 1234567890123000000, -17⟩
  , debtMaximum := Number.zero, coverAvailable := ⟨false, 1300000000000000000, -18⟩
  , loanCount := 1 }

def wbFloorL : LoanBroker := ⟨wbFloor, by native_decide, by native_decide⟩

/-- The cover floor holds at vault scale `e` and fails at vault scale `e'`. -/
def floorFlips (lb : LoanBroker) (e e' : Int) : Bool :=
  match lb.hasMinimumCover e, lb.hasMinimumCover e' with
  | .ok true, .ok false => true
  | _, _ => false

private lemma floorFlips_witness : floorFlips wbFloorL (-13) 0 = true := by native_decide

/-- A broker can hold the minimum cover at a finer vault scale and fall below it
at a coarser one. -/
lemma LoanBroker.hasMinimumCover_scale_witness :
    ∃ (lb : LoanBroker) (e e' : Int), e < e' ∧ lb.HasMinimumCover e ∧
      lb.hasMinimumCover e' = .ok false := by
  have h := floorFlips_witness
  unfold floorFlips at h
  split at h
  · rename_i h1 h2
    exact ⟨_, -13, 0, by decide, h1, h2⟩
  · exact absurd h (by decide)

end XRPL.Model.Lending
