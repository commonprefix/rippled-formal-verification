import XRPL.Properties.Lending.LoanBroker.Common.DeleteAccuracy
import XRPL.Properties.Lending.LoanBroker.Common.DeleteWitness
import XRPL.Properties.Lending.LoanBroker.Common.MaxValueFits

/-! # `LoanBroker.roundedCoverAvailable`

On deletion the broker pays back `coverAvailable` rounded to nearest in the vault asset: exactly on a reachable
broker, and within half a unit in the last digit of the amount on any lawful broker. -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol

variable (lb : LoanBroker)

/-- On a reachable broker the returned amount `s` = CoverAvailable. -/
theorem LoanBroker.Reachable.roundedCoverAvailable_exact (base : Int) (hr : lb.Reachable base)
    (s : STAmount) (hok : lb.roundedCoverAvailable = .ok s) :
    s.toRat = lb.toExact.coverAvailable :=
  LoanBroker.Reachable.roundedCoverAvailable_exact_proof lb base hr s hok

/-- When the returned amount `s` ≠ 0 -> |s − CoverAvailable| ≤ half a unit in the last digit of `s` (half a
whole unit for XRP and MPT). On a reachable broker nothing rounds here. -/
theorem LoanBroker.roundedCoverAvailable_bounds (s : STAmount)
    (hok : lb.roundedCoverAvailable = .ok s)
    (hnz : s.mValue ≠ 0) :
    |s.toRat - lb.toExact.coverAvailable| ≤ (1 / 2 : ℚ) * (10 : ℚ) ^ s.exponent :=
  LoanBroker.roundedCoverAvailable_bounds_proof lb s hok hnz

/-- Witness: a run where the error reaches the bound. A cover of `1000000000000000.5` needs 17
digits, so the IOU amount returned is half a unit away. -/
theorem LoanBroker.roundedCoverAvailable_bounds_attained :
    ∃ (lb : LoanBroker) (s : STAmount), lb.roundedCoverAvailable = .ok s ∧ s.mValue ≠ 0 ∧
      |s.toRat - lb.toExact.coverAvailable| = (1 / 2 : ℚ) * (10 : ℚ) ^ s.exponent :=
  LoanBroker.roundedCoverAvailable_bounds_witness

end XRPL.Model.Lending
