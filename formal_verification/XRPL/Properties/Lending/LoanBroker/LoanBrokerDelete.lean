import XRPL.Properties.Lending.LoanBroker.Common.DeleteAccuracy
import XRPL.Properties.Lending.LoanBroker.Common.MaxValueFits

/-! # `LoanBroker.roundedCoverAvailable`

On deletion the broker pays back `coverAvailable` rounded to nearest in the vault asset: exactly on a reachable
broker, and within half a unit in the last digit of the amount on any lawful broker. -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol

variable (lb : LoanBroker)

/-- Loan broker delete -> the amount `s` sent to the owner is CoverAvailable. On any lawful broker, with `s` ≠ 0 -> `s`
is CoverAvailable rounded to nearest at the precision of `s`. -/
theorem LoanBroker.roundedCoverAvailable_bounds (s : STAmount) (hok : lb.roundedCoverAvailable = .ok s) :
    (∀ base : Int, lb.Reachable base → s.toRat = lb.toExact.coverAvailable) ∧
    (s.mValue ≠ 0 → |s.toRat - lb.toExact.coverAvailable| ≤ (1 / 2 : ℚ) * (10 : ℚ) ^ s.exponent) :=
  ⟨fun base hr =>
      LoanBroker.roundedCoverAvailable_of_exact lb s (LoanBroker.Reachable.openZone lb base hr).coverExact hok,
    fun hnz => LoanBroker.roundedCoverAvailable_bounds_proof lb s hok hnz⟩

end XRPL.Model.Lending
