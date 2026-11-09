import XRPL.Properties.Lending.LoanBroker.Common.OpenZone
import XRPL.Properties.Lending.LoanBroker.Common.MaxValueFits

/-! # `LoanBroker.roundedCoverAvailable`

On deletion the broker pays back `coverAvailable` rounded to nearest in the vault asset, which on a reachable broker
is exactly `coverAvailable`. -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol

variable (lb : LoanBroker)

/-- Loan broker delete -> the amount `s` sent to the owner is CoverAvailable. -/
theorem LoanBroker.roundedCoverAvailable_bounds (s : STAmount) (hok : lb.roundedCoverAvailable = .ok s) :
    ∀ base : Int, lb.Reachable base → s.toRat = lb.toExact.coverAvailable :=
  fun base hr =>
    LoanBroker.roundedCoverAvailable_of_exact lb s (LoanBroker.Reachable.openZone lb base hr).coverExact hok

end XRPL.Model.Lending
