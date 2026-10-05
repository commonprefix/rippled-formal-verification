import XRPL.Properties.Lending.LoanBroker.Common.DeleteAccuracy
import XRPL.Properties.Lending.LoanBroker.Common.ReachableProofs

/-! # `LoanBroker.roundedCoverAvailable`

On deletion the broker pays back `coverAvailable` rounded to nearest in the vault asset:
exact when the asset can hold it, otherwise within half a unit. -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol

variable (lb : LoanBroker)

/-- A `coverAvailable` the asset holds exactly is returned without rounding. -/
theorem LoanBroker.roundedCoverAvailable_exact (s : STAmount)
    (hok : lb.roundedCoverAvailable = .ok s)
    -- `coverAvailable` is on the STAmount grid of the vault asset, so it converts without rounding
    (hrep : ∃ a : STAmount, a.ExactCanonical ∧ a.mNumericType = lb.numericType ∧
      a.toRat = lb.toExact.coverAvailable) :
    s.toRat = lb.toExact.coverAvailable :=
  LoanBroker.roundedCoverAvailable_exact_proof lb s hok hrep

/-- The returned amount is within half a unit of its exponent from
`coverAvailable`. For XRP and MPT the exponent is `0`, so the bound is `1/2`. -/
theorem LoanBroker.roundedCoverAvailable_within_half (s : STAmount)
    (hok : lb.roundedCoverAvailable = .ok s)
    (hnz : s.mValue ≠ 0) :
    |s.toRat - lb.toExact.coverAvailable| ≤ (1 / 2 : ℚ) * (10 : ℚ) ^ s.exponent :=
  LoanBroker.roundedCoverAvailable_within_half_proof lb s hok hnz

/-- Integral strengthening of `roundedCoverAvailable_exact`: an XRP or MPT
broker whose cover history keeps `coverAvailable` whole returns it exactly, with
no representability condition. -/
theorem LoanBroker.WholeCoverFrom.roundedCoverAvailable_exact (start lb : LoanBroker)
    (s : STAmount)
    (hint : start.numericType.isIntegral = true)
    (hstart : start.toExact.coverAvailable.den = 1 ∧ start.toExact.coverAvailable < 2 ^ 63)
    (hr : LoanBroker.WholeCoverFrom start lb)
    (hok : lb.roundedCoverAvailable = .ok s) :
    s.toRat = lb.toExact.coverAvailable :=
  LoanBroker.WholeCoverFrom.roundedCoverAvailable_exact_proof start lb s hint hstart hr hok

end XRPL.Model.Lending
