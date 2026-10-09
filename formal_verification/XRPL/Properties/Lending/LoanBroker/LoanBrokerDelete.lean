import XRPL.Properties.Lending.LoanBroker.Common.DeleteAccuracy
import XRPL.Properties.Lending.LoanBroker.Common.DeleteWitness
import XRPL.Properties.Lending.LoanBroker.Common.ReachableProofs

/-! # `LoanBroker.roundedCoverAvailable`

On deletion the broker pays back `coverAvailable` rounded to nearest in the vault asset:
exact when the asset can hold it, otherwise within half a unit. -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol

variable (lb : LoanBroker)

/-- When CoverAvailable fits an STAmount exactly -> the returned amount `s` = CoverAvailable. -/
theorem LoanBroker.roundedCoverAvailable_exact (s : STAmount)
    (hok : lb.roundedCoverAvailable = .ok s)
    -- `coverAvailable` is on the STAmount grid of the vault asset, so it converts without rounding
    (hrep : ∃ a : STAmount, a.ExactCanonical ∧ a.mNumericType = lb.numericType ∧
      a.toRat = lb.toExact.coverAvailable) :
    s.toRat = lb.toExact.coverAvailable :=
  LoanBroker.roundedCoverAvailable_exact_proof lb s hok hrep

/-- When the returned amount `s` ≠ 0 -> |s - CoverAvailable| ≤ ½ ULP of `s`. For XRP and MPT the ULP
is `1`. C++ `associateAsset` keeps CoverAvailable on the asset grid, so today nothing rounds here.
Without it the broker could be paid more than CoverAvailable. -/
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

/-- For XRP and MPT, when every cover operation moves a whole amount and keeps CoverAvailable below
2^63 -> the returned amount `s` = CoverAvailable. -/
theorem LoanBroker.WholeCoverFrom.roundedCoverAvailable_exact (start lb : LoanBroker)
    (s : STAmount)
    (hint : start.numericType.isIntegral = true)
    (hstart : start.toExact.coverAvailable.den = 1 ∧ start.toExact.coverAvailable < 2 ^ 63)
    (hr : LoanBroker.WholeCoverFrom start lb)
    (hok : lb.roundedCoverAvailable = .ok s) :
    s.toRat = lb.toExact.coverAvailable :=
  LoanBroker.WholeCoverFrom.roundedCoverAvailable_exact_proof start lb s hint hstart hr hok

end XRPL.Model.Lending
