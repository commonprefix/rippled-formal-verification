import XRPL.Properties.Protocol.STAmount.RoundToScale.Common.Proofs

/-! # `STAmount.roundToExponent` is correctly rounded onto the scale grid

`roundToExponent` quantizes an IOU `STAmount` onto the `10^s · ℤ` grid faithfully (in every
mode). Built from the `roundToExponent_sum_spec` workhorse in `RoundToScale.Common.Sum`. -/

namespace XRPL.Model.Protocol

/-- **`STAmount.roundToExponent` rounds `value.toRat` onto the `10^s` grid faithfully.**
Holds on the full IOU scale range `[-96, 80]` given a nonzero result: below `-81`
the 16-digit clamp only ever flushes a tiny grid coefficient to zero, so a nonzero
result is always the exact grid point. -/
theorem STAmount.roundToExponent_rounded (value result : STAmount) (s : ℤ)
    (mode : rounding_mode)
    (hc : value.IOUCanonical)
    (h_s : (-96 : ℤ) ≤ s) (h_s_hi : s ≤ 80)
    (hnz : result.mValue ≠ 0)
    (hok : STAmount.roundToExponent value s mode = .ok result) :
    RoundsToRepresentableAt result value.toRat s mode :=
  STAmount.roundToExponent_rounded_proof value result s mode hc h_s h_s_hi hnz hok

end XRPL.Model.Protocol
