import XRPL.Properties.Protocol.STAmount.RoundToScale.Common.Proofs

/-! # `STAmount.roundToExponent` rounds onto the scale grid

`roundToExponent` rounds an IOU `STAmount` onto the `10^s · ℤ` grid in every rounding mode. -/

namespace XRPL.Model.Protocol

/-- `STAmount.roundToExponent` rounds `value` onto the `10^s` grid in the given mode. For `s` below `-81` the result
can flush to zero, so the theorem assumes a nonzero result. -/
theorem STAmount.roundToExponent_rounded (value result : STAmount) (s : ℤ)
    (mode : rounding_mode)
    (hc : value.IOUCanonical)
    (h_s : (-96 : ℤ) ≤ s) (h_s_hi : s ≤ 80)
    (hnz : result.mValue ≠ 0)
    (hok : STAmount.roundToExponent value s mode = .ok result) :
    RoundsToRepresentableAt result value.toRat s mode :=
  STAmount.roundToExponent_rounded_proof value result s mode hc h_s h_s_hi hnz hok

end XRPL.Model.Protocol
