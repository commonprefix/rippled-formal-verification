import XRPL.Properties.Protocol.STAmount.RoundToScale.Common.Proofs
import XRPL.Properties.Protocol.STAmount.RoundToScale.Common.AnyResult
import XRPL.Properties.Protocol.STAmount.RoundToScale.Common.NearestWitness

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
    RoundsToRepresentableAt result value.toRat s mode := by
  sorry

/-- At a scale of at least `-81` the rounded value never flushes to zero, so `STAmount.roundToExponent` rounds onto
the `10^s` grid with no assumption on the result. -/
theorem STAmount.roundToExponent_rounded_any (value result : STAmount) (s : ℤ)
    (mode : rounding_mode)
    (hc : value.IOUCanonical)
    (h_s : (-81 : ℤ) ≤ s) (h_s_hi : s ≤ 80)
    (hok : STAmount.roundToExponent value s mode = .ok result) :
    RoundsToRepresentableAt result value.toRat s mode := by
  sorry

/-- Witness that ToNearest can end more than half a step away: `1.499999999999999` at exponent 0 gives `2`. -/
theorem STAmount.roundToExponent_nearest_up_attained :
    ∃ (value result : STAmount) (s : ℤ),
      value.IOUCanonical ∧
      -81 ≤ s ∧ s ≤ 80 ∧
      STAmount.roundToExponent value s .to_nearest = .ok result ∧
      (10 : ℚ) ^ s / 2 < |result.toRat - value.toRat| := by
  sorry

/-- Witness that ToNearest can end more than half a step away: `2.500000000000001` at exponent 0 gives `2`. -/
theorem STAmount.roundToExponent_nearest_down_attained :
    ∃ (value result : STAmount) (s : ℤ),
      value.IOUCanonical ∧
      -81 ≤ s ∧ s ≤ 80 ∧
      STAmount.roundToExponent value s .to_nearest = .ok result ∧
      (10 : ℚ) ^ s / 2 < |result.toRat - value.toRat| := by
  sorry

end XRPL.Model.Protocol
