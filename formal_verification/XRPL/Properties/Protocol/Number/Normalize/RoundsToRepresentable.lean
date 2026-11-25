import XRPL.Properties.Protocol.Number.Normalize.Common.Downward.RoundedHelpers
import XRPL.Properties.Protocol.Number.Normalize.Common.Upward.RoundedHelpers
import XRPL.Properties.Protocol.Number.Normalize.Common.TowardsZero.RoundedHelpers
import XRPL.Properties.Protocol.Number.Normalize.Common.ToNearest.RoundedHelpers

/-! # `normalize` rounds to a neighbouring `Number`

The result is the neighbouring `Number` on the side the mode asks for, or either neighbour in `to_nearest`.
`downward` and `upward` assume a nonzero result, since a value too small for a `Number` becomes zero. -/

namespace XRPL.Model.Protocol

theorem Number.normalize_rounded_downward (n result : Number)
    (hok : n.normalize largeRange.min largeRange.max .downward = .ok result)
    (hresult : result.mantissa_ ≠ 0) :
    Number.RoundsToRepresentable result n.toRat .downward :=
  Number.normalize_rounded_downward_proof n result hok hresult

theorem Number.normalize_rounded_upward (n result : Number)
    (hok : n.normalize largeRange.min largeRange.max .upward = .ok result)
    (hresult : result.mantissa_ ≠ 0) :
    Number.RoundsToRepresentable result n.toRat .upward :=
  Number.normalize_rounded_upward_proof n result hok hresult

theorem Number.normalize_rounded_towards_zero (n result : Number)
    (hok : n.normalize largeRange.min largeRange.max .towards_zero = .ok result) :
    Number.RoundsToRepresentable result n.toRat .towards_zero :=
  Number.normalize_rounded_towards_zero_proof n result hok

theorem Number.normalize_rounded_to_nearest (n result : Number)
    (hok : n.normalize largeRange.min largeRange.max .to_nearest = .ok result) :
    Number.RoundsToRepresentable result n.toRat .to_nearest :=
  Number.normalize_rounded_to_nearest_proof n result hok

end XRPL.Model.Protocol
