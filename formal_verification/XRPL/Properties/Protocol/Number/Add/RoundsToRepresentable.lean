import XRPL.Properties.Protocol.Number.Add.Common.Downward.RoundedHelpers
import XRPL.Properties.Protocol.Number.Add.Common.Upward.RoundedHelpers
import XRPL.Properties.Protocol.Number.Add.Common.TowardsZero.RoundedHelpers
import XRPL.Properties.Protocol.Number.Add.Common.ToNearest.RoundedHelpers

/-! # `operator_add` rounds to a neighbouring `Number`

The result is the largest `Number` at or below the exact value (`downward`), the smallest at or above it (`upward`),
the one of these two nearer zero (`towards_zero`), or either of them (`to_nearest`). `downward` and `upward` assume a
nonzero result, since a value too small for a `Number` becomes zero. -/

namespace XRPL.Model.Protocol

theorem operator_add_rounded_downward (x y result : Number)
    (hx : x.isNormalized) (hy : y.isNormalized)
    (hok : Number.operator_add x y .downward = .ok result)
    (hresult : result.mantissa_ ≠ 0) :
    Number.RoundsToRepresentable result (x.toRat + y.toRat) .downward :=
  operator_add_rounded_downward_proof x y result hx hy hok hresult

theorem operator_add_rounded_upward (x y result : Number)
    (hx : x.isNormalized) (hy : y.isNormalized)
    (hok : Number.operator_add x y .upward = .ok result)
    (hresult : result.mantissa_ ≠ 0) :
    Number.RoundsToRepresentable result (x.toRat + y.toRat) .upward :=
  operator_add_rounded_upward_proof x y result hx hy hok hresult

theorem operator_add_rounded_towards_zero (x y result : Number)
    (hx : x.isNormalized) (hy : y.isNormalized)
    (hok : Number.operator_add x y .towards_zero = .ok result) :
    Number.RoundsToRepresentable result (x.toRat + y.toRat) .towards_zero :=
  operator_add_rounded_towards_zero_proof x y result hx hy hok

theorem operator_add_rounded_to_nearest (x y result : Number)
    (hx : x.isNormalized) (hy : y.isNormalized)
    (hok : Number.operator_add x y .to_nearest = .ok result) :
    Number.RoundsToRepresentable result (x.toRat + y.toRat) .to_nearest :=
  operator_add_rounded_to_nearest_proof x y result hx hy hok

end XRPL.Model.Protocol
