import XRPL.Properties.Protocol.Number.Sub.Common.RoundsToRepresentableProofs
import XRPL.Properties.Protocol.Number.Add.Common.ToNearest.Nearest

/-! # `operator_sub` rounds to a neighbouring `Number`

`x - y` is computed as `x + (-y)`. The result is the largest `Number` at or below the exact value (`downward`), the
smallest at or above it (`upward`), the one of these two nearer zero (`towards_zero`), or either of them
(`to_nearest`). `downward` and `upward` assume a nonzero result, since a value too small for a `Number` becomes zero. -/

namespace XRPL.Model.Protocol

theorem Number.operator_sub_rounded_downward (x y result : Number)
    (hx : x.isNormalized) (hy : y.isNormalized)
    (hok : Number.operator_sub x y .downward = .ok result)
    (hresult : result.mantissa_ ≠ 0) :
    Number.RoundsToRepresentable result (x.toRat - y.toRat) .downward :=
  Number.operator_sub_rounded_downward_proof x y result hx hy hok hresult

theorem Number.operator_sub_rounded_upward (x y result : Number)
    (hx : x.isNormalized) (hy : y.isNormalized)
    (hok : Number.operator_sub x y .upward = .ok result)
    (hresult : result.mantissa_ ≠ 0) :
    Number.RoundsToRepresentable result (x.toRat - y.toRat) .upward :=
  Number.operator_sub_rounded_upward_proof x y result hx hy hok hresult

theorem Number.operator_sub_rounded_towards_zero (x y result : Number)
    (hx : x.isNormalized) (hy : y.isNormalized)
    (hok : Number.operator_sub x y .towards_zero = .ok result) :
    Number.RoundsToRepresentable result (x.toRat - y.toRat) .towards_zero :=
  Number.operator_sub_rounded_towards_zero_proof x y result hx hy hok

theorem Number.operator_sub_rounded_to_nearest (x y result : Number)
    (hx : x.isNormalized) (hy : y.isNormalized)
    (hok : Number.operator_sub x y .to_nearest = .ok result) :
    Number.RoundsToRepresentable result (x.toRat - y.toRat) .to_nearest :=
  Number.operator_sub_rounded_to_nearest_proof x y result hx hy hok

/-- A `to_nearest` subtraction of normalized Numbers returns a nearest Number, unless it flushes a nonzero
difference to zero. -/
theorem Number.operator_sub_nearest (x y result : Number)
    (hx : x.isNormalized) (hy : y.isNormalized)
    (hok : Number.operator_sub x y .to_nearest = .ok result)
    (hresult : result.mantissa_ ≠ 0 ∨ x.toRat - y.toRat = 0) :
    result.RoundsToNearest (x.toRat - y.toRat) :=
  Number.operator_sub_nearest_proof x y result hx hy hok hresult

end XRPL.Model.Protocol
