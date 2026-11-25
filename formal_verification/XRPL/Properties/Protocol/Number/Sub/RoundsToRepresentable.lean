import XRPL.Properties.Protocol.Number.Sub.Common.RoundsToRepresentableProofs
import XRPL.Properties.Protocol.Number.Add.Common.ToNearest.Nearest

/-! # `operator_sub` rounds to a neighbouring `Number`

`x - y` is `x + (-y)`, so the result is the neighbouring `Number` on the side the mode asks for, or either neighbour
in `to_nearest`. `downward` and `upward` assume a nonzero result. -/

namespace XRPL.Model.Protocol

theorem Number.operator_sub_rounded_downward (x y result : Number)
    (hx : x.isNormalized) (hy : y.isNormalized)
    (hok : Number.operator_sub x y .downward = .ok result)
    (hresult : result.mantissa_ ≠ 0) :
    Number.RoundsToRepresentable result (x.toRat - y.toRat) .downward := by
  sorry

theorem Number.operator_sub_rounded_upward (x y result : Number)
    (hx : x.isNormalized) (hy : y.isNormalized)
    (hok : Number.operator_sub x y .upward = .ok result)
    (hresult : result.mantissa_ ≠ 0) :
    Number.RoundsToRepresentable result (x.toRat - y.toRat) .upward := by
  sorry

theorem Number.operator_sub_rounded_towards_zero (x y result : Number)
    (hx : x.isNormalized) (hy : y.isNormalized)
    (hok : Number.operator_sub x y .towards_zero = .ok result) :
    Number.RoundsToRepresentable result (x.toRat - y.toRat) .towards_zero := by
  sorry

theorem Number.operator_sub_rounded_to_nearest (x y result : Number)
    (hx : x.isNormalized) (hy : y.isNormalized)
    (hok : Number.operator_sub x y .to_nearest = .ok result) :
    Number.RoundsToRepresentable result (x.toRat - y.toRat) .to_nearest := by
  sorry

/-- A `to_nearest` subtraction of normalized Numbers returns a nearest Number, unless it flushes a nonzero
difference to zero. -/
theorem Number.operator_sub_nearest (x y result : Number)
    (hx : x.isNormalized) (hy : y.isNormalized)
    (hok : Number.operator_sub x y .to_nearest = .ok result)
    (hresult : result.mantissa_ ≠ 0 ∨ x.toRat - y.toRat = 0) :
    result.RoundsToNearest (x.toRat - y.toRat) := by
  sorry

end XRPL.Model.Protocol
