import XRPL.Properties.Protocol.Number.Mul.Common.Downward.RoundedHelpers
import XRPL.Properties.Protocol.Number.Mul.Common.Upward.RoundedHelpers
import XRPL.Properties.Protocol.Number.Mul.Common.TowardsZero.RoundedHelpers
import XRPL.Properties.Protocol.Number.Mul.Common.ToNearest.RoundedHelpers

/-! # `operator_mul` rounds to a neighbouring `Number`

The result is the neighbouring `Number` on the side the mode asks for, or either neighbour in `to_nearest`.
`downward` and `upward` assume a nonzero result, since a value too small for a `Number` becomes zero. -/

namespace XRPL.Model.Protocol

theorem Number.operator_mul_rounded_downward (x y result : Number)
    (hx : x.isNormalized) (hy : y.isNormalized)
    (hok : Number.operator_mul x y .downward = .ok result)
    (hresult : result.mantissa_ ≠ 0) :
    Number.RoundsToRepresentable result (x.toRat * y.toRat) .downward := by
  sorry

theorem Number.operator_mul_rounded_upward (x y result : Number)
    (hx : x.isNormalized) (hy : y.isNormalized)
    (hok : Number.operator_mul x y .upward = .ok result)
    (hresult : result.mantissa_ ≠ 0) :
    Number.RoundsToRepresentable result (x.toRat * y.toRat) .upward := by
  sorry

theorem Number.operator_mul_rounded_towards_zero (x y result : Number)
    (hx : x.isNormalized) (hy : y.isNormalized)
    (hok : Number.operator_mul x y .towards_zero = .ok result) :
    Number.RoundsToRepresentable result (x.toRat * y.toRat) .towards_zero := by
  sorry

theorem Number.operator_mul_rounded_to_nearest (x y result : Number)
    (hx : x.isNormalized) (hy : y.isNormalized)
    (hok : Number.operator_mul x y .to_nearest = .ok result) :
    Number.RoundsToRepresentable result (x.toRat * y.toRat) .to_nearest := by
  sorry

end XRPL.Model.Protocol
