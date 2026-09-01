import XRPL.Model.Protocol.Number
import XRPL.Model.Protocol.NumericType
import XRPL.Model.Protocol.STAmount

namespace XRPL.Model.Protocol

def adjustImpreciseNumber (nt : NumericType) (value adjustment : Number) (scale : Int)
    : Except Error Number := do
  let adjusted ← value.operator_add adjustment .to_nearest
  let rounded ← STAmount.roundToNumericType nt adjusted .to_nearest (some scale)
  if rounded.signum < 0 then return Number.zero else return rounded

-- exactly representable at scale (round-down == round-up)
def isRounded (nt : NumericType) (value : Number) (scale : Int) : Except Error Bool := do
  let down ← STAmount.roundToNumericType nt value .downward (some scale)
  let up ← STAmount.roundToNumericType nt value .upward (some scale)
  return down.operator_eq up

end XRPL.Model.Protocol
