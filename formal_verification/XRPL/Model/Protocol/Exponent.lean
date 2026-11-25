import XRPL.Model.Protocol.Number
import XRPL.Model.Protocol.STAmount

namespace XRPL.Model.Protocol

-- exponent of a Number represented as an STAmount, never finer than `exponent`.
def numberExponent (amount : Number) (exponent : Int) (nt : NumericType) : Except Error Int := do
  if amount.operator_eq Number.zero then
    return exponent

  let amount' ← STAmount.ofNumber nt amount .downward
  return max exponent amount'.exponent

def postSumExponent (amount amountDelta : Number) (exponent : Int) (nt : NumericType)
    : Except Error Int := do
  let sum ← amount.operator_add amountDelta .to_nearest
  numberExponent sum exponent nt

end XRPL.Model.Protocol
