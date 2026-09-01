import XRPL.Model.Protocol.Number
import XRPL.Model.Protocol.STAmount

namespace XRPL.Model.Protocol

-- exponent of a Number represented as an STAmount. Models the function `scale` from xrpld
def numberExponent (amount : Number) (nt : NumericType) : Except Error Int := do
  let a ← STAmount.ofNumber nt amount .to_nearest
  return a.exponent

end XRPL.Model.Protocol
