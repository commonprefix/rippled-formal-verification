import XRPL.Model.Protocol.Number
import XRPL.Model.Protocol.Exponent
import XRPL.Model.Protocol.NumericType

namespace XRPL.Model.Lending

open XRPL.Model.Protocol (Number NumericType Error numberExponent)

-- The amounts of a pool the lending protocol reads and writes
structure PoolAmounts where
  assetsTotal : Number
  assetsAvailable : Number
  assetsReserved : Number
  lossUnrealized : Number

-- Any container of funds a loan broker can draw on to issue loans.
class AssetPool (α : Type) where
  amounts : α → PoolAmounts
  updateAmounts : α → PoolAmounts → Except Error α

def AssetPool.exponent {α : Type} [AssetPool α] (pool : α) (nt : NumericType) : Except Error Int :=
  numberExponent (AssetPool.amounts pool).assetsTotal nt

end XRPL.Model.Lending
