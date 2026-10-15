import XRPL.Model.Protocol.Number
import XRPL.Model.Protocol.Exponent
import XRPL.Model.Protocol.NumericType
import XRPL.Model.Protocol.TER

namespace XRPL.Model.Lending

open XRPL.Model.Protocol (Number NumericType TerExcept Error numberExponent)

-- C++ `VaultPhase`: the lifecycle phase of a closed-ended pool. An open-ended pool has none.
inductive PoolPhase where
  | noPhase
  | subscription
  | investment
  | redemption
  deriving DecidableEq, Repr

-- C++ `VaultBalanceChange`: signed changes to the balances of a pool, zero when absent.
structure PoolBalanceChange where
  cash : Number := Number.zero
  deployed : Number := Number.zero
  yield : Number := Number.zero
  loss : Number := Number.zero
  reserved : Number := Number.zero

-- The amounts of a pool the lending protocol reads
structure PoolAmounts where
  assetsAvailable : Number
  assetsDeployed : Number
  assetsReserved : Number
  lossUnrealized : Number
  yieldUnrealized : Number

-- Any container of funds a loan broker can draw on to issue loans.
class AssetPool (α : Type) where
  amounts : α → PoolAmounts
  assetsTotal : α → Except Error Number
  baseExponent : α → Int
  phase : α → UInt32 → PoolPhase
  redemptionDate : α → Option UInt32
  openLimit : α → Except Error Number
  exceedsOpenLimit : α → Number → Except Error Bool
  adjustBalances : α → PoolBalanceChange → TerExcept α

-- The exponent of `assetsTotal`, never finer than the base exponent
def AssetPool.exponent {α : Type} [AssetPool α] (pool : α) (nt : NumericType) : Except Error Int := do
  let assetsTotal ← AssetPool.assetsTotal pool
  let baseExponent := AssetPool.baseExponent pool
  numberExponent assetsTotal baseExponent nt

end XRPL.Model.Lending
