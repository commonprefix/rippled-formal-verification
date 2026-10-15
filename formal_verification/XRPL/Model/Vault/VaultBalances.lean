import XRPL.Model.Protocol.Exponent
import XRPL.Model.Protocol.Number
import XRPL.Model.Protocol.STAmount
import XRPL.Model.Protocol.TER
import XRPL.Model.Lending.AssetPool
import XRPL.Model.Vault.Vault

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol
open XRPL.Model.Lending (PoolBalanceChange)

def RawVault.openLimit (rv : RawVault) : Except Error Number :=
  Number.from_rep 9 (15 + rv.baseExponent) largeRange.min largeRange.max .to_nearest

def RawVault.exceedsOpenLimit (rv : RawVault) (amount : Number) : Except Error Bool := do
  let assetsTotal ← rv.assetsTotal
  let assetsWithYield ← assetsTotal.operator_add rv.yieldUnrealized .towards_zero
  let capacity ← assetsWithYield.operator_add amount .towards_zero
  let openLimit ← rv.openLimit
  return capacity.operator_gt openLimit

def RawVault.checkOptionalInflow (rv : RawVault) (amount : STAmount) : Except Error TER := do
  let assetsTotal ← rv.assetsTotal
  let amountNum ← amount.toNumber .to_nearest
  let exponent ← postSumExponent assetsTotal amountNum rv.baseExponent rv.numericType

  if exponent != rv.baseExponent then
    return .tecLIMIT_EXCEEDED

  let exceedsOpenLimit ← rv.exceedsOpenLimit amountNum
  if exceedsOpenLimit then
    return .tecLIMIT_EXCEEDED

  return .tesSUCCESS

def RawVault.checkDebitNotDust (rv : RawVault) (amount : Number) : Except Error TER := do
  if amount.operator_eq Number.zero then
    return .tesSUCCESS

  try
    let assetsAvailable' ← rv.assetsAvailable.operator_sub amount .to_nearest
    let storedAvailable ← STAmount.ofNumber rv.numericType rv.assetsAvailable .to_nearest
    let storedAvailable' ← STAmount.ofNumber rv.numericType assetsAvailable' .to_nearest
    if storedAvailable'.operator_eq storedAvailable then
      return .tecPRECISION_LOSS
    return .tesSUCCESS
  catch e =>
    if isOverflow e then
      return .tecPATH_DRY
    else
      throw e

def RawVault.adjustBalances (rv : RawVault) (change : PoolBalanceChange) : TerExcept RawVault := do
  let assetsAvailable ← rv.assetsAvailable.operator_add change.cash .to_nearest
  let assetsAvailable' ← STAmount.roundToNumericType rv.numericType assetsAvailable .to_nearest
  let assetsDeployed' ← rv.assetsDeployed.operator_add change.deployed .to_nearest
  let lossUnrealized' ← rv.lossUnrealized.operator_add change.loss .to_nearest
  let assetsReserved' ← rv.assetsReserved.operator_add change.reserved .to_nearest
  let yieldUnrealized' ← rv.yieldUnrealized.operator_add change.yield .to_nearest

  if assetsAvailable'.signum < 0 || assetsDeployed'.signum < 0 || lossUnrealized'.signum < 0 ||
      yieldUnrealized'.signum < 0 || assetsReserved'.signum < 0 then
    throw .tefBAD_LEDGER

  -- A loan can only be impaired for as much as the vault has lent out.
  if lossUnrealized'.operator_gt assetsDeployed' then
    throw .tecLIMIT_EXCEEDED

  return { rv with
    assetsAvailable := assetsAvailable'
    assetsDeployed := assetsDeployed'
    assetsReserved := assetsReserved'
    lossUnrealized := lossUnrealized'
    yieldUnrealized := yieldUnrealized' }

def Vault.adjustAssetsAndShares (v : Vault) (assets shares : STAmount) : TerExcept RawVault := do
  let assetsNum ← assets.toNumber .to_nearest
  let sharesNum ← shares.toNumber .to_nearest
  let sharesTotal' ← v.sharesTotal.operator_add sharesNum .to_nearest

  let rawVault' ← v.adjustBalances { cash := assetsNum }
  return { rawVault' with sharesTotal := sharesTotal' }

end XRPL.Model.SingleAssetVault
