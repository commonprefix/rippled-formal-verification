import XRPL.Model.Protocol.Exponent
import XRPL.Model.Protocol.Number
import XRPL.Model.Protocol.STAmount
import XRPL.Model.Protocol.TER
import XRPL.Model.Lending.AssetPool
import XRPL.Model.Vault.Vault

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol
open XRPL.Model.Lending (PoolBalanceChange)

def Vault.openLimit (v : Vault) : Except Error Number :=
  Number.from_rep 9 (15 + v.baseExponent) largeRange.min largeRange.max .to_nearest

def Vault.exceedsOpenLimit (v : Vault) (amount : Number) : Except Error Bool := do
  let assetsTotal ← v.assetsTotal
  let assetsWithYield ← assetsTotal.operator_add v.yieldUnrealized .towards_zero
  let capacity ← assetsWithYield.operator_add amount .towards_zero
  let openLimit ← v.openLimit
  return capacity.operator_gt openLimit

-- C++ `checkOptionalVaultInflow`: a deposit must keep the total at the base exponent and inside the Open zone.
def Vault.checkOpenLimit (v : Vault) (amount : STAmount) : Except Error TER := do
  let assetsTotal ← v.assetsTotal
  let amountNum ← amount.toNumber .to_nearest
  let exponent ← postSumExponent assetsTotal amountNum v.baseExponent v.numericType

  if exponent != v.baseExponent then
    return .tecLIMIT_EXCEEDED

  let exceedsOpenLimit ← v.exceedsOpenLimit amountNum
  if exceedsOpenLimit then
    return .tecLIMIT_EXCEEDED

  return .tesSUCCESS

def Vault.checkDebitNotDust (v : Vault) (amount : Number) : Except Error TER := do
  if amount.operator_eq Number.zero then
    return .tesSUCCESS

  try
    let assetsAvailable' ← v.assetsAvailable.operator_sub amount .to_nearest
    let storedAvailable ← STAmount.ofNumber v.numericType v.assetsAvailable .to_nearest
    let storedAvailable' ← STAmount.ofNumber v.numericType assetsAvailable' .to_nearest
    if storedAvailable'.operator_eq storedAvailable then
      return .tecPRECISION_LOSS
    return .tesSUCCESS
  catch e =>
    if isOverflow e then
      return .tecPATH_DRY
    else
      throw e

def Vault.adjustBalances (v : Vault) (change : PoolBalanceChange) : TerExcept RawVault := do
  let assetsAvailable ← v.assetsAvailable.operator_add change.cash .to_nearest
  let assetsAvailable' ← STAmount.roundToNumericType v.numericType assetsAvailable .to_nearest
  let assetsDeployed' ← v.assetsDeployed.operator_add change.deployed .to_nearest
  let lossUnrealized' ← v.lossUnrealized.operator_add change.loss .to_nearest
  let assetsReserved' ← v.assetsReserved.operator_add change.reserved .to_nearest
  let yieldUnrealized' ← v.yieldUnrealized.operator_add change.yield .to_nearest

  if assetsAvailable'.signum < 0 || assetsDeployed'.signum < 0 || lossUnrealized'.signum < 0 ||
      yieldUnrealized'.signum < 0 || assetsReserved'.signum < 0 then
    throw .tefBAD_LEDGER

  -- A loan can only be impaired for as much as the vault has lent out.
  if lossUnrealized'.operator_gt assetsDeployed' then
    throw .tecLIMIT_EXCEEDED

  return { v.toRawVault with
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
