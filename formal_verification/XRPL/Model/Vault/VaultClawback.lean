import XRPL.Model.Protocol.Number
import XRPL.Model.Protocol.Rounding
import XRPL.Model.Protocol.STAmount
import XRPL.Model.Protocol.TER
import XRPL.Model.Vault.Vault
import XRPL.Model.Vault.VaultBalances
import XRPL.Model.Vault.VaultWithdraw

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol

def assetsToSharesClawback (v : Vault) (assets holderShares : STAmount) (waiveUnrealizedLoss : Bool)
    : Except Error STAmount := do
  if assets.isZero then
    if waiveUnrealizedLoss then
      return ← STAmount.ofNumber .int64 v.sharesTotal .to_nearest
    return holderShares
  assetsToSharesWithdraw v assets true waiveUnrealizedLoss

def computeClawback (v : Vault) (assets holderShares : STAmount) (waiveUnrealizedLoss : Bool)
    : TerExcept VaultAmounts := do
  try
    let mut sharesDestroyed ← assetsToSharesClawback v assets holderShares waiveUnrealizedLoss
    let mut assetsRecovered ← v.sharesToAssetsWithdraw sharesDestroyed waiveUnrealizedLoss

    let assetsRecoveredNumber ← assetsRecovered.toNumber .to_nearest
    if assetsRecoveredNumber.operator_gt v.assetsAvailable then
      assetsRecovered ← STAmount.ofNumber v.numericType v.assetsAvailable .to_nearest
      sharesDestroyed ← assetsToSharesWithdraw v assetsRecovered true waiveUnrealizedLoss
      assetsRecovered ← v.sharesToAssetsWithdraw sharesDestroyed waiveUnrealizedLoss

      let assetsRecoveredNumber ← assetsRecovered.toNumber .to_nearest
      if assetsRecoveredNumber.operator_gt v.assetsAvailable then
        throw .tecINTERNAL

    let sharesTotal ← STAmount.ofNumber .int64 v.sharesTotal .to_nearest
    if sharesDestroyed.operator_eq sharesTotal && v.assetsDeployed.operator_ne Number.zero then
      throw .tecHAS_OBLIGATIONS

    if !assetsRecovered.isZero then
      assetsRecovered ← clampToSumExponent v.assetsAvailable assetsRecovered.operator_neg v.baseExponent
      if ← assetsRecovered.isFractionalNonPositive then
        throw .tecPRECISION_LOSS
    return { assets := assetsRecovered, shares := sharesDestroyed }
  catch e : Error =>
    if isOverflow e then
      throw .tecPATH_DRY
    else
      throwThe Error e


-- `hnn`: the preflight check `sfAmount >= 0` passed (zero means all); callers outside the model check it
def Vault.clawback (v : Vault) (assets holderShares : STAmount) (waiveUnrealizedLoss : Bool)
    (_hnn : 0 ≤ assets.toRat) : TerExcept VaultWithAmounts := do
  let amounts ← computeClawback v assets holderShares waiveUnrealizedLoss

  if amounts.shares.isZero then
    throw .tecPRECISION_LOSS

  let assetsNumber ← amounts.assets.toNumber .to_nearest
  let dustCheck ← v.checkDebitNotDust assetsNumber
  if dustCheck != .tesSUCCESS then
    throw dustCheck

  let rawVault' ← v.adjustAssetsAndShares amounts.assets.operator_neg amounts.shares.operator_neg
  let v' ← rawVault'.to_lawful
  return { amounts with vault' := v' }

end XRPL.Model.SingleAssetVault
