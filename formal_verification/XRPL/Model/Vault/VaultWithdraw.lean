import XRPL.Model.Protocol.Number
import XRPL.Model.Protocol.Rounding
import XRPL.Model.Protocol.STAmount
import XRPL.Model.Protocol.TER
import XRPL.Model.Protocol.TenthBips
import XRPL.Model.Vault.Vault
import XRPL.Model.Vault.VaultBalances

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol

def Vault.assetsTotalForWithdrawal (v : Vault) (waiveUnrealizedLoss : Bool) : Except Error Number := do
  let assetsTotal ← v.assetsTotal

  let lossUnrealized := match waiveUnrealizedLoss with
  | true => Number.zero
  | false => v.lossUnrealized

  assetsTotal.operator_sub lossUnrealized .to_nearest

-- if the amount supplied for the withdrawal is specified as an amount of shares, this function
-- calculates the amount of assets that will be withdrawn from the vault.
def Vault.sharesToAssetsWithdraw (v : Vault) (shares : STAmount) (waiveUnrealizedLoss : Bool) : Except Error STAmount := do
  let netAssetValue ← v.assetsTotalForWithdrawal waiveUnrealizedLoss

  if netAssetValue.mantissa_ == 0 then
    return STAmount.zero v.numericType

  let sharesNumber ← shares.toNumber .to_nearest
  let NAVShares ← netAssetValue.operator_mul sharesNumber .to_nearest
  let assetsNumber ← NAVShares.operator_div v.sharesTotal .to_nearest
  let assets ← STAmount.ofNumber v.numericType assetsNumber .to_nearest
  return assets


def assetsToSharesWithdraw (v : Vault) (assets : STAmount) (truncateShares waiveUnrealizedLoss : Bool) : Except Error STAmount := do
  let netAssetValue ← v.assetsTotalForWithdrawal waiveUnrealizedLoss

  if netAssetValue.mantissa_ == 0 then
    return STAmount.zero .int64

  let assetsNumber ← assets.toNumber .to_nearest
  let sharesAssets ← v.sharesTotal.operator_mul assetsNumber .to_nearest
  let sharesNumber ← sharesAssets.operator_div netAssetValue .to_nearest
  let sharesNumber ← match truncateShares with
  | true => sharesNumber.truncate
  | false => pure sharesNumber

  STAmount.ofNumber .int64 sharesNumber .to_nearest

-- withdrawal amount, either as vault assets or as vault shares
inductive WithdrawAmount where
  | vaultAssets (amount : STAmount)
  | vaultShares (amount : STAmount)

def WithdrawAmount.amount : WithdrawAmount → STAmount
  | .vaultAssets a => a
  | .vaultShares s => s

def computeWithdraw (v : Vault) (amount : WithdrawAmount) (waiveUnrealizedLoss : Bool) : TerExcept VaultAmounts := do
  try
    let shares ← match amount with
      | .vaultShares shares => pure shares
      | .vaultAssets assets => assetsToSharesWithdraw v assets true waiveUnrealizedLoss
    if shares.isZero then
      throw .tecPRECISION_LOSS

    let assets ← v.sharesToAssetsWithdraw shares waiveUnrealizedLoss
    return { assets := assets, shares := shares }
  catch e : Error =>
    if isOverflow e then
      throw .tecPATH_DRY
    else
      throwThe Error e

-- withdraw assets from the vault
-- returns the updated vault, the assets withdrawn and the shares redeemed, or the TER that rejects it
-- `hpos`: the preflight check `sfAmount > 0` passed; callers outside the model check it
def Vault.withdraw (v : Vault) (amount : WithdrawAmount) (waiveUnrealizedLoss : Bool) (parentCloseTime : UInt32)
    (_hpos : 0 < amount.amount.toRat) : TerExcept VaultWithAmounts := do
  -- a vault with an early-exit fee rate, even a zero one, allows withdrawals in the investment phase
  if v.earlyExitFeeRate.isNone && v.phase parentCloseTime == .investment then
    throw .tecTOO_SOON

  let amounts ← computeWithdraw v amount waiveUnrealizedLoss

  let sharesTotalAmount ← STAmount.ofNumber .int64 v.sharesTotal .to_nearest
  let isFinalWithdrawal := amounts.shares.operator_eq sharesTotalAmount
  if isFinalWithdrawal && v.assetsDeployed.operator_ne Number.zero then
    throw .tecHAS_OBLIGATIONS

  let mut assets' := amounts.assets
  let assetsNumber' ← assets'.toNumber .to_nearest
  if !isFinalWithdrawal then
    let isByShares := match amount with | .vaultShares _ => true | .vaultAssets _ => false
    let netAssetValue ← v.assetsTotalForWithdrawal waiveUnrealizedLoss
    if isByShares && assets'.isZero && netAssetValue.operator_ne Number.zero then
      throw .tecPRECISION_LOSS

    let dustCheck ← v.checkDebitNotDust assetsNumber'
    if dustCheck != .tesSUCCESS then
      throw dustCheck

  if !isFinalWithdrawal && !assets'.isZero then
    -- the shares are burned for the whole amount, the early-exit fee stays in the vault
    let feeRate := v.earlyExitFeeRateAt parentCloseTime
    if feeRate == 0 && v.assetsAvailable.operator_lt assetsNumber' then
      throw .tecINSUFFICIENT_FUNDS

    try
      if feeRate == maxEarlyExitFeeRate then
        assets' := STAmount.zero v.numericType
      else
        let fee ← tenthBipsOfValue assetsNumber' feeRate .upward
        let payoutNumber ← assetsNumber'.operator_sub fee .downward
        let payout ← STAmount.ofNumber v.numericType payoutNumber .downward
        if payout.isZero then
          throw .tecPRECISION_LOSS
        assets' ← clampToSumExponent v.assetsAvailable payout.operator_neg v.baseExponent
        if ← assets'.isFractionalNonPositive then
          throw .tecPRECISION_LOSS
    catch e : Error =>
      if isOverflow e then throw .tecPATH_DRY else throwThe Error e

  let payoutNumber ← assets'.toNumber .to_nearest
  if v.assetsAvailable.operator_lt payoutNumber then
    throw .tecINSUFFICIENT_FUNDS

  if isFinalWithdrawal then
    if v.lossUnrealized.operator_ne Number.zero then
      throw .tefINTERNAL
    assets' ← STAmount.ofNumber v.numericType v.assetsAvailable .to_nearest

  let rawVault' ← v.adjustAssetsAndShares assets'.operator_neg amounts.shares.operator_neg
  let v' ← rawVault'.to_lawful

  return { vault' := v', assets := assets', shares := amounts.shares }


end XRPL.Model.SingleAssetVault
