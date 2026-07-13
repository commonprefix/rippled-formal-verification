import XRPL.Model.Protocol.STAmount
import XRPL.Model.Protocol.Number
import XRPL.Model.Protocol.TER
import XRPL.Model.Vault.Vault
import XRPL.Model.Vault.Helpers

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault

-- if the amount supplied for the withdrawal is specified as an amount of shares, this function
-- calculates the amount of assets that will be withdrawn from the vault.
def Vault.sharesToAssetsWithdraw (vault : Vault) (shares : STAmount) (waiveUnrealizedLoss : Bool) : Except String STAmount := do
  let lossUnrealized := match waiveUnrealizedLoss with
  | true => Number.zero
  | false => vault.lossUnrealized

  let netAssetValue ← vault.assetsTotal.operator_sub vault.interestUnrealized .to_nearest
  let netAssetValue ← netAssetValue.operator_sub lossUnrealized .to_nearest
  
  if netAssetValue.mantissa_ == 0 then
    return STAmount.ofAsset vault.asset

  let sharesNumber ← shares.toNumber .to_nearest
  let NAVShares ← netAssetValue.operator_mul sharesNumber .to_nearest
  let assetsNumber ← NAVShares.operator_div vault.sharesTotal .to_nearest
  let assets ← STAmount.ofNumber vault.asset assetsNumber .to_nearest
  return assets


structure WithdrawResult where
  error : Option TER
  vault' : Vault
  assets' : STAmount
  sharesBurned : STAmount


def assetsToSharesWithdraw (vault : Vault) (assets : STAmount) (truncateShares waiveUnrealizedLoss : Bool) : Except String STAmount := do
  let lossUnrealized := match waiveUnrealizedLoss with
  | true => Number.zero
  | false => vault.lossUnrealized

  let netAssetValue ← vault.assetsTotal.operator_sub vault.interestUnrealized .to_nearest
  let netAssetValue ← netAssetValue.operator_sub lossUnrealized .to_nearest

  if netAssetValue.mantissa_ == 0 then
    return STAmount.ofAsset vault.sharesAsset

  let assetsNumber ← assets.toNumber .to_nearest
  let sharesAssets ← vault.sharesTotal.operator_mul assetsNumber .to_nearest
  let sharesNumber ← sharesAssets.operator_div netAssetValue .to_nearest
  let sharesNumber ← match truncateShares with
  | true => sharesNumber.truncate
  | false => pure sharesNumber

  STAmount.ofNumber vault.sharesAsset sharesNumber .to_nearest


structure ComputeWithdrawResult where
  error : Option TER
  assets' : STAmount
  sharesRedeemed : STAmount




def computeWithdrawByAssets (vault : Vault) (assets : STAmount) : Except String ComputeWithdrawResult := do
  try
    let result : ComputeWithdrawResult := ⟨none, assets, STAmount.ofAsset vault.sharesAsset⟩
    -- waiveUnrealizedLoss = false by default value, defined in header file
    -- truncateShares = false in fn call
    let shares ← assetsToSharesWithdraw vault assets false false
    if shares.isZero then
      return {result with error := some .tecPRECISION_LOSS}

    -- truncateShares = false in fn call
    let assets' ← Vault.sharesToAssetsWithdraw vault shares false
    return {result with
      assets' := assets',
      sharesRedeemed := shares}
  catch e =>
    if isOverflow e then
      return ⟨.some .tecPATH_DRY, assets, STAmount.ofAsset vault.sharesAsset⟩
    else
      throw e


def computeWithdrawByShares (vault : Vault) (shares : STAmount) : Except String ComputeWithdrawResult := do
  try
    let result : ComputeWithdrawResult := ⟨none, STAmount.ofAsset vault.asset, shares⟩
    -- waiveUnrealizedLoss = false by default value, defined in header file
    let assets ← Vault.sharesToAssetsWithdraw vault shares false
    return {result with
      assets' := assets,
      sharesRedeemed := shares}
  catch e =>
    if isOverflow e then
      return ⟨.some .tecPATH_DRY, STAmount.ofAsset vault.asset, shares⟩
    else
      throw e


inductive WithdrawAmount where
  | vaultAssets (amount : STAmount)
  | vaultShares (amount : STAmount)


-- withdraw assets from the vault
-- returns an optional error, or the updated vault state, the amount withdrawn, and the shares redeemed
def Vault.withdraw (vault : Vault) (assets : STAmount) : Except String WithdrawResult := do
  let result ← if assets.asset == vault.asset then
      let result ← computeWithdrawByAssets vault assets
      pure result
    else if assets.asset == vault.sharesAsset then
      let result ← computeWithdrawByShares vault assets
      pure result
    else
      throw "Invalid asset for withdrawal"
  if result.error.isSome then
    return ⟨result.error, vault, result.assets', result.sharesRedeemed⟩

  let assetsNumber' ← result.assets'.toNumber .to_nearest
  if vault.assetsAvailable.operator_lt assetsNumber' then
    return ⟨.some .tecINSUFFICIENT_FUNDS, vault, result.assets', result.sharesRedeemed⟩

  let sharesTotalAmount ← STAmount.ofNumber vault.sharesAsset vault.sharesTotal .to_nearest
  if result.sharesRedeemed.operator_eq sharesTotalAmount then -- isFinalWithdrawal
    if vault.lossUnrealized.operator_ne Number.zero then
      return ⟨.some .tefINTERNAL, vault, result.assets', result.sharesRedeemed⟩
    let allAvailable ← STAmount.ofNumber vault.asset vault.assetsAvailable .to_nearest
    let assets' := allAvailable
    let vault' := {vault with
      assetsAvailable := Number.zero,
      assetsTotal := Number.zero,
      sharesTotal := Number.zero}
    return ⟨none, vault', assets', result.sharesRedeemed⟩

  let sharesBurnedNumber ← result.sharesRedeemed.toNumber .to_nearest
  let vault' := {vault with
    assetsAvailable := ← vault.assetsAvailable.operator_sub assetsNumber' .to_nearest,
    assetsTotal := ← vault.assetsTotal.operator_sub assetsNumber' .to_nearest,
    sharesTotal := ← vault.sharesTotal.operator_sub sharesBurnedNumber .to_nearest,}

  return ⟨none, vault', result.assets', result.sharesRedeemed⟩
  
end XRPL.Model.SingleAssetVault




