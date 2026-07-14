import XRPL.Model.Protocol.STAmount
import XRPL.Model.Protocol.Number
import XRPL.Model.Protocol.TER
import XRPL.Model.Vault.Vault

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol

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
  -- (waiting the C++ fix) round the payout down so a withdrawer never receives more than the shares are worth
  let assets ← STAmount.ofNumber vault.asset assetsNumber .downward
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



def computeWithdrawByAssets (vault : Vault) (assets : STAmount) (waiveUnrealizedLoss : Bool) : Except String ComputeWithdrawResult := do
  try
    let result : ComputeWithdrawResult := ⟨none, assets, STAmount.ofAsset vault.sharesAsset⟩
    -- truncateShares = false in fn call
    let shares ← assetsToSharesWithdraw vault assets false waiveUnrealizedLoss
    if shares.isZero then
      return {result with error := some .tecPRECISION_LOSS}

    let assets' ← Vault.sharesToAssetsWithdraw vault shares waiveUnrealizedLoss
    return {result with
      assets' := assets',
      sharesRedeemed := shares}
  catch e =>
    if isOverflow e then
      return ⟨.some .tecPATH_DRY, assets, STAmount.ofAsset vault.sharesAsset⟩
    else
      throw e


def computeWithdrawByShares (vault : Vault) (shares : STAmount) (waiveUnrealizedLoss : Bool) : Except String ComputeWithdrawResult := do
  try
    let result : ComputeWithdrawResult := ⟨none, STAmount.ofAsset vault.asset, shares⟩
    let assets ← Vault.sharesToAssetsWithdraw vault shares waiveUnrealizedLoss
    return {result with
      assets' := assets,
      sharesRedeemed := shares}
  catch e =>
    if isOverflow e then
      return ⟨.some .tecPATH_DRY, STAmount.ofAsset vault.asset, shares⟩
    else
      throw e


-- withdrawal amount, either as vault assets or as vault shares
inductive WithdrawAmount where
  | vaultAssets (amount : STAmount)
  | vaultShares (amount : STAmount)

-- withdraw assets from the vault
-- returns an optional error, or the updated vault state, the amount withdrawn, and the shares redeemed
def Vault.withdraw (vault : Vault) (amount : WithdrawAmount) (waiveUnrealizedLoss : Bool) : Except String WithdrawResult := do
  let result ← match amount with
    | .vaultAssets assets => computeWithdrawByAssets vault assets waiveUnrealizedLoss
    | .vaultShares shares => computeWithdrawByShares vault shares waiveUnrealizedLoss
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
  let assetsTotal' ← vault.assetsTotal.operator_sub assetsNumber' .to_nearest

  -- (waiting the C++ fix) reject a payout too small to reduce the stored assetsTotal
  let assetsTotalRounded ← STAmount.ofNumber vault.asset vault.assetsTotal .to_nearest
  let assetsTotalRounded' ← STAmount.ofNumber vault.asset assetsTotal' .to_nearest
  if assetsNumber'.mantissa_ != 0 && assetsTotalRounded.operator_eq assetsTotalRounded' then
    return ⟨.some .tecPRECISION_LOSS, vault, result.assets', result.sharesRedeemed⟩

  let vault' := {vault with
    assetsAvailable := ← vault.assetsAvailable.operator_sub assetsNumber' .to_nearest,
    assetsTotal := assetsTotal',
    sharesTotal := ← vault.sharesTotal.operator_sub sharesBurnedNumber .to_nearest,}

  return ⟨none, vault', result.assets', result.sharesRedeemed⟩


end XRPL.Model.SingleAssetVault
