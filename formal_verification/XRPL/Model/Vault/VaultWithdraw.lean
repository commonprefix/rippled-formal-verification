import XRPL.Model.Protocol.Number
import XRPL.Model.Protocol.STAmount
import XRPL.Model.Protocol.TER
import XRPL.Model.Vault.Vault

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol

-- if the amount supplied for the withdrawal is specified as an amount of shares, this function
-- calculates the amount of assets that will be withdrawn from the vault.
def LawfulVault.sharesToAssetsWithdraw (lv : LawfulVault) (shares : STAmount) (waiveUnrealizedLoss : Bool) : Except Error STAmount := do
  let lossUnrealized := match waiveUnrealizedLoss with
  | true => Number.zero
  | false => lv.lossUnrealized

  let netAssetValue ← lv.assetsTotal.operator_sub lossUnrealized .to_nearest

  if netAssetValue.mantissa_ == 0 then
    return STAmount.zero lv.numericType

  let sharesNumber ← shares.toNumber .to_nearest
  let NAVShares ← netAssetValue.operator_mul sharesNumber .to_nearest
  let assetsNumber ← NAVShares.operator_div lv.sharesTotal .to_nearest
  -- (waiting the C++ fix) round the payout down so a withdrawer never receives more than the shares are worth
  let assets ← STAmount.ofNumber lv.numericType assetsNumber .downward
  return assets


structure WithdrawResult where
  error : Option TER
  vault' : LawfulVault
  assets' : STAmount
  sharesBurned : STAmount

-- A rejection changes nothing and reports nothing: the vault is returned
-- unchanged and both amount fields are zero.
def WithdrawResult.rejected (lv : LawfulVault) (ter : TER) : WithdrawResult :=
  ⟨some ter, lv, STAmount.zero lv.numericType, STAmount.zero .int64⟩


def assetsToSharesWithdraw (lv : LawfulVault) (assets : STAmount) (truncateShares waiveUnrealizedLoss : Bool) : Except Error STAmount := do
  let lossUnrealized := match waiveUnrealizedLoss with
  | true => Number.zero
  | false => lv.lossUnrealized

  let netAssetValue ← lv.assetsTotal.operator_sub lossUnrealized .to_nearest

  if netAssetValue.mantissa_ == 0 then
    return STAmount.zero .int64

  let assetsNumber ← assets.toNumber .to_nearest
  let sharesAssets ← lv.sharesTotal.operator_mul assetsNumber .to_nearest
  let sharesNumber ← sharesAssets.operator_div netAssetValue .to_nearest
  let sharesNumber ← match truncateShares with
  | true => sharesNumber.truncate
  | false => pure sharesNumber

  STAmount.ofNumber .int64 sharesNumber .to_nearest


structure ComputeWithdrawResult where
  error : Option TER
  assets' : STAmount
  sharesRedeemed : STAmount



def computeWithdrawByAssets (lv : LawfulVault) (assets : STAmount) (waiveUnrealizedLoss : Bool) : Except Error ComputeWithdrawResult := do
  try
    -- truncateShares = false in fn call
    let shares ← assetsToSharesWithdraw lv assets false waiveUnrealizedLoss
    if shares.isZero then
      return ⟨some .tecPRECISION_LOSS, STAmount.zero lv.numericType, STAmount.zero .int64⟩

    let assets' ← lv.sharesToAssetsWithdraw shares waiveUnrealizedLoss
    return ⟨none, assets', shares⟩
  catch e =>
    if isOverflow e then
      return ⟨.some .tecPATH_DRY, STAmount.zero lv.numericType, STAmount.zero .int64⟩
    else
      throw e


def computeWithdrawByShares (lv : LawfulVault) (shares : STAmount) (waiveUnrealizedLoss : Bool) : Except Error ComputeWithdrawResult := do
  try
    let assets ← lv.sharesToAssetsWithdraw shares waiveUnrealizedLoss
    return ⟨none, assets, shares⟩
  catch e =>
    if isOverflow e then
      return ⟨.some .tecPATH_DRY, STAmount.zero lv.numericType, STAmount.zero .int64⟩
    else
      throw e


-- withdrawal amount, either as vault assets or as vault shares
inductive WithdrawAmount where
  | vaultAssets (amount : STAmount)
  | vaultShares (amount : STAmount)

-- withdraw assets from the vault
-- returns an optional error, or the updated vault state, the amount withdrawn, and the shares redeemed
def LawfulVault.withdraw (lv : LawfulVault) (amount : WithdrawAmount) (waiveUnrealizedLoss : Bool) : Except Error WithdrawResult := do
  let vault := lv.toRawVault
  let result ← match amount with
    | .vaultAssets assets => computeWithdrawByAssets lv assets waiveUnrealizedLoss
    | .vaultShares shares => computeWithdrawByShares lv shares waiveUnrealizedLoss
  if result.error.isSome then
    return ⟨result.error, lv, STAmount.zero lv.numericType, STAmount.zero .int64⟩

  let assetsNumber' ← result.assets'.toNumber .to_nearest
  if vault.assetsAvailable.operator_lt assetsNumber' then
    return .rejected lv .tecINSUFFICIENT_FUNDS

  let sharesTotalAmount ← STAmount.ofNumber .int64 vault.sharesTotal .to_nearest
  if result.sharesRedeemed.operator_eq sharesTotalAmount then -- isFinalWithdrawal
    if vault.lossUnrealized.operator_ne Number.zero then
      return .rejected lv .tefINTERNAL
    let allAvailable ← STAmount.ofNumber vault.numericType vault.assetsAvailable .to_nearest
    let assets' := allAvailable
    let vault' := {vault with
      assetsAvailable := Number.zero,
      assetsTotal := Number.zero,
      sharesTotal := Number.zero}
    let lv' ← vault'.to_lawful
    return ⟨none, lv', assets', result.sharesRedeemed⟩

  let sharesBurnedNumber ← result.sharesRedeemed.toNumber .to_nearest
  let assetsTotal' ← vault.assetsTotal.operator_sub assetsNumber' .to_nearest

  -- (waiting the C++ fix) reject a payout too small to reduce the stored assetsTotal
  let assetsTotalRounded ← STAmount.ofNumber vault.numericType vault.assetsTotal .to_nearest
  let assetsTotalRounded' ← STAmount.ofNumber vault.numericType assetsTotal' .to_nearest
  if assetsNumber'.mantissa_ != 0 && assetsTotalRounded.operator_eq assetsTotalRounded' then
    return .rejected lv .tecPRECISION_LOSS

  let vault' := {vault with
    assetsAvailable := ← vault.assetsAvailable.operator_sub assetsNumber' .to_nearest,
    assetsTotal := assetsTotal',
    sharesTotal := ← vault.sharesTotal.operator_sub sharesBurnedNumber .to_nearest,}

  let lv' ← vault'.to_lawful
  return ⟨none, lv', result.assets', result.sharesRedeemed⟩


end XRPL.Model.SingleAssetVault
