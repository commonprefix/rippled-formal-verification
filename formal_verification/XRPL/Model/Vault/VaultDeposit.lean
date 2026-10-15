import XRPL.Model.Protocol.Number
import XRPL.Model.Protocol.Rounding
import XRPL.Model.Protocol.STAmount
import XRPL.Model.Protocol.TER
import XRPL.Model.Vault.Vault
import XRPL.Model.Vault.VaultBalances

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol

-- Round the deposit down to the new total's exponent, rejecting it if nothing is left.
def Vault.roundedDepositAmount (v : Vault) (amountDeposit : STAmount) : TerExcept STAmount := do
  let assetsTotal ← v.assetsTotal

  let roundedAmount ← clampToSumExponent assetsTotal amountDeposit v.baseExponent
  if roundedAmount.isZero then
    throw .tecPRECISION_LOSS

  return roundedAmount

def assetsToSharesDeposit (v : Vault) (amountDeposit : STAmount) : Except Error STAmount := do
  let assetsTotal ← v.assetsTotal
  if assetsTotal.mantissa_ = 0 then
    let sharesExponent := amountDeposit.exponent + v.scale.toNat
    let sharesNumber ← Number.normalized false amountDeposit.mantissa sharesExponent
      largeRange.min largeRange.max .to_nearest

    let sharesNumber ← sharesNumber.truncate
    let shares ← STAmount.ofNumber .int64 sharesNumber .to_nearest

    return shares

  let amountDepositNumber ← amountDeposit.toNumber .to_nearest
  let sharesAssets ← v.sharesTotal.operator_mul amountDepositNumber .to_nearest

  let sharesNumber ← sharesAssets.operator_div assetsTotal .to_nearest
  let sharesNumber ← sharesNumber.truncate
  let shares ← STAmount.ofNumber .int64 sharesNumber .to_nearest

  return shares

def sharesToAssetsDeposit (v : Vault) (shares : STAmount) : Except Error STAmount := do
  let assetsTotal ← v.assetsTotal
  if assetsTotal.mantissa_ = 0 then
    let assets ← STAmount.checked v.numericType shares.mantissa (shares.exponent - v.scale.toNat) false .to_nearest
    return assets

  let sharesNumber ← shares.toNumber .to_nearest
  let assetsShares ← assetsTotal.operator_mul sharesNumber .to_nearest

  let amountDepositNumber ← assetsShares.operator_div v.sharesTotal .to_nearest
  let amountDeposit ← STAmount.ofNumber v.numericType amountDepositNumber .to_nearest

  return amountDeposit

def computeDeposit (v : Vault) (amountDeposit : STAmount) (isDonation : Bool) : TerExcept VaultAmounts := do
  try
    let mut assets := amountDeposit
    let mut shares := STAmount.zero .int64

    if !isDonation then
      shares ← assetsToSharesDeposit v amountDeposit
      if shares.isZero then
        throw .tecPRECISION_LOSS

      assets ← sharesToAssetsDeposit v shares
      if ← assets.operator_gt amountDeposit then
        throw .tecINTERNAL

    let assetsTotal ← v.assetsTotal
    let assetDeposited ← clampToSumExponent assetsTotal assets v.baseExponent
    if ← assetDeposited.isFractionalNonPositive then
      throw .tecPRECISION_LOSS

    return { assets := assetDeposited, shares := shares }
  catch e : Error =>
    if isOverflow e then
      throw .tecPATH_DRY
    else
      throwThe Error e

-- `hpos`: the preflight check `sfAmount > 0` passed; callers outside the model check it
def Vault.deposit (v : Vault) (amountDeposit : STAmount) (isDonation : Bool) (parentCloseTime : UInt32)
    (_hpos : 0 < amountDeposit.toRat) : TerExcept VaultWithAmounts := do
  let phase := v.phase parentCloseTime
  if !isDonation && (phase == .investment || phase == .redemption) then
    throw .tecEXPIRED

  if isDonation && v.sharesTotal.mantissa_ == 0 then
    throw .tecNO_PERMISSION

  if v.isInsolvent && !isDonation then
    throw .tecLOCKED

  if v.depositBlocked then
    throw .tecLOCKED

  let amount ← v.roundedDepositAmount amountDeposit

  let amounts ← computeDeposit v amount isDonation

  let inflowCheck ← v.checkOpenLimit amounts.assets
  if inflowCheck != .tesSUCCESS then
    throw inflowCheck

  let rawVault' ← v.adjustAssetsAndShares amounts.assets amounts.shares

  let assetsMaximum := v.assetsMaximum.getD Number.zero
  let assetsTotal' ← rawVault'.assetsTotal
  if assetsMaximum.operator_ne Number.zero && assetsTotal'.operator_gt assetsMaximum then
    throw .tecLIMIT_EXCEEDED

  let v' ← rawVault'.to_lawful
  return { amounts with vault' := v' }

end XRPL.Model.SingleAssetVault
