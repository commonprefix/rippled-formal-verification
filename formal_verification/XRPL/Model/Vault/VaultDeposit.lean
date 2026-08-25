import XRPL.Model.Protocol.Number
import XRPL.Model.Protocol.Result
import XRPL.Model.Protocol.STAmount
import XRPL.Model.Protocol.TER
import XRPL.Model.Vault.Vault

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol
open XRPL.Model.Result

-- model of `roundToVaultScale` from xrpld
def roundToVaultExponent (amountDeposit : STAmount) (assetsTotal : Number) : Except Error STAmount := do
  if amountDeposit.integral then
    return amountDeposit
  let amountNumber ← amountDeposit.toNumber .to_nearest
  let assetsTotal' ← Number.operator_add assetsTotal amountNumber .to_nearest
  let postScale ← exponent assetsTotal' amountDeposit.numericType
  let rounded ← STAmount.roundToExponent amountDeposit postScale .downward
  return rounded

/-- The preclaim check on a deposit amount. An IOU vault cannot track digits
below the exponent its `assetsTotal` will have after the deposit, so any such
digits in `amountDeposit` are dropped before the deposit runs (integral assets
pass through unchanged). Returns the amount the deposit will actually use, or
`tecPRECISION_LOSS` when nothing of it survives. An `Error` from
`roundToVaultExponent` (e.g. overflow) propagates through the outer `Except`
(a C++ throw). -/
def Vault.roundedDepositAmount (vault : Vault) (amountDeposit : STAmount)
    : Except Error RoundingResult := do
  let roundedAmount ← roundToVaultExponent amountDeposit vault.assetsTotal
  if roundedAmount.isZero then
    return .rejected .tecPRECISION_LOSS
  return .rounded roundedAmount

structure DepositResult where
  error : Option TER
  vault' : Vault
  amountDeposit' : STAmount
  sharesIssued : STAmount

-- A rejection changes nothing and reports nothing: the vault is returned
-- unchanged and both amount fields are zero.
def DepositResult.rejected (vault : Vault) (ter : TER) : DepositResult :=
  ⟨some ter, vault, STAmount.zero vault.numericType, STAmount.zero .int64⟩

def assetsToSharesDeposit (vault : Vault) (amountDeposit : STAmount) : Except Error STAmount := do
  if vault.assetsTotal.mantissa_ = 0 then
    let sharesNumber ← Number.normalized false amountDeposit.mantissa (amountDeposit.exponent + vault.scale.toNat) largeRange.min largeRange.max .to_nearest
    let sharesNumber ← sharesNumber.truncate
    let shares ← STAmount.ofNumber .int64 sharesNumber .to_nearest
    return shares
  let amountDepositNumber ← amountDeposit.toNumber .to_nearest
  let sharesAssets ← vault.sharesTotal.operator_mul amountDepositNumber .to_nearest
  let sharesNumber ← sharesAssets.operator_div vault.assetsTotal .to_nearest
  let sharesNumber ← sharesNumber.truncate
  let shares ← STAmount.ofNumber .int64 sharesNumber .to_nearest
  return shares

def sharesToAssetsDeposit (vault : Vault) (shares : STAmount) : Except Error STAmount := do
  if vault.assetsTotal.mantissa_ = 0 then
    let assets ← STAmount.checked vault.numericType shares.mantissa (shares.exponent - vault.scale.toNat) false .to_nearest
    return assets
  let sharesNumber ← shares.toNumber .to_nearest
  let assetsShares ← vault.assetsTotal.operator_mul sharesNumber .to_nearest
  let amountDepositNumber ← assetsShares.operator_div vault.sharesTotal .to_nearest
  -- (waiting the C++ fix) round the charge up so a depositor never pays less than the issued shares are worth
  let amountDeposit ← STAmount.ofNumber vault.numericType amountDepositNumber .upward
  return amountDeposit

inductive ComputeDepositResult where
  | error (error : TER)
  | success (assetDeposited : STAmount) (sharesCreated : STAmount)

def computeDeposit (vault : Vault) (amountDeposit : STAmount) : Except Error ComputeDepositResult := do
  try
    let shares ← assetsToSharesDeposit vault amountDeposit
    if shares.isZero then
      return .error .tecPRECISION_LOSS
    let amountDeposit' ← sharesToAssetsDeposit vault shares
    if ← amountDeposit'.operator_gt amountDeposit then
      return .error .tecINTERNAL
    return .success amountDeposit' shares
  catch e =>
    if isOverflow e then
      return .error .tecPATH_DRY
    else
      throw e

def Vault.deposit (vault : Vault) (amountDeposit : STAmount) (isDonation : Bool) : Except Error DepositResult := do
  let amount ← roundToVaultExponent amountDeposit vault.assetsTotal

  if amount.isZero then
    return .rejected vault .tecINTERNAL

  if isDonation && vault.sharesTotal.mantissa_ == 0 then
    return .rejected vault .tecNO_PERMISSION

  if vault.isInsolvent && !isDonation then
    return .rejected vault .tecLOCKED

  let (assetDeposited, sharesCreated) ←
    if isDonation then
      pure (amount, STAmount.zero .int64)
    else
      match ← computeDeposit vault amount with
      | .error e => return .rejected vault e
      | .success a s => pure (a, s)

  let vault' : Vault := {
    vault with
    assetsTotal := ← vault.assetsTotal.operator_add (← assetDeposited.toNumber .to_nearest) .to_nearest
    assetsAvailable := ← vault.assetsAvailable.operator_add (← assetDeposited.toNumber .to_nearest) .to_nearest
    sharesTotal := ← vault.sharesTotal.operator_add (← sharesCreated.toNumber .to_nearest) .to_nearest
  }

  -- C++: if (maximum != 0 && assetsTotal > maximum)
  let assetsMaximum := vault.assetsMaximum.getD Number.zero
  if assetsMaximum.operator_ne Number.zero && vault'.assetsTotal.operator_gt assetsMaximum then
    return .rejected vault .tecLIMIT_EXCEEDED

  return ⟨none, vault', assetDeposited, sharesCreated⟩

end XRPL.Model.SingleAssetVault
