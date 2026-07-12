import XRPL.Model.Protocol.STAmount
import XRPL.Model.Protocol.Number
import XRPL.Model.Protocol.TER
import XRPL.Model.Vault.Vault

open XRPL.Model.Protocol

-- exponent of a Number represented as an STAmount. Models the function `scale` from xrpld
def exponent (amount : Number) (asset : Asset) : Except String Int := do
  let a ← STAmount.ofNumber asset amount .to_nearest
  return a.exponent

-- model of `roundToVaultScale` from xrpld
def roundToVaultExponent (amountDeposit : STAmount) (assetsTotal : Number) : Except String STAmount := do
  if amountDeposit.integral then
    return amountDeposit
  let amountNumber ← amountDeposit.toNumber .to_nearest
  let assetsTotal' ← Number.operator_add assetsTotal amountNumber .to_nearest
  let postScale ← exponent assetsTotal' amountDeposit.asset
  let rounded ← STAmount.roundToExponent amountDeposit postScale .downward
  return rounded

-- The deposit either rounds to a usable amount, or is rejected with a TER. A String error
-- from roundToVaultScale (e.g. overflow) propagates through the outer Except (a C++ throw).
inductive RoundedDepositResult where
  | rejected (ter : TER)
  | rounded (amount : STAmount)

def Vault.roundedDepositAmount (vault : Vault) (amountDeposit : STAmount)
    : Except String RoundedDepositResult := do
  let roundedAmount ← roundToVaultExponent amountDeposit vault.assetsTotal
  if roundedAmount.isZero then
    return .rejected .tecPRECISION_LOSS
  return .rounded roundedAmount

structure DepositResult where
  error : Option TER
  vault' : Vault
  amountDeposit' : STAmount
  sharesIssued : STAmount

def assetsToSharesDeposit (vault : Vault) (amountDeposit : STAmount) : Except String STAmount := do
  if vault.assetsTotal.mantissa_ = 0 then
    let sharesNumber ← Number.normalized false amountDeposit.mantissa (amountDeposit.exponent + vault.scale.toNat) largeRange.min largeRange.max .to_nearest
    let sharesNumber ← sharesNumber.truncate
    let shares ← STAmount.ofNumber vault.sharesAsset sharesNumber .to_nearest
    return shares
  let amountDepositNumber ← amountDeposit.toNumber .to_nearest
  let netAssetValue ← vault.assetsTotal.operator_sub vault.interestUnrealized .to_nearest
  let sharesAssets ← vault.sharesTotal.operator_mul amountDepositNumber .to_nearest
  let sharesNumber ← sharesAssets.operator_div netAssetValue .to_nearest
  let sharesNumber ← sharesNumber.truncate
  let shares ← STAmount.ofNumber vault.sharesAsset sharesNumber .to_nearest
  return shares

def sharesToAssetsDeposit (vault : Vault) (shares : STAmount) : Except String STAmount := do
  if vault.assetsTotal.mantissa_ = 0 then
    let assets ← STAmount.checked vault.asset shares.mantissa (shares.exponent - vault.scale.toNat) false .to_nearest
    return assets
  let netAssetValue ← vault.assetsTotal.operator_sub vault.interestUnrealized .to_nearest
  let sharesNumber ← shares.toNumber .to_nearest
  let assetsShares ← netAssetValue.operator_mul sharesNumber .to_nearest
  let amountDepositNumber ← assetsShares.operator_div vault.sharesTotal .to_nearest
  let amountDeposit ← STAmount.ofNumber vault.asset amountDepositNumber .to_nearest
  return amountDeposit

inductive ComputeDepositResult where
  | error (error : TER)
  | success (assetDeposited : STAmount) (sharesCreated : STAmount)

def computeDeposit (vault : Vault) (amountDeposit : STAmount) : Except String ComputeDepositResult := do
  let shares ← assetsToSharesDeposit vault amountDeposit
  if shares.isZero then
    return .error .tecPRECISION_LOSS
  let amountDeposit' ← sharesToAssetsDeposit vault shares
  if ← amountDeposit'.operator_gt amountDeposit then
    return .error .tecINTERNAL
  return .success amountDeposit' shares

def Vault.deposit (vault : Vault) (amountDeposit : STAmount) (isDonation : Bool) : Except String DepositResult := do
  let amount ← roundToVaultExponent amountDeposit vault.assetsTotal
  let result : DepositResult := ⟨none, vault, amount, STAmount.ofAsset vault.asset⟩
  if amount.isZero then
    return {result with error := some .tecINTERNAL}
  let (assetDeposited, sharesCreated) ←
    if isDonation then
      pure (amount, STAmount.ofAsset vault.sharesAsset)
    else
      match ← computeDeposit vault amount with
      | .error e => return {result with error := some e}
      | .success a s => pure (a, s)
  let vault' : Vault := {
    vault with
    assetsTotal := ← vault.assetsTotal.operator_add (← assetDeposited.toNumber .to_nearest) .to_nearest
    assetsAvailable := ← vault.assetsAvailable.operator_add (← assetDeposited.toNumber .to_nearest) .to_nearest
    sharesTotal := ← vault.sharesTotal.operator_add (← sharesCreated.toNumber .to_nearest) .to_nearest
  }
  return { result with vault' := vault', amountDeposit' := assetDeposited, sharesIssued := sharesCreated }
