import XRPL.Model.Protocol.STAmount
import XRPL.Model.Protocol.Number
import XRPL.Model.Protocol.TER
import XRPL.NewModel.SingleAssetVault.Vault

open XRPL.Model.Protocol


def exponent (amount : Number) (asset : Asset) : Except String Int := do
  let a ← STAmount.ofNumber asset amount .to_nearest
  return a.exponent

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

def Vault.roundedDepositAmount (state : Vault) (amountDeposit : STAmount)
    : Except String RoundedDepositResult := do
  let roundedAmount ← roundToVaultExponent amountDeposit state.assetsTotal
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
    let sharesExponent ← Number.normalized false amountDeposit.mantissa (amountDeposit.exponent + vault.scale.toNat) largeRange.min largeRange.max .to_nearest
    let shares ← STAmount.ofNumber vault.sharesAsset sharesExponent .to_nearest
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

def computeDeposit (state : Vault) (amountDeposit : STAmount) : Except String (STAmount × STAmount) := do
  let shares ← assetsToSharesDeposit state amountDeposit
  let amountDeposit' ← sharesToAssetsDeposit state shares
  return (amountDeposit', shares)

def Vault.deposit (state : Vault) (amountDeposit : STAmount) (isDonation : Bool) : Except String DepositResult := do
  -- Round the deposit to the vault-scale precision before computing the exchange.
  let amount ← roundToVaultExponent amountDeposit state.assetsTotal
  let result : DepositResult := ⟨none, state, amount, STAmount.ofAsset state.asset⟩
  if amount.isZero then
    return {result with error := some .tecINTERNAL}
  let (assetDeposited, sharesCreated) ←
    if isDonation then
      pure (amount, STAmount.ofAsset state.sharesAsset)
    else
      computeDeposit state amount
  let state' : Vault := {
    state with
    assetsTotal := ← state.assetsTotal.operator_add (← assetDeposited.toNumber .to_nearest) .to_nearest
    sharesTotal := ← state.sharesTotal.operator_add (← sharesCreated.toNumber .to_nearest) .to_nearest
  }
  return { result with vault' := state', amountDeposit' := assetDeposited, sharesIssued := sharesCreated }








--
-- temporary code to find edge cases 
--

-- TEMPORARY (rounding-mode probe): roundToVaultScale with the final roundToScale step's mode
-- parameterized, to measure how the rounded deposit depends on the rounding mode. Production
-- uses `.downward`; roundToVaultScaleMode amount total .downward == roundToVaultScale amount total.
def roundToVaultScaleMode (amountDeposit : STAmount) (assetsTotal : Number) (mode : rounding_mode)
    : Except String STAmount := do
  if amountDeposit.integral then
    return amountDeposit
  let amountNumber ← amountDeposit.toNumber .to_nearest
  let assetsTotal' ← Number.operator_add assetsTotal amountNumber .to_nearest
  let postScale ← exponent assetsTotal' amountDeposit.asset
  let rounded ← STAmount.roundToExponent amountDeposit postScale mode
  return rounded

-- TEMPORARY (rounding-mode probe): roundedDepositAmount with the final roundToScale mode chosen.
def Vault.roundedDepositAmountMode (state : Vault) (amountDeposit : STAmount) (mode : rounding_mode)
    : Except String RoundedDepositResult := do
  let roundedAmount ← roundToVaultScaleMode amountDeposit state.assetsTotal mode
  if roundedAmount.isZero then
    return .rejected .tecPRECISION_LOSS
  return .rounded roundedAmount

-- TEMPORARY (rounding-mode probe): `scale` with its ofNumber rounding mode parameterized.
-- Production uses `.to_nearest`.
def scaleMode (amount : Number) (asset : Asset) (mode : rounding_mode) : Except String Int := do
  let a ← STAmount.ofNumber asset amount mode
  return a.exponent

-- TEMPORARY (rounding-mode probe): both rounding stages parameterized. `scaleMode` governs the
-- scale computation (toNumber / operator_add / scale), production `.to_nearest`; `roundMode`
-- governs the final roundToScale, production `.downward`.
def roundToVaultScaleModes (amountDeposit : STAmount) (assetsTotal : Number)
    (scaleRounding roundMode : rounding_mode) : Except String STAmount := do
  if amountDeposit.integral then
    return amountDeposit
  let amountNumber ← amountDeposit.toNumber scaleRounding
  let assetsTotal' ← Number.operator_add assetsTotal amountNumber scaleRounding
  let postScale ← scaleMode assetsTotal' amountDeposit.asset scaleRounding
  let rounded ← STAmount.roundToExponent amountDeposit postScale roundMode
  return rounded

-- TEMPORARY (rounding-mode probe): roundedDepositAmount with both rounding stages chosen.
def Vault.roundedDepositAmountModes (state : Vault) (amountDeposit : STAmount)
    (scaleRounding roundMode : rounding_mode) : Except String RoundedDepositResult := do
  let roundedAmount ← roundToVaultScaleModes amountDeposit state.assetsTotal scaleRounding roundMode
  if roundedAmount.isZero then
    return .rejected .tecPRECISION_LOSS
  return .rounded roundedAmount
