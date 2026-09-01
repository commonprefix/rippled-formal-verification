import XRPL.Model.Protocol.Number
import XRPL.Model.Protocol.STAmount
import XRPL.Model.Protocol.TER
import XRPL.Model.Vault.Vault

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol

-- model of `roundToVaultScale` from xrpld
def roundToVaultExponent (amountDeposit : STAmount) (assetsTotal : Number) : Except Error STAmount := do
  if amountDeposit.integral then
    return amountDeposit
  let amountNumber ← amountDeposit.toNumber .to_nearest
  let assetsTotal' ← Number.operator_add assetsTotal amountNumber .to_nearest
  let postScale ← exponent assetsTotal' amountDeposit.numericType
  let rounded ← STAmount.roundToExponent amountDeposit postScale .downward
  return rounded

-- The deposit either rounds to a usable amount, or is rejected with a TER. An Error
-- from roundToVaultScale (e.g. overflow) propagates through the outer Except (a C++ throw).
inductive RoundedDepositResult where
  | rejected (ter : TER)
  | rounded (amount : STAmount)

/-- The preclaim check on a deposit amount. An IOU vault cannot track digits
below the exponent its `assetsTotal` will have after the deposit, so any such
digits in `amountDeposit` are dropped before the deposit runs (integral assets
pass through unchanged). Returns the amount the deposit will actually use, or
`tecPRECISION_LOSS` when nothing of it survives. -/
def LawfulVault.roundedDepositAmount (lv : LawfulVault) (amountDeposit : STAmount)
    : Except Error RoundedDepositResult := do
  let vault := lv.toRawVault
  let roundedAmount ← roundToVaultExponent amountDeposit vault.assetsTotal
  if roundedAmount.isZero then
    return .rejected .tecPRECISION_LOSS
  return .rounded roundedAmount

structure DepositResult where
  error : Option TER
  vault' : LawfulVault
  amountDeposit' : STAmount
  sharesIssued : STAmount

-- A rejection changes nothing and reports nothing: the vault is returned
-- unchanged and both amount fields are zero.
def DepositResult.rejected (lv : LawfulVault) (ter : TER) : DepositResult :=
  ⟨some ter, lv, STAmount.zero lv.numericType, STAmount.zero .int64⟩

def assetsToSharesDeposit (lv : LawfulVault) (amountDeposit : STAmount) : Except Error STAmount := do
  if lv.assetsTotal.mantissa_ = 0 then
    let sharesNumber ← Number.normalized false amountDeposit.mantissa (amountDeposit.exponent + lv.scale.toNat) largeRange.min largeRange.max .to_nearest
    let sharesNumber ← sharesNumber.truncate
    let shares ← STAmount.ofNumber .int64 sharesNumber .to_nearest
    return shares
  let amountDepositNumber ← amountDeposit.toNumber .to_nearest
  let sharesAssets ← lv.sharesTotal.operator_mul amountDepositNumber .to_nearest
  let sharesNumber ← sharesAssets.operator_div lv.assetsTotal .to_nearest
  let sharesNumber ← sharesNumber.truncate
  let shares ← STAmount.ofNumber .int64 sharesNumber .to_nearest
  return shares

def sharesToAssetsDeposit (lv : LawfulVault) (shares : STAmount) : Except Error STAmount := do
  if lv.assetsTotal.mantissa_ = 0 then
    let assets ← STAmount.checked lv.numericType shares.mantissa (shares.exponent - lv.scale.toNat) false .to_nearest
    return assets
  let sharesNumber ← shares.toNumber .to_nearest
  let assetsShares ← lv.assetsTotal.operator_mul sharesNumber .to_nearest
  let amountDepositNumber ← assetsShares.operator_div lv.sharesTotal .to_nearest
  -- (waiting the C++ fix) round the charge up so a depositor never pays less than the issued shares are worth
  let amountDeposit ← STAmount.ofNumber lv.numericType amountDepositNumber .upward
  return amountDeposit

inductive ComputeDepositResult where
  | error (error : TER)
  | success (assetDeposited : STAmount) (sharesCreated : STAmount)

def computeDeposit (lv : LawfulVault) (amountDeposit : STAmount) : Except Error ComputeDepositResult := do
  try
    let shares ← assetsToSharesDeposit lv amountDeposit
    if shares.isZero then
      return .error .tecPRECISION_LOSS
    let amountDeposit' ← sharesToAssetsDeposit lv shares
    if ← amountDeposit'.operator_gt amountDeposit then
      return .error .tecINTERNAL
    return .success amountDeposit' shares
  catch e =>
    if isOverflow e then
      return .error .tecPATH_DRY
    else
      throw e

def LawfulVault.deposit (lv : LawfulVault) (amountDeposit : STAmount) (isDonation : Bool) : Except Error DepositResult := do
  let vault := lv.toRawVault
  let amount ← roundToVaultExponent amountDeposit vault.assetsTotal

  if amount.isZero then
    return .rejected lv .tecINTERNAL

  if isDonation && vault.sharesTotal.mantissa_ == 0 then
    return .rejected lv .tecNO_PERMISSION

  if lv.isInsolvent && !isDonation then
    return .rejected lv .tecLOCKED

  let (assetDeposited, sharesCreated) ←
    if isDonation then
      pure (amount, STAmount.zero .int64)
    else
      match ← computeDeposit lv amount with
      | .error e => return .rejected lv e
      | .success a s => pure (a, s)

  let vault' : RawVault := {
    vault with
    assetsTotal := ← vault.assetsTotal.operator_add (← assetDeposited.toNumber .to_nearest) .to_nearest
    assetsAvailable := ← vault.assetsAvailable.operator_add (← assetDeposited.toNumber .to_nearest) .to_nearest
    sharesTotal := ← vault.sharesTotal.operator_add (← sharesCreated.toNumber .to_nearest) .to_nearest
  }

  -- C++: if (maximum != 0 && assetsTotal > maximum)
  let assetsMaximum := vault.assetsMaximum.getD Number.zero
  if assetsMaximum.operator_ne Number.zero && vault'.assetsTotal.operator_gt assetsMaximum then
    return .rejected lv .tecLIMIT_EXCEEDED

  let lv' ← vault'.to_lawful
  return ⟨none, lv', assetDeposited, sharesCreated⟩

end XRPL.Model.SingleAssetVault
