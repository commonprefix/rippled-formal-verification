import XRPL.Model.Protocol.STAmount
import XRPL.Model.Protocol.Number
import XRPL.Model.Protocol.TER

open XRPL.Model.Protocol

structure VaultState where
  assetsTotal : Number
  accountBalance : STAmount
  asset : Asset

structure VaultDeposit where
  amount : STAmount

def scale (amount : Number) (asset : Asset) : Except String Int := do
  let a ← STAmount.ofNumber asset amount .to_nearest
  return a.exponent

def roundToVaultScale (amount : STAmount) (assetsTotal : Number) : Except String STAmount := do
  if amount.integral then
    return amount
  let amountNumber ← amount.toNumber .to_nearest 
  let postTotal ← Number.operator_add assetsTotal amountNumber .to_nearest
  let postScale ← scale postTotal amount.asset
  let rounded ← STAmount.roundToScale amount postScale .downward
  return rounded

def isZeroAtScale (amount : STAmount) (scale : Int) : Except String Bool := do
  let rounded ← STAmount.roundToScale amount scale .to_nearest
  return rounded.isZero

def canDeposit (state : VaultState) (tx : VaultDeposit) : Except String TER := do
  let roundedAmount ← roundToVaultScale tx.amount state.assetsTotal
  if roundedAmount.isZero then
    return .tecPRECISION_LOSS
  let accountBalance := state.accountBalance

  if ← accountBalance.operator_lt roundedAmount then
    return .tecINSUFFICIENT_FUNDS

  if !roundedAmount.integral then -- how to check the issuer?
    let accountBalanceNumber ← accountBalance.toNumber .to_nearest
    let assetScale ← scale accountBalanceNumber state.asset
    if ← isZeroAtScale accountBalance assetScale then
      return .tecPRECISION_LOSS

  return .tesSUCCESS


@[export lean_can_deposit]
def lean_can_deposit (state : VaultState) (tx : VaultDeposit) : Except String TER := do
  canDeposit state tx
