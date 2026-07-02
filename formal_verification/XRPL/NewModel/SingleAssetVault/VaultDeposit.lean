import XRPL.Model.Protocol.STAmount
import XRPL.Model.Protocol.Number
import XRPL.Model.Protocol.TER

open XRPL.Model.Protocol

structure VaultState where
  assetsTotal : Number
  asset : Asset

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

def accountBalanceChecks (roundedAmount accountBalance : STAmount) : Except String TER := do
  if ← accountBalance.operator_lt roundedAmount then
    return .tecINSUFFICIENT_FUNDS
  if !roundedAmount.integral then
    -- accountBalance is already an STAmount, its scale is equal to its exponent
    if ← isZeroAtScale accountBalance accountBalance.exponent then 
      return .tecPRECISION_LOSS
  return .tesSUCCESS

/-- check whether the amount can be deposited. Checks are performed on accountBalance if it is Some. -/
def canDeposit (state : VaultState) (amount : STAmount) (accountBalance : Option STAmount) : Except String TER := do
  let roundedAmount ← roundToVaultScale amount state.assetsTotal
  if roundedAmount.isZero then
    return .tecPRECISION_LOSS

  match accountBalance with
  | none => return .tesSUCCESS
  | some balance => accountBalanceChecks roundedAmount balance



