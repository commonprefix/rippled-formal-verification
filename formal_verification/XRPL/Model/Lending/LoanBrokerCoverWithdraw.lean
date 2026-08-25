import XRPL.Model.Protocol.Number
import XRPL.Model.Protocol.Result
import XRPL.Model.Protocol.STAmount
import XRPL.Model.Protocol.TER
import XRPL.Model.Vault.Vault
import XRPL.Model.Lending.LoanBroker
import XRPL.Model.Lending.LendingHelpers

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.Result
open XRPL.Model.SingleAssetVault

def LoanBroker.roundedCoverWithdraw (lb : LoanBroker) (numericType : NumericType) (amount : STAmount) : Except Error RoundingResult := do
  let exponent ← exponent lb.coverAvailable numericType
  let rounded ← STAmount.roundToExponent amount exponent .downward
  if rounded.signum == 0 then
    return .rejected .tecPRECISION_LOSS
  return .rounded rounded


def LoanBroker.canCoverWithdraw (lb : LoanBroker) (vault : Vault) (amount : STAmount)
    : Except Error TER := do
  let ter ← canApplyToBrokerCover vault.numericType lb.coverAvailable amount
  if ter.operator_bool then
    return ter

  let rounded ← match (← lb.roundedCoverWithdraw vault.numericType amount) with
    | .rejected ter => return ter
    | .rounded amount => .pure amount

  let vaultScale ← getAssetsTotalScale vault.numericType vault.assetsTotal
  let minimumCover ← minimumBrokerCover vault.numericType lb.debtTotal lb.coverRateMinimum vaultScale
  let amountNumber ← rounded.toNumber .to_nearest
  if lb.coverAvailable.operator_lt amountNumber then
    return .tecINSUFFICIENT_FUNDS
  let coverAvailable' ← lb.coverAvailable.operator_sub amountNumber .to_nearest
  if coverAvailable'.operator_lt minimumCover then
    return .tecINSUFFICIENT_FUNDS

  return .tesSUCCESS


structure LoanBrokerCoverWithdrawResult where
  status : TER
  withdrawAmount' : STAmount
  loanBroker' : LoanBroker

def LoanBroker.coverWithdraw (lb : LoanBroker) (numericType : NumericType) (amount : STAmount) : Except Error LoanBrokerCoverWithdrawResult := do
  let result : LoanBrokerCoverWithdrawResult := {
    status := .tesSUCCESS,
    withdrawAmount' := STAmount.zero numericType,
    loanBroker' := lb
  }

  let rounded ← match (← lb.roundedCoverWithdraw numericType amount) with
    | .rejected _ => return { result with status := .tecINTERNAL }
    | .rounded amount => .pure amount

  let roundedNumber ← rounded.toNumber .to_nearest
  let coverAvailable' ← lb.coverAvailable.operator_sub roundedNumber .to_nearest
  let lb' := { lb with coverAvailable := coverAvailable' }
  return { result with withdrawAmount' := rounded, loanBroker' := lb' }

end XRPL.Model.Lending
