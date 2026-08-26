import XRPL.Model.Protocol.Exponent
import XRPL.Model.Protocol.Number
import XRPL.Model.Protocol.Result
import XRPL.Model.Protocol.STAmount
import XRPL.Model.Protocol.TER
import XRPL.Model.Lending.AssetPool
import XRPL.Model.Lending.LoanBroker
import XRPL.Model.Lending.LendingHelpers

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.Result

def LoanBroker.roundedCoverWithdraw (lb : LoanBroker) (numericType : NumericType) (amount : STAmount) : Except Error RoundingResult := do
  let exponent ← numberExponent lb.coverAvailable numericType
  let rounded ← STAmount.roundToExponent amount exponent .downward
  if rounded.signum == 0 then
    return .rejected .tecPRECISION_LOSS
  return .rounded rounded


def LoanBroker.canCoverWithdraw {α : Type} [AssetPool α] (lb : LoanBroker) (pool : α)
    (amount : STAmount) : Except Error TER := do
  let ter ← canApplyToBrokerCover (AssetPool.numericType pool) lb.coverAvailable amount
  if ter.operator_bool then
    return ter

  let rounded ← match (← lb.roundedCoverWithdraw (AssetPool.numericType pool) amount) with
    | .rejected ter => return ter
    | .rounded amount => .pure amount

  let poolExponent ← AssetPool.exponent pool
  let minimumCover ← minimumBrokerCover (AssetPool.numericType pool) lb.debtTotal
    lb.coverRateMinimum poolExponent
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
