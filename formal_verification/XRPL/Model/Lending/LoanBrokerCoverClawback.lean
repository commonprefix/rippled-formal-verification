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

def LoanBroker.roundedCoverClawback {α : Type} [AssetPool α] (lb : LoanBroker) (pool : α)
    (amount : Option STAmount) : Except Error RoundingResult := do
  let poolExponent ← AssetPool.exponent pool
  let minRequiredCover ← minimumBrokerCover (AssetPool.numericType pool) lb.debtTotal
    lb.coverRateMinimum poolExponent
  let maxClawAmount ← lb.coverAvailable.operator_sub minRequiredCover .downward
  if maxClawAmount.signum ≤ 0 then
    return .rejected .tecINSUFFICIENT_FUNDS

  let claw ← match amount with
    | none => .pure maxClawAmount
    | some a =>
      if a.isZero then .pure maxClawAmount
      else do
        let magnitude ← a.toNumber .to_nearest
        .pure (if magnitude.operator_gt maxClawAmount then maxClawAmount else magnitude)

  return .rounded (← STAmount.ofNumber (AssetPool.numericType pool) claw .to_nearest)

def LoanBroker.canCoverClawback {α : Type} [AssetPool α] (lb : LoanBroker) (pool : α)
    (amount : Option STAmount) : Except Error TER := do
  match ← lb.roundedCoverClawback pool amount with
  | .rejected ter => return ter
  | .rounded clawAmount =>
    canApplyToBrokerCover (AssetPool.numericType pool) lb.coverAvailable clawAmount

structure LoanBrokerCoverClawbackResult where
  status : TER
  clawAmount' : STAmount
  loanBroker' : LoanBroker

def LoanBroker.coverClawback {α : Type} [AssetPool α] (lb : LoanBroker) (pool : α)
    (amount : Option STAmount) : Except Error LoanBrokerCoverClawbackResult := do
  let result : LoanBrokerCoverClawbackResult := {
    status := .tesSUCCESS,
    clawAmount' := STAmount.zero (AssetPool.numericType pool),
    loanBroker' := lb
  }

  let clawAmount ← match (← lb.roundedCoverClawback pool amount) with
    | .rejected _ => return { result with status := .tecINTERNAL }
    | .rounded amount => .pure amount

  let clawNumber ← clawAmount.toNumber .to_nearest
  let coverAvailable' ← lb.coverAvailable.operator_sub clawNumber .to_nearest
  let lb' := { lb with coverAvailable := coverAvailable' }
  return { result with clawAmount' := clawAmount, loanBroker' := lb' }

end XRPL.Model.Lending
