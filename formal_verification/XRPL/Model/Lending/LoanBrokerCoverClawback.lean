import XRPL.Model.Protocol.Number
import XRPL.Model.Protocol.STAmount
import XRPL.Model.Protocol.TER
import XRPL.Model.Vault.Vault
import XRPL.Model.Lending.LoanBroker
import XRPL.Model.Lending.LendingHelpers

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault

inductive RoundedCoverClawbackResult where
  | rejected (ter : TER)
  | rounded (amount : STAmount)

def LoanBroker.roundedCoverClawback (lb : LoanBroker) (vault : RawVault) (amount : Option STAmount)
    : Except Error RoundedCoverClawbackResult := do
  let vaultScale ← getAssetsTotalScale vault.numericType vault.assetsTotal
  let minRequiredCover ← minimumBrokerCover vault.numericType lb.debtTotal lb.coverRateMinimum vaultScale
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

  return .rounded (← STAmount.ofNumber vault.numericType claw .to_nearest)

def LoanBroker.canCoverClawback (lb : LoanBroker) (vault : RawVault) (amount : Option STAmount)
    : Except Error TER := do
  match ← lb.roundedCoverClawback vault amount with
  | .rejected ter => return ter
  | .rounded clawAmount => canApplyToBrokerCover vault.numericType lb.coverAvailable clawAmount

structure LoanBrokerCoverClawbackResult where
  status : TER
  clawAmount' : STAmount
  loanBroker' : LoanBroker

def LoanBroker.coverClawback (lb : LoanBroker) (vault : RawVault) (amount : Option STAmount)
    : Except Error LoanBrokerCoverClawbackResult := do
  let result : LoanBrokerCoverClawbackResult := {
    status := .tesSUCCESS,
    clawAmount' := STAmount.zero vault.numericType,
    loanBroker' := lb
  }

  let clawAmount ← match (← lb.roundedCoverClawback vault amount) with
    | .rejected _ => return { result with status := .tecINTERNAL }
    | .rounded amount => .pure amount

  let clawNumber ← clawAmount.toNumber .to_nearest
  let coverAvailable' ← lb.coverAvailable.operator_sub clawNumber .to_nearest
  let lb' := { lb with coverAvailable := coverAvailable' }
  return { result with clawAmount' := clawAmount, loanBroker' := lb' }

end XRPL.Model.Lending
