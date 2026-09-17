import XRPL.Model.Protocol.Exponent
import XRPL.Model.Protocol.Number
import XRPL.Model.Protocol.Result
import XRPL.Model.Protocol.STAmount
import XRPL.Model.Protocol.TER
import XRPL.Model.Lending.LoanBroker.BrokerCover

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.Result

def LoanBroker.roundedCoverClawback (lb : LoanBroker) (amount : Option STAmount)
    : Except Error RoundingResult := do
  let nt := lb.vault.numericType
  let vaultExponent ← numberExponent lb.vault.assetsTotal nt
  let minimumCover ← minimumBrokerCover nt lb.debtTotal lb.coverRateMinimum vaultExponent
  let maxClawAmount ← lb.coverAvailable.operator_sub minimumCover .downward
  if maxClawAmount.signum ≤ 0 then
    return .rejected .tecINSUFFICIENT_FUNDS

  let claw ← match amount with
    | none => .pure maxClawAmount
    | some a =>
      if a.isZero then .pure maxClawAmount
      else do
        let magnitude ← a.toNumber .to_nearest
        .pure (if magnitude.operator_gt maxClawAmount then maxClawAmount else magnitude)

  return .rounded (← STAmount.ofNumber nt claw .to_nearest)

-- LoanBrokerCoverClawback -> preclaim
def LoanBroker.canCoverClawback (lb : LoanBroker) (amount : Option STAmount) : Except Error TER := do
  match ← lb.roundedCoverClawback amount with
  | .rejected ter => return ter
  | .rounded clawAmount =>
    canApplyToBrokerCover lb.vault.numericType lb.coverAvailable clawAmount

-- LoanBrokerCoverClawback -> doApply
def LoanBroker.coverClawback (lb : LoanBroker) (amount : Option STAmount)
    : Except Error LoanBrokerCoverTerResult := do
  let amount ← match (← lb.roundedCoverClawback amount) with
    | .rejected _ => return .error .tecINTERNAL
    | .rounded amount => .pure amount
  return .ok (← lb.applyCoverTransaction .debit amount)

end XRPL.Model.Lending
