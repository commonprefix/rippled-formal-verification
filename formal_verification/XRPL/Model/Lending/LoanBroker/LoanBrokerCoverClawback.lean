import XRPL.Model.Protocol.Number
import XRPL.Model.Protocol.Rounding
import XRPL.Model.Protocol.STAmount
import XRPL.Model.Protocol.TER
import XRPL.Model.Lending.AssetPool
import XRPL.Model.Lending.LoanBroker.BrokerCover

namespace XRPL.Model.Lending

open XRPL.Model.Protocol

def LoanBroker.roundedCoverClawback {α : Type} [AssetPool α] (lb : LoanBroker) (pool : α)
    (amount : Option STAmount) : TerExcept STAmount := do
  let nt := lb.numericType
  let vaultExponent := AssetPool.baseExponent pool
  let minimumCover ← minimumBrokerCover nt lb.debtTotal lb.coverRateMinimum vaultExponent
  let maxClawAmount ← lb.coverAvailable.operator_sub minimumCover .downward
  if maxClawAmount.signum ≤ 0 then
    throw .tecINSUFFICIENT_FUNDS

  let claw ← match amount with
    | none => .pure maxClawAmount
    | some a =>
      if a.isZero then .pure maxClawAmount
      else do
        let magnitude ← a.toNumber .to_nearest
        .pure (if magnitude.operator_gt maxClawAmount then maxClawAmount else magnitude)

  let claw' ← STAmount.ofNumber nt claw .to_nearest
  let coverAvailable' ← clampToSumExponent lb.coverAvailable claw'.operator_neg vaultExponent
  if coverAvailable'.isZero then
    throw .tecPRECISION_LOSS

  return coverAvailable'

-- LoanBrokerCoverClawback -> preclaim
def LoanBroker.canCoverClawback {α : Type} [AssetPool α] (lb : LoanBroker) (pool : α)
    (amount : Option STAmount) : Except Error TER := do
  match ← (lb.roundedCoverClawback pool amount).run with
  | .error ter => return ter
  | .ok _ => return .tesSUCCESS

-- LoanBrokerCoverClawback -> doApply
def LoanBroker.coverClawback {α : Type} [AssetPool α] (lb : LoanBroker) (pool : α)
    (amount : Option STAmount) : TerExcept LoanBrokerCoverResult := do
  let amount ← try lb.roundedCoverClawback pool amount catch _ : TER => throw .tecINTERNAL
  lb.applyCoverTransaction .debit amount

end XRPL.Model.Lending
