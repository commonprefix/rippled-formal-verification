import XRPL.Model.Protocol.Number
import XRPL.Model.Protocol.Rounding
import XRPL.Model.Protocol.STAmount
import XRPL.Model.Protocol.TER
import XRPL.Model.Lending.AssetPool
import XRPL.Model.Lending.LoanBroker.BrokerCover

namespace XRPL.Model.Lending

open XRPL.Model.Protocol

-- LoanBrokerCoverWithdraw -> preclaim
def LoanBroker.canCoverWithdraw {α : Type} [AssetPool α] (lb : LoanBroker) (pool : α) (amount : STAmount)
    : Except Error TER := do
  let baseExponent := AssetPool.baseExponent pool
  let amount ← clampToSumExponent lb.coverAvailable amount.operator_neg baseExponent
  if amount.isZero then
    return .tecPRECISION_LOSS

  let amountNum ← amount.toNumber .to_nearest
  if lb.coverAvailable.operator_lt amountNum then
    return .tecINSUFFICIENT_FUNDS

  let coverAvailable' ← lb.coverAvailable.operator_sub amountNum .to_nearest
  let rawBroker' : RawLoanBroker := { lb.toRawLoanBroker with coverAvailable := coverAvailable' }

  let hasMinimumCover ← rawBroker'.hasMinimumCover baseExponent
  if !hasMinimumCover then
    return .tecINSUFFICIENT_FUNDS

  return .tesSUCCESS

-- LoanBrokerCoverWithdraw -> doApply
def LoanBroker.coverWithdraw {α : Type} [AssetPool α] (lb : LoanBroker) (pool : α) (amount : STAmount)
    : TerExcept LoanBrokerCoverResult := do
  let vaultExponent := AssetPool.baseExponent pool
  let amount ← clampToSumExponent lb.coverAvailable amount.operator_neg vaultExponent
  lb.applyCoverTransaction .debit amount

end XRPL.Model.Lending
