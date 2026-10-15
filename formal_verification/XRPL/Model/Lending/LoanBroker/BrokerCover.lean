import XRPL.Model.Protocol.Exponent
import XRPL.Model.Protocol.Number
import XRPL.Model.Protocol.NumericType
import XRPL.Model.Protocol.Rounding
import XRPL.Model.Protocol.STAmount
import XRPL.Model.Protocol.TER
import XRPL.Model.Protocol.TenthBips
import XRPL.Model.Lending.AssetPool
import XRPL.Model.Lending.LoanBroker.LoanBroker

namespace XRPL.Model.Lending

open XRPL.Model.Protocol

-- minimum first-loss cover for the debt, rounded up
def minimumBrokerCover (nt : NumericType) (debtTotal : Number) (coverRateMinimum : TenthBips32) (poolExponent : Int)
    : Except Error Number := do
  let minimumCover ← tenthBipsOfValue debtTotal coverRateMinimum .upward
  STAmount.roundToNumericType nt minimumCover .upward (some poolExponent)

-- the first-loss cover is at least the minimum the debt requires
def RawLoanBroker.hasMinimumCover (rb : RawLoanBroker) (poolExponent : Int) : Except Error Bool := do
  let minimumCover ← minimumBrokerCover rb.numericType rb.debtTotal rb.coverRateMinimum poolExponent
  return minimumCover.operator_le rb.coverAvailable

-- C++ `checkOptionalBrokerCoverInflow`: a deposit must keep the cover at the base exponent and inside the Open zone.
def LoanBroker.checkCoverOpenLimit {α : Type} [AssetPool α] (lb : LoanBroker) (pool : α)
    (amount : STAmount) : Except Error TER := do
  let baseExponent := AssetPool.baseExponent pool
  let amountNum ← amount.toNumber .to_nearest
  let exponent ← postSumExponent lb.coverAvailable amountNum baseExponent lb.numericType
  if exponent != baseExponent then
    return .tecLIMIT_EXCEEDED

  let coverAvailable' ← lb.coverAvailable.operator_add amountNum .towards_zero
  let openLimit ← AssetPool.openLimit pool
  if coverAvailable'.operator_gt openLimit then
    return .tecLIMIT_EXCEEDED

  return .tesSUCCESS

-- the cover movement actually applied: sub-scale dust is rejected rather than truncated
def LoanBroker.roundedCoverAmount {α : Type} [AssetPool α] (lb : LoanBroker) (pool : α) (amount : STAmount)
    : TerExcept STAmount := do
  let baseExponent := AssetPool.baseExponent pool
  let amountNum ← amount.toNumber .to_nearest

  let rounded ← sumRoundAndSubtract lb.coverAvailable amountNum baseExponent lb.numericType .downward
  if rounded.signum == 0 then
    throw .tecPRECISION_LOSS

  return rounded

structure LoanBrokerCoverResult where
  amount' : STAmount
  loanBroker' : LoanBroker

inductive CoverDirection where
  | credit
  | debit

-- settle a rounded cover movement against coverAvailable
def LoanBroker.applyCoverTransaction (lb : LoanBroker) (direction : CoverDirection) (amount : STAmount)
   : Except Error LoanBrokerCoverResult := do
  let amountNum ← amount.toNumber .to_nearest
  let coverAvailable' ← match direction with
    | .credit => lb.coverAvailable.operator_add amountNum .to_nearest
    | .debit => lb.coverAvailable.operator_sub amountNum .to_nearest
  let rawBroker' : RawLoanBroker := { lb.toRawLoanBroker with coverAvailable := coverAvailable' }
  let loanBroker' ← rawBroker'.to_lawful

  return { amount' := amount, loanBroker' := loanBroker' }

end XRPL.Model.Lending
