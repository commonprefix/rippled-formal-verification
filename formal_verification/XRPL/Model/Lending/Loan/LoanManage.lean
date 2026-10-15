import XRPL.Model.Protocol.Number
import XRPL.Model.Protocol.NumericType
import XRPL.Model.Protocol.Rounding
import XRPL.Model.Protocol.STAmount
import XRPL.Model.Protocol.TenthBips
import XRPL.Model.Lending.AssetPool
import XRPL.Model.Lending.Loan.Loan
import XRPL.Model.Lending.LoanBroker.LoanBroker

namespace XRPL.Model.Lending

open XRPL.Model.Protocol

-- The management action a transaction requests (only one may be set).
inductive LoanManageAction where
  | impair | unimpair | default
  deriving DecidableEq, Repr

-- Amount of the default the broker's first-loss cover absorbs
private def defaultCoveredAmount {α : Type} [AssetPool α] (broker : LoanBroker) (pool : α)
    (totalDefaultAmount : Number) : Except Error Number := do
  let minimumCover ← tenthBipsOfValue broker.debtTotal broker.coverRateMinimum .upward
  let liquidationAmount ← tenthBipsOfValue minimumCover broker.coverRateLiquidation .upward
  let coveredAmount := Number.min liquidationAmount totalDefaultAmount
  let cappedAmount := Number.min coveredAmount broker.coverAvailable

  let nt := broker.numericType
  let coveredAmount' ← STAmount.roundToNumericType nt cappedAmount .towards_zero

  let poolAmounts := AssetPool.amounts pool
  let baseExponent := AssetPool.baseExponent pool
  let defaultCovered ← sumRoundAndSubtract poolAmounts.assetsAvailable coveredAmount' baseExponent nt .downward
  defaultCovered.toNumber .to_nearest

-- LoanManage -> preclaim
def Loan.canManage (loan : Loan) (action : LoanManageAction) (now : UInt32) : TER :=
  let gracePeriodEnd := loan.nextPaymentDueDate + loan.schedule.gracePeriod
  let hasExpired : Bool := now > gracePeriodEnd

  if loan.isPending then
    .tecNO_PERMISSION
  else if loan.isDefault then
    .tecNO_PERMISSION
  else if loan.isImpaired && action == .impair then
    .tecNO_PERMISSION
  else if !(loan.isImpaired || loan.isDefault) && action == .unimpair then
    .tecNO_PERMISSION
  else if loan.paymentRemaining == 0 then
    .tecNO_PERMISSION
  else if action == .default && !hasExpired then
    .tecTOO_SOON
  else
    .tesSUCCESS

-- Record the loan's principal as a paper loss when impairing, reverse it when not.
private def Loan.changeImpairment {α : Type} [AssetPool α] (loan : Loan) (pool : α) (impaired : Bool)
    : TerExcept (LoanWithPool α) := do
  let principal := loan.principalOutstanding
  let loss := if impaired then principal else principal.operator_neg
  let pool' ← AssetPool.adjustBalances pool { loss := loss }

  let rawLoan' : RawLoan := { loan.toRawLoan with isImpaired := impaired }
  let loan' ← rawLoan'.to_lawful

  return { loan' := loan', pool' := pool' }

-- Record the loan's exposure as a paper loss.
def Loan.manageImpair {α : Type} [AssetPool α] (loan : Loan) (pool : α) (now : UInt32)
    : TerExcept (LoanWithPool α) := do
  -- a loan that is not late yet can not be impaired
  if !(loan.isPaymentLate now) then
    throw .tecTOO_SOON

  loan.changeImpairment pool (impaired := true)

-- Reverse the paper loss an impairment recorded
def Loan.manageUnimpair {α : Type} [AssetPool α] (loan : Loan) (pool : α) : TerExcept (LoanWithPool α) :=
  loan.changeImpairment pool (impaired := false)

-- Default a loan: first-loss cover absorbs part of the loss, the rest reduces the vault's AssetsTotal.
def Loan.manageDefault {α : Type} [AssetPool α] (loan : Loan) (pool : α) : TerExcept (LoanWithAmounts α) := do
  let broker := loan.broker
  let totalDefaultAmount := loan.principalOutstanding
  let scheduledInterest ← loan.interestDue
  let defaultCovered ← defaultCoveredAmount broker pool totalDefaultAmount

  -- the cover joins the available assets, an impaired loan also releases its paper loss
  let change : PoolBalanceChange := {
    cash := defaultCovered
    deployed := totalDefaultAmount.operator_neg
    yield := scheduledInterest.operator_neg
    loss := if loan.isImpaired then totalDefaultAmount.operator_neg else Number.zero }
  let pool' ← AssetPool.adjustBalances pool change

  let debtTotal' ← broker.debtTotal.operator_sub totalDefaultAmount .to_nearest
  let coverAvailable' ← broker.coverAvailable.operator_sub defaultCovered .to_nearest
  let rawBroker' : RawLoanBroker := { broker.toRawLoanBroker with
    debtTotal := debtTotal', coverAvailable := coverAvailable' }
  let broker' ← rawBroker'.to_lawful

  let rawLoan' : RawLoan := { loan.toRawLoan with
    broker := broker'
    isDefault := true
    totalValueOutstanding := Number.zero
    principalOutstanding := Number.zero
    managementFeeOutstanding := Number.zero
    paymentRemaining := 0
    nextPaymentDueDate := 0 }
  let loan' ← rawLoan'.to_lawful

  return { loan' := loan', pool' := pool', amountToPool := defaultCovered, amountToBroker := Number.zero }

end XRPL.Model.Lending
