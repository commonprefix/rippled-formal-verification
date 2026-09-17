import XRPL.Model.Protocol.Exponent
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
private def defaultCoveredAmount (broker : LoanBroker) (totalDefaultAmount : Number) (scale : Int)
    : Except Error Number := do
  let minimumCover ← tenthBipsOfValue broker.debtTotal broker.coverRateMinimum .upward
  let liquidationAmount ← tenthBipsOfValue minimumCover broker.coverRateLiquidation .upward

  let coveredAmount := Number.min liquidationAmount totalDefaultAmount
  let coveredAmount' ← STAmount.roundToNumericType broker.numericType coveredAmount .upward (some scale)

  return Number.min coveredAmount' broker.coverAvailable

-- If AA exceeds AT by only a dust amount (more than 13 exponents smaller), raise AT to AA.
private def dustAdjustedAssetsTotal (assetsAvailable assetsTotal : Number) (nt : NumericType)
    : Except Error Number := do
  if nt.isIntegral || assetsAvailable.operator_le assetsTotal then
    return assetsTotal
  let assetsDiff ← assetsAvailable.operator_sub assetsTotal .to_nearest
  let isDust := assetsAvailable.exponent_ - assetsDiff.exponent_ > 13
  return (if isDust then assetsAvailable else assetsTotal)

-- LoanManage -> preclaim
def Loan.canManage (loan : Loan) (action : LoanManageAction) (now : UInt32) : TER :=
  let gracePeriodEnd := loan.nextPaymentDueDate + loan.schedule.gracePeriod

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
  else if action == .default && !hasExpired now gracePeriodEnd (exclusive := true) then
    .tecTOO_SOON
  else
    .tesSUCCESS

-- Record the loan's exposure as a paper loss.
def Loan.manageImpair {α : Type} [AssetPool α] (loan : Loan) (pool : α) (now : UInt32)
    : Except Error (LoanWithPoolTerResult α) := do
  -- a loan that is not late yet can not be impaired
  if !(loan.isPaymentLate now) then
    return .error .tecTOO_SOON

  let nt := loan.broker.numericType
  let poolAmounts := AssetPool.amounts pool
  let vaultScale ← AssetPool.exponent pool nt
  let lossUnrealized' ← sumRoundAndClamp poolAmounts.lossUnrealized loan.principalOutstanding vaultScale nt

  let assetsDiff ← poolAmounts.assetsTotal.operator_sub poolAmounts.assetsAvailable .to_nearest
  if lossUnrealized'.operator_gt assetsDiff then
    return .error .tecLIMIT_EXCEEDED

  let pool' ← AssetPool.updateAmounts pool { poolAmounts with lossUnrealized := lossUnrealized' }

  let rawLoan' : RawLoan := { loan.toRawLoan with isImpaired := true }
  let loan' ← rawLoan'.to_lawful
  return .ok { loan' := loan', pool' := pool' }

-- Reverse the paper loss an impairment recorded
def Loan.manageUnimpair {α : Type} [AssetPool α] (loan : Loan) (pool : α)
    : Except Error (LoanWithPoolTerResult α) := do
  let nt := loan.broker.numericType
  let poolAmounts := AssetPool.amounts pool
  let vaultScale ← AssetPool.exponent pool nt
  if poolAmounts.lossUnrealized.operator_lt loan.principalOutstanding then
    return .error .tefBAD_LEDGER

  let loanPrincipalNeg := loan.principalOutstanding.operator_neg
  let lossUnrealized' ← sumRoundAndClamp poolAmounts.lossUnrealized loanPrincipalNeg vaultScale nt

  let pool' ← AssetPool.updateAmounts pool { poolAmounts with lossUnrealized := lossUnrealized' }

  let rawLoan' : RawLoan := { loan.toRawLoan with isImpaired := false }
  let loan' ← rawLoan'.to_lawful

  return .ok { loan' := loan', pool' := pool' }

-- Default a loan: first-loss cover absorbs part of the loss, the rest reduces the vault's AssetsTotal.
def Loan.manageDefault {α : Type} [AssetPool α] (loan : Loan) (pool : α)
    : Except Error (LoanWithAmountsTerResult α) := do
  let broker := loan.broker
  let nt := broker.numericType
  let poolAmounts := AssetPool.amounts pool
  let totalDefaultAmount := loan.principalOutstanding
  let defaultCovered ← defaultCoveredAmount broker totalDefaultAmount loan.loanScale

  -- the vault absorbs the remaining default amount by reducing AssetsTotal
  let vaultDefaultAmount ← totalDefaultAmount.operator_sub defaultCovered .to_nearest
  let vaultScale ← AssetPool.exponent pool nt
  if poolAmounts.assetsTotal.operator_lt vaultDefaultAmount then
    return .error .tefBAD_LEDGER

  let vaultDefaultAmount' ← STAmount.roundToNumericType nt vaultDefaultAmount .downward (some vaultScale)
  let assetsTotal ← poolAmounts.assetsTotal.operator_sub vaultDefaultAmount' .to_nearest
  let assetsAvailable' ← poolAmounts.assetsAvailable.operator_add defaultCovered .to_nearest

  let assetsTotal' ← dustAdjustedAssetsTotal assetsAvailable' assetsTotal nt
  if assetsAvailable'.operator_gt assetsTotal' then
    return .error .tecINTERNAL

  -- realize the loss only when the loan was already impaired
  if loan.isImpaired && poolAmounts.lossUnrealized.operator_lt totalDefaultAmount then
    return .error .tefBAD_LEDGER
  let lossUnrealized' ←
    if loan.isImpaired then
      sumRoundAndClamp poolAmounts.lossUnrealized totalDefaultAmount.operator_neg vaultScale nt
    else
      pure poolAmounts.lossUnrealized

  let debtTotal' ← sumRoundAndClamp broker.debtTotal totalDefaultAmount.operator_neg vaultScale nt
  if broker.coverAvailable.operator_lt defaultCovered then
    return .error .tefBAD_LEDGER
  let coverAvailable' ← broker.coverAvailable.operator_sub defaultCovered .to_nearest

  let pool' ← AssetPool.updateAmounts pool { poolAmounts with
    assetsTotal := assetsTotal'
    assetsAvailable := assetsAvailable'
    lossUnrealized := lossUnrealized' }

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

  return .ok { loan' := loan', pool' := pool', amountToPool := defaultCovered, amountToBroker := Number.zero }

end XRPL.Model.Lending
