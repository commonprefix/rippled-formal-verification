import XRPL.Model.Protocol.Exponent
import XRPL.Model.Protocol.Number
import XRPL.Model.Protocol.NumericType
import XRPL.Model.Protocol.Rounding
import XRPL.Model.Protocol.STAmount
import XRPL.Model.Protocol.TenthBips
import XRPL.Model.Vault.Vault
import XRPL.Model.Lending.Loan.Loan
import XRPL.Model.Lending.Loan.LoanResult
import XRPL.Model.Lending.LoanBroker.LoanBroker

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault

-- The management action a transaction requests (only one may be set).
inductive LoanManageAction where
  | impair | unimpair | default
  deriving DecidableEq, Repr

-- Amount of the default the broker's first-loss cover absorbs
private def defaultCoveredAmount (broker : LoanBroker) (totalDefaultAmount : Number) (nt : NumericType) (scale : Int)
    : Except Error Number := do
  let minimumCover ← tenthBipsOfValue broker.debtTotal broker.coverRateMinimum .upward
  let liquidationAmount ← tenthBipsOfValue minimumCover broker.coverRateLiquidation .upward

  let coveredAmount := Number.min liquidationAmount totalDefaultAmount
  let coveredAmount' ← STAmount.roundToNumericType nt coveredAmount .upward (some scale)

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
def Loan.manageImpair (loan : Loan) (vault : Vault) (now : UInt32) : Except Error (LoanResult LoanVault) := do
  -- a loan that is not late yet can not be impaired
  if !(loan.isPaymentLate now) then
    return .rejected .tecTOO_SOON

  let vaultScale ← numberExponent vault.assetsTotal vault.numericType
  let lossUnrealized' ← sumRoundAndClamp vault.lossUnrealized loan.principalOutstanding vaultScale vault.numericType

  let assetsDiff ← vault.assetsTotal.operator_sub vault.assetsAvailable .to_nearest
  if lossUnrealized'.operator_gt assetsDiff then
    return .rejected .tecLIMIT_EXCEEDED

  let vault' ← ({ vault.toRawVault with lossUnrealized := lossUnrealized' } : RawVault).to_lawful
  let loan' := { loan with isImpaired := true }
  return .ok { loan := loan', vault := vault' }

-- Reverse the paper loss an impairment recorded
def Loan.manageUnimpair (loan : Loan) (vault : Vault) : Except Error (LoanResult LoanVault) := do
  let vaultScale ← numberExponent vault.assetsTotal vault.numericType
  if vault.lossUnrealized.operator_lt loan.principalOutstanding then
    return .rejected .tefBAD_LEDGER

  let loanPrincipalNeg := loan.principalOutstanding.operator_neg
  let lossUnrealized' ← sumRoundAndClamp vault.lossUnrealized loanPrincipalNeg vaultScale vault.numericType

  let vault' ← ({ vault.toRawVault with lossUnrealized := lossUnrealized' } : RawVault).to_lawful
  let loan' := { loan with isImpaired := false }
  return .ok { loan := loan', vault := vault' }

-- Default a loan: first-loss cover absorbs part of the loss, the rest reduces the vault's AssetsTotal.
def Loan.manageDefault (loan : Loan) (vault : Vault) (broker : LoanBroker) (impaired : Bool)
    : Except Error (LoanResult LendingState) := do
  let totalDefaultAmount := loan.principalOutstanding
  let defaultCovered ← defaultCoveredAmount broker totalDefaultAmount vault.numericType loan.loanScale

  -- the vault absorbs the remaining default amount by reducing AssetsTotal
  let vaultDefaultAmount ← totalDefaultAmount.operator_sub defaultCovered .to_nearest
  let vaultScale ← numberExponent vault.assetsTotal vault.numericType
  if vault.assetsTotal.operator_lt vaultDefaultAmount then
    return .rejected .tefBAD_LEDGER

  let vaultDefaultAmount' ← STAmount.roundToNumericType vault.numericType vaultDefaultAmount .downward (some vaultScale)
  let assetsTotal ← vault.assetsTotal.operator_sub vaultDefaultAmount' .to_nearest
  let assetsAvailable' ← vault.assetsAvailable.operator_add defaultCovered .to_nearest

  let assetsTotal' ← dustAdjustedAssetsTotal assetsAvailable' assetsTotal vault.numericType
  if assetsAvailable'.operator_gt assetsTotal' then
    return .rejected .tecINTERNAL

  -- realize the loss only when the loan was already impaired
  if impaired && vault.lossUnrealized.operator_lt totalDefaultAmount then
    return .rejected .tefBAD_LEDGER
  let lossUnrealized' ←
    if impaired then sumRoundAndClamp vault.lossUnrealized totalDefaultAmount.operator_neg vaultScale vault.numericType
    else pure vault.lossUnrealized

  let debtTotal' ← sumRoundAndClamp broker.debtTotal totalDefaultAmount.operator_neg vaultScale vault.numericType
  if broker.coverAvailable.operator_lt defaultCovered then
    return .rejected .tefBAD_LEDGER
  let coverAvailable' ← broker.coverAvailable.operator_sub defaultCovered .to_nearest

  let rawVault' : RawVault := { vault.toRawVault with
    assetsTotal := assetsTotal'
    assetsAvailable := assetsAvailable'
    lossUnrealized := lossUnrealized'
  }
  let vault' ← rawVault'.to_lawful
  let broker' := { broker with debtTotal := debtTotal', coverAvailable := coverAvailable' }
  let loan' := { loan with
    isDefault := true
    totalValueOutstanding := Number.zero
    principalOutstanding := Number.zero
    managementFeeOutstanding := Number.zero
    paymentRemaining := 0
    nextPaymentDueDate := 0 }
  return .ok { vault := vault', broker := broker', loan := loan', amount := some defaultCovered }

end XRPL.Model.Lending
