import XRPL.Model.Protocol.Number
import XRPL.Model.Protocol.Rounding
import XRPL.Model.Protocol.STAmount
import XRPL.Model.Protocol.TER
import XRPL.Model.Lending.Amortization
import XRPL.Model.Lending.AssetPool
import XRPL.Model.Lending.Interest
import XRPL.Model.Lending.Loan.Loan
import XRPL.Model.Lending.LoanBroker.BrokerCover
import XRPL.Model.Lending.LoanBroker.LoanBroker

namespace XRPL.Model.Lending

open XRPL.Model.Protocol

-- The derived values of a loan, rounded at the loan scale
structure LoanProperties where
  periodicPayment : Number
  totalValueOutstanding : Number
  managementFeeOutstanding : Number
  loanScale : Int
  principalOutstanding : Number
  -- the unrounded principal part of the first payment, positive when the loan can amortize
  firstPaymentPrincipal : Number

-- C++ getValueFields: principalRequested and each fee must pass the check
private def checkPrecisionFields (principal : Number) (fees : LoanFees) (checkFnc : Number → Except Error Bool)
    : Except Error TER := do
  for value in principal :: fees.amountFields do
    if !(← checkFnc value) then return .tecPRECISION_LOSS
  return .tesSUCCESS

-- C++ `checkVaultAcceptsLoan`
private def canFundLoan {α : Type} [AssetPool α] (pool : α) (schedule : LoanSchedule) (ledgerCloseTime : UInt32)
    (nt : NumericType) : Except Error TER := do
  let phase := AssetPool.phase pool ledgerCloseTime
  match phase with
  | .subscription => return .tecTOO_SOON
  | .redemption => return .tecEXPIRED
  | .investment =>
    let finalPayment := schedule.startDate.toNat + schedule.paymentInterval.toNat * schedule.paymentTotal.toNat
    let redemptionDate := (AssetPool.redemptionDate pool).getD 0
    if finalPayment + loanRedemptionBuffer > redemptionDate.toNat then return .tecNO_PERMISSION
  | .noPhase => pure ()

  let exponent ← AssetPool.exponent pool nt
  let baseExponent := AssetPool.baseExponent pool
  if exponent != baseExponent then return .tecLIMIT_EXCEEDED

  return .tesSUCCESS

-- LoanSet -> preclaim
def Loan.canCreate {α : Type} [AssetPool α] (broker : LoanBroker) (pool : α) (principalRequested : Number)
    (fees : LoanFees) (schedule : LoanSchedule) (ledgerCloseTime : UInt32) (twoStep : Bool) : Except Error TER := do
  let scheduleTer := schedule.checkTimeAvailability
  if !scheduleTer.isTesSuccess then return scheduleTer

  let hasExpired : Bool := ledgerCloseTime ≥ schedule.startDate
  if twoStep && hasExpired then return .tecEXPIRED

  let vaultTer ← canFundLoan pool schedule ledgerCloseTime broker.numericType
  if !vaultTer.isTesSuccess then return vaultTer

  let precisionTer ← checkPrecisionFields principalRequested fees
    (fun value => pure !(STAmount.isRounded broker.numericType value))
  if !precisionTer.isTesSuccess then return precisionTer

  return .tesSUCCESS

def computeLoanPropertiesFromPeriodicRate (principal periodicRate : Number) (paymentsRemaining : UInt32)
    (managementFeeRate : TenthBips16) (nt : NumericType) (minimumScale : Int)
    : Except Error LoanProperties := do
  let periodicPayment ← loanPeriodicPayment principal periodicRate paymentsRemaining

  -- Round up when there is interest, else to nearest. The scale of the total value sets the loan scale.
  let mode : rounding_mode := if periodicRate.operator_eq Number.zero then .to_nearest else .upward
  let amount ← periodicPayment.operator_mul (Number.ofInt64 paymentsRemaining.toUInt64.toInt64) mode
  let amountSt ← STAmount.ofNumber nt amount mode
  let loanScale := max minimumScale amountSt.exponent
  let totalValueOutstanding ← STAmount.roundToNumericType nt amount mode (some loanScale)

  let roundedPrincipal ← STAmount.roundToNumericType nt principal .to_nearest (some loanScale)
  let totalInterest ← totalValueOutstanding.operator_sub roundedPrincipal .to_nearest
  let managementFeeOutstanding ← computeManagementFee nt totalInterest managementFeeRate loanScale

  let startPrincipal ← loanPrincipalFromPeriodicPayment periodicPayment periodicRate paymentsRemaining
  let nextPrincipal ← loanPrincipalFromPeriodicPayment periodicPayment periodicRate (paymentsRemaining - 1)
  let firstPaymentPrincipal ← startPrincipal.operator_sub nextPrincipal .to_nearest

  return {
    periodicPayment := periodicPayment
    totalValueOutstanding := totalValueOutstanding
    managementFeeOutstanding := managementFeeOutstanding
    loanScale := loanScale
    principalOutstanding := roundedPrincipal
    firstPaymentPrincipal := firstPaymentPrincipal
  }

def computeLoanProperties (principal : Number) (interestRate : TenthBips32)
    (paymentInterval paymentsRemaining : UInt32) (managementFeeRate : TenthBips16)
    (nt : NumericType) (minimumScale : Int) : Except Error LoanProperties := do
  let periodicRate ← loanPeriodicRate interestRate paymentInterval
  computeLoanPropertiesFromPeriodicRate principal periodicRate paymentsRemaining managementFeeRate nt minimumScale

def LoanProperties.amortizationGuards (properties : LoanProperties) (principal : Number) (expectInterest : Bool)
    (paymentsRemaining : UInt32) (nt : NumericType) : Except Error TER := do
  -- guard 1: a loan with an interest rate must carry some interest, one without must carry none
  let totalInterest ← properties.totalValueOutstanding.operator_sub principal .to_nearest
  if expectInterest && totalInterest.signum ≤ 0 then return .tecPRECISION_LOSS
  if !expectInterest && totalInterest.signum > 0 then return .tecINTERNAL

  -- guard 2: the first payment, which pays the least principal, must still pay some
  if properties.firstPaymentPrincipal.signum ≤ 0 then return .tecPRECISION_LOSS

  -- guard 3: the rounded payment must not vanish
  let roundedPayment ← STAmount.roundToNumericType nt properties.periodicPayment .upward (some properties.loanScale)
  if roundedPayment.operator_eq Number.zero then return .tecPRECISION_LOSS

  -- guard 4: the rounded payments must complete the loan in exactly the scheduled count
  let ratio ← properties.totalValueOutstanding.operator_div roundedPayment .upward
  let computedPayments ← ratio.to_rep .upward
  if computedPayments != paymentsRemaining.toUInt64.toInt64 then return .tecPRECISION_LOSS
  return .tesSUCCESS

-- The amortization guards, then the sanity check on the computed values that follows them in LoanSet
def LoanProperties.checkGuards (properties : LoanProperties) (principal : Number) (interestRate : TenthBips32)
    (paymentsRemaining : UInt32) (nt : NumericType) : Except Error TER := do
  let guardTer ← properties.amortizationGuards principal (interestRate != 0) paymentsRemaining nt
  if !guardTer.isTesSuccess then return guardTer

  if properties.managementFeeOutstanding.signum < 0 || properties.totalValueOutstanding.signum ≤ 0
      || properties.periodicPayment.signum ≤ 0 then return .tecINTERNAL
  return .tesSUCCESS

-- broker stays under its debt cap and keeps enough cover
def LoanBroker.checkLimits (broker : LoanBroker) (debtTotal' : Number) (vaultExponent : Int)
    : Except Error TER := do
  if broker.debtMaximum.operator_ne Number.zero && broker.debtMaximum.operator_lt debtTotal' then
    return .tecLIMIT_EXCEEDED
  let rawBroker' : RawLoanBroker := { broker.toRawLoanBroker with debtTotal := debtTotal' }
  let hasMinimumCover ← rawBroker'.hasMinimumCover vaultExponent
  if !hasMinimumCover then return .tecINSUFFICIENT_FUNDS
  return .tesSUCCESS

-- Assemble the raw loan object from its computed properties (C++ buildLoan)
def RawLoan.build (properties : LoanProperties) (rates : LoanRates) (fees : LoanFees) (schedule : LoanSchedule)
    (broker : LoanBroker) (allowsOverpayment isPending : Bool) : RawLoan := {
  broker := broker
  rates := rates
  fees := fees
  schedule := schedule
  paymentRemaining := schedule.paymentTotal
  periodicPayment := properties.periodicPayment
  principalOutstanding := properties.principalOutstanding
  totalValueOutstanding := properties.totalValueOutstanding
  managementFeeOutstanding := properties.managementFeeOutstanding
  loanScale := properties.loanScale
  previousPaymentDueDate := 0
  nextPaymentDueDate := schedule.startDate + schedule.paymentInterval
  isPending := isPending
  isImpaired := false
  isDefault := false
  allowsOverpayment := allowsOverpayment
}

-- LoanSet -> doApply
def Loan.create {α : Type} [AssetPool α] (broker : LoanBroker) (pool : α) (principal : Number)
    (rates : LoanRates) (fees : LoanFees) (schedule : LoanSchedule) (allowsOverpayment pending : Bool)
    : TerExcept (LoanWithPool α) := do
  let nt := broker.numericType
  let poolAmounts := AssetPool.amounts pool
  if poolAmounts.assetsAvailable.operator_lt principal then throw .tecINSUFFICIENT_FUNDS
  let vaultExponent := AssetPool.baseExponent pool

  let properties ← computeLoanProperties principal rates.interestRate
    schedule.paymentInterval schedule.paymentTotal broker.managementFeeRate nt vaultExponent
  let precisionTer ← checkPrecisionFields principal fees
    (fun value => isRounded value properties.loanScale nt)
  if !precisionTer.isTesSuccess then throw precisionTer

  let guardTer ← properties.checkGuards principal rates.interestRate schedule.paymentTotal nt
  if !guardTer.isTesSuccess then throw guardTer

  -- the interest of the new loan must fit in the vault's Open zone
  let loanState ← LoanState.build properties.totalValueOutstanding principal properties.managementFeeOutstanding
  let exceedsOpenLimit ← AssetPool.exceedsOpenLimit pool loanState.interestDue
  if exceedsOpenLimit then
    throw .tecLIMIT_EXCEEDED

  let debtTotal' ← broker.debtTotal.operator_add principal .to_nearest
  let limitTer ← broker.checkLimits debtTotal' vaultExponent
  if !limitTer.isTesSuccess then throw limitTer

  -- the principal is deployed, a pending loan also reserves it, an active loan adds its interest to the yield
  let principal' ← STAmount.roundToNumericType nt principal .to_nearest
  let change : PoolBalanceChange := {
    cash := principal'.operator_neg
    deployed := principal
    yield := if pending then Number.zero else loanState.interestDue
    reserved := if pending then principal' else Number.zero }
  let pool' ← AssetPool.adjustBalances pool change

  let rawBroker' : RawLoanBroker := { broker.toRawLoanBroker with
    debtTotal := debtTotal', loanCount := broker.loanCount + 1 }
  let broker' ← rawBroker'.to_lawful

  let rawLoan := RawLoan.build properties rates fees schedule broker'
    allowsOverpayment pending
  let loan ← rawLoan.to_lawful

  return { loan' := loan, pool' := pool' }

def Loan.createPending {α : Type} [AssetPool α] (broker : LoanBroker) (pool : α) (principal : Number)
    (rates : LoanRates) (fees : LoanFees) (schedule : LoanSchedule) (allowsOverpayment : Bool)
    : TerExcept (LoanWithPool α) :=
  Loan.create broker pool principal rates fees schedule allowsOverpayment true

def Loan.createImmediate {α : Type} [AssetPool α] (broker : LoanBroker) (pool : α) (principal : Number)
    (rates : LoanRates) (fees : LoanFees) (schedule : LoanSchedule) (allowsOverpayment : Bool)
    : TerExcept (LoanWithPool α) :=
  Loan.create broker pool principal rates fees schedule allowsOverpayment false

end XRPL.Model.Lending
