import XRPL.Model.Protocol.Exponent
import XRPL.Model.Protocol.Number
import XRPL.Model.Protocol.Rounding
import XRPL.Model.Protocol.STAmount
import XRPL.Model.Protocol.TER
import XRPL.Model.Vault.Vault
import XRPL.Model.Lending.Amortization
import XRPL.Model.Lending.Interest
import XRPL.Model.Lending.Loan.Loan
import XRPL.Model.Lending.Loan.LoanResult
import XRPL.Model.Lending.LoanBroker.BrokerCover
import XRPL.Model.Lending.LoanBroker.LoanBroker

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault

-- C++ getValueFields: principalRequested and each fee must pass the check
private def checkPrecisionFields (principal : Number) (fees : LoanFees) (checkFnc : Number → Except Error Bool)
    : Except Error TER := do
  for value in principal :: fees.amountFields do
    if !(← checkFnc value) then return .tecPRECISION_LOSS
  return .tesSUCCESS

-- LoanSet -> preclaim
def Loan.canCreate (vault : Vault) (principalRequested : Number) (fees : LoanFees) (schedule : LoanSchedule)
    (ledgerCloseTime : UInt32) (twoStep : Bool) : Except Error TER := do
  let scheduleTer := schedule.checkTimeAvailability
  if !scheduleTer.isTesSuccess then return scheduleTer

  let precisionTer ← checkPrecisionFields principalRequested fees
    (STAmount.equalAfterNumberConvert vault.numericType)
  if !precisionTer.isTesSuccess then return precisionTer

  if twoStep && hasExpired ledgerCloseTime schedule.startDate then return .tecEXPIRED
  return .tesSUCCESS

-- The derived values of a loan, rounded at the loan scale
structure LoanProperties where
  periodicPayment : Number
  totalValueOutstanding : Number
  managementFeeOutstanding : Number
  loanScale : Int
  principalOutstanding : Number
  -- the unrounded principal part of the first payment, positive when the loan can amortize
  firstPaymentPrincipal : Number

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
def LoanBroker.checkLimits (broker : LoanBroker) (newDebtTotal : Number) (nt : NumericType)
    (vaultExponent : Int) : Except Error TER := do
  if broker.debtMaximum.operator_ne Number.zero && broker.debtMaximum.operator_lt newDebtTotal then
    return .tecLIMIT_EXCEEDED
  let minimumCover ← minimumBrokerCover nt newDebtTotal broker.coverRateMinimum vaultExponent
  if broker.coverAvailable.operator_lt minimumCover then return .tecINSUFFICIENT_FUNDS
  return .tesSUCCESS

-- Assemble the loan object from its computed properties (C++ buildLoan)
def Loan.build (properties : LoanProperties) (rates : LoanRates) (fees : LoanFees) (schedule : LoanSchedule)
    (allowsOverpayment isPending : Bool) : Loan := {
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
def Loan.create (vault : Vault) (broker : LoanBroker) (principal : Number)
    (rates : LoanRates) (fees : LoanFees) (schedule : LoanSchedule) (allowsOverpayment pending : Bool)
    : Except Error (LoanResult LendingState) := do
  if vault.assetsAvailable.operator_lt principal then return .rejected .tecINSUFFICIENT_FUNDS
  let vaultExponent ← numberExponent vault.assetsTotal vault.numericType

  let properties ← computeLoanProperties principal rates.interestRate
    schedule.paymentInterval schedule.paymentTotal broker.managementFeeRate vault.numericType vaultExponent
  let precisionTer ← checkPrecisionFields principal fees
    (fun value => isRounded vault.numericType value properties.loanScale)
  if !precisionTer.isTesSuccess then return .rejected precisionTer

  let guardTer ← properties.checkGuards principal rates.interestRate schedule.paymentTotal vault.numericType
  if !guardTer.isTesSuccess then return .rejected guardTer

  let newDebtTotal ← broker.debtTotal.operator_add principal .to_nearest
  let limitTer ← broker.checkLimits newDebtTotal vault.numericType vaultExponent
  if !limitTer.isTesSuccess then return .rejected limitTer

  let loan := Loan.build properties rates fees schedule allowsOverpayment pending

  -- the principal leaves the available assets, a pending loan adds it in the reserved assets
  let assetsAvailable' ← vault.assetsAvailable.operator_sub principal .to_nearest
  let assetsReserved' ← if pending then vault.assetsReserved.operator_add principal .to_nearest
                        else pure vault.assetsReserved
  let rawVault' : RawVault := { vault.toRawVault with assetsAvailable := assetsAvailable', assetsReserved := assetsReserved' }
  let vault' ← rawVault'.to_lawful

  let debtTotal' ← adjustImpreciseNumber vault.numericType broker.debtTotal principal vaultExponent
  let broker' := { broker with debtTotal := debtTotal', loanCount := broker.loanCount + 1 }

  return .ok { vault := vault', broker := broker', loan := loan }

def Loan.createPending (vault : Vault) (broker : LoanBroker) (principal : Number)
    (rates : LoanRates) (fees : LoanFees) (schedule : LoanSchedule) (allowsOverpayment : Bool)
    : Except Error (LoanResult LendingState) :=
  Loan.create vault broker principal rates fees schedule allowsOverpayment true

def Loan.createImmediate (vault : Vault) (broker : LoanBroker) (principal : Number)
    (rates : LoanRates) (fees : LoanFees) (schedule : LoanSchedule) (allowsOverpayment : Bool)
    : Except Error (LoanResult LendingState) :=
  Loan.create vault broker principal rates fees schedule allowsOverpayment false

end XRPL.Model.Lending
