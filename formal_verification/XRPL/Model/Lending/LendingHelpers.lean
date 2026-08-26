import XRPL.Model.Protocol.Exponent
import XRPL.Model.Protocol.Number
import XRPL.Model.Protocol.STAmount
import XRPL.Model.Protocol.NumericType
import XRPL.Model.Protocol.TER
import XRPL.Model.Protocol.TenthBips

namespace XRPL.Model.Lending

open XRPL.Model.Protocol

def secondsInYear : Number := Number.ofInt64 31_536_000

def hasExpired (ledgerCloseTime expTime : UInt32) : Bool :=
  ledgerCloseTime ≥ expTime

-- XLS-66 (1): annual rate prorated to the interval
def loanPeriodicRate (interestRate : TenthBips32) (paymentInterval : UInt32)
    : Except Error Number := do
  let paymentIntervalInt64 := paymentInterval.toUInt64.toInt64
  let tenthBips ← tenthBipsOfValue (Number.ofInt64 paymentIntervalInt64) interestRate .to_nearest
  tenthBips.operator_div secondsInYear .to_nearest

-- binomial series for (1+rate)^paymentsRemaining - 1, stop once a term underflows
def powerMinusOneLoop (rate : Number) (paymentsRemaining index : Nat)
    (currentTerm runningSum : Number) : Except Error Number := do
  if h : index < paymentsRemaining then
    let currentTerm ← currentTerm.operator_mul rate .to_nearest
    let currentTerm ←
      currentTerm.operator_mul (Number.ofInt64 (paymentsRemaining - index).toInt64) .to_nearest

    let currentTerm ← currentTerm.operator_div (Number.ofInt64 (index + 1).toInt64) .to_nearest
    let nextSum ← runningSum.operator_add currentTerm .to_nearest

    if nextSum.operator_eq runningSum then return runningSum
    else powerMinusOneLoop rate paymentsRemaining (index + 1) currentTerm nextSum
  else return runningSum
  termination_by paymentsRemaining - index
  decreasing_by omega

-- (1+rate)^paymentsRemaining - 1 by binomial series, for near-zero rate
def computePowerMinusOne (rate paymentsRemainingNum : Number) (paymentsRemaining : UInt32)
    : Except Error Number := do
  if paymentsRemaining == 0 || rate.operator_eq Number.zero then return Number.zero
  let currentTerm ← paymentsRemainingNum.operator_mul rate .to_nearest
  powerMinusOneLoop rate paymentsRemaining.toNat 1 currentTerm currentTerm

-- (1+rate)^paymentsRemaining - 1: closed form for large paymentsRemaining*rate, else binomial
def computePowerMinusOneHybrid (rate paymentsRemainingNum : Number) (paymentsRemaining : UInt32)
    : Except Error Number := do
  if paymentsRemaining == 0 || rate.operator_eq Number.zero then return Number.zero
  let nRate ← paymentsRemainingNum.operator_mul rate .to_nearest

  let cancellationThreshold ← Number.from_rep 1 (-9) largeRange.min largeRange.max .to_nearest
  if nRate.operator_ge cancellationThreshold then
    let one := Number.ofInt64 1
    let base ← one.operator_add rate .to_nearest
    let raised ← Number.power base paymentsRemaining.toNat
    raised.operator_sub one .to_nearest
  else
    computePowerMinusOne rate paymentsRemainingNum paymentsRemaining

-- XLS-66 (6): payment factor rate*(1+m)/m, m = (1+rate)^paymentsRemaining - 1
def computePaymentFactor (rate paymentsRemainingNum : Number) (paymentsRemaining : UInt32)
    : Except Error Number := do
  if paymentsRemaining == 0 then return Number.zero
  if rate.operator_eq Number.zero then
    (Number.ofInt64 1).operator_div paymentsRemainingNum .to_nearest
  else
    let powerMinusOne ← computePowerMinusOneHybrid rate paymentsRemainingNum paymentsRemaining
    let raisedRate ← (Number.ofInt64 1).operator_add powerMinusOne .to_nearest
    let numerator ← rate.operator_mul raisedRate .to_nearest
    numerator.operator_div powerMinusOne .to_nearest

-- XLS-66 (7): fixed per-period payment
def loanPeriodicPayment (principal rate : Number) (paymentsRemaining : UInt32)
    : Except Error Number := do
  if principal.operator_eq Number.zero || paymentsRemaining == 0 then return Number.zero
  let paymentsRemainingNum := Number.ofInt64 paymentsRemaining.toUInt64.toInt64
  if rate.operator_eq Number.zero then
    principal.operator_div paymentsRemainingNum .to_nearest
  else
    let factor ← computePaymentFactor rate paymentsRemainingNum paymentsRemaining
    principal.operator_mul factor .to_nearest

-- XLS-66 (32): management fee on the interest, rounded down
def computeManagementFee (nt : NumericType) (value : Number) (feeRate : TenthBips16) (scale : Int)
    : Except Error Number := do
  let raw ← tenthBipsOfValue value feeRate.toTenthBips32 .to_nearest
  STAmount.roundToNumericType nt raw .downward (some scale)

def adjustImpreciseNumber (nt : NumericType) (value adjustment : Number) (scale : Int)
    : Except Error Number := do
  let adjusted ← value.operator_add adjustment .to_nearest
  let rounded ← STAmount.roundToNumericType nt adjusted .to_nearest (some scale)
  if rounded.signum < 0 then return Number.zero else return rounded

-- minimum first-loss cover for the debt, rounded up
def minimumBrokerCover (nt : NumericType) (debtTotal : Number) (coverRateMinimum : TenthBips32) (poolExponent : Int)
    : Except Error Number := do
  let raw ← tenthBipsOfValue debtTotal coverRateMinimum .upward
  STAmount.roundToNumericType nt raw .upward (some poolExponent)

-- reject a cover deposit/withdraw/clawback that rounds to zero at the cover's own scale
def canApplyToBrokerCover (nt : NumericType) (coverAvailable : Number) (amount : STAmount)
    : Except Error TER := do
  if amount.isZero then
    return .tecPRECISION_LOSS
  let coverExponent ← numberExponent coverAvailable nt
  let rounded ← STAmount.roundToExponent amount coverExponent .to_nearest
  if rounded.signum == 0 then
    return .tecPRECISION_LOSS
  return .tesSUCCESS

-- XLS-66 (10): principal implied by a periodic payment
def loanPrincipalFromPeriodicPayment (periodicPayment rate : Number) (paymentsRemaining : UInt32)
    : Except Error Number := do
  if paymentsRemaining == 0 then return Number.zero
  let paymentsRemainingNum := Number.ofInt64 paymentsRemaining.toUInt64.toInt64
  if rate.operator_eq Number.zero then
    periodicPayment.operator_mul paymentsRemainingNum .to_nearest
  else
    let factor ← computePaymentFactor rate paymentsRemainingNum paymentsRemaining
    periodicPayment.operator_div factor .to_nearest

-- exactly representable at scale (round-down == round-up)
def isRounded (nt : NumericType) (value : Number) (scale : Int) : Except Error Bool := do
  let down ← STAmount.roundToNumericType nt value .downward (some scale)
  let up ← STAmount.roundToNumericType nt value .upward (some scale)
  return down.operator_eq up

end XRPL.Model.Lending
