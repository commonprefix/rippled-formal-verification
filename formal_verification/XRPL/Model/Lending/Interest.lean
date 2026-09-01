import XRPL.Model.Protocol.Number
import XRPL.Model.Protocol.TenthBips

namespace XRPL.Model.Lending

open XRPL.Model.Protocol

def secondsInYear : Number := Number.ofInt64 31_536_000

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

end XRPL.Model.Lending
