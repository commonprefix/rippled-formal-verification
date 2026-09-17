import XRPL.Model.Protocol.Number
import XRPL.Model.Protocol.NumericType
import XRPL.Model.Protocol.Rounding
import XRPL.Model.Protocol.STAmount
import XRPL.Model.Protocol.TenthBips
import XRPL.Model.Lending.Amortization
import XRPL.Model.Lending.AssetPool
import XRPL.Model.Lending.CashBasis
import XRPL.Model.Lending.Interest
import XRPL.Model.Lending.Loan.Loan
import XRPL.Model.Lending.Loan.LoanManage
import XRPL.Model.Lending.Loan.LoanSet
import XRPL.Model.Lending.Loan.LoanState
import XRPL.Model.Lending.LoanBroker.LoanBroker

namespace XRPL.Model.Lending

open XRPL.Model.Protocol

-- The kind of payment a LoanPay transaction requests
inductive LoanPaymentType where
  | regular | late | full | overpayment
  deriving DecidableEq, Repr

-- The loan re-amortized after an overpayment, with the amounts the overpayment changes
structure Reamortization where
  amounts : PaymentAmounts
  state : LoanState
  periodicPayment : Number

-- A scheduled payment that has advanced the loan but not yet paid the pool and broker.
structure UnsettledPayment (α : Type) where
  loan : Loan
  pool : α
  amounts : PaymentAmounts
  totalPaid : Number
  count : Nat

-- Round the interest, then split it into the net interest and the management fee on it.
private def roundAndSplitInterest (interest : Number) (mgmtRate : TenthBips16) (mode : rounding_mode)
    (nt : NumericType) (scale : Int) : Except Error (Number × Number) := do
  let interest' ← STAmount.roundToNumericType nt interest mode (some scale)
  let managementFee ← computeManagementFee nt interest' mgmtRate scale
  let netInterest ← interest'.operator_sub managementFee .to_nearest
  return (netInterest, managementFee)

-- The deltas of the next scheduled instalment, regular or final
private def Loan.scheduledComponents (loan : Loan) : Except Error PaymentComponents := do
  let nt := loan.broker.numericType
  let mgmtRate := loan.broker.managementFeeRate
  let tvo := loan.totalValueOutstanding
  let po := loan.principalOutstanding
  let mfo := loan.managementFeeOutstanding
  let periodicPayment := loan.periodicPayment
  let paymentRemaining := loan.paymentRemaining
  let scale := loan.loanScale
  let periodicRate ← loan.periodicRate
  let periodicPayment' ← STAmount.roundToNumericType nt periodicPayment .upward (some scale)

  -- the final instalment clears everything that is left
  if paymentRemaining == 1 || tvo.operator_le periodicPayment' then
    return { totalValueDelta := tvo
             principalDelta := po
             managementFeeDelta := mfo
             isFinal := true }

  let currentState ← loan.state
  let targetState ← LoanState.buildTheoretical periodicPayment periodicRate (paymentRemaining - 1) mgmtRate

  let targetPO ← STAmount.roundToNumericType nt targetState.principalOutstanding .upward (some scale)
  let targetInterest ← STAmount.roundToNumericType nt targetState.interestDue .downward (some scale)
  let targetMFO ← STAmount.roundToNumericType nt targetState.managementFeeDue .to_nearest (some scale)

  -- deltas = current minus target, floored at zero
  let deltas := ({ principal := ← currentState.principalOutstanding.operator_sub targetPO .to_nearest,
                   interest := ← currentState.interestDue.operator_sub targetInterest .to_nearest,
                   managementFee := ← currentState.managementFeeDue.operator_sub targetMFO .to_nearest }
                 : LoanStateDeltas).nonNegative

  -- cap each component: principal by what is outstanding, then the rest by the room left in the payment
  let cappedPrincipal := Number.min deltas.principal currentState.principalOutstanding

  let roomForInterest ← periodicPayment'.operator_sub cappedPrincipal .to_nearest
  let cappedInterest := Number.min (Number.min deltas.interest (Number.max Number.zero roomForInterest))
    currentState.interestDue
  let principalPlusInterest ← cappedPrincipal.operator_add cappedInterest .to_nearest

  let roomForFee ← periodicPayment'.operator_sub principalPlusInterest .to_nearest
  let cappedManagementFee := Number.min (Number.min deltas.managementFee roomForFee)
    currentState.managementFeeDue

  let deltas : LoanStateDeltas :=
    { principal := cappedPrincipal, interest := cappedInterest, managementFee := cappedManagementFee }

  -- remove any overpayment
  let overpayment ← (← deltas.total).operator_sub currentState.valueOutstanding .to_nearest
  let deltas ← if overpayment.operator_gt Number.zero then deltas.reduceByExcess overpayment else pure deltas

  -- if the deltas exceed the periodic payment, remove the excess
  let shortage ← periodicPayment'.operator_sub (← deltas.total) .to_nearest
  let deltas ← if shortage.signum < 0 then deltas.reduceByExcess shortage.operator_neg else pure deltas

  return { totalValueDelta := Number.clamp (← deltas.total) Number.zero currentState.valueOutstanding
           principalDelta := Number.clamp deltas.principal Number.zero currentState.principalOutstanding
           managementFeeDelta := Number.clamp deltas.managementFee Number.zero currentState.managementFeeDue
           isFinal := false }

-- The components of a late instalment
private def Loan.lateComponents (loan : Loan) (now : UInt32) : Except Error PaymentComponents := do
  let nt := loan.broker.numericType
  let mgmtRate := loan.broker.managementFeeRate
  let pc ← loan.scheduledComponents

  -- penalty interest for the overdue seconds
  let lateInterest ← loanLatePaymentInterest loan.principalOutstanding loan.rates.lateInterestRate
    now loan.nextPaymentDueDate
  let (lateInterestNet, lateFeeSplit) ← roundAndSplitInterest lateInterest mgmtRate
    .to_nearest nt loan.loanScale

  -- the broker gets the service fee
  let serviceAndLateFee ← loan.fees.serviceFee.operator_add loan.fees.latePaymentFee .to_nearest
  let untrackedFee ← serviceAndLateFee.operator_add lateFeeSplit .to_nearest

  return { pc with untrackedInterest := lateInterestNet, untrackedManagementFee := untrackedFee }

-- The components of an early payoff
private def Loan.fullComponents (loan : Loan) (now : UInt32) : Except Error PaymentComponents := do
  let nt := loan.broker.numericType
  let mgmtRate := loan.broker.managementFeeRate
  let periodicRate ← loan.periodicRate

  let theoreticalPO ← loanPrincipalFromPeriodicPayment loan.periodicPayment periodicRate loan.paymentRemaining
  let fullInterest ← computeFullPaymentInterest theoreticalPO periodicRate now
    loan.schedule.paymentInterval loan.previousPaymentDueDate loan.schedule.startDate loan.rates.closeInterestRate
  let (fullInterestNet, fullFeeSplit) ← roundAndSplitInterest fullInterest mgmtRate
    .downward nt loan.loanScale

  -- clear the whole outstanding value
  let state ← loan.state
  let closePaymentFee ← STAmount.roundToNumericType nt loan.fees.closePaymentFee .to_nearest (some loan.loanScale)
  let principalPlusInterest ← state.principalOutstanding.operator_add state.interestDue .to_nearest
  let trackedValue ← principalPlusInterest.operator_add state.managementFeeDue .to_nearest
  let closeFeePlusManagementFee ← closePaymentFee.operator_add fullFeeSplit .to_nearest
  let untrackedFee ← closeFeePlusManagementFee.operator_sub state.managementFeeDue .to_nearest
  let untrackedInterest ← fullInterestNet.operator_sub state.interestDue .to_nearest

  return { totalValueDelta := trackedValue
           principalDelta := state.principalOutstanding
           managementFeeDelta := state.managementFeeDue
           isFinal := true
           untrackedInterest := untrackedInterest
           untrackedManagementFee := untrackedFee }

-- Split an overpayment into its fee, its interest, and the principal it pays down
private def Loan.overpaymentComponents (loan : Loan) (overpayment : Number) : Except Error PaymentComponents := do
  let nt := loan.broker.numericType
  let mgmtRate := loan.broker.managementFeeRate
  let scale := loan.loanScale

  let overpaymentFee ← tenthBipsOfValue overpayment loan.rates.overpaymentFee .to_nearest
  let overpaymentFee' ← STAmount.roundToNumericType nt overpaymentFee .to_nearest (some scale)
  let valueDelta ← overpayment.operator_sub overpaymentFee' .to_nearest

  -- the interest, split into net interest and its management fee
  let overpaymentInterest ← tenthBipsOfValue overpayment loan.rates.overpaymentInterestRate .to_nearest
  let (netInterest, managementFee) ← roundAndSplitInterest overpaymentInterest mgmtRate .to_nearest nt scale

  let principalAfterInterest ← overpayment.operator_sub netInterest .to_nearest
  let principalAfterFee ← principalAfterInterest.operator_sub managementFee .to_nearest
  let principalDelta ← principalAfterFee.operator_sub overpaymentFee' .to_nearest

  return { totalValueDelta := valueDelta
           principalDelta := principalDelta
           managementFeeDelta := managementFee
           isFinal := false
           untrackedInterest := netInterest
           untrackedManagementFee := overpaymentFee' }

-- Re-amortize the remaining schedule after an overpayment. `none` when a guard drops it.
private def Loan.tryOverpayment (loan : Loan) (opc : PaymentComponents)
    : Except Error (Option Reamortization) := do
  let nt := loan.broker.numericType
  let mgmtRate := loan.broker.managementFeeRate
  let scale := loan.loanScale
  let periodicPayment := loan.periodicPayment
  let paymentRemaining := loan.paymentRemaining
  let periodicRate ← loan.periodicRate
  let state ← loan.state

  -- re-amortize for the reduced principal
  let theoreticalState ← LoanState.buildTheoretical periodicPayment periodicRate paymentRemaining mgmtRate
  let deltaErrors ← LoanState.calculateDeltas state theoreticalState
  let reducedPrincipal := Number.max
    (← theoreticalState.principalOutstanding.operator_sub opc.principalDelta .to_nearest) Number.zero
  let reamortizedProps ← computeLoanPropertiesFromPeriodicRate reducedPrincipal periodicRate paymentRemaining
    mgmtRate nt scale

  -- rebuild the state at the new payment, carrying the rounding errors
  let state' ← LoanState.buildTheoretical reamortizedProps.periodicPayment periodicRate paymentRemaining mgmtRate
  let state' ← state'.addDeltas deltaErrors

  -- pin principal and fee to the actual post-overpayment values
  let pinnedPrincipal ← state.principalOutstanding.operator_sub opc.principalDelta .to_nearest
  let grossInterest ← state'.valueOutstanding.operator_sub pinnedPrincipal .to_nearest
  let pinnedMgmtFee ← tenthBipsOfValue grossInterest mgmtRate.toTenthBips32 .to_nearest
  let state' ← LoanState.build state'.valueOutstanding pinnedPrincipal pinnedMgmtFee

  -- round and clamp into the committed new state
  let po ← roundAndClamp state'.principalOutstanding state.principalOutstanding .upward nt scale
  let interest ← state'.grossInterestOutstanding
  let tvo ← po.operator_add interest .to_nearest
  let tvo' ← roundAndClamp tvo state.valueOutstanding .upward nt scale
  let mfo ← roundAndClamp state'.managementFeeDue state.managementFeeDue .to_nearest nt scale
  let state' ← LoanState.build tvo' po mfo
  let deltas ← LoanState.calculateDeltas state state'

  -- the re-amortization guards
  let interestOut ← state'.grossInterestOutstanding
  let reamortizedProps' : LoanProperties := { reamortizedProps with
    totalValueOutstanding := tvo'
    principalOutstanding := po
    managementFeeOutstanding := mfo
    loanScale := scale }
  let guardTer ← reamortizedProps'.amortizationGuards po
    (interestOut.operator_ne Number.zero) paymentRemaining nt
  if !guardTer.isTesSuccess then return none

  if reamortizedProps'.periodicPayment.signum ≤ 0 || reamortizedProps'.totalValueOutstanding.signum ≤ 0
      || reamortizedProps'.managementFeeOutstanding.signum < 0 then return none

  if state.principalOutstanding.operator_le po then return none
  if deltas.interest.operator_neg.operator_gt Number.zero then return none

  let feePaid ← opc.managementFeeDelta.operator_add opc.untrackedManagementFee .to_nearest
  return some {
    amounts := { principalPaid := deltas.principal, interestPaid := opc.untrackedInterest, feePaid := feePaid }
    state := state'
    periodicPayment := reamortizedProps.periodicPayment
  }

-- Re-check the pool after a payment, matching the doApply checks once amounts are rounded
private def validatePostPayment {α : Type} [AssetPool α] (pool : α) (result : LoanWithAmounts α)
    (assetsTotalDelta : Number) : LoanWithAmountsTerResult α :=
  let poolAmounts := AssetPool.amounts pool
  let poolAmounts' := AssetPool.amounts result.pool'
  let assetsAvailableChanged := poolAmounts'.assetsAvailable.operator_ne poolAmounts.assetsAvailable
  let assetsTotalChanged := poolAmounts'.assetsTotal.operator_ne poolAmounts.assetsTotal
  let expectedChange := assetsTotalDelta.operator_ne Number.zero

  if !assetsAvailableChanged then .error .tecPRECISION_LOSS
  else if expectedChange && !assetsTotalChanged then .error .tecPRECISION_LOSS
  else if !expectedChange && assetsTotalChanged then .error .tecINTERNAL
  else if poolAmounts'.assetsAvailable.operator_gt poolAmounts'.assetsTotal then .error .tecINTERNAL
  else .ok result

-- Advance the loan by one instalment and report the amounts it changes
private def Loan.doPayment (loan : Loan) (pc : PaymentComponents) : Except Error (Loan × PaymentAmounts) := do
  let interestDelta ← pc.interestDelta
  let interestPaid ← interestDelta.operator_add pc.untrackedInterest .to_nearest
  let feePaid ← pc.managementFeeDelta.operator_add pc.untrackedManagementFee .to_nearest
  let amounts : PaymentAmounts :=
    { principalPaid := pc.principalDelta, interestPaid := interestPaid, feePaid := feePaid }

  if pc.isFinal then
    let rawLoan' : RawLoan := { loan.toRawLoan with
      totalValueOutstanding := Number.zero, principalOutstanding := Number.zero,
      managementFeeOutstanding := Number.zero, paymentRemaining := 0,
      previousPaymentDueDate := loan.nextPaymentDueDate, nextPaymentDueDate := 0 }
    let loan' ← rawLoan'.to_lawful
    return (loan', amounts)

  let totalValueOutstanding' ← loan.totalValueOutstanding.operator_sub pc.totalValueDelta .to_nearest
  let principalOutstanding' ← loan.principalOutstanding.operator_sub pc.principalDelta .to_nearest
  let managementFeeOutstanding' ← loan.managementFeeOutstanding.operator_sub pc.managementFeeDelta .to_nearest

  let rawLoan' : RawLoan := { loan.toRawLoan with
    totalValueOutstanding := totalValueOutstanding'
    principalOutstanding := principalOutstanding'
    managementFeeOutstanding := managementFeeOutstanding'
    paymentRemaining := loan.paymentRemaining - 1
    previousPaymentDueDate := loan.nextPaymentDueDate
    nextPaymentDueDate := loan.nextPaymentDueDate + loan.schedule.paymentInterval }
  let loan' ← rawLoan'.to_lawful
  return (loan', amounts)

-- Settle the summed amounts against the broker and its pool, then re-check the pool
private def Loan.settlePayment {α : Type} [AssetPool α] (loan : Loan) (pool : α) (amounts : PaymentAmounts)
    : Except Error (LoanWithAmountsTerResult α) := do
  let (⟨broker', pool'⟩, amountToPool) ← CashBasis.applyPayment loan.broker pool amounts

  let rawLoan' : RawLoan := { loan.toRawLoan with broker := broker' }
  let loan' ← rawLoan'.to_lawful
  let result : LoanWithAmounts α := {
    loan' := loan', pool' := pool',
    amountToPool := amountToPool, amountToBroker := amounts.feePaid }

  return validatePostPayment pool result amounts.interestPaid

-- Settle one instalment if the amount covers it, then re-check the pool
private def Loan.paySingleInstalment {α : Type} [AssetPool α] (loan : Loan) (pool : α)
    (pc : PaymentComponents) (amount : Number) : Except Error (LoanWithAmountsTerResult α) := do
  if amount.operator_lt (← pc.totalDue) then
    return .error .tecINSUFFICIENT_PAYMENT

  let (loan, amounts) ← loan.doPayment pc
  loan.settlePayment pool amounts

-- Pay scheduled instalments one at a time while the amount covers the next due and the loan is unpaid, up to 100.
private def UnsettledPayment.payInstalments {α : Type} (payment : UnsettledPayment α) (instalmentsLeft : Nat)
    (amount : Number) : Except Error (UnsettledPayment α) := do
  match instalmentsLeft with
  | 0 => return payment
  | remaining + 1 =>
    let loan := payment.loan
    if loan.paymentRemaining == 0 then return payment

    -- compute the next scheduled instalment and its amount due
    let pc ← loan.scheduledComponents
    let pc' : PaymentComponents := { pc with untrackedManagementFee := loan.fees.serviceFee }
    let due ← pc'.totalDue

    -- stop when the remaining amount cannot cover the next instalment
    if amount.operator_lt (← payment.totalPaid.operator_add due .to_nearest) then return payment

    -- advance the loan and add this instalment to the running totals
    let (loan', instalment) ← loan.doPayment pc'
    let amounts' ← payment.amounts.add instalment
    let totalPaid' ← payment.totalPaid.operator_add due .to_nearest
    let payment' : UnsettledPayment α := { payment with
      loan := loan', amounts := amounts', totalPaid := totalPaid', count := payment.count + 1 }

    if pc.isFinal then return payment'
    else payment'.payInstalments remaining amount

-- Reverse any impairment before paying
private def Loan.unimpairIfImpaired {α : Type} [AssetPool α] (loan : Loan) (pool : α)
    : Except Error (LoanWithPoolTerResult α) :=
  if loan.isImpaired then loan.manageUnimpair pool else pure (.ok { loan' := loan, pool' := pool })

private def Loan.payScheduledInstalments {α : Type} [AssetPool α] (loan : Loan) (pool : α) (amount : Number)
    (now : UInt32) : Except Error (Except TER (UnsettledPayment α)) := do
  if loan.nextPaymentDueDate == 0 then return .error .tecINTERNAL
  if loan.isPaymentLate now then return .error .tecEXPIRED

  match ← loan.unimpairIfImpaired pool with
  | .error ter => return .error ter
  | .ok ⟨loan, pool⟩ =>
    let emptyPayment : UnsettledPayment α := {
      loan := loan, pool := pool,
      amounts := PaymentAmounts.zero, totalPaid := Number.zero, count := 0 }
    let payment ← emptyPayment.payInstalments maxPaymentsPerTransaction amount
    if payment.count == 0 then
      return .error .tecINSUFFICIENT_PAYMENT   -- amount covered no instalments

    return .ok payment

-- Add the overpayment tail to an unsettled payment.
private def UnsettledPayment.applyOverpayment {α : Type} (payment : UnsettledPayment α) (amount : Number)
    : Except Error (UnsettledPayment α) := do
  let loan := payment.loan
  let nt := loan.broker.numericType

  -- the tail needs budget, remaining payments and room in the per-transaction cap
  if !(loan.allowsOverpayment && loan.paymentRemaining != 0 && payment.totalPaid.operator_lt amount
        && payment.count < maxPaymentsPerTransaction) then return payment

  -- the unspent amount, capped at the outstanding value and rounded down at loan scale
  let unspent ← amount.operator_sub payment.totalPaid .to_nearest
  let cappedUnspent := Number.min unspent loan.totalValueOutstanding
  let overpayment ← STAmount.roundToNumericType nt cappedUnspent .downward (some loan.loanScale)
  if !(overpayment.operator_gt Number.zero) then return payment

  -- split the overpayment into principal, interest, and fees. Drop it if no principal is left
  let opc ← loan.overpaymentComponents overpayment
  if !(opc.principalDelta.operator_gt Number.zero) then return payment

  -- re-amortize the remaining schedule for the reduced principal
  let some reamortization ← loan.tryOverpayment opc
    | return payment   -- a re-amortization guard dropped the overpayment

  -- add the overpayment to the summed amounts and commit the re-amortized loan
  let amounts ← payment.amounts.add reamortization.amounts
  let rawLoan' : RawLoan := { loan.toRawLoan with
    totalValueOutstanding := reamortization.state.valueOutstanding
    principalOutstanding := reamortization.state.principalOutstanding
    managementFeeOutstanding := reamortization.state.managementFeeDue
    periodicPayment := reamortization.periodicPayment }
  let loan' ← rawLoan'.to_lawful

  return { payment with loan := loan', amounts := amounts }

-- LoanPay -> preclaim
def Loan.canPay (loan : Loan) (paymentType : LoanPaymentType) : TER :=
  if loan.isPending then
    .tecNO_PERMISSION
  else if (paymentType matches .overpayment) && !loan.allowsOverpayment then
    .tecNO_PERMISSION
  else if loan.paymentRemaining == 0 || loan.principalOutstanding.operator_eq Number.zero then
    .tecKILLED
  else
    .tesSUCCESS

-- Pay one or more scheduled instalments.
def Loan.regularPayment {α : Type} [AssetPool α] (loan : Loan) (pool : α) (amount : Number)
    (now : UInt32) : Except Error (LoanWithAmountsTerResult α) := do
  match ← loan.payScheduledInstalments pool amount now with
  | .error ter => return .error ter
  | .ok payment => payment.loan.settlePayment payment.pool payment.amounts

-- Pay scheduled instalments, then an overpayment tail that pays down extra principal.
def Loan.overpayment {α : Type} [AssetPool α] (loan : Loan) (pool : α) (amount : Number)
    (now : UInt32) : Except Error (LoanWithAmountsTerResult α) := do
  match ← loan.payScheduledInstalments pool amount now with
  | .error ter => return .error ter
  | .ok payment =>
    let payment ← payment.applyOverpayment amount
    payment.loan.settlePayment payment.pool payment.amounts

-- Pay a late instalment: the scheduled amount plus penalty interest for the overdue seconds and the fixed late fee.
def Loan.latePayment {α : Type} [AssetPool α] (loan : Loan) (pool : α) (amount : Number)
    (now : UInt32) : Except Error (LoanWithAmountsTerResult α) := do
  if loan.nextPaymentDueDate == 0 then return .error .tecINTERNAL
  if !(loan.isPaymentLate now) then return .error .tecTOO_SOON

  match ← loan.unimpairIfImpaired pool with
  | .error ter => return .error ter
  | .ok ⟨loan, pool⟩ =>
    let pc ← loan.lateComponents now
    loan.paySingleInstalment pool pc amount

-- Pay off the loan early: clear the whole outstanding value plus early-payoff interest and the close fee
def Loan.fullPayment {α : Type} [AssetPool α] (loan : Loan) (pool : α) (amount : Number)
    (now : UInt32) : Except Error (LoanWithAmountsTerResult α) := do
  if loan.nextPaymentDueDate == 0 then return .error .tecINTERNAL
  if loan.isPaymentLate now then return .error .tecEXPIRED
  -- the last instalment must be a regular payment
  if loan.paymentRemaining ≤ 1 then return .error .tecKILLED

  match ← loan.unimpairIfImpaired pool with
  | .error ter => return .error ter
  | .ok ⟨loan, pool⟩ =>
    let pc ← loan.fullComponents now
    loan.paySingleInstalment pool pc amount

end XRPL.Model.Lending
