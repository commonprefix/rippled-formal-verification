import XRPL.Model.Protocol.Number
import XRPL.Model.Protocol.NumericType
import XRPL.Model.Protocol.Rounding
import XRPL.Model.Protocol.STAmount
import XRPL.Model.Protocol.TenthBips
import XRPL.Model.Vault.Vault
import XRPL.Model.Lending.Amortization
import XRPL.Model.Lending.CashBasis
import XRPL.Model.Lending.Interest
import XRPL.Model.Lending.Loan.Loan
import XRPL.Model.Lending.Loan.LoanResult
import XRPL.Model.Lending.Loan.LoanSet
import XRPL.Model.Lending.Loan.LoanState
import XRPL.Model.Lending.LoanBroker.LoanBroker

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault

-- The kind of payment a LoanPay transaction requests
inductive LoanPaymentType where
  | regular | late | full | overpayment
  deriving DecidableEq, Repr

-- The loan re-amortized after an overpayment, with the amounts the overpayment changes
structure Reamortization where
  amounts : PaymentAmounts
  state : LoanState
  periodicPayment : Number

-- Round the interest, then split it into the net interest and the management fee on it.
private def roundAndSplitInterest (interest : Number) (mgmtRate : TenthBips16) (mode : rounding_mode)
    (nt : NumericType) (scale : Int) : Except Error (Number × Number) := do
  let interest' ← STAmount.roundToNumericType nt interest mode (some scale)
  let managementFee ← computeManagementFee nt interest' mgmtRate scale
  let netInterest ← interest'.operator_sub managementFee .to_nearest
  return (netInterest, managementFee)

-- The deltas of the next scheduled instalment, regular or final
private def Loan.scheduledComponents (loan : Loan) (nt : NumericType) (mgmtRate : TenthBips16)
    : Except Error PaymentComponents := do
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
private def Loan.lateComponents (loan : Loan) (nt : NumericType) (mgmtRate : TenthBips16) (now : UInt32)
    : Except Error PaymentComponents := do
  let pc ← loan.scheduledComponents nt mgmtRate

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
private def Loan.fullComponents (loan : Loan) (nt : NumericType) (mgmtRate : TenthBips16) (now : UInt32)
    : Except Error PaymentComponents := do
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
private def computeOverpaymentComponents (overpayment : Number)
    (overRate overFeeRate : TenthBips32) (mgmtRate : TenthBips16)
    (nt : NumericType) (scale : Int) : Except Error PaymentComponents := do
  let overpaymentFee ← tenthBipsOfValue overpayment overFeeRate .to_nearest
  let overpaymentFee' ← STAmount.roundToNumericType nt overpaymentFee .to_nearest (some scale)
  let valueDelta ← overpayment.operator_sub overpaymentFee' .to_nearest

  -- the interest, split into net interest and its management fee
  let overpaymentInterest ← tenthBipsOfValue overpayment overRate .to_nearest
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

-- Re-amortize the remaining schedule after an overpayment. `none` when a guard drops the overpayment.
private def processOverpayment (opc : PaymentComponents) (state : LoanState)
    (periodicPayment periodicRate : Number) (paymentRemaining : UInt32) (mgmtRate : TenthBips16)
    (nt : NumericType) (scale : Int) : Except Error (Option Reamortization) := do
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
  let newProperties : LoanProperties := { reamortizedProps with
    totalValueOutstanding := tvo'
    principalOutstanding := po
    managementFeeOutstanding := mfo
    loanScale := scale }
  let guardTer ← newProperties.amortizationGuards po
    (interestOut.operator_ne Number.zero) paymentRemaining nt
  if !guardTer.isTesSuccess then return none

  if state.principalOutstanding.operator_le po then return none
  if deltas.interest.operator_neg.operator_gt Number.zero then return none

  let feePaid ← opc.managementFeeDelta.operator_add opc.untrackedManagementFee .to_nearest
  return some {
    amounts := { principalPaid := deltas.principal, interestPaid := opc.untrackedInterest, feePaid := feePaid }
    state := state'
    periodicPayment := reamortizedProps.periodicPayment
  }

-- Re-check the vault after a payment, matching the doApply checks once amounts are rounded
private def validatePostPayment (vault : Vault) (s : LendingState) (assetsTotalDelta : Number)
    : LoanResult LendingState :=
  let vault' := s.vault
  let assetsAvailableChanged := vault'.assetsAvailable.operator_ne vault.assetsAvailable
  let assetsTotalChanged := vault'.assetsTotal.operator_ne vault.assetsTotal
  let expectedChange := assetsTotalDelta.operator_ne Number.zero

  if !assetsAvailableChanged then .rejected .tecPRECISION_LOSS
  else if expectedChange && !assetsTotalChanged then .rejected .tecPRECISION_LOSS
  else if !expectedChange && assetsTotalChanged then .rejected .tecINTERNAL
  else if vault'.assetsAvailable.operator_gt vault'.assetsTotal then .rejected .tecINTERNAL
  else .ok s

-- Apply one instalment to the vault and broker, then advance the loan
private def Loan.doPayment (loan : Loan) (vault : Vault) (broker : LoanBroker) (pc : PaymentComponents)
    : Except Error (LendingState × Number) := do
  let interestDelta ← pc.interestDelta
  let interestPaid ← interestDelta.operator_add pc.untrackedInterest .to_nearest
  let feePaid ← pc.managementFeeDelta.operator_add pc.untrackedManagementFee .to_nearest
  let amounts : PaymentAmounts :=
    { principalPaid := pc.principalDelta, interestPaid := interestPaid, feePaid := feePaid }
  let vb ← CashBasis.applyPayment vault broker amounts

  if pc.isFinal then
    let loan' := { loan with
      totalValueOutstanding := Number.zero, principalOutstanding := Number.zero,
      managementFeeOutstanding := Number.zero, paymentRemaining := 0,
      previousPaymentDueDate := loan.nextPaymentDueDate, nextPaymentDueDate := 0 }
    return ({ vault := vb.vault, broker := vb.broker, loan := loan' }, interestPaid)

  let loan' := { loan with
    totalValueOutstanding := ← loan.totalValueOutstanding.operator_sub pc.totalValueDelta .to_nearest
    principalOutstanding := ← loan.principalOutstanding.operator_sub pc.principalDelta .to_nearest
    managementFeeOutstanding := ← loan.managementFeeOutstanding.operator_sub pc.managementFeeDelta .to_nearest
    paymentRemaining := loan.paymentRemaining - 1
    previousPaymentDueDate := loan.nextPaymentDueDate
    nextPaymentDueDate := loan.nextPaymentDueDate + loan.schedule.paymentInterval }

  return ({ vault := vb.vault, broker := vb.broker, loan := loan' }, interestPaid)

-- Settle one instalment if the amount covers it, then re-check the vault
private def Loan.paySingleInstalment (loan : Loan) (vault : Vault) (broker : LoanBroker)
    (pc : PaymentComponents) (amount : Number) : Except Error (LoanResult LendingState) := do
  if amount.operator_lt (← pc.totalDue) then return .rejected .tecINSUFFICIENT_PAYMENT
  let (s, assetsTotalDelta) ← loan.doPayment vault broker pc
  return validatePostPayment vault s assetsTotalDelta

-- Pay scheduled instalments one at a time while the amount covers the next due and the loan is unpaid, up to 100.
private def payScheduledInstalments (instalmentsLeft : Nat) (amount serviceFee : Number) (nt : NumericType)
    (mgmtRate : TenthBips16) (loan : Loan) (vault : Vault) (broker : LoanBroker)
    (totalPaid assetsTotalDelta : Number) (count : Nat)
    : Except Error (LendingState × Number × Number × Nat) := do
  let accumulated := (({ vault, broker, loan } : LendingState), totalPaid, assetsTotalDelta, count)

  match instalmentsLeft with
  | 0 => return accumulated
  | remaining + 1 =>
    if loan.paymentRemaining == 0 then return accumulated

    -- compute the next scheduled instalment and its amount due
    let pc ← loan.scheduledComponents nt mgmtRate
    let pc' : PaymentComponents := { pc with untrackedManagementFee := serviceFee }
    let due ← pc'.totalDue

    -- stop when the remaining amount cannot cover the next instalment
    if amount.operator_lt (← totalPaid.operator_add due .to_nearest) then return accumulated

    -- apply the instalment and update the running totals
    let (s, interestPaid) ← loan.doPayment vault broker pc'
    let totalPaid ← totalPaid.operator_add due .to_nearest
    let assetsTotalDelta ← assetsTotalDelta.operator_add interestPaid .to_nearest

    if pc.isFinal then
      return (s, totalPaid, assetsTotalDelta, count + 1)
    else
      payScheduledInstalments remaining amount serviceFee nt mgmtRate
        s.loan s.vault s.broker totalPaid assetsTotalDelta (count + 1)

-- Pay as many scheduled instalments as the amount covers, then apply any overpayment tail
private def Loan.payInstalmentsAndOverpayment (loan : Loan) (vault : Vault) (broker : LoanBroker)
    (paymentType : LoanPaymentType) (amount : Number) : Except Error (LoanResult (LendingState × Number)) := do
  let nt := vault.numericType
  let mgmtRate := broker.managementFeeRate
  let (s, totalPaid, assetsTotalDelta, count) ← payScheduledInstalments maxPaymentsPerTransaction
    amount loan.fees.serviceFee nt mgmtRate loan vault broker Number.zero Number.zero 0
  if count == 0 then return .rejected .tecINSUFFICIENT_PAYMENT   -- amount covered no instalments

  let ⟨vault, broker, loan⟩ := s
  let instalmentsResult : LoanResult (LendingState × Number) := .ok (s, assetsTotalDelta)

  -- the overpayment tail applies only to an overpayment transaction with remaining budget and payments
  let applyOverpayment := paymentType matches .overpayment
    && loan.allowsOverpayment && loan.paymentRemaining != 0 && totalPaid.operator_lt amount
  if !applyOverpayment then return instalmentsResult

  -- the unspent amount, capped at the outstanding value and rounded down at loan scale
  let unspent ← amount.operator_sub totalPaid .to_nearest
  let cappedUnspent := Number.min unspent loan.totalValueOutstanding
  let overpayment ← STAmount.roundToNumericType nt cappedUnspent .downward (some loan.loanScale)
  if !(overpayment.operator_gt Number.zero) then return instalmentsResult   -- the overpayment rounded to zero

  -- split the overpayment into principal, interest, and fees
  let opc ← computeOverpaymentComponents overpayment loan.rates.overpaymentInterestRate
    loan.rates.overpaymentFee mgmtRate nt loan.loanScale
  if !(opc.principalDelta.operator_gt Number.zero) then
    return instalmentsResult   -- no principal left after fees and interest

  -- re-amortize the remaining schedule for the reduced principal
  let periodicRate ← loan.periodicRate
  let oldState ← loan.state
  let some reamortization ← processOverpayment opc oldState loan.periodicPayment periodicRate
      loan.paymentRemaining mgmtRate nt loan.loanScale
    | return instalmentsResult   -- a re-amortization guard rejected the overpayment

  -- apply the overpayment to the vault and broker, then commit the re-amortized loan
  let vb ← CashBasis.applyPayment vault broker reamortization.amounts
  let loan' := { loan with
    totalValueOutstanding := reamortization.state.valueOutstanding
    principalOutstanding := reamortization.state.principalOutstanding
    managementFeeOutstanding := reamortization.state.managementFeeDue
    periodicPayment := reamortization.periodicPayment }
  let assetsTotalDelta ← assetsTotalDelta.operator_add reamortization.amounts.interestPaid .to_nearest

  return .ok ({ vault := vb.vault, broker := vb.broker, loan := loan' }, assetsTotalDelta)

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

-- Pay a regular (or overpayment) instalment.
def Loan.regularPayment (loan : Loan) (vault : Vault) (broker : LoanBroker) (paymentType : LoanPaymentType)
    (amount : Number) (now : UInt32) : Except Error (LoanResult LendingState) := do
  if loan.nextPaymentDueDate == 0 then return .rejected .tecINTERNAL
  if loan.isPaymentLate now then return .rejected .tecEXPIRED

  match ← loan.payInstalmentsAndOverpayment vault broker paymentType amount with
  | .rejected ter => return .rejected ter
  | .ok (s, assetsTotalDelta) => return validatePostPayment vault s assetsTotalDelta

-- Pay a late instalment: scheduled amount + penalty interest for the overdue seconds + fixed late fee.
def Loan.latePayment (loan : Loan) (vault : Vault) (broker : LoanBroker) (amount : Number) (now : UInt32)
    : Except Error (LoanResult LendingState) := do
  if loan.nextPaymentDueDate == 0 then return .rejected .tecINTERNAL
  if !(loan.isPaymentLate now) then return .rejected .tecTOO_SOON

  let pc ← loan.lateComponents vault.numericType broker.managementFeeRate now
  loan.paySingleInstalment vault broker pc amount

-- Pay off the loan early: clear the whole outstanding value + early-payoff interest + close fee, then close it.
def Loan.fullPayment (loan : Loan) (vault : Vault) (broker : LoanBroker) (amount : Number) (now : UInt32)
    : Except Error (LoanResult LendingState) := do
  if loan.nextPaymentDueDate == 0 then return .rejected .tecINTERNAL
  if loan.isPaymentLate now then return .rejected .tecEXPIRED
  if loan.paymentRemaining ≤ 1 then return .rejected .tecKILLED   -- the last instalment must be a regular payment

  let pc ← loan.fullComponents vault.numericType broker.managementFeeRate now
  loan.paySingleInstalment vault broker pc amount

end XRPL.Model.Lending
