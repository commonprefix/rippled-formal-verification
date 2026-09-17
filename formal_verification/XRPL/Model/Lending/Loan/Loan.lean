import XRPL.Model.Protocol.Number
import XRPL.Model.Protocol.NumericType
import XRPL.Model.Protocol.STAmount
import XRPL.Model.Protocol.TER
import XRPL.Model.Protocol.TenthBips
import XRPL.Model.Lending.Interest
import XRPL.Model.Lending.Loan.LoanState
import XRPL.Model.Lending.LoanBroker.LoanBroker

namespace XRPL.Model.Lending

open XRPL.Model.Protocol

def defaultPaymentTotal : UInt32 := 1      -- payments count
def defaultPaymentInterval : UInt32 := 60  -- seconds
def defaultGracePeriod : UInt32 := 60      -- seconds

-- The most scheduled instalments for one LoanPay transaction
def maxPaymentsPerTransaction : Nat := 100

-- UInt32 max (2³² − 1)
def maxTime : UInt32 := 4_294_967_295

def hasExpired (ledgerCloseTime expTime : UInt32) (exclusive : Bool := false) : Bool :=
  if exclusive then ledgerCloseTime > expTime else ledgerCloseTime ≥ expTime

-- 1/10 bips: 0.1 bp = 0.001% = 0.00001
structure LoanRates where
  interestRate : TenthBips32
  lateInterestRate : TenthBips32
  closeInterestRate : TenthBips32
  overpaymentInterestRate : TenthBips32
  overpaymentFee : TenthBips32

-- fixed fee amounts
structure LoanFees where
  originationFee : Number
  serviceFee : Number
  latePaymentFee : Number
  closePaymentFee : Number

-- fee amounts (C++ getValueFields, with principalRequested prepended)
def LoanFees.amountFields (fees : LoanFees) : List Number :=
  [fees.originationFee, fees.serviceFee, fees.latePaymentFee, fees.closePaymentFee]

structure LoanSchedule where
  paymentInterval : UInt32
  paymentTotal : UInt32
  gracePeriod : UInt32
  startDate : UInt32

-- build the schedule, filling defaults
def LoanSchedule.build (paymentInterval paymentTotal gracePeriod : Option UInt32)
    (startDate ledgerCloseTime : UInt32) (twoStep : Bool) : LoanSchedule :=
  { paymentInterval := paymentInterval.getD defaultPaymentInterval
    paymentTotal := paymentTotal.getD defaultPaymentTotal
    gracePeriod := gracePeriod.getD defaultGracePeriod
    -- C++ getStartDate: two-step keeps the provided StartDate, one-step uses ledgerCloseTime
    startDate := if twoStep then startDate else ledgerCloseTime }

def LoanSchedule.checkTimeAvailability (schedule : LoanSchedule) : TER :=
  let timeAvailable := maxTime - schedule.startDate
  if schedule.gracePeriod > timeAvailable
      || schedule.paymentInterval > timeAvailable
      || schedule.paymentTotal > timeAvailable  -- double check as paymentTotal is count, not seconds?
      || (timeAvailable - schedule.gracePeriod) / schedule.paymentInterval < schedule.paymentTotal then
    .tecKILLED
  else
    .tesSUCCESS

structure RawLoan where
  broker : LoanBroker
  rates : LoanRates
  fees : LoanFees
  schedule : LoanSchedule
  -- accounting
  paymentRemaining : UInt32
  periodicPayment : Number
  principalOutstanding : Number
  totalValueOutstanding : Number
  managementFeeOutstanding : Number
  loanScale : Int
  -- due dates in seconds
  previousPaymentDueDate : UInt32
  nextPaymentDueDate : UInt32
  -- modeled from the flags
  isPending : Bool
  isImpaired : Bool
  isDefault : Bool
  allowsOverpayment : Bool

def RawLoan.interestDue (rl : RawLoan) : Except Error Number := do
  let totalValueOutstanding' ← rl.totalValueOutstanding.operator_sub rl.principalOutstanding .to_nearest
  totalValueOutstanding'.operator_sub rl.managementFeeOutstanding .to_nearest

-- matching C++ `Number{-1, loanScale}` tolerance
def RawLoan.interestTolerance (rl : RawLoan) : Except Error Number :=
  if rl.broker.numericType.isIntegral then .ok Number.zero
  else Number.from_rep (-1 : Int64) rl.loanScale largeRange.min largeRange.max .to_nearest

def RawLoan.interestWithinTolerance (rl : RawLoan) : Bool :=
  match rl.interestDue, rl.interestTolerance with
  | .ok i, .ok tol => tol.operator_le i
  | _, _ => false

structure RawLoan.WF (rl : RawLoan) : Prop where
  periodicPayment_norm : rl.periodicPayment.isNormalized
  principalOutstanding_norm : rl.principalOutstanding.isNormalized
  totalValueOutstanding_norm : rl.totalValueOutstanding.isNormalized
  managementFeeOutstanding_norm : rl.managementFeeOutstanding.isNormalized
  originationFee_norm : rl.fees.originationFee.isNormalized
  serviceFee_norm : rl.fees.serviceFee.isNormalized
  latePaymentFee_norm : rl.fees.latePaymentFee.isNormalized
  closePaymentFee_norm : rl.fees.closePaymentFee.isNormalized

structure RawLoan.Valid (rl : RawLoan) : Prop where
  -- fully paid off exactly when no payments remain
  paid_zeroed : rl.paymentRemaining = 0 →
    rl.totalValueOutstanding = Number.zero ∧ rl.principalOutstanding = Number.zero ∧
      rl.managementFeeOutstanding = Number.zero
  unpaid_nonzero : rl.paymentRemaining ≠ 0 →
    rl.totalValueOutstanding ≠ Number.zero ∨ rl.principalOutstanding ≠ Number.zero ∨
      rl.managementFeeOutstanding ≠ Number.zero
  -- amounts never negative
  principalOutstanding_nonneg : Number.zero.operator_le rl.principalOutstanding = true
  totalValueOutstanding_nonneg : Number.zero.operator_le rl.totalValueOutstanding = true
  managementFeeOutstanding_nonneg : Number.zero.operator_le rl.managementFeeOutstanding = true
  serviceFee_nonneg : Number.zero.operator_le rl.fees.serviceFee = true
  latePaymentFee_nonneg : Number.zero.operator_le rl.fees.latePaymentFee = true
  closePaymentFee_nonneg : Number.zero.operator_le rl.fees.closePaymentFee = true
  -- the periodic payment is strictly positive
  periodicPayment_pos : Number.zero.operator_lt rl.periodicPayment = true
  -- a fully paid loan carries no next due date
  paid_no_due_date : rl.paymentRemaining = 0 → rl.nextPaymentDueDate = 0
  -- interest due stays non-negative within the loan-scale tolerance
  interest_within_tolerance : rl.interestWithinTolerance = true

instance RawLoan.decidableWF (rl : RawLoan) : Decidable rl.WF :=
  decidable_of_iff
    (rl.periodicPayment.isNormalized ∧ rl.principalOutstanding.isNormalized ∧
      rl.totalValueOutstanding.isNormalized ∧ rl.managementFeeOutstanding.isNormalized ∧
      rl.fees.originationFee.isNormalized ∧ rl.fees.serviceFee.isNormalized ∧
      rl.fees.latePaymentFee.isNormalized ∧ rl.fees.closePaymentFee.isNormalized)
    ⟨fun ⟨a, b, c, d, e, f, g, h⟩ => ⟨a, b, c, d, e, f, g, h⟩,
     fun ⟨a, b, c, d, e, f, g, h⟩ => ⟨a, b, c, d, e, f, g, h⟩⟩

instance RawLoan.decidableValid (rl : RawLoan) : Decidable rl.Valid :=
  decidable_of_iff
    ((rl.paymentRemaining = 0 → rl.totalValueOutstanding = Number.zero ∧
        rl.principalOutstanding = Number.zero ∧ rl.managementFeeOutstanding = Number.zero) ∧
      (rl.paymentRemaining ≠ 0 → rl.totalValueOutstanding ≠ Number.zero ∨
        rl.principalOutstanding ≠ Number.zero ∨ rl.managementFeeOutstanding ≠ Number.zero) ∧
      Number.zero.operator_le rl.principalOutstanding = true ∧
      Number.zero.operator_le rl.totalValueOutstanding = true ∧
      Number.zero.operator_le rl.managementFeeOutstanding = true ∧
      Number.zero.operator_le rl.fees.serviceFee = true ∧
      Number.zero.operator_le rl.fees.latePaymentFee = true ∧
      Number.zero.operator_le rl.fees.closePaymentFee = true ∧
      Number.zero.operator_lt rl.periodicPayment = true ∧
      (rl.paymentRemaining = 0 → rl.nextPaymentDueDate = 0) ∧
      rl.interestWithinTolerance = true)
    ⟨fun ⟨a, b, c, d, e, f, g, h, i, j, k⟩ => ⟨a, b, c, d, e, f, g, h, i, j, k⟩,
     fun ⟨a, b, c, d, e, f, g, h, i, j, k⟩ => ⟨a, b, c, d, e, f, g, h, i, j, k⟩⟩

structure Loan extends RawLoan where
  wf : toRawLoan.WF
  valid : toRawLoan.Valid

def RawLoan.to_lawful (rl : RawLoan) : Except Error Loan :=
  if h : rl.WF ∧ rl.Valid then .ok { toRawLoan := rl, wf := h.1, valid := h.2 } else .error .notLawful

-- The loan with the pool it draws on, after an operation that changes both
structure LoanWithPool (α : Type) where
  loan' : Loan
  pool' : α

-- The loan with the amounts a fund-moving operation transfers (zero where nothing moves to that party)
structure LoanWithAmounts (α : Type) extends LoanWithPool α where
  amountToPool : Number
  amountToBroker : Number

abbrev LoanWithPoolTerResult (α : Type) := Except TER (LoanWithPool α)
abbrev LoanWithAmountsTerResult (α : Type) := Except TER (LoanWithAmounts α)

def Loan.periodicRate (loan : Loan) : Except Error Number :=
  loanPeriodicRate loan.rates.interestRate loan.schedule.paymentInterval

def Loan.state (loan : Loan) : Except Error LoanState :=
  LoanState.build loan.totalValueOutstanding loan.principalOutstanding loan.managementFeeOutstanding

def Loan.isPaymentLate (loan : Loan) (now : UInt32) : Bool :=
  loan.nextPaymentDueDate < now

end XRPL.Model.Lending
