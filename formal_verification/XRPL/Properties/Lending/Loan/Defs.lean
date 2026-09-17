import XRPL.Model.Lending.Loan.Loan
import XRPL.Properties.Protocol.Number.AtExponent

/-! # Loan state validity (exact-rational view) -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol

/-- The loan state in exact arithmetic. -/
structure RawLoan.Exact where
  paymentRemaining : UInt32
  periodicPayment : ℚ
  principalOutstanding : ℚ
  totalValueOutstanding : ℚ
  managementFeeOutstanding : ℚ
  loanScale : Int
  numericType : NumericType
  nextPaymentDueDate : UInt32
  originationFee : ℚ
  serviceFee : ℚ
  latePaymentFee : ℚ
  closePaymentFee : ℚ
  interestRate : ℕ
  lateInterestRate : ℕ
  closeInterestRate : ℕ
  overpaymentInterestRate : ℕ
  overpaymentFee : ℕ
  paymentInterval : UInt32
  paymentTotal : UInt32
  gracePeriod : UInt32
  startDate : UInt32
  previousPaymentDueDate : UInt32

/-- The exact value of a loan state. -/
def RawLoan.toExact (rl : RawLoan) : RawLoan.Exact where
  paymentRemaining := rl.paymentRemaining
  periodicPayment := rl.periodicPayment.toRat
  principalOutstanding := rl.principalOutstanding.toRat
  totalValueOutstanding := rl.totalValueOutstanding.toRat
  managementFeeOutstanding := rl.managementFeeOutstanding.toRat
  loanScale := rl.loanScale
  numericType := rl.broker.numericType
  nextPaymentDueDate := rl.nextPaymentDueDate
  originationFee := rl.fees.originationFee.toRat
  serviceFee := rl.fees.serviceFee.toRat
  latePaymentFee := rl.fees.latePaymentFee.toRat
  closePaymentFee := rl.fees.closePaymentFee.toRat
  interestRate := rl.rates.interestRate.toNat
  lateInterestRate := rl.rates.lateInterestRate.toNat
  closeInterestRate := rl.rates.closeInterestRate.toNat
  overpaymentInterestRate := rl.rates.overpaymentInterestRate.toNat
  overpaymentFee := rl.rates.overpaymentFee.toNat
  paymentInterval := rl.schedule.paymentInterval
  paymentTotal := rl.schedule.paymentTotal
  gracePeriod := rl.schedule.gracePeriod
  startDate := rl.schedule.startDate
  previousPaymentDueDate := rl.previousPaymentDueDate

def RawLoan.Exact.interestDue (s : RawLoan.Exact) : ℚ :=
  s.totalValueOutstanding - s.principalOutstanding - s.managementFeeOutstanding

def RawLoan.Exact.interestTolerance (s : RawLoan.Exact) : ℚ :=
  if s.numericType.isIntegral then 0 else -((10 : ℚ) ^ s.loanScale)

structure RawLoan.Exact.Valid (s : RawLoan.Exact) : Prop where
  paid_zeroed : s.paymentRemaining = 0 →
    s.totalValueOutstanding = 0 ∧ s.principalOutstanding = 0 ∧ s.managementFeeOutstanding = 0
  unpaid_nonzero : s.paymentRemaining ≠ 0 →
    s.totalValueOutstanding ≠ 0 ∨ s.principalOutstanding ≠ 0 ∨ s.managementFeeOutstanding ≠ 0
  principalOutstanding_nonneg : 0 ≤ s.principalOutstanding
  totalValueOutstanding_nonneg : 0 ≤ s.totalValueOutstanding
  managementFeeOutstanding_nonneg : 0 ≤ s.managementFeeOutstanding
  serviceFee_nonneg : 0 ≤ s.serviceFee
  latePaymentFee_nonneg : 0 ≤ s.latePaymentFee
  closePaymentFee_nonneg : 0 ≤ s.closePaymentFee
  periodicPayment_pos : 0 < s.periodicPayment
  paid_no_due_date : s.paymentRemaining = 0 → s.nextPaymentDueDate = 0
  interest_within_tolerance : s.interestTolerance ≤ s.interestDue
  interestRate_cap : s.interestRate ≤ maxLoanRate.toNat
  lateInterestRate_cap : s.lateInterestRate ≤ maxLoanRate.toNat
  closeInterestRate_cap : s.closeInterestRate ≤ maxLoanRate.toNat
  overpaymentInterestRate_cap : s.overpaymentInterestRate ≤ maxLoanRate.toNat
  overpaymentFee_cap : s.overpaymentFee ≤ maxLoanRate.toNat
  originationFee_nonneg : 0 ≤ s.originationFee
  paymentTotal_pos : 0 < s.paymentTotal
  paymentInterval_min : minPaymentInterval ≤ s.paymentInterval
  gracePeriod_range : defaultGracePeriod ≤ s.gracePeriod ∧ s.gracePeriod ≤ s.paymentInterval
  loanScale_range : cMinOffset ≤ s.loanScale ∧ s.loanScale ≤ cMaxOffset
  paymentRemaining_le : s.paymentRemaining ≤ s.paymentTotal
  dueDates_ordered : s.paymentRemaining ≠ 0 → s.previousPaymentDueDate < s.nextPaymentDueDate
  nextPaymentDueDate_on_schedule : s.paymentRemaining ≠ 0 →
    s.startDate ≤ s.nextPaymentDueDate ∧ (s.nextPaymentDueDate - s.startDate) % s.paymentInterval = 0
  totalValueOutstanding_atExponent :
    Number.AtExponent s.totalValueOutstanding s.loanScale s.numericType.mantissaBound
  principalOutstanding_atExponent : Number.AtExponent s.principalOutstanding s.loanScale s.numericType.mantissaBound
  managementFeeOutstanding_atExponent :
    Number.AtExponent s.managementFeeOutstanding s.loanScale s.numericType.mantissaBound

end XRPL.Model.Lending
