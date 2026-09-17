import XRPL.Model.Lending.Loan.Loan

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
  serviceFee : ℚ
  latePaymentFee : ℚ
  closePaymentFee : ℚ

/-- The exact value of a loan state. -/
def RawLoan.toExact (rl : RawLoan) : RawLoan.Exact where
  paymentRemaining := rl.paymentRemaining
  periodicPayment := rl.periodicPayment.toRat
  principalOutstanding := rl.principalOutstanding.toRat
  totalValueOutstanding := rl.totalValueOutstanding.toRat
  managementFeeOutstanding := rl.managementFeeOutstanding.toRat
  loanScale := rl.loanScale
  numericType := rl.broker.vault.numericType
  nextPaymentDueDate := rl.nextPaymentDueDate
  serviceFee := rl.fees.serviceFee.toRat
  latePaymentFee := rl.fees.latePaymentFee.toRat
  closePaymentFee := rl.fees.closePaymentFee.toRat

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

end XRPL.Model.Lending
