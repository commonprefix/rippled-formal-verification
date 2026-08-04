import XRPL.Model.Protocol.Number

namespace XRPL.Model.Lending

open XRPL.Model.Protocol

structure Loan where
  -- all rates in 1/10 bips
  interestRate : UInt32
  lateInterestRate : UInt32
  closeInterestRate : UInt32
  overpaymentInterestRate : UInt32
  overpaymentFee : UInt32
  -- fixed fee amounts
  loanOriginationFee : Number
  loanServiceFee : Number
  latePaymentFee : Number
  closePaymentFee : Number
  -- accounting
  paymentRemaining : UInt32
  periodicPayment : Number
  principalOutstanding : Number
  totalValueOutstanding : Number
  managementFeeOutstanding : Number
  loanScale : Int32
  -- payment schedule in seconds
  startDate : UInt32
  paymentInterval : UInt32
  gracePeriod : UInt32
  previousPaymentDueDate : UInt32
  nextPaymentDueDate : UInt32
  -- modeled from the flags
  isPending : Bool
  isImpaired : Bool
  isDefault : Bool
  allowsOverpayment : Bool

def Loan.isPaidOff (loan : Loan) : Bool :=
  loan.paymentRemaining == 0

end XRPL.Model.Lending
