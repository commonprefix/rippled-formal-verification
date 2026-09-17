import XRPL.Model.Lending.LoanBroker.LoanBroker

/-! # LoanBroker state validity (exact-rational view) -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol

/-- The loan-broker state in exact arithmetic. -/
structure RawLoanBroker.Exact where
  debtTotal : ℚ
  coverAvailable : ℚ

/-- The exact value of a loan-broker state. -/
def RawLoanBroker.toExact (rb : RawLoanBroker) : RawLoanBroker.Exact where
  debtTotal := rb.debtTotal.toRat
  coverAvailable := rb.coverAvailable.toRat

structure RawLoanBroker.Exact.Valid (s : RawLoanBroker.Exact) : Prop where
  debtTotal_nonneg : 0 ≤ s.debtTotal
  coverAvailable_nonneg : 0 ≤ s.coverAvailable

end XRPL.Model.Lending
