import XRPL.Model.Lending.LoanBroker.LoanBroker
import XRPL.Model.Lending.LoanBroker.BrokerCover

/-! # LoanBroker state validity (exact-rational view) -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol

/-- The loan-broker state in exact arithmetic. -/
structure RawLoanBroker.Exact where
  debtTotal : ℚ
  debtMaximum : ℚ
  coverAvailable : ℚ
  loanCount : ℕ
  managementFeeRate : ℕ
  coverRateMinimum : ℕ
  coverRateLiquidation : ℕ

/-- The exact value of a loan-broker state. -/
def RawLoanBroker.toExact (rb : RawLoanBroker) : RawLoanBroker.Exact where
  debtTotal := rb.debtTotal.toRat
  debtMaximum := rb.debtMaximum.toRat
  coverAvailable := rb.coverAvailable.toRat
  loanCount := rb.loanCount.toNat
  managementFeeRate := rb.managementFeeRate.toNat
  coverRateMinimum := rb.coverRateMinimum.toNat
  coverRateLiquidation := rb.coverRateLiquidation.toNat

structure RawLoanBroker.Exact.Valid (s : RawLoanBroker.Exact) : Prop where
  debtTotal_nonneg : 0 ≤ s.debtTotal
  coverAvailable_nonneg : 0 ≤ s.coverAvailable
  debt_within_cap : s.debtMaximum ≠ 0 → s.debtTotal ≤ s.debtMaximum
  empty_broker : s.loanCount = 0 → s.debtTotal = 0
  debtMaximum_nonneg : 0 ≤ s.debtMaximum
  debtMaximum_cap : s.debtMaximum ≤ (2 : ℚ) ^ 63 - 1
  managementFeeRate_cap : s.managementFeeRate ≤ maxManagementFeeRate.toNat
  coverRateMinimum_cap : s.coverRateMinimum ≤ maxCoverRate.toNat
  coverRateLiquidation_cap : s.coverRateLiquidation ≤ maxCoverRate.toNat
  coverRates_coupled : s.coverRateMinimum = 0 ↔ s.coverRateLiquidation = 0

/-- The cover floor of XLS-66: the broker's first-loss cover is at least the minimum its debt
requires, at the pool's scale. -/
def LoanBroker.HasMinimumCover (lb : LoanBroker) (poolExponent : Int) : Prop :=
  lb.hasMinimumCover poolExponent = .ok true

end XRPL.Model.Lending
