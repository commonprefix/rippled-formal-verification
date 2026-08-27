import XRPL.Model.Lending.LoanBroker
import XRPL.Model.Protocol.TenthBips

/-! # Loan broker state validity

`WF` checks the stored `Number` fields are normalized. `Exact.Valid` states
the invariant in exact rationals. `Valid` states the same invariant with the `Number`
operators the code compares with. A `Lawful` state is both well-formed and valid. -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol

/-- The broker state in exact arithmetic. -/
structure LoanBroker.Exact where
  debtTotal : ℚ
  debtMaximum : ℚ
  coverAvailable : ℚ
  managementFeeRate : ℕ
  coverRateMinimum : ℕ
  coverRateLiquidation : ℕ
  loanCount : ℕ

/-- The exact value of a broker state. -/
def LoanBroker.toExact (lb : LoanBroker) : LoanBroker.Exact where
  debtTotal := lb.debtTotal.toRat
  debtMaximum := lb.debtMaximum.toRat
  coverAvailable := lb.coverAvailable.toRat
  managementFeeRate := lb.managementFeeRate.toNat
  coverRateMinimum := lb.coverRateMinimum.toNat
  coverRateLiquidation := lb.coverRateLiquidation.toNat
  loanCount := lb.loanCount.toNat

/-- Representation well-formed: every stored amount is a normalized `Number`.
The rates and loan count are integers, so they need no extra clause. -/
structure LoanBroker.WF (lb : LoanBroker) : Prop where
  debtTotal_norm : lb.debtTotal.isNormalized
  debtMaximum_norm : lb.debtMaximum.isNormalized
  coverAvailable_norm : lb.coverAvailable.isNormalized

/-- The broker invariant in exact arithmetic. -/
structure LoanBroker.Exact.Valid (s : LoanBroker.Exact) : Prop where
  debtTotal_nonneg : 0 ≤ s.debtTotal
  debtMaximum_nonneg : 0 ≤ s.debtMaximum
  coverAvailable_nonneg : 0 ≤ s.coverAvailable
  debtMaximum_cap : s.debtMaximum ≤ (2 : ℚ) ^ 63 - 1
  debt_within_cap : s.debtMaximum ≠ 0 → s.debtTotal ≤ s.debtMaximum
  cover_floor : s.debtTotal * (s.coverRateMinimum : ℚ) ≤ 100000 * s.coverAvailable
  empty_broker : s.loanCount = 0 → s.debtTotal = 0
  mgmtFee_cap : s.managementFeeRate ≤ maxManagementFeeRate
  coverMin_cap : s.coverRateMinimum ≤ maxCoverRate
  coverLiq_cap : s.coverRateLiquidation ≤ maxCoverRate
  rate_coupling : s.coverRateMinimum = 0 ↔ s.coverRateLiquidation = 0

/-- `LoanBroker.Exact.Valid`, restated with the modeled `Number` operators on the
stored fields. -/
structure LoanBroker.Valid (lb : LoanBroker) : Prop where
  debtTotal_nonneg : Number.zero.operator_le lb.debtTotal = true
  debtMaximum_nonneg : Number.zero.operator_le lb.debtMaximum = true
  coverAvailable_nonneg : Number.zero.operator_le lb.coverAvailable = true
  debtMaximum_cap : lb.debtMaximum.operator_le debtMaxCap = true
  debt_within_cap : lb.debtMaximum ≠ Number.zero →
    lb.debtTotal.operator_le lb.debtMaximum = true
  cover_floor : ∀ lhs rhs,
    lb.debtTotal.operator_mul lb.coverRateMinimum.toNumber .upward = .ok lhs →
    lb.coverAvailable.operator_mul kTenthBipsPerUnity.toNumber .to_nearest = .ok rhs →
    lhs.operator_le rhs = true
  empty_broker : lb.loanCount = 0 → lb.debtTotal = Number.zero
  mgmtFee_cap : lb.managementFeeRate.toNat ≤ maxManagementFeeRate
  coverMin_cap : lb.coverRateMinimum.toNat ≤ maxCoverRate
  coverLiq_cap : lb.coverRateLiquidation.toNat ≤ maxCoverRate
  rate_coupling : lb.coverRateMinimum.toNat = 0 ↔ lb.coverRateLiquidation.toNat = 0

/-- A lawful broker is a well-formed representation whose exact value satisfies
the invariant. -/
structure LoanBroker.Lawful (lb : LoanBroker) : Prop where
  wf : lb.WF
  valid : lb.toExact.Valid

/-- A broker bundled with its lawfulness proof. -/
def LawfulLoanBroker : Type := {lb : LoanBroker // lb.Lawful}

/-- Raw broker of a lawful broker. -/
def LawfulLoanBroker.val (lb : LawfulLoanBroker) : LoanBroker := Subtype.val lb

/-- Lawfulness proof of a lawful broker. -/
def LawfulLoanBroker.lawful (lb : LawfulLoanBroker) : lb.val.Lawful := Subtype.property lb

/-- The untrusted-boundary check: promote a raw broker to a `LawfulLoanBroker` if it
is lawful. TODO: derive the `Decidable` instance so this is usable without
`Classical`. -/
def LoanBroker.validate (lb : LoanBroker) [Decidable lb.Lawful] : Option LawfulLoanBroker :=
  if h : lb.Lawful then some ⟨lb, h⟩ else none

end XRPL.Model.Lending
