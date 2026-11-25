import XRPL.Properties.Lending.Loan.Defs
import XRPL.Properties.Protocol.Number.Compare.Compare
import XRPL.Properties.Protocol.Number.Common.Constants
import XRPL.Properties.Protocol.Number.Common.ToRatLemmas
import XRPL.Properties.Protocol.Number.Constructors.FromRepExact
import XRPL.Properties.Protocol.Number.Sub.RoundsToRepresentable
import XRPL.Properties.Protocol.Number.Sub.ZeroShape
import XRPL.Properties.Protocol.Number.AtExponent
import XRPL.Properties.Protocol.Common.Reduction

/-! # Equivalence of the operator and exact-rational loan invariants -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol

private lemma scale_room (s : Int) (hs : cMinOffset ≤ s ∧ s ≤ cMaxOffset) :
    minExponent + 18 ≤ s ∧ s ≤ maxExponent - 1 := by
  sorry

/-- Forward: a successful twice-rounded interest that clears the tolerance is the exact interest. -/
private lemma interest_exact_of_ok (tvo po mfo t i tol : Number) (s : Int) (bound m1 m2 m3 : ℕ)
    (htn : tvo.isNormalized) (hpn : po.isNormalized) (hmn : mfo.isNormalized) (htoln : tol.isNormalized)
    (hbound : bound ≤ 2 ^ 63) (hm1 : m1 < bound) (hm2 : m2 < bound) (hm3 : m3 < bound)
    (htv : tvo.toRat = (m1 : ℚ) * (10 : ℚ) ^ s) (hpv : po.toRat = (m2 : ℚ) * (10 : ℚ) ^ s)
    (hmv : mfo.toRat = (m3 : ℚ) * (10 : ℚ) ^ s)
    (hs : cMinOffset ≤ s ∧ s ≤ cMaxOffset)
    (htol : tol.toRat = 0 ∨ tol.toRat = -((10 : ℚ) ^ s))
    (h1 : tvo.operator_sub po .to_nearest = .ok t) (h2 : t.operator_sub mfo .to_nearest = .ok i)
    (hle : tol.operator_le i = true) :
    i.toRat = tvo.toRat - po.toRat - mfo.toRat := by
  sorry

/-- Backward: when the exact interest clears the tolerance, both subtractions succeed and are exact. -/
private lemma interest_ok_of_exact (tvo po mfo : Number) (s : Int) (bound m1 m2 m3 : ℕ)
    (htn : tvo.isNormalized) (hpn : po.isNormalized) (hmn : mfo.isNormalized)
    (hbound : bound ≤ 2 ^ 63) (hm1 : m1 < bound) (hm2 : m2 < bound) (hm3 : m3 < bound)
    (htv : tvo.toRat = (m1 : ℚ) * (10 : ℚ) ^ s) (hpv : po.toRat = (m2 : ℚ) * (10 : ℚ) ^ s)
    (hmv : mfo.toRat = (m3 : ℚ) * (10 : ℚ) ^ s)
    (hs : cMinOffset ≤ s ∧ s ≤ cMaxOffset)
    (hexact : -((10 : ℚ) ^ s) ≤ tvo.toRat - po.toRat - mfo.toRat) :
    ∃ t i, tvo.operator_sub po .to_nearest = .ok t ∧ t.operator_sub mfo .to_nearest = .ok i ∧
      i.isNormalized ∧ i.toRat = tvo.toRat - po.toRat - mfo.toRat := by
  sorry

/-- The operator interest clause implies the exact one. -/
private lemma RawLoan.interest_exact_of_valid (rl : RawLoan) (hwf : rl.WF) (hv : rl.Valid) :
    0 ≤ rl.toExact.interestDue := by
  sorry

/-- The exact interest clause implies the operator one. -/
private lemma RawLoan.interest_valid_of_exact (rl : RawLoan) (hwf : rl.WF) (he : rl.toExact.Valid) :
    rl.interestNonneg = true := by
  sorry

/-- For a well-formed representation, the operator invariant (`RawLoan.Valid`) and the exact-rational invariant
coincide. `WF` is required because `operator_le` matches `≤` only on normalized `Number`s. -/
theorem RawLoan.valid_iff_exact (rl : RawLoan) (hwf : rl.WF) :
    rl.Valid ↔ rl.toExact.Valid := by
  sorry

/-- The exact-rational invariant of a lawful loan, derived from its operator proof and
well-formedness. -/
theorem Loan.exact (loan : Loan) : loan.toExact.Valid := by
  sorry

/-- The grid clauses of a well-formed loan, read exactly. The sign of each amount comes from the exact invariant. -/
theorem RawLoan.WF.toExact_grid {rl : RawLoan} (hwf : rl.WF) (he : rl.toExact.Valid) : rl.toExact.Grid := by
  sorry

/-- The grid clauses of a lawful loan, read exactly: whole LoanScale units the asset stores. -/
theorem Loan.grid (loan : Loan) : loan.toExact.Grid := by
  sorry

/-- When the re-validation succeeds, the lawful loan is the raw state it checked, and that state
is well-formed and valid. -/
theorem RawLoan.to_lawful_ok {rl : RawLoan} {loan : Loan}
    (h : rl.to_lawful = .ok loan) : loan.toRawLoan = rl ∧ rl.WF ∧ rl.Valid := by
  sorry

/-- A well-formed, valid raw state passes the re-validation unchanged. -/
theorem RawLoan.to_lawful_ok_of {rl : RawLoan} (hwf : rl.WF) (hvalid : rl.Valid) :
    ∃ loan, rl.to_lawful = .ok loan ∧ loan.toRawLoan = rl := by
  sorry

/-- A raw state that is not well-formed and valid fails the re-validation with `notLawful`. -/
theorem RawLoan.to_lawful_not_lawful {rl : RawLoan} (h : ¬ (rl.WF ∧ rl.Valid)) :
    rl.to_lawful = .error .notLawful := by
  sorry

/-- A lawful loan's grace period ends within the ledger clock: its due date is on the schedule, and the schedule
with the grace period fits. -/
lemma Loan.gracePeriodEnd_lt (loan : Loan) :
    loan.nextPaymentDueDate.toNat + loan.schedule.gracePeriod.toNat < 2 ^ 32 := by
  sorry

/-- A lawful loan with two or more payments left is due within the ledger clock one interval later. -/
lemma Loan.nextDue_lt (loan : Loan) (h2 : 2 ≤ loan.paymentRemaining.toNat) :
    loan.nextPaymentDueDate.toNat + loan.schedule.paymentInterval.toNat < 2 ^ 32 := by
  sorry

/-- The interest a loan computes is a normalized `Number`. -/
lemma RawLoan.interestDue_isNormalized (loan : Loan) (i : Number) (hi : loan.interestDue = .ok i) :
    i.isNormalized := by
  sorry

/-- Loans with the same outstanding amounts have the same exact interest. -/
lemma Loan.toExact_interestDue_congr {l l' : Loan} (h1 : l'.totalValueOutstanding = l.totalValueOutstanding)
    (h2 : l'.principalOutstanding = l.principalOutstanding)
    (h3 : l'.managementFeeOutstanding = l.managementFeeOutstanding) :
    l'.toExact.interestDue = l.toExact.interestDue := by
  sorry

/-- The interest a lawful loan still owes is computed exactly. -/
lemma Loan.interestDue_toExact (loan : Loan) (i : Number) (h : loan.interestDue = .ok i) :
    i.toRat = loan.toExact.interestDue := by
  sorry

end XRPL.Model.Lending
