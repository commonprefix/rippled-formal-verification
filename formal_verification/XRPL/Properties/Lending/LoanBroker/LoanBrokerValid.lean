import XRPL.Properties.Lending.LoanBroker.Defs
import XRPL.Properties.Protocol.Number.Compare.Compare
import XRPL.Properties.Protocol.Number.Common.Constants
import XRPL.Properties.Protocol.Number.Common.ToRatLemmas
import XRPL.Properties.Protocol.Number.Constructors.FromRepExact
import XRPL.Properties.Protocol.Common.AmountArith

/-! # Equivalence of the operator and exact-rational loan-broker invariants -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol

/-- The debt cap `Number` is `2^63 − 1` and normalized. -/
lemma debtMaximumCap_facts :
    debtMaximumCap.toRat = (2 : ℚ) ^ 63 - 1 ∧ debtMaximumCap.isNormalized := by
  sorry

/-- For a well-formed broker, the `Number` checks of `Valid` and their exact versions agree. `WF` is
needed because `operator_le` matches `≤` only on normalized `Number`s. -/
theorem RawLoanBroker.valid_iff_exact (rb : RawLoanBroker) (hwf : rb.WF) :
    rb.Valid ↔ rb.toExact.Valid := by
  sorry

/-- The exact-rational invariant of a lawful loan broker, derived from its operator proof and
well-formedness. -/
theorem LoanBroker.exact (lb : LoanBroker) : lb.toExact.Valid := by
  sorry

/-- When the re-validation succeeds, the lawful broker is the raw state it checked, and that state
is well-formed and valid. -/
theorem RawLoanBroker.to_lawful_ok {rb : RawLoanBroker} {lb : LoanBroker}
    (h : rb.to_lawful = .ok lb) : lb.toRawLoanBroker = rb ∧ rb.WF ∧ rb.Valid := by
  sorry

/-- A well-formed, valid raw state passes the re-validation unchanged. -/
theorem RawLoanBroker.to_lawful_ok_of {rb : RawLoanBroker} (hwf : rb.WF) (hvalid : rb.Valid) :
    ∃ lb, rb.to_lawful = .ok lb ∧ lb.toRawLoanBroker = rb := by
  sorry

/-- A raw state that is not well-formed and valid fails the re-validation with `notLawful`. -/
theorem RawLoanBroker.to_lawful_not_lawful {rb : RawLoanBroker} (h : ¬ (rb.WF ∧ rb.Valid)) :
    rb.to_lawful = .error .notLawful := by
  sorry

/-- Two lawful brokers with the same record are the same broker. -/
lemma broker_eq_of_raw {a b : LoanBroker} (h : a.toRawLoanBroker = b.toRawLoanBroker) : a = b := by
  sorry

end XRPL.Model.Lending
