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
  obtain ⟨r, hok, hval, hnorm⟩ := Number.from_rep_exact (9223372036854775807 : Int64) 0 .to_nearest
    (by decide) (by unfold minExponent; norm_num) (by unfold maxExponent; norm_num)
  have hcap : debtMaximumCap = r := by
    unfold debtMaximumCap Number.ofInt64; rw [hok]; rfl
  refine ⟨?_, hcap ▸ hnorm⟩
  rw [hcap, hval, show (9223372036854775807 : Int64).toInt = 9223372036854775807 from by decide]
  push_cast; norm_num

/-- For a well-formed broker, the `Number` checks of `Valid` and their exact versions agree. `WF` is
needed because `operator_le` matches `≤` only on normalized `Number`s. -/
theorem RawLoanBroker.valid_iff_exact (rb : RawLoanBroker) (hwf : rb.WF) :
    rb.Valid ↔ rb.toExact.Valid := by
  constructor
  · -- FORWARD: rb.Valid → rb.toExact.Valid
    intro hv
    refine
      { debtTotal_nonneg := ?_
        coverAvailable_nonneg := ?_
        debt_within_cap := ?_
        empty_broker := ?_
        debtMaximum_nonneg := ?_
        debtMaximum_cap := ?_
        managementFeeRate_cap := ?_
        coverRateMinimum_cap := ?_
        coverRateLiquidation_cap := ?_
        coverRates_coupled := ?_ }
    · -- 0 ≤ debtTotal
      have := (operator_le_iff _ _ Number.zero_isNormalized
          hwf.debtTotal_norm).mp hv.debtTotal_nonneg
      rwa [Number.toRat_zero] at this
    · -- 0 ≤ coverAvailable
      have := (operator_le_iff _ _ Number.zero_isNormalized
          hwf.coverAvailable_norm).mp hv.coverAvailable_nonneg
      rwa [Number.toRat_zero] at this
    · -- debtMaximum ≠ 0 → debtTotal ≤ debtMaximum
      intro hne
      have hne' : rb.debtMaximum ≠ Number.zero := fun h =>
        hne ((Number.toRat_eq_zero_iff_eq_zero hwf.debtMaximum_norm).mpr h)
      exact (operator_le_iff _ _ hwf.debtTotal_norm hwf.debtMaximum_norm).mp (hv.debt_within_cap hne')
    · -- loanCount = 0 → debtTotal = 0
      intro h0
      have h0' : rb.loanCount = 0 := (UInt32.toNat_eq_zero_iff _).mp h0
      show rb.debtTotal.toRat = 0
      exact (Number.toRat_eq_zero_iff_eq_zero hwf.debtTotal_norm).mpr (hv.empty_broker h0')
    · -- 0 ≤ debtMaximum
      have := (operator_le_iff _ _ Number.zero_isNormalized
          hwf.debtMaximum_norm).mp hv.debtMaximum_nonneg
      rwa [Number.toRat_zero] at this
    · -- debtMaximum ≤ 2^63 − 1
      have := (operator_le_iff _ _ hwf.debtMaximum_norm debtMaximumCap_facts.2).mp hv.debtMaximum_cap
      rwa [debtMaximumCap_facts.1] at this
    · exact UInt16.le_iff_toNat_le.mp hv.managementFeeRate_cap
    · exact UInt32.le_iff_toNat_le.mp hv.coverRateMinimum_cap
    · exact UInt32.le_iff_toNat_le.mp hv.coverRateLiquidation_cap
    · -- coverRateMinimum = 0 ↔ coverRateLiquidation = 0
      show rb.coverRateMinimum.toNat = 0 ↔ rb.coverRateLiquidation.toNat = 0
      rw [UInt32.toNat_eq_zero_iff, UInt32.toNat_eq_zero_iff]
      exact hv.coverRates_coupled
  · -- BACKWARD: rb.toExact.Valid → rb.Valid
    intro he
    refine
      { debtTotal_nonneg := ?_
        coverAvailable_nonneg := ?_
        debt_within_cap := ?_
        empty_broker := ?_
        debtMaximum_nonneg := ?_
        debtMaximum_cap := ?_
        managementFeeRate_cap := ?_
        coverRateMinimum_cap := ?_
        coverRateLiquidation_cap := ?_
        coverRates_coupled := ?_ }
    · -- 0 ≤ debtTotal
      have h : (0 : ℚ) ≤ rb.debtTotal.toRat := he.debtTotal_nonneg
      exact (operator_le_iff _ _ Number.zero_isNormalized
          hwf.debtTotal_norm).mpr (by rw [Number.toRat_zero]; exact h)
    · -- 0 ≤ coverAvailable
      have h : (0 : ℚ) ≤ rb.coverAvailable.toRat := he.coverAvailable_nonneg
      exact (operator_le_iff _ _ Number.zero_isNormalized
          hwf.coverAvailable_norm).mpr (by rw [Number.toRat_zero]; exact h)
    · -- debtMaximum ≠ 0 → debtTotal ≤ debtMaximum
      intro hne
      have hne' : rb.debtMaximum.toRat ≠ 0 := fun h =>
        hne ((Number.toRat_eq_zero_iff_eq_zero hwf.debtMaximum_norm).mp h)
      exact (operator_le_iff _ _ hwf.debtTotal_norm hwf.debtMaximum_norm).mpr (he.debt_within_cap hne')
    · -- loanCount = 0 → debtTotal = 0
      intro h0
      have h0' : rb.loanCount.toNat = 0 := (UInt32.toNat_eq_zero_iff _).mpr h0
      exact (Number.toRat_eq_zero_iff_eq_zero hwf.debtTotal_norm).mp (he.empty_broker h0')
    · -- 0 ≤ debtMaximum
      have h : (0 : ℚ) ≤ rb.debtMaximum.toRat := he.debtMaximum_nonneg
      exact (operator_le_iff _ _ Number.zero_isNormalized
          hwf.debtMaximum_norm).mpr (by rw [Number.toRat_zero]; exact h)
    · -- debtMaximum ≤ 2^63 − 1
      have h : rb.debtMaximum.toRat ≤ (2 : ℚ) ^ 63 - 1 := he.debtMaximum_cap
      exact (operator_le_iff _ _ hwf.debtMaximum_norm debtMaximumCap_facts.2).mpr
        (by rw [debtMaximumCap_facts.1]; exact h)
    · exact UInt16.le_iff_toNat_le.mpr he.managementFeeRate_cap
    · exact UInt32.le_iff_toNat_le.mpr he.coverRateMinimum_cap
    · exact UInt32.le_iff_toNat_le.mpr he.coverRateLiquidation_cap
    · -- coverRateMinimum = 0 ↔ coverRateLiquidation = 0
      have h : rb.coverRateMinimum.toNat = 0 ↔ rb.coverRateLiquidation.toNat = 0 := he.coverRates_coupled
      rwa [UInt32.toNat_eq_zero_iff, UInt32.toNat_eq_zero_iff] at h

/-- The exact-rational invariant of a lawful loan broker, derived from its operator proof and
well-formedness. -/
theorem LoanBroker.exact (lb : LoanBroker) : lb.toExact.Valid :=
  (RawLoanBroker.valid_iff_exact lb.toRawLoanBroker lb.wf).mp lb.valid

/-- A lawful broker's `coverAvailable` has a clear sign bit. -/
lemma LoanBroker.coverAvailable_negative_false (lb : LoanBroker) :
    lb.coverAvailable.negative_ = false :=
  Number.negative_false_of_nonneg _ lb.wf.coverAvailable_norm lb.exact.coverAvailable_nonneg

/-- When the re-validation succeeds, the lawful broker is the raw state it checked, and that state
is well-formed and valid. -/
theorem RawLoanBroker.to_lawful_ok {rb : RawLoanBroker} {lb : LoanBroker}
    (h : rb.to_lawful = .ok lb) : lb.toRawLoanBroker = rb ∧ rb.WF ∧ rb.Valid := by
  unfold RawLoanBroker.to_lawful at h
  split at h
  · rename_i hcond; injection h with h'; exact ⟨by rw [← h'], hcond.1, hcond.2⟩
  · exact absurd h (by simp)

/-- A well-formed, valid raw state passes the re-validation unchanged. -/
theorem RawLoanBroker.to_lawful_ok_of {rb : RawLoanBroker} (hwf : rb.WF) (hvalid : rb.Valid) :
    ∃ lb, rb.to_lawful = .ok lb ∧ lb.toRawLoanBroker = rb := by
  refine ⟨⟨rb, hwf, hvalid⟩, ?_, rfl⟩
  unfold RawLoanBroker.to_lawful; rw [dif_pos ⟨hwf, hvalid⟩]

/-- A raw state that is not well-formed and valid fails the re-validation with `notLawful`. -/
theorem RawLoanBroker.to_lawful_not_lawful {rb : RawLoanBroker} (h : ¬ (rb.WF ∧ rb.Valid)) :
    rb.to_lawful = .error .notLawful := by
  unfold RawLoanBroker.to_lawful; rw [dif_neg h]

end XRPL.Model.Lending
