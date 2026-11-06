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
  have h1 := hs.1; have h2 := hs.2
  unfold cMinOffset at h1; unfold cMaxOffset at h2; unfold minExponent maxExponent; omega

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
  have hs' := scale_room s hs
  have hpos : (0 : ℚ) < (10 : ℚ) ^ s := zpow_pos (by norm_num) _
  have htn' : t.isNormalized := operator_sub_isNormalized_to_nearest_sz _ _ t htn hpn h1
  have hin : i.isNormalized := operator_sub_isNormalized_to_nearest_sz _ _ i htn' hmn h2
  have ht : t.toRat = (((m1 : ℤ) - m2 : ℤ) : ℚ) * (10 : ℚ) ^ s :=
    Number.operator_sub_toRat_of_grid tvo po t m1 m2 s htn hpn (by rw [htv]; norm_cast)
      (by rw [hpv]; norm_cast) (by omega) hs' h1
  rw [htv, hpv, hmv]
  by_cases hm30 : m3 = 0
  · -- nothing to subtract: the result is the first difference
    subst hm30
    have hmz : mfo = Number.zero :=
      (Number.toRat_eq_zero_iff_eq_zero hmn).mp (by rw [hmv]; simp)
    have hid : t.operator_sub mfo .to_nearest = .ok t :=
      Number.operator_sub_of_mantissa_zero t mfo .to_nearest (by rw [hmz]; rfl)
    rw [hid] at h2
    rw [← Except.ok.inj h2, ht]; push_cast; ring
  · by_cases hge : m2 ≤ m1
    · -- the second subtraction is exact too
      have hi := Number.operator_sub_toRat_of_grid t mfo i ((m1 : ℤ) - m2) m3 s htn' hmn ht
        (by rw [hmv]; norm_cast) (by omega) hs' h2
      rw [hi]; push_cast; ring
    · -- a negative first difference would leave the rounded interest below the tolerance
      exfalso
      push Not at hge
      have hR := operator_sub_rounded_to_nearest t mfo i htn' hmn h2
      obtain ⟨w, hw, hwv⟩ := Number.exists_normalized_int_mul_pow (-2) s (by norm_num) hs'
      have htruth : t.toRat - mfo.toRat ≤ w.toRat := by
        rw [ht, hmv, hwv]
        have : (((m1 : ℤ) - m2 : ℤ) : ℚ) - (m3 : ℚ) ≤ ((-2 : ℤ) : ℚ) := by
          have : (m1 : ℤ) - m2 - m3 ≤ -2 := by omega
          exact_mod_cast this
        nlinarith [hpos]
      have hiw : i.toRat ≤ w.toRat := Number.roundsToRepresentable_le i _ hR w hw htruth
      have hti : tol.toRat ≤ i.toRat := (operator_le_iff _ _ htoln hin).mp hle
      rw [hwv] at hiw
      rcases htol with h0 | hneg
      · push_cast at hiw; linarith
      · push_cast at hiw; linarith

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
  have hs' := scale_room s hs
  have hpos : (0 : ℚ) < (10 : ℚ) ^ s := zpow_pos (by norm_num) _
  -- the exact interest is at least minus one unit
  have hk : (-1 : ℤ) ≤ (m1 : ℤ) - m2 - m3 := by
    have h : (-1 : ℚ) * (10 : ℚ) ^ s ≤ (((m1 : ℤ) - m2 - m3 : ℤ) : ℚ) * (10 : ℚ) ^ s := by
      rw [htv, hpv, hmv] at hexact; push_cast; linarith
    exact_mod_cast le_of_mul_le_mul_right h hpos
  obtain ⟨t, h1⟩ := Number.operator_sub_ok_of_grid tvo po m1 m2 s htn hpn htv hpv
    (lt_of_lt_of_le hm1 hbound) (lt_of_lt_of_le hm2 hbound) hs
  have htn' : t.isNormalized := operator_sub_isNormalized_to_nearest_sz _ _ t htn hpn h1
  have ht : t.toRat = (((m1 : ℤ) - m2 : ℤ) : ℚ) * (10 : ℚ) ^ s :=
    Number.operator_sub_toRat_of_grid tvo po t m1 m2 s htn hpn (by rw [htv]; norm_cast)
      (by rw [hpv]; norm_cast) (by omega) hs' h1
  by_cases hm30 : m3 = 0
  · subst hm30
    have hmz : mfo = Number.zero :=
      (Number.toRat_eq_zero_iff_eq_zero hmn).mp (by rw [hmv]; simp)
    refine ⟨t, t, h1, Number.operator_sub_of_mantissa_zero t mfo .to_nearest (by rw [hmz]; rfl), htn', ?_⟩
    rw [ht, htv, hpv, hmv]; push_cast; ring
  · -- with a fee left to subtract the first difference is nonnegative, so the second step is total
    have hge : m2 ≤ m1 := by omega
    have ht' : t.toRat = ((m1 - m2 : ℕ) : ℚ) * (10 : ℚ) ^ s := by
      rw [ht]; congr 1; push_cast [Nat.cast_sub hge]; ring
    obtain ⟨i, h2⟩ := Number.operator_sub_ok_of_grid t mfo (m1 - m2) m3 s htn' hmn ht' hmv
      (by omega) (lt_of_lt_of_le hm3 hbound) hs
    have hin : i.isNormalized := operator_sub_isNormalized_to_nearest_sz _ _ i htn' hmn h2
    have hi := Number.operator_sub_toRat_of_grid t mfo i ((m1 : ℤ) - m2) m3 s htn' hmn ht
      (by rw [hmv]; norm_cast) (by omega) hs' h2
    refine ⟨t, i, h1, h2, hin, ?_⟩
    rw [hi, htv, hpv, hmv]; push_cast; ring

/-- The operator interest clause implies the exact one. -/
private lemma RawLoan.interest_exact_of_valid (rl : RawLoan) (hwf : rl.WF) (hv : rl.Valid) :
    0 ≤ rl.toExact.interestDue := by
  have nonneg : ∀ n : Number, n.isNormalized → Number.zero.operator_le n = true → 0 ≤ n.toRat :=
    fun n hn h => by
      have := (operator_le_iff _ _ Number.zero_isNormalized hn).mp h
      rwa [Number.toRat_zero] at this
  obtain ⟨m1, hm1, htv⟩ := (Number.isAtExponent_iff _ _ _ hwf.totalValueOutstanding_norm
    (nonneg _ hwf.totalValueOutstanding_norm hv.totalValueOutstanding_nonneg)).mp
    hwf.totalValueOutstanding_atExponent
  obtain ⟨m2, hm2, hpv⟩ := (Number.isAtExponent_iff _ _ _ hwf.principalOutstanding_norm
    (nonneg _ hwf.principalOutstanding_norm hv.principalOutstanding_nonneg)).mp
    hwf.principalOutstanding_atExponent
  obtain ⟨m3, hm3, hmv⟩ := (Number.isAtExponent_iff _ _ _ hwf.managementFeeOutstanding_norm
    (nonneg _ hwf.managementFeeOutstanding_norm hv.managementFeeOutstanding_nonneg)).mp
    hwf.managementFeeOutstanding_atExponent
  -- the operator clause supplies a successful computation of at least zero
  have h := hv.interest_nonneg
  unfold RawLoan.interestNonneg at h
  cases hI : rl.interestDue with
  | error e => rw [hI] at h; simp at h
  | ok i =>
    rw [hI] at h
    have hI' := hI
    unfold RawLoan.interestDue at hI'
    cases h1 : rl.totalValueOutstanding.operator_sub rl.principalOutstanding .to_nearest with
    | error e => rw [h1] at hI'; simp [bind, Except.bind] at hI'
    | ok t =>
      rw [h1] at hI'
      simp only [bind, Except.bind] at hI'
      have hexact := interest_exact_of_ok rl.totalValueOutstanding rl.principalOutstanding
        rl.managementFeeOutstanding t i Number.zero rl.loanScale rl.broker.numericType.mantissaBound m1 m2 m3
        hwf.totalValueOutstanding_norm hwf.principalOutstanding_norm hwf.managementFeeOutstanding_norm
        Number.zero_isNormalized (NumericType.mantissaBound_le _) hm1 hm2 hm3 htv hpv hmv hwf.loanScale_range
        (Or.inl Number.toRat_zero) h1 hI' h
      have hin : i.isNormalized := operator_sub_isNormalized_to_nearest_sz _ _ i
        (operator_sub_isNormalized_to_nearest_sz _ _ t hwf.totalValueOutstanding_norm
          hwf.principalOutstanding_norm h1) hwf.managementFeeOutstanding_norm hI'
      have hle := nonneg i hin h
      show 0 ≤ rl.totalValueOutstanding.toRat - rl.principalOutstanding.toRat - rl.managementFeeOutstanding.toRat
      rw [← hexact]; exact hle

/-- The exact interest clause implies the operator one. -/
private lemma RawLoan.interest_valid_of_exact (rl : RawLoan) (hwf : rl.WF) (he : rl.toExact.Valid) :
    rl.interestNonneg = true := by
  obtain ⟨m1, hm1, htv⟩ := (Number.isAtExponent_iff _ _ _ hwf.totalValueOutstanding_norm
    he.totalValueOutstanding_nonneg).mp hwf.totalValueOutstanding_atExponent
  obtain ⟨m2, hm2, hpv⟩ := (Number.isAtExponent_iff _ _ _ hwf.principalOutstanding_norm
    he.principalOutstanding_nonneg).mp hwf.principalOutstanding_atExponent
  obtain ⟨m3, hm3, hmv⟩ := (Number.isAtExponent_iff _ _ _ hwf.managementFeeOutstanding_norm
    he.managementFeeOutstanding_nonneg).mp hwf.managementFeeOutstanding_atExponent
  have hpos : (0 : ℚ) < (10 : ℚ) ^ rl.loanScale := zpow_pos (by norm_num) _
  have hexactQ : 0 ≤ rl.totalValueOutstanding.toRat - rl.principalOutstanding.toRat -
      rl.managementFeeOutstanding.toRat := he.interest_nonneg
  obtain ⟨t, i, h1, h2, hin, hi⟩ := interest_ok_of_exact rl.totalValueOutstanding
    rl.principalOutstanding rl.managementFeeOutstanding rl.loanScale rl.broker.numericType.mantissaBound
    m1 m2 m3 hwf.totalValueOutstanding_norm hwf.principalOutstanding_norm hwf.managementFeeOutstanding_norm
    (NumericType.mantissaBound_le _) hm1 hm2 hm3 htv hpv hmv hwf.loanScale_range (by linarith)
  have hI : rl.interestDue = .ok i := by
    unfold RawLoan.interestDue; rw [h1]; simp only [bind, Except.bind]; exact h2
  unfold RawLoan.interestNonneg
  rw [hI]
  apply (operator_le_iff _ _ Number.zero_isNormalized hin).mpr
  rw [hi, Number.toRat_zero]
  exact hexactQ

/-- For a well-formed representation, the operator invariant (`RawLoan.Valid`) and the exact-rational invariant
coincide. `WF` is required because `operator_le` matches `≤` only on normalized `Number`s. -/
theorem RawLoan.valid_iff_exact (rl : RawLoan) (hwf : rl.WF) :
    rl.Valid ↔ rl.toExact.Valid := by
  have nonneg : ∀ n : Number, n.isNormalized → Number.zero.operator_le n = true → 0 ≤ n.toRat :=
    fun n hn h => by
      have := (operator_le_iff _ _ Number.zero_isNormalized hn).mp h
      rwa [Number.toRat_zero] at this
  have nonneg' : ∀ n : Number, n.isNormalized → 0 ≤ n.toRat → Number.zero.operator_le n = true :=
    fun n hn h => (operator_le_iff _ _ Number.zero_isNormalized
        hn).mpr (by rw [Number.toRat_zero]; exact h)
  constructor
  · -- the operator invariant gives the exact one
    intro hv
    refine
      { paid_zeroed := ?_
        unpaid_nonzero := ?_
        principalOutstanding_nonneg := nonneg _ hwf.principalOutstanding_norm hv.principalOutstanding_nonneg
        totalValueOutstanding_nonneg :=
          nonneg _ hwf.totalValueOutstanding_norm hv.totalValueOutstanding_nonneg
        managementFeeOutstanding_nonneg :=
          nonneg _ hwf.managementFeeOutstanding_norm hv.managementFeeOutstanding_nonneg
        serviceFee_nonneg := nonneg _ hwf.serviceFee_norm hv.serviceFee_nonneg
        latePaymentFee_nonneg := nonneg _ hwf.latePaymentFee_norm hv.latePaymentFee_nonneg
        closePaymentFee_nonneg := nonneg _ hwf.closePaymentFee_norm hv.closePaymentFee_nonneg
        periodicPayment_pos := ?_
        paid_no_due_date := hv.paid_no_due_date
        interest_nonneg := RawLoan.interest_exact_of_valid rl hwf hv
        paymentRemaining_le_total := hv.paymentRemaining_le_total
        dueDate_schedule := hv.dueDate_schedule
        schedule_in_time := hv.schedule_in_time
        interestRate_cap := UInt32.le_iff_toNat_le.mp hv.interestRate_cap
        lateInterestRate_cap := UInt32.le_iff_toNat_le.mp hv.lateInterestRate_cap
        closeInterestRate_cap := UInt32.le_iff_toNat_le.mp hv.closeInterestRate_cap
        overpaymentInterestRate_cap := UInt32.le_iff_toNat_le.mp hv.overpaymentInterestRate_cap
        overpaymentFee_cap := UInt32.le_iff_toNat_le.mp hv.overpaymentFee_cap
        originationFee_nonneg := nonneg _ hwf.originationFee_norm hv.originationFee_nonneg
        paymentTotal_pos := hv.paymentTotal_pos
        paymentInterval_min := hv.paymentInterval_min
        gracePeriod_range := hv.gracePeriod_range }
    · -- paid off exactly when no payments remain
      intro h0
      obtain ⟨hT, hP, hM⟩ := hv.paid_zeroed h0
      exact ⟨(Number.toRat_eq_zero_iff_eq_zero hwf.totalValueOutstanding_norm).mpr hT,
             (Number.toRat_eq_zero_iff_eq_zero hwf.principalOutstanding_norm).mpr hP,
             (Number.toRat_eq_zero_iff_eq_zero hwf.managementFeeOutstanding_norm).mpr hM⟩
    · -- unpaid while payments remain
      intro hne
      rcases hv.unpaid_nonzero hne with hT | hP | hM
      · exact Or.inl fun h =>
          hT ((Number.toRat_eq_zero_iff_eq_zero hwf.totalValueOutstanding_norm).mp h)
      · exact Or.inr (Or.inl fun h =>
          hP ((Number.toRat_eq_zero_iff_eq_zero hwf.principalOutstanding_norm).mp h))
      · exact Or.inr (Or.inr fun h =>
          hM ((Number.toRat_eq_zero_iff_eq_zero hwf.managementFeeOutstanding_norm).mp h))
    · -- 0 < periodicPayment
      have := (operator_lt_iff _ _ Number.zero_isNormalized
          hwf.periodicPayment_norm).mp hv.periodicPayment_pos
      rwa [Number.toRat_zero] at this
  · -- the exact invariant gives the operator one
    intro he
    refine
      { paid_zeroed := ?_
        unpaid_nonzero := ?_
        principalOutstanding_nonneg := nonneg' _ hwf.principalOutstanding_norm he.principalOutstanding_nonneg
        totalValueOutstanding_nonneg :=
          nonneg' _ hwf.totalValueOutstanding_norm he.totalValueOutstanding_nonneg
        managementFeeOutstanding_nonneg :=
          nonneg' _ hwf.managementFeeOutstanding_norm he.managementFeeOutstanding_nonneg
        serviceFee_nonneg := nonneg' _ hwf.serviceFee_norm he.serviceFee_nonneg
        latePaymentFee_nonneg := nonneg' _ hwf.latePaymentFee_norm he.latePaymentFee_nonneg
        closePaymentFee_nonneg := nonneg' _ hwf.closePaymentFee_norm he.closePaymentFee_nonneg
        periodicPayment_pos := ?_
        paid_no_due_date := he.paid_no_due_date
        interest_nonneg := RawLoan.interest_valid_of_exact rl hwf he
        paymentRemaining_le_total := he.paymentRemaining_le_total
        dueDate_schedule := he.dueDate_schedule
        schedule_in_time := he.schedule_in_time
        interestRate_cap := UInt32.le_iff_toNat_le.mpr he.interestRate_cap
        lateInterestRate_cap := UInt32.le_iff_toNat_le.mpr he.lateInterestRate_cap
        closeInterestRate_cap := UInt32.le_iff_toNat_le.mpr he.closeInterestRate_cap
        overpaymentInterestRate_cap := UInt32.le_iff_toNat_le.mpr he.overpaymentInterestRate_cap
        overpaymentFee_cap := UInt32.le_iff_toNat_le.mpr he.overpaymentFee_cap
        originationFee_nonneg := nonneg' _ hwf.originationFee_norm he.originationFee_nonneg
        paymentTotal_pos := he.paymentTotal_pos
        paymentInterval_min := he.paymentInterval_min
        gracePeriod_range := he.gracePeriod_range }
    · intro h0
      obtain ⟨hT, hP, hM⟩ := he.paid_zeroed h0
      exact ⟨(Number.toRat_eq_zero_iff_eq_zero hwf.totalValueOutstanding_norm).mp hT,
             (Number.toRat_eq_zero_iff_eq_zero hwf.principalOutstanding_norm).mp hP,
             (Number.toRat_eq_zero_iff_eq_zero hwf.managementFeeOutstanding_norm).mp hM⟩
    · intro hne
      rcases he.unpaid_nonzero hne with hT | hP | hM
      · exact Or.inl fun h =>
          hT ((Number.toRat_eq_zero_iff_eq_zero hwf.totalValueOutstanding_norm).mpr h)
      · exact Or.inr (Or.inl fun h =>
          hP ((Number.toRat_eq_zero_iff_eq_zero hwf.principalOutstanding_norm).mpr h))
      · exact Or.inr (Or.inr fun h =>
          hM ((Number.toRat_eq_zero_iff_eq_zero hwf.managementFeeOutstanding_norm).mpr h))
    · have h : (0 : ℚ) < rl.periodicPayment.toRat := he.periodicPayment_pos
      exact (operator_lt_iff _ _ Number.zero_isNormalized
          hwf.periodicPayment_norm).mpr (by rw [Number.toRat_zero]; exact h)

/-- The exact-rational invariant of a lawful loan, derived from its operator proof and
well-formedness. -/
theorem Loan.exact (loan : Loan) : loan.toExact.Valid :=
  (RawLoan.valid_iff_exact loan.toRawLoan loan.wf).mp loan.valid

/-- The grid clauses of a well-formed loan, read exactly. The sign of each amount comes from the exact invariant. -/
theorem RawLoan.WF.toExact_grid {rl : RawLoan} (hwf : rl.WF) (he : rl.toExact.Valid) : rl.toExact.Grid where
  loanScale_range := hwf.loanScale_range
  totalValueOutstanding_atExponent := (Number.isAtExponent_iff _ _ _ hwf.totalValueOutstanding_norm
    he.totalValueOutstanding_nonneg).mp hwf.totalValueOutstanding_atExponent
  principalOutstanding_atExponent := (Number.isAtExponent_iff _ _ _ hwf.principalOutstanding_norm
    he.principalOutstanding_nonneg).mp hwf.principalOutstanding_atExponent
  managementFeeOutstanding_atExponent := (Number.isAtExponent_iff _ _ _ hwf.managementFeeOutstanding_norm
    he.managementFeeOutstanding_nonneg).mp hwf.managementFeeOutstanding_atExponent

/-- The grid clauses of a lawful loan, read exactly: whole LoanScale units the asset stores. -/
theorem Loan.grid (loan : Loan) : loan.toExact.Grid :=
  loan.wf.toExact_grid loan.exact

/-- When the re-validation succeeds, the lawful loan is the raw state it checked, and that state
is well-formed and valid. -/
theorem RawLoan.to_lawful_ok {rl : RawLoan} {loan : Loan}
    (h : rl.to_lawful = .ok loan) : loan.toRawLoan = rl ∧ rl.WF ∧ rl.Valid := by
  unfold RawLoan.to_lawful at h
  split at h
  · rename_i hcond; injection h with h'; exact ⟨by rw [← h'], hcond.1, hcond.2⟩
  · exact absurd h (by simp)

/-- A well-formed, valid raw state passes the re-validation unchanged. -/
theorem RawLoan.to_lawful_ok_of {rl : RawLoan} (hwf : rl.WF) (hvalid : rl.Valid) :
    ∃ loan, rl.to_lawful = .ok loan ∧ loan.toRawLoan = rl := by
  refine ⟨⟨rl, hwf, hvalid⟩, ?_, rfl⟩
  unfold RawLoan.to_lawful; rw [dif_pos ⟨hwf, hvalid⟩]

/-- A raw state that is not well-formed and valid fails the re-validation with `notLawful`. -/
theorem RawLoan.to_lawful_not_lawful {rl : RawLoan} (h : ¬ (rl.WF ∧ rl.Valid)) :
    rl.to_lawful = .error .notLawful := by
  unfold RawLoan.to_lawful; rw [dif_neg h]

/-- A lawful loan's grace period ends within the ledger clock: its due date is on the schedule, and the schedule
with the grace period fits. -/
lemma Loan.gracePeriodEnd_lt (loan : Loan) :
    loan.nextPaymentDueDate.toNat + loan.schedule.gracePeriod.toNat < 2 ^ 32 := by
  have hv := loan.valid
  have hM : maxTime.toNat = 4294967295 := rfl
  have hin := hv.schedule_in_time
  by_cases hr : loan.paymentRemaining = 0
  · have hd : loan.nextPaymentDueDate = 0 := hv.paid_no_due_date hr
    rw [hd, UInt32.toNat_zero]
    have := loan.schedule.gracePeriod.toNat_lt
    omega
  · have hd := hv.dueDate_schedule hr
    have hle := UInt32.le_iff_toNat_le.mp hv.paymentRemaining_le_total
    have hpos : 1 ≤ loan.paymentRemaining.toNat := by
      rcases Nat.eq_zero_or_pos loan.paymentRemaining.toNat with h0 | h0
      · exact absurd (UInt32.toNat_inj.mp (by rw [h0, UInt32.toNat_zero])) hr
      · exact h0
    have hmul : (loan.schedule.paymentTotal.toNat - loan.paymentRemaining.toNat + 1) *
        loan.schedule.paymentInterval.toNat ≤ loan.schedule.paymentTotal.toNat * loan.schedule.paymentInterval.toNat :=
      Nat.mul_le_mul_right _ (by omega)
    change loan.toRawLoan.nextPaymentDueDate.toNat + loan.toRawLoan.schedule.gracePeriod.toNat < 2 ^ 32
    omega

/-- A lawful loan with two or more payments left is due within the ledger clock one interval later. -/
lemma Loan.nextDue_lt (loan : Loan) (h2 : 2 ≤ loan.paymentRemaining.toNat) :
    loan.nextPaymentDueDate.toNat + loan.schedule.paymentInterval.toNat < 2 ^ 32 := by
  have hv := loan.valid
  have hM : maxTime.toNat = 4294967295 := rfl
  have hin := hv.schedule_in_time
  have hne : loan.paymentRemaining ≠ 0 := by
    intro h0; rw [h0, UInt32.toNat_zero] at h2; omega
  have hd := hv.dueDate_schedule hne
  have hle := UInt32.le_iff_toNat_le.mp hv.paymentRemaining_le_total
  have hmul : (loan.schedule.paymentTotal.toNat - loan.paymentRemaining.toNat + 1) *
      loan.schedule.paymentInterval.toNat + loan.schedule.paymentInterval.toNat ≤
      loan.schedule.paymentTotal.toNat * loan.schedule.paymentInterval.toNat := by
    rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ (by omega)
  change loan.toRawLoan.nextPaymentDueDate.toNat + loan.toRawLoan.schedule.paymentInterval.toNat < 2 ^ 32
  omega

/-- The interest a loan computes is a normalized `Number`. -/
lemma RawLoan.interestDue_isNormalized (loan : Loan) (i : Number) (hi : loan.interestDue = .ok i) :
    i.isNormalized := by
  unfold RawLoan.interestDue at hi
  cases h1 : loan.totalValueOutstanding.operator_sub loan.principalOutstanding .to_nearest with
  | error e => rw [h1] at hi; cases hi
  | ok t =>
    rw [h1] at hi
    exact operator_sub_isNormalized_to_nearest_sz _ _ _
      (operator_sub_isNormalized_to_nearest_sz _ _ _ loan.wf.totalValueOutstanding_norm
        loan.wf.principalOutstanding_norm h1) loan.wf.managementFeeOutstanding_norm hi

/-- Loans with the same outstanding amounts have the same exact interest. -/
lemma Loan.toExact_interestDue_congr {l l' : Loan} (h1 : l'.totalValueOutstanding = l.totalValueOutstanding)
    (h2 : l'.principalOutstanding = l.principalOutstanding)
    (h3 : l'.managementFeeOutstanding = l.managementFeeOutstanding) :
    l'.toExact.interestDue = l.toExact.interestDue := by
  show l'.totalValueOutstanding.toRat - l'.principalOutstanding.toRat - l'.managementFeeOutstanding.toRat = _
  rw [h1, h2, h3]; rfl

/-- The interest a lawful loan still owes is computed exactly. -/
lemma Loan.interestDue_toExact (loan : Loan) (i : Number) (h : loan.interestDue = .ok i) :
    i.toRat = loan.toExact.interestDue := by
  have he := loan.exact
  have heg := loan.grid
  have hwf := loan.wf
  obtain ⟨m1, hm1, htv⟩ := heg.totalValueOutstanding_atExponent
  obtain ⟨m2, hm2, hpv⟩ := heg.principalOutstanding_atExponent
  obtain ⟨m3, hm3, hmv⟩ := heg.managementFeeOutstanding_atExponent
  change loan.totalValueOutstanding.toRat = (m1 : ℚ) * (10 : ℚ) ^ loan.loanScale at htv
  change loan.principalOutstanding.toRat = (m2 : ℚ) * (10 : ℚ) ^ loan.loanScale at hpv
  change loan.managementFeeOutstanding.toRat = (m3 : ℚ) * (10 : ℚ) ^ loan.loanScale at hmv
  change m1 < loan.broker.numericType.mantissaBound at hm1
  change m2 < loan.broker.numericType.mantissaBound at hm2
  change m3 < loan.broker.numericType.mantissaBound at hm3
  have hb := NumericType.mantissaBound_le loan.broker.numericType
  have hs := scale_room loan.loanScale heg.loanScale_range
  have hpos : (0 : ℚ) < (10 : ℚ) ^ loan.loanScale := zpow_pos (by norm_num) _
  unfold RawLoan.interestDue at h
  obtain ⟨t, ht, h⟩ := bind_ok_peel _ _ _ h
  have htn := operator_sub_isNormalized_to_nearest_sz _ _ _ hwf.totalValueOutstanding_norm
    hwf.principalOutstanding_norm ht
  have htv' := Number.operator_sub_toRat_of_grid _ _ t m1 m2 _ hwf.totalValueOutstanding_norm
    hwf.principalOutstanding_norm (by rw [htv]; norm_cast) (by rw [hpv]; norm_cast) (by omega) hs ht
  -- the interest is at least zero, so the second difference is exact too
  have htol : -((10 : ℚ) ^ loan.loanScale) ≤ ((m1 : ℚ) - m2 - m3) * (10 : ℚ) ^ loan.loanScale := by
    have hq' : 0 ≤ loan.totalValueOutstanding.toRat - loan.principalOutstanding.toRat -
        loan.managementFeeOutstanding.toRat := he.interest_nonneg
    rw [htv, hpv, hmv] at hq'; linarith
  have hlo : (-1 : ℚ) ≤ (m1 : ℚ) - m2 - m3 := by
    by_contra hc
    push Not at hc
    nlinarith
  have hlo' : (-1 : ℤ) ≤ (m1 : ℤ) - m2 - m3 := by exact_mod_cast hlo
  have hi := Number.operator_sub_toRat_of_grid t _ i ((m1 : ℤ) - m2) m3 _ htn hwf.managementFeeOutstanding_norm
    htv' (by rw [hmv]; norm_cast) (by omega) hs h
  show i.toRat = loan.totalValueOutstanding.toRat - loan.principalOutstanding.toRat -
    loan.managementFeeOutstanding.toRat
  rw [hi, htv, hpv, hmv]; push_cast; ring

end XRPL.Model.Lending
