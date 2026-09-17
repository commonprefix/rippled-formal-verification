import XRPL.Properties.Lending.Loan.Defs
import XRPL.Properties.Protocol.Number.Compare.Compare
import XRPL.Properties.Protocol.Number.Common.Constants
import XRPL.Properties.Protocol.Number.Common.ToRatLemmas
import XRPL.Properties.Protocol.Number.Constructors.FromRepExact
import XRPL.Properties.Protocol.Number.Sub.RoundsToRepresentable
import XRPL.Properties.Protocol.Number.Sub.ZeroShape
import XRPL.Properties.Protocol.Number.AtExponent

/-! # Equivalence of the operator and exact-rational loan invariants -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol

private lemma zero_norm : (Number.zero).isNormalized := Or.inl rfl

private lemma toRat_eq_zero_iff_eq_zero {n : Number} (hn : n.isNormalized) :
    n.toRat = 0 ↔ n = Number.zero := by
  constructor
  · intro h; exact Number.eq_zero_of_mantissa_zero n hn (Number.toRat_eq_zero_iff.mp h)
  · intro h; rw [h, Number.toRat_zero]

private lemma scale_room (s : Int) (hs : cMinOffset ≤ s ∧ s ≤ cMaxOffset) :
    minExponent + 18 ≤ s ∧ s ≤ maxExponent - 1 := by
  have h1 := hs.1; have h2 := hs.2
  unfold cMinOffset at h1; unfold cMaxOffset at h2; unfold minExponent maxExponent; omega

/-- The tolerance of a loan whose scale is an STAmount exponent is a normalized `Number` -/
private lemma RawLoan.interestTolerance_facts (rl : RawLoan)
    (hscale : cMinOffset ≤ rl.loanScale ∧ rl.loanScale ≤ cMaxOffset) :
    ∃ tol, rl.interestTolerance = .ok tol ∧ tol.isNormalized ∧
      tol.toRat = (if rl.broker.numericType.isIntegral then (0 : ℚ) else -((10 : ℚ) ^ rl.loanScale)) := by
  unfold RawLoan.interestTolerance
  by_cases hint : rl.broker.numericType.isIntegral = true
  · refine ⟨Number.zero, by rw [if_pos hint], zero_norm, ?_⟩
    rw [if_pos hint, Number.toRat_zero]
  · obtain ⟨tol, hok, hval, hnorm⟩ := Number.from_rep_exact (-1 : Int64) rl.loanScale .to_nearest
      (by decide) (scale_room _ hscale).1 (scale_room _ hscale).2
    refine ⟨tol, by rw [if_neg hint]; exact hok, hnorm, ?_⟩
    rw [if_neg hint, hval]
    have hm1 : ((-1 : Int64).toInt : ℚ) = -1 := by
      rw [show (-1 : Int64).toInt = -1 from by decide]; push_cast; rfl
    rw [hm1]; ring

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
  -- the first subtraction is exact
  have ht : t.toRat = (((m1 : ℤ) - m2 : ℤ) : ℚ) * (10 : ℚ) ^ s :=
    Number.operator_sub_toRat_of_grid tvo po t m1 m2 s htn hpn (by rw [htv]; norm_cast)
      (by rw [hpv]; norm_cast) (by omega) hs' h1
  rw [htv, hpv, hmv]
  by_cases hm30 : m3 = 0
  · -- nothing to subtract: the result is the first difference
    subst hm30
    have hmz : mfo = Number.zero :=
      (toRat_eq_zero_iff_eq_zero hmn).mp (by rw [hmv]; simp)
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
      push_neg at hge
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
      (toRat_eq_zero_iff_eq_zero hmn).mp (by rw [hmv]; simp)
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

/-- The operator tolerance clause implies the exact one. -/
private lemma RawLoan.interest_exact_of_valid (rl : RawLoan) (hwf : rl.WF) (hv : rl.Valid) :
    rl.toExact.interestTolerance ≤ rl.toExact.interestDue := by
  have nonneg : ∀ n : Number, n.isNormalized → Number.zero.operator_le n = true → 0 ≤ n.toRat :=
    fun n hn h => by have := (operator_le_iff _ _ zero_norm hn).mp h; rwa [Number.toRat_zero] at this
  obtain ⟨m1, hm1, htv⟩ := (Number.isAtExponent_iff _ _ _ hwf.totalValueOutstanding_norm
    (nonneg _ hwf.totalValueOutstanding_norm hv.totalValueOutstanding_nonneg)).mp
    hv.totalValueOutstanding_atExponent
  obtain ⟨m2, hm2, hpv⟩ := (Number.isAtExponent_iff _ _ _ hwf.principalOutstanding_norm
    (nonneg _ hwf.principalOutstanding_norm hv.principalOutstanding_nonneg)).mp
    hv.principalOutstanding_atExponent
  obtain ⟨m3, hm3, hmv⟩ := (Number.isAtExponent_iff _ _ _ hwf.managementFeeOutstanding_norm
    (nonneg _ hwf.managementFeeOutstanding_norm hv.managementFeeOutstanding_nonneg)).mp
    hv.managementFeeOutstanding_atExponent
  obtain ⟨tol, htol, htoln, htolval⟩ := RawLoan.interestTolerance_facts rl hv.loanScale_range
  -- the operator clause supplies a successful computation that clears the tolerance
  have h := hv.interest_within_tolerance
  unfold RawLoan.interestWithinTolerance at h
  cases hI : rl.interestDue with
  | error e => rw [hI] at h; simp at h
  | ok i =>
    rw [hI, htol] at h
    -- split the computation into its two subtractions
    have hI' := hI
    unfold RawLoan.interestDue at hI'
    cases h1 : rl.totalValueOutstanding.operator_sub rl.principalOutstanding .to_nearest with
    | error e => rw [h1] at hI'; simp [bind, Except.bind] at hI'
    | ok t =>
      rw [h1] at hI'
      simp only [bind, Except.bind] at hI'
      have hexact := interest_exact_of_ok rl.totalValueOutstanding rl.principalOutstanding
        rl.managementFeeOutstanding t i tol rl.loanScale rl.broker.numericType.mantissaBound m1 m2 m3
        hwf.totalValueOutstanding_norm hwf.principalOutstanding_norm hwf.managementFeeOutstanding_norm
        htoln (NumericType.mantissaBound_le _) hm1 hm2 hm3 htv hpv hmv hv.loanScale_range
        (by rw [htolval]; split_ifs <;> simp) h1 hI' h
      have hin : i.isNormalized := operator_sub_isNormalized_to_nearest_sz _ _ i
        (operator_sub_isNormalized_to_nearest_sz _ _ t hwf.totalValueOutstanding_norm
          hwf.principalOutstanding_norm h1) hwf.managementFeeOutstanding_norm hI'
      have hle := (operator_le_iff _ _ htoln hin).mp h
      show (if rl.broker.numericType.isIntegral = true then (0 : ℚ) else -((10 : ℚ) ^ rl.loanScale)) ≤
        rl.totalValueOutstanding.toRat - rl.principalOutstanding.toRat - rl.managementFeeOutstanding.toRat
      rw [← htolval, ← hexact]; exact hle

/-- The exact tolerance clause implies the operator one. -/
private lemma RawLoan.interest_valid_of_exact (rl : RawLoan) (hwf : rl.WF) (he : rl.toExact.Valid) :
    rl.interestWithinTolerance = true := by
  obtain ⟨m1, hm1, htv⟩ := he.totalValueOutstanding_atExponent
  obtain ⟨m2, hm2, hpv⟩ := he.principalOutstanding_atExponent
  obtain ⟨m3, hm3, hmv⟩ := he.managementFeeOutstanding_atExponent
  obtain ⟨tol, htol, htoln, htolval⟩ := RawLoan.interestTolerance_facts rl he.loanScale_range
  have hpos : (0 : ℚ) < (10 : ℚ) ^ rl.loanScale := zpow_pos (by norm_num) _
  have hexactQ : rl.toExact.interestTolerance ≤ rl.toExact.interestDue := he.interest_within_tolerance
  have hexact : -((10 : ℚ) ^ rl.loanScale) ≤ rl.totalValueOutstanding.toRat
      - rl.principalOutstanding.toRat - rl.managementFeeOutstanding.toRat := by
    unfold RawLoan.Exact.interestTolerance RawLoan.Exact.interestDue at hexactQ
    refine le_trans ?_ hexactQ
    show -((10 : ℚ) ^ rl.loanScale) ≤
      (if rl.broker.numericType.isIntegral = true then (0 : ℚ) else -((10 : ℚ) ^ rl.loanScale))
    split_ifs <;> linarith
  obtain ⟨t, i, h1, h2, hin, hi⟩ := interest_ok_of_exact rl.totalValueOutstanding
    rl.principalOutstanding rl.managementFeeOutstanding rl.loanScale rl.broker.numericType.mantissaBound
    m1 m2 m3 hwf.totalValueOutstanding_norm hwf.principalOutstanding_norm hwf.managementFeeOutstanding_norm
    (NumericType.mantissaBound_le _) hm1 hm2 hm3 htv hpv hmv he.loanScale_range hexact
  have hI : rl.interestDue = .ok i := by
    unfold RawLoan.interestDue; rw [h1]; simp only [bind, Except.bind]; exact h2
  unfold RawLoan.interestWithinTolerance
  rw [hI, htol]
  apply (operator_le_iff _ _ htoln hin).mpr
  rw [hi, htolval]
  unfold RawLoan.Exact.interestTolerance RawLoan.Exact.interestDue at hexactQ
  exact hexactQ

/-- For a well-formed representation, the operator invariant (`RawLoan.Valid`) and the
exact-rational invariant coincide. `WF` is required because `operator_le` is faithful to `≤`
only on normalized `Number`s. -/
theorem RawLoan.valid_iff_exact (rl : RawLoan) (hwf : rl.WF) :
    rl.Valid ↔ rl.toExact.Valid := by
  have nonneg : ∀ n : Number, n.isNormalized → Number.zero.operator_le n = true → 0 ≤ n.toRat :=
    fun n hn h => by have := (operator_le_iff _ _ zero_norm hn).mp h; rwa [Number.toRat_zero] at this
  have nonneg' : ∀ n : Number, n.isNormalized → 0 ≤ n.toRat → Number.zero.operator_le n = true :=
    fun n hn h => (operator_le_iff _ _ zero_norm hn).mpr (by rw [Number.toRat_zero]; exact h)
  constructor
  · -- FORWARD: rl.Valid → rl.toExact.Valid
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
        interest_within_tolerance := RawLoan.interest_exact_of_valid rl hwf hv
        interestRate_cap := UInt32.le_iff_toNat_le.mp hv.interestRate_cap
        lateInterestRate_cap := UInt32.le_iff_toNat_le.mp hv.lateInterestRate_cap
        closeInterestRate_cap := UInt32.le_iff_toNat_le.mp hv.closeInterestRate_cap
        overpaymentInterestRate_cap := UInt32.le_iff_toNat_le.mp hv.overpaymentInterestRate_cap
        overpaymentFee_cap := UInt32.le_iff_toNat_le.mp hv.overpaymentFee_cap
        originationFee_nonneg := nonneg _ hwf.originationFee_norm hv.originationFee_nonneg
        paymentTotal_pos := hv.paymentTotal_pos
        paymentInterval_min := hv.paymentInterval_min
        gracePeriod_range := hv.gracePeriod_range
        loanScale_range := hv.loanScale_range
        paymentRemaining_le := hv.paymentRemaining_le
        dueDates_ordered := hv.dueDates_ordered
        nextPaymentDueDate_on_schedule := hv.nextPaymentDueDate_on_schedule
        totalValueOutstanding_atExponent := (Number.isAtExponent_iff _ _ _ hwf.totalValueOutstanding_norm
          (nonneg _ hwf.totalValueOutstanding_norm hv.totalValueOutstanding_nonneg)).mp
          hv.totalValueOutstanding_atExponent
        principalOutstanding_atExponent := (Number.isAtExponent_iff _ _ _ hwf.principalOutstanding_norm
          (nonneg _ hwf.principalOutstanding_norm hv.principalOutstanding_nonneg)).mp
          hv.principalOutstanding_atExponent
        managementFeeOutstanding_atExponent := (Number.isAtExponent_iff _ _ _ hwf.managementFeeOutstanding_norm
          (nonneg _ hwf.managementFeeOutstanding_norm hv.managementFeeOutstanding_nonneg)).mp
          hv.managementFeeOutstanding_atExponent }
    · -- paid off exactly when no payments remain
      intro h0
      obtain ⟨hT, hP, hM⟩ := hv.paid_zeroed h0
      exact ⟨(toRat_eq_zero_iff_eq_zero hwf.totalValueOutstanding_norm).mpr hT,
             (toRat_eq_zero_iff_eq_zero hwf.principalOutstanding_norm).mpr hP,
             (toRat_eq_zero_iff_eq_zero hwf.managementFeeOutstanding_norm).mpr hM⟩
    · -- unpaid while payments remain
      intro hne
      rcases hv.unpaid_nonzero hne with hT | hP | hM
      · exact Or.inl fun h => hT ((toRat_eq_zero_iff_eq_zero hwf.totalValueOutstanding_norm).mp h)
      · exact Or.inr (Or.inl fun h => hP ((toRat_eq_zero_iff_eq_zero hwf.principalOutstanding_norm).mp h))
      · exact Or.inr (Or.inr fun h =>
          hM ((toRat_eq_zero_iff_eq_zero hwf.managementFeeOutstanding_norm).mp h))
    · -- 0 < periodicPayment
      have := (operator_lt_iff _ _ zero_norm hwf.periodicPayment_norm).mp hv.periodicPayment_pos
      rwa [Number.toRat_zero] at this
  · -- BACKWARD: rl.toExact.Valid → rl.Valid
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
        interest_within_tolerance := RawLoan.interest_valid_of_exact rl hwf he
        interestRate_cap := UInt32.le_iff_toNat_le.mpr he.interestRate_cap
        lateInterestRate_cap := UInt32.le_iff_toNat_le.mpr he.lateInterestRate_cap
        closeInterestRate_cap := UInt32.le_iff_toNat_le.mpr he.closeInterestRate_cap
        overpaymentInterestRate_cap := UInt32.le_iff_toNat_le.mpr he.overpaymentInterestRate_cap
        overpaymentFee_cap := UInt32.le_iff_toNat_le.mpr he.overpaymentFee_cap
        originationFee_nonneg := nonneg' _ hwf.originationFee_norm he.originationFee_nonneg
        paymentTotal_pos := he.paymentTotal_pos
        paymentInterval_min := he.paymentInterval_min
        gracePeriod_range := he.gracePeriod_range
        loanScale_range := he.loanScale_range
        paymentRemaining_le := he.paymentRemaining_le
        dueDates_ordered := he.dueDates_ordered
        nextPaymentDueDate_on_schedule := he.nextPaymentDueDate_on_schedule
        totalValueOutstanding_atExponent := (Number.isAtExponent_iff _ _ _ hwf.totalValueOutstanding_norm
          he.totalValueOutstanding_nonneg).mpr he.totalValueOutstanding_atExponent
        principalOutstanding_atExponent := (Number.isAtExponent_iff _ _ _ hwf.principalOutstanding_norm
          he.principalOutstanding_nonneg).mpr he.principalOutstanding_atExponent
        managementFeeOutstanding_atExponent := (Number.isAtExponent_iff _ _ _ hwf.managementFeeOutstanding_norm
          he.managementFeeOutstanding_nonneg).mpr he.managementFeeOutstanding_atExponent }
    · intro h0
      obtain ⟨hT, hP, hM⟩ := he.paid_zeroed h0
      exact ⟨(toRat_eq_zero_iff_eq_zero hwf.totalValueOutstanding_norm).mp hT,
             (toRat_eq_zero_iff_eq_zero hwf.principalOutstanding_norm).mp hP,
             (toRat_eq_zero_iff_eq_zero hwf.managementFeeOutstanding_norm).mp hM⟩
    · intro hne
      rcases he.unpaid_nonzero hne with hT | hP | hM
      · exact Or.inl fun h => hT ((toRat_eq_zero_iff_eq_zero hwf.totalValueOutstanding_norm).mpr h)
      · exact Or.inr (Or.inl fun h => hP ((toRat_eq_zero_iff_eq_zero hwf.principalOutstanding_norm).mpr h))
      · exact Or.inr (Or.inr fun h =>
          hM ((toRat_eq_zero_iff_eq_zero hwf.managementFeeOutstanding_norm).mpr h))
    · have h : (0 : ℚ) < rl.periodicPayment.toRat := he.periodicPayment_pos
      exact (operator_lt_iff _ _ zero_norm hwf.periodicPayment_norm).mpr (by rw [Number.toRat_zero]; exact h)

end XRPL.Model.Lending
