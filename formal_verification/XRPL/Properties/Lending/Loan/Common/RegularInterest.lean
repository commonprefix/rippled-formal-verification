import XRPL.Properties.Lending.Loan.Common.PaidAmounts

/-! # The interest a regular payment pays

Every scheduled instalment takes whole LoanScale units off the loan, so the interest it pays is exactly the drop in
the loan's interestDue, and a regular payment's interest is the drop over all of its instalments. -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault (Vault RawVault)

open private Loan.scheduledComponents Loan.doPayment UnsettledPayment.payInstalments
  from XRPL.Model.Lending.Loan.LoanPay
open private Number.clamp_zero_nonneg Number.clamp_zero_le from XRPL.Properties.Lending.Loan.Common.PayMonotone

/-- A lawful loan's exact interestDue in LoanScale units: at least minus one, at least zero for an XRP or MPT loan,
and below the asset's mantissa bound. -/
lemma Loan.interestDue_units (l : Loan) :
    ∃ k : ℤ, l.toExact.interestDue = (k : ℚ) * 10 ^ l.loanScale ∧ -1 ≤ k ∧
      k < l.toExact.numericType.mantissaBound ∧ (l.broker.numericType.isIntegral = true → 0 ≤ k) := by
  have heg := Loan.grid l
  obtain ⟨t, ht, htv⟩ := UnitsAt.of_atExponent l.wf.totalValueOutstanding_norm heg.totalValueOutstanding_atExponent
  obtain ⟨p, -, hpv⟩ := UnitsAt.of_atExponent l.wf.principalOutstanding_norm heg.principalOutstanding_atExponent
  obtain ⟨m, -, hmv⟩ := UnitsAt.of_atExponent l.wf.managementFeeOutstanding_norm
    heg.managementFeeOutstanding_atExponent
  have hls : l.toExact.loanScale = l.loanScale := rfl
  rw [hls] at htv hpv hmv
  have hpos : (0 : ℚ) < 10 ^ l.loanScale := zpow_pos (by norm_num) _
  have hv : l.toExact.interestDue = (((t : ℤ) - p - m : ℤ) : ℚ) * 10 ^ l.loanScale := by
    show l.totalValueOutstanding.toRat - l.principalOutstanding.toRat - l.managementFeeOutstanding.toRat = _
    rw [htv.val, hpv.val, hmv.val]; push_cast; ring
  have htol := l.exact.interest_nonneg
  rw [hv] at htol
  refine ⟨(t : ℤ) - p - m, hv, ?_, by omega, fun _ => ?_⟩
  · by_contra hlt
    have hle : (((t : ℤ) - p - m : ℤ) : ℚ) ≤ -2 := by exact_mod_cast (show (t : ℤ) - p - m ≤ -2 by omega)
    nlinarith
  · exact_mod_cast nonneg_of_mul_nonneg_left htol hpos

/-- The deltas of the next scheduled instalment. A final one clears the loan, any other takes whole LoanScale units
off each outstanding amount, between zero and all of it. -/
private lemma Loan.scheduledComponents_deltas (l : Loan) (pc : PaymentComponents)
    (hr : -81 ≤ l.loanScale ∧ l.loanScale ≤ 0) (h : Loan.scheduledComponents l = .ok pc) :
    pc.untrackedInterest = Number.zero ∧
      ((pc.isFinal = true ∧ pc.totalValueDelta = l.totalValueOutstanding ∧
          pc.principalDelta = l.principalOutstanding ∧ pc.managementFeeDelta = l.managementFeeOutstanding) ∨
        (pc.isFinal = false ∧ Number.OnGrid l.loanScale pc.totalValueDelta ∧
          Number.OnGrid l.loanScale pc.principalDelta ∧ Number.OnGrid l.loanScale pc.managementFeeDelta ∧
          0 ≤ pc.totalValueDelta.toRat ∧ pc.totalValueDelta.toRat ≤ l.totalValueOutstanding.toRat ∧
          0 ≤ pc.principalDelta.toRat ∧ pc.principalDelta.toRat ≤ l.principalOutstanding.toRat ∧
          0 ≤ pc.managementFeeDelta.toRat ∧ pc.managementFeeDelta.toRat ≤ l.managementFeeOutstanding.toRat)) := by
  have hsb := Loan.loanScale_bounds l
  have hT := l.wf.totalValueOutstanding_norm
  have hP := l.wf.principalOutstanding_norm
  have hM := l.wf.managementFeeOutstanding_norm
  have hT0 : 0 ≤ l.totalValueOutstanding.toRat := l.exact.totalValueOutstanding_nonneg
  have hP0 : 0 ≤ l.principalOutstanding.toRat := l.exact.principalOutstanding_nonneg
  have hM0 : 0 ≤ l.managementFeeOutstanding.toRat := l.exact.managementFeeOutstanding_nonneg
  unfold Loan.scheduledComponents at h
  simp only [bind, Except.bind] at h
  walk_ok
  all_goals
    simp only [pure, Except.pure, Except.ok.injEq] at *
    subst_vars
  all_goals first
    | exact ⟨rfl, Or.inl ⟨rfl, rfl, rfl, rfl⟩⟩
    | (obtain ⟨t, p, m, -, -, -, ht, hp, hm, hi, -, h1, h2, h3⟩ := Loan.state_units l _ ‹l.state = _›
       have g1 := ht.onGrid
       have g2 := hp.onGrid
       have g3 := hm.onGrid
       have g4 := hi.onGrid
       rw [← h1] at hT hT0
       rw [← h2] at hP hP0
       rw [← h3] at hM hM0
       grid_forward l.loanScale
       refine ⟨rfl, Or.inr ⟨rfl, ?_, ?_, ?_, Number.clamp_zero_nonneg _ _ hT0, ?_, Number.clamp_zero_nonneg _ _ hP0,
         ?_, Number.clamp_zero_nonneg _ _ hM0, ?_⟩⟩
       · grid_prove
       · grid_prove
       · grid_prove
       · rw [← h1]
         apply Number.clamp_zero_le _ _ _ hT hT0
         refine (?_ : Number.OnGrid l.loanScale _).1
         grid_prove
       · rw [← h2]
         apply Number.clamp_zero_le _ _ _ hP hP0
         refine (?_ : Number.OnGrid l.loanScale _).1
         grid_prove
       · rw [← h3]
         apply Number.clamp_zero_le _ _ _ hM hM0
         refine (?_ : Number.OnGrid l.loanScale _).1
         grid_prove)

/-- An instalment takes its deltas off the loan, a final one clears it. -/
private lemma Loan.doPayment_outstanding (l l' : Loan) (pc : PaymentComponents) (h : Loan.doPayment l pc = .ok l') :
    (pc.isFinal = true → l'.totalValueOutstanding = Number.zero ∧ l'.principalOutstanding = Number.zero ∧
        l'.managementFeeOutstanding = Number.zero) ∧
      (pc.isFinal = false →
        l.totalValueOutstanding.operator_sub pc.totalValueDelta .to_nearest = .ok l'.totalValueOutstanding ∧
        l.principalOutstanding.operator_sub pc.principalDelta .to_nearest = .ok l'.principalOutstanding ∧
        l.managementFeeOutstanding.operator_sub pc.managementFeeDelta .to_nearest =
          .ok l'.managementFeeOutstanding) := by
  cases hf : pc.isFinal
  · simp only [Loan.doPayment, hf, Bool.false_eq_true, ↓reduceIte] at h
    unfold_ter at h
    walk_ok
    have h1 := (RawLoan.to_lawful_ok ‹_›).1
    refine ⟨fun h => (by cases h), fun _ => ?_⟩
    rw [show l'.totalValueOutstanding = l'.toRawLoan.totalValueOutstanding from rfl,
      show l'.principalOutstanding = l'.toRawLoan.principalOutstanding from rfl,
      show l'.managementFeeOutstanding = l'.toRawLoan.managementFeeOutstanding from rfl, h1]
    exact ⟨‹_›, ‹_›, ‹_›⟩
  · simp only [Loan.doPayment, hf, ↓reduceIte] at h
    unfold_ter at h
    walk_ok
    have h1 := (RawLoan.to_lawful_ok ‹_›).1
    refine ⟨fun _ => ?_, fun h => (by cases h)⟩
    rw [show l'.totalValueOutstanding = l'.toRawLoan.totalValueOutstanding from rfl,
      show l'.principalOutstanding = l'.toRawLoan.principalOutstanding from rfl,
      show l'.managementFeeOutstanding = l'.toRawLoan.managementFeeOutstanding from rfl, h1]
    exact ⟨rfl, rfl, rfl⟩

/-- A difference of two interests of loans on the same asset fits the exact grid arithmetic. -/
private lemma Loan.interest_diff_range (l l' : Loan) (k k' : ℤ) (hnt : l'.broker.numericType = l.broker.numericType)
    (hk : -1 ≤ k ∧ k < l.toExact.numericType.mantissaBound ∧ (l.broker.numericType.isIntegral = true → 0 ≤ k))
    (hk' : -1 ≤ k' ∧ k' < l'.toExact.numericType.mantissaBound ∧
      (l'.broker.numericType.isIntegral = true → 0 ≤ k')) :
    -2 ^ 63 < k - k' ∧ k - k' < 2 ^ 63 := by
  have hnt' : l'.toExact.numericType = l.toExact.numericType := hnt
  rw [hnt'] at hk'
  rw [hnt] at hk'
  have hB : (l.toExact.numericType.mantissaBound : ℤ) ≤ 2 ^ 63 := by
    exact_mod_cast NumericType.mantissaBound_le l.toExact.numericType
  cases hi : l.broker.numericType.isIntegral
  · have hfr : l.toExact.numericType = .fractional := NumericType.eq_fractional_of_not_integral (by simpa using hi)
    rw [hfr] at hk hk'
    simp only [NumericType.mantissaBound] at hk hk'
    push_cast at hk hk'
    constructor <;> omega
  · have h1 := hk.2.2 hi
    have h2 := hk'.2.2 hi
    constructor <;> omega

/-- The deltas of the next scheduled instalment, as `Loan.scheduledComponents_deltas` states them. -/
private def PaymentComponents.Scheduled (l : Loan) (pc : PaymentComponents) : Prop :=
  pc.untrackedInterest = Number.zero ∧
    ((pc.isFinal = true ∧ pc.totalValueDelta = l.totalValueOutstanding ∧
        pc.principalDelta = l.principalOutstanding ∧ pc.managementFeeDelta = l.managementFeeOutstanding) ∨
      (pc.isFinal = false ∧ Number.OnGrid l.loanScale pc.totalValueDelta ∧
        Number.OnGrid l.loanScale pc.principalDelta ∧ Number.OnGrid l.loanScale pc.managementFeeDelta ∧
        0 ≤ pc.totalValueDelta.toRat ∧ pc.totalValueDelta.toRat ≤ l.totalValueOutstanding.toRat ∧
        0 ≤ pc.principalDelta.toRat ∧ pc.principalDelta.toRat ≤ l.principalOutstanding.toRat ∧
        0 ≤ pc.managementFeeDelta.toRat ∧ pc.managementFeeDelta.toRat ≤ l.managementFeeOutstanding.toRat))

private lemma PaymentComponents.Scheduled.norm {l : Loan} {pc : PaymentComponents}
    (h : PaymentComponents.Scheduled l pc) :
    pc.totalValueDelta.isNormalized ∧ pc.principalDelta.isNormalized ∧ pc.managementFeeDelta.isNormalized := by
  rcases h.2 with ⟨-, h1, h2, h3⟩ | ⟨-, g1, g2, g3, -⟩
  · rw [h1, h2, h3]
    exact ⟨l.wf.totalValueOutstanding_norm, l.wf.principalOutstanding_norm, l.wf.managementFeeOutstanding_norm⟩
  · exact ⟨g1.1, g2.1, g3.1⟩

/-- One scheduled instalment pays as interest exactly the drop in interestDue. -/
private lemma Loan.instalment_interest (l l' : Loan) (pc : PaymentComponents) (inst : PaymentAmounts)
    (hδ : PaymentComponents.Scheduled l pc) (hpaid : pc.paidAmounts = .ok inst) (hdo : Loan.doPayment l pc = .ok l') :
    inst.interestPaid.toRat = l.toExact.interestDue - l'.toExact.interestDue := by
  have hsb := Loan.loanScale_bounds l
  have hst := Loan.doPayment_sameTerms l l' pc hdo
  have hnt : l'.broker.numericType = l.broker.numericType := by rw [hst.broker]
  obtain ⟨vap, id, e1, e2, e3, -, -⟩ := PaymentComponents.paidAmounts_ok_inv pc inst hpaid
  rw [hδ.1, Number.operator_add_zero_right, Except.ok.injEq] at e3
  subst e3
  obtain ⟨hfin, hnf⟩ := Loan.doPayment_outstanding l l' pc hdo
  -- the loan's amounts in LoanScale units
  have heg := Loan.grid l
  have hls : l.toExact.loanScale = l.loanScale := rfl
  obtain ⟨t, ht, htv⟩ := UnitsAt.of_atExponent l.wf.totalValueOutstanding_norm heg.totalValueOutstanding_atExponent
  obtain ⟨p, hp, hpv⟩ := UnitsAt.of_atExponent l.wf.principalOutstanding_norm heg.principalOutstanding_atExponent
  obtain ⟨m, hm, hmv⟩ := UnitsAt.of_atExponent l.wf.managementFeeOutstanding_norm
    heg.managementFeeOutstanding_atExponent
  rw [hls] at htv hpv hmv
  have hB : l.toExact.numericType.mantissaBound ≤ 2 ^ 63 := NumericType.mantissaBound_le _
  obtain ⟨k, hkv, hk1, hkB, hkI⟩ := Loan.interestDue_units l
  obtain ⟨k', hkv', hk1', hkB', hkI'⟩ := Loan.interestDue_units l'
  rw [hst.loanScale] at hkv'
  have hkk := Loan.interest_diff_range l l' k k' hnt ⟨hk1, hkB, hkI⟩ ⟨hk1', hkB', hkI'⟩
  have hpos : (0 : ℚ) < 10 ^ l.loanScale := zpow_pos (by norm_num) _
  have hkt : k = (t : ℤ) - p - m := by
    have : l.toExact.interestDue = (((t : ℤ) - p - m : ℤ) : ℚ) * 10 ^ l.loanScale := by
      show l.totalValueOutstanding.toRat - l.principalOutstanding.toRat - l.managementFeeOutstanding.toRat = _
      rw [htv.val, hpv.val, hmv.val]; push_cast; ring
    rw [hkv] at this
    exact_mod_cast mul_right_cancel₀ hpos.ne' this
  rcases hδ.2 with ⟨hf, h1, h2, h3⟩ | ⟨hf, g1, g2, g3, a0, a1, b0, b1, c0, c1⟩
  · -- the final instalment clears the loan
    obtain ⟨z1, z2, z3⟩ := hfin hf
    have hz : l'.toExact.interestDue = 0 := by
      show l'.totalValueOutstanding.toRat - l'.principalOutstanding.toRat - l'.managementFeeOutstanding.toRat = 0
      rw [z1, z2, z3, Number.toRat_zero]; ring
    rw [h1, h2] at e1
    rw [h3] at e2
    have hvap := UnitsAt.sub htv hpv (by constructor <;> omega) hsb e1
    have hid := UnitsAt.sub hvap hmv (by constructor <;> omega) hsb e2
    rw [hid.val, hz, hkv, hkt]
    push_cast; ring
  · -- any other instalment takes whole units off each amount
    obtain ⟨d1, d2, d3⟩ := hnf hf
    have hT63 : l.totalValueOutstanding.toRat < 2 ^ 63 * (10 : ℚ) ^ l.loanScale := by
      rw [htv.val]
      exact mul_lt_mul_of_pos_right (by exact_mod_cast lt_of_lt_of_le ht hB) hpos
    have hP63 : l.principalOutstanding.toRat < 2 ^ 63 * (10 : ℚ) ^ l.loanScale := by
      rw [hpv.val]
      exact mul_lt_mul_of_pos_right (by exact_mod_cast lt_of_lt_of_le hp hB) hpos
    have hM63 : l.managementFeeOutstanding.toRat < 2 ^ 63 * (10 : ℚ) ^ l.loanScale := by
      rw [hmv.val]
      exact mul_lt_mul_of_pos_right (by exact_mod_cast lt_of_lt_of_le hm hB) hpos
    have v1 := Number.OnGrid.sub_exact htv.onGrid g1 a0 a1 hT63 hsb d1
    have v2 := Number.OnGrid.sub_exact hpv.onGrid g2 b0 b1 hP63 hsb d2
    have v3 := Number.OnGrid.sub_exact hmv.onGrid g3 c0 c1 hM63 hsb d3
    obtain ⟨a, ha⟩ := g1.units a0
    obtain ⟨b, hb⟩ := g2.units b0
    obtain ⟨c, hc⟩ := g3.units c0
    have hat : (a : ℚ) * 10 ^ l.loanScale ≤ (t : ℚ) * 10 ^ l.loanScale := by
      have := a1; rw [htv.val, ha] at this; exact_mod_cast this
    have hbt : (b : ℚ) * 10 ^ l.loanScale ≤ (p : ℚ) * 10 ^ l.loanScale := by
      have := b1; rw [hpv.val, hb] at this; exact_mod_cast this
    have hct : (c : ℚ) * 10 ^ l.loanScale ≤ (m : ℚ) * 10 ^ l.loanScale := by
      have := c1; rw [hmv.val, hc] at this; exact_mod_cast this
    have hat' : a ≤ t := by exact_mod_cast le_of_mul_le_mul_right hat hpos
    have hbt' : b ≤ p := by exact_mod_cast le_of_mul_le_mul_right hbt hpos
    have hct' : c ≤ m := by exact_mod_cast le_of_mul_le_mul_right hct hpos
    have hk'v : k' = k - ((a : ℤ) - b - c) := by
      have : l'.toExact.interestDue = ((k - ((a : ℤ) - b - c) : ℤ) : ℚ) * 10 ^ l.loanScale := by
        show l'.totalValueOutstanding.toRat - l'.principalOutstanding.toRat - l'.managementFeeOutstanding.toRat = _
        rw [v1, v2, v3, htv.val, hpv.val, hmv.val, ha, hb, hc, hkt]; push_cast; ring
      rw [hkv'] at this
      exact_mod_cast mul_right_cancel₀ hpos.ne' this
    have hvap := Number.operator_sub_toRat_of_grid _ _ _ a b l.loanScale g1.1 g2.1 (by rw [ha]; push_cast; ring)
      (by rw [hb]; push_cast; ring) (by constructor <;> omega) hsb e1
    have hvapn := operator_sub_isNormalized_to_nearest_sz _ _ _ g1.1 g2.1 e1
    have hid := Number.operator_sub_toRat_of_grid _ _ _ ((a : ℤ) - b) c l.loanScale hvapn g3.1 hvap
      (by rw [hc]; push_cast; ring) (by constructor <;> omega) hsb e2
    rw [hid, hkv, hkv', hk'v]
    push_cast; ring

/-- One instalment keeps the interest sum exact. -/
private lemma Loan.instalment_sum (l l' : Loan) (pc : PaymentComponents) (inst amounts amounts' : PaymentAmounts)
    (s : Int) (I0 : ℚ) (k0 : ℤ) (nt : NumericType)
    (hk0 : I0 = (k0 : ℚ) * 10 ^ s ∧ -1 ≤ k0 ∧ k0 < nt.mantissaBound ∧ (nt.isIntegral = true → 0 ≤ k0))
    (hls : l.loanScale = s) (hnt : l.broker.numericType = nt) (hδ : PaymentComponents.Scheduled l pc)
    (hpaid : pc.paidAmounts = .ok inst) (hdo : Loan.doPayment l pc = .ok l') (hadd : amounts.add inst = .ok amounts')
    (hg : Number.OnGrid s amounts.interestPaid) (hI : amounts.interestPaid.toRat + l.toExact.interestDue = I0) :
    Number.OnGrid s amounts'.interestPaid ∧ amounts'.interestPaid.toRat + l'.toExact.interestDue = I0 ∧
      l'.loanScale = s ∧ l'.broker.numericType = nt := by
  have hinst := Loan.instalment_interest l l' pc inst hδ hpaid hdo
  have hst := Loan.doPayment_sameTerms l l' pc hdo
  have hsb := Loan.loanScale_bounds l
  rw [hls] at hsb
  obtain ⟨kl, hkl, -, -, -⟩ := Loan.interestDue_units l
  obtain ⟨kl', hkl', hkl1', hklB', hklI'⟩ := Loan.interestDue_units l'
  rw [hst.loanScale, hls] at hkl'
  rw [hls] at hkl
  have hnt' : l'.broker.numericType = nt := by rw [hst.broker, hnt]
  have hntE : l'.toExact.numericType = nt := hnt'
  rw [hntE] at hklB'
  rw [hnt'] at hklI'
  have hsum := PaymentAmounts.add_interest _ _ _ hadd
  have hav : amounts.interestPaid.toRat = ((k0 - kl : ℤ) : ℚ) * 10 ^ s := by
    rw [show amounts.interestPaid.toRat = I0 - l.toExact.interestDue by linarith, hk0.1, hkl]; push_cast; ring

  have hbv : inst.interestPaid.toRat = ((kl - kl' : ℤ) : ℚ) * 10 ^ s := by rw [hinst, hkl, hkl']; push_cast; ring
  have hB : (nt.mantissaBound : ℤ) ≤ 2 ^ 63 := by exact_mod_cast NumericType.mantissaBound_le nt
  obtain ⟨hk0v, hk01, hk0B, hk0I⟩ := hk0
  have hrange : -2 ^ 63 < (k0 - kl) + (kl - kl') ∧ (k0 - kl) + (kl - kl') < 2 ^ 63 := by
    cases hi : nt.isIntegral
    · have hfr : nt = .fractional := NumericType.eq_fractional_of_not_integral (by simpa using hi)
      rw [hfr] at hk0B hklB'
      simp only [NumericType.mantissaBound] at hk0B hklB'
      push_cast at hk0B hklB'
      constructor <;> omega
    · have h1 := hk0I hi
      have h2 := hklI' hi
      constructor <;> omega
  have hinstn : inst.interestPaid.isNormalized := by
    obtain ⟨_, _, e1, e2, e3, -, -⟩ := PaymentComponents.paidAmounts_ok_inv pc inst hpaid
    obtain ⟨n1, n2, n3⟩ := hδ.norm
    exact operator_add_isNormalized_to_nearest_sz _ _ _ (operator_sub_isNormalized_to_nearest_sz _ _ _
      (operator_sub_isNormalized_to_nearest_sz _ _ _ n1 n2 e1) n3 e2) (by rw [hδ.1]; exact Number.zero_isNormalized) e3
  have hv := Number.operator_add_toRat_of_grid _ _ _ (k0 - kl) (kl - kl') s hg.1 hinstn hav hbv hrange hsb hsum
  refine ⟨⟨operator_add_isNormalized_to_nearest_sz _ _ _ hg.1 hinstn hsum, _, hv⟩, ?_, by rw [hst.loanScale, hls],
    hnt'⟩
  rw [hv, hkl', hk0v]; push_cast; ring

/-- The scheduled instalments keep the interest sum exact: the interest summed so far plus the loan's interestDue is
the interestDue the loan started with. -/
private lemma UnsettledPayment.payInstalments_interest {α : Type} (amount : Number) (s : Int) (I0 : ℚ) (k0 : ℤ)
    (nt : NumericType) (hr : -81 ≤ s ∧ s ≤ 0)
    (hk0 : I0 = (k0 : ℚ) * 10 ^ s ∧ -1 ≤ k0 ∧ k0 < nt.mantissaBound ∧ (nt.isIntegral = true → 0 ≤ k0)) :
    ∀ (n : Nat) (payment p : UnsettledPayment α), UnsettledPayment.payInstalments payment n amount = .ok p →
      payment.loan.loanScale = s → payment.loan.broker.numericType = nt →
      Number.OnGrid s payment.amounts.interestPaid →
      payment.amounts.interestPaid.toRat + payment.loan.toExact.interestDue = I0 →
      p.amounts.interestPaid.toRat + p.loan.toExact.interestDue = I0 := by
  intro n
  induction n with
  | zero =>
    intro payment p h _ _ _ hI
    unfold UnsettledPayment.payInstalments at h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    exact hI
  | succ k ih =>
    intro payment p h hls hnt hg hI
    unfold UnsettledPayment.payInstalments at h
    unfold_ter at h
    walk_ok'
    all_goals first
      | exact hI
      | (have hδ := Loan.scheduledComponents_deltas payment.loan _ (hls ▸ hr)
           ‹Loan.scheduledComponents payment.loan = _›
         have hpaid := ‹PaymentComponents.paidAmounts _ = _›
         have hdo := ‹Loan.doPayment _ _ = _›
         have hadd := ‹PaymentAmounts.add _ _ = _›
         have hstep := Loan.instalment_sum payment.loan _ _ _ payment.amounts _ s I0 k0 nt hk0 hls hnt (by exact hδ)
           hpaid hdo hadd hg hI
         first
           | exact hstep.2.1
           | exact ih _ _ ‹UnsettledPayment.payInstalments _ k amount = _› hstep.2.2.1 hstep.2.2.2 hstep.1 hstep.2.1)

/-- A regular payment's interest is the drop in interestDue. -/
lemma Loan.regularPayment_interest (loan : Loan) (v : Vault) (amount : Number) (now : UInt32)
    (p : UnsettledPayment Vault) (hr : -81 ≤ loan.loanScale ∧ loan.loanScale ≤ 0)
    (h : (loan.payInstalments v .regular amount now).run = .ok (.ok p)) :
    p.amounts.interestPaid.toRat = loan.toExact.interestDue - p.loan.toExact.interestDue := by
  obtain ⟨si, -, hloop, -⟩ := Loan.payScheduled_loop loan v amount now p h
  obtain ⟨k0, hk0, hk01, hk0B, hk0I⟩ := Loan.interestDue_units loan
  have := UnsettledPayment.payInstalments_interest amount loan.loanScale _ k0 loan.broker.numericType hr
    ⟨hk0, hk01, hk0B, hk0I⟩ _ _ _ hloop rfl rfl (Number.OnGrid.zero _)
    (by show Number.zero.toRat + loan.toExact.interestDue = _; rw [Number.toRat_zero, zero_add])
  linarith

end XRPL.Model.Lending
