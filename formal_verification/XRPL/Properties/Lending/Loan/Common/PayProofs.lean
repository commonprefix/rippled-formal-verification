import XRPL.Properties.Lending.Loan.Common.PaySteps

/-! # Proof bodies for the LoanPay theorems -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault (Vault RawVault)

open private Loan.scheduledComponents Loan.lateComponents UnsettledPayment.applyOverpayment
  UnsettledPayment.payInstalments Loan.settlePayment Loan.doPayment from XRPL.Model.Lending.Loan.LoanPay

variable (loan : Loan) (v : Vault) (amount : Number) (now : UInt32) (paymentType : LoanPaymentType)
  (r : LoanWithAmounts Vault)

/-- Proof body of `Lending.payment_cover_unchanged`. -/
lemma Loan.payment_fees_proof (hcover : loan.broker.hasMinimumCover v.baseExponent = .ok true)
    (hok : (loan.pay v paymentType amount now).run = .ok (.ok r)) :
    r.loan'.broker.coverAvailable = loan.broker.coverAvailable := by
  obtain ⟨p, hp, hs⟩ := Loan.pay_ok loan v paymentType amount now r hok
  obtain ⟨-, hu, hst, -, -⟩ := Loan.payInstalments_ok loan v paymentType amount now p hp
  obtain ⟨toPool, yieldDelta, toBroker, cover', debtTotal', raw, broker', hsums, -, -, hbroker, hloan, -, -⟩ :=
    UnsettledPayment.settle_ok p r hs
  have hbe := Loan.unimpairIfImpaired_baseExponent loan v p.pool _ hu
  have hb : p.loan.broker = loan.broker := hst.broker
  have hcover' : cover' = loan.broker.coverAvailable := by
    rcases hsums.fee with ⟨-, -, h⟩ | ⟨hc, -⟩
    · rw [h, hb]
    · rw [hb, hbe, hcover] at hc; cases hc
  have h1 := (RawLoan.to_lawful_ok hloan).1
  have h2 := (RawLoanBroker.to_lawful_ok hbroker).1
  rw [show r.loan'.broker = r.loan'.toRawLoan.broker from rfl, h1]
  simp only
  rw [show broker'.coverAvailable = broker'.toRawLoanBroker.coverAvailable from rfl, h2]
  exact hcover'

/-- Proof body of the paid-off part of `Lending.fullPayment_payoff`. -/
lemma Loan.fullPayment_closes_proof (hok : (loan.fullPayment v amount now).run = .ok (.ok r)) :
    r.loan'.paymentRemaining = 0 ∧ r.loan'.totalValueOutstanding = Number.zero ∧
      r.loan'.principalOutstanding = Number.zero ∧ r.loan'.managementFeeOutstanding = Number.zero := by
  obtain ⟨p, hp, hs⟩ := Loan.pay_ok loan v .full amount now r hok
  have hpaid := Loan.fullPayInstalments_paid loan v amount now p hp
  obtain ⟨_, _, _, _, _, _, _, -, -, -, -, hloan, -, -⟩ := UnsettledPayment.settle_ok p r hs
  have h1 := (RawLoan.to_lawful_ok hloan).1
  have hr : r.loan'.paymentRemaining = 0 := by
    rw [show r.loan'.paymentRemaining = r.loan'.toRawLoan.paymentRemaining from rfl, h1]; exact hpaid
  exact ⟨hr, r.loan'.valid.paid_zeroed hr⟩

/-- Proof body of the schedule part of `Lending.overpayment_extra`. -/
lemma Loan.overpayment_schedule_proof (hok : (loan.overpayment v amount now).run = .ok (.ok r)) :
    ∃ payment, (loan.payInstalments v .regular amount now).run = .ok (.ok payment) ∧
      r.loan'.paymentRemaining = payment.loan.paymentRemaining ∧
      r.loan'.nextPaymentDueDate = payment.loan.nextPaymentDueDate := by
  obtain ⟨p, hp, hs⟩ := Loan.pay_ok loan v .overpayment amount now r hok
  obtain ⟨p0, h0, h1⟩ := Loan.overPayInstalments_ok loan v amount now p hp
  obtain ⟨-, -, -, -, hpr, hnd⟩ := UnsettledPayment.applyOverpayment_sameTerms _ _ _ h1
  obtain ⟨_, _, _, _, _, _, _, -, -, -, -, hloan, -, -⟩ := UnsettledPayment.settle_ok p r hs
  have h2 := (RawLoan.to_lawful_ok hloan).1
  refine ⟨p0, h0, ?_, ?_⟩
  · rw [show r.loan'.paymentRemaining = r.loan'.toRawLoan.paymentRemaining from rfl, h2]; exact hpr
  · rw [show r.loan'.nextPaymentDueDate = r.loan'.toRawLoan.nextPaymentDueDate from rfl, h2]; exact hnd

/-- Proof body of `payment_lateness`. -/
lemma Loan.payment_lateness_proof (hr : loan.paymentRemaining ≠ 0) (hpo : loan.principalOutstanding ≠ Number.zero)
    (hdue : loan.paymentRemaining ≠ 0 → loan.nextPaymentDueDate ≠ 0) :
    (now ≤ loan.nextPaymentDueDate →
      (loan.regularPayment v amount now).run ≠ .ok (.error .tecEXPIRED) ∧
        (loan.fullPayment v amount now).run ≠ .ok (.error .tecEXPIRED) ∧
        (loan.overpayment v amount now).run ≠ .ok (.error .tecEXPIRED) ∧
        (loan.latePayment v amount now).run = .ok (.error .tecTOO_SOON)) ∧
    (loan.nextPaymentDueDate < now →
      (loan.regularPayment v amount now).run = .ok (.error .tecEXPIRED) ∧
        (loan.fullPayment v amount now).run = .ok (.error .tecEXPIRED) ∧
        (loan.overpayment v amount now).run = .ok (.error .tecEXPIRED) ∧
        (loan.latePayment v amount now).run ≠ .ok (.error .tecTOO_SOON)) := by
  have hexp : ∀ pt, now ≤ loan.nextPaymentDueDate → (loan.pay v pt amount now).run ≠ .ok (.error .tecEXPIRED) := by
    intro pt hsoon h
    rcases Loan.pay_codes loan v amount now pt _ hdue h with ⟨h', -⟩ | ⟨-, -, hl⟩ | ⟨h', -⟩ | h' | h' | h' | ⟨h', -⟩
    · exact absurd h' (by decide)
    · exact absurd hsoon (UInt32.not_le.mpr hl)
    all_goals exact absurd h' (by decide)
  refine ⟨fun hsoon => ⟨hexp .regular hsoon, hexp .full hsoon, hexp .overpayment hsoon,
    Loan.latePayment_too_soon_proof loan v amount now hr hpo hdue hsoon⟩, fun hlate => ⟨?_, ?_, ?_, ?_⟩⟩
  · exact Loan.regularPayment_late_proof loan v amount now hr hpo hdue hlate
  · exact Loan.fullPayment_late_proof loan v amount now hr hpo hdue hlate
  · exact Loan.overpayment_late_proof loan v amount now hr hpo hdue hlate
  · intro h
    rcases Loan.pay_codes loan v amount now .late _ hdue h with ⟨h', -⟩ | ⟨h', -⟩ | ⟨-, -, hs⟩ | h' | h' | h' | ⟨h', -⟩
    · exact absurd h' (by decide)
    · exact absurd h' (by decide)
    · exact absurd hs (UInt32.not_le.mpr hlate)
    all_goals exact absurd h' (by decide)

/-- Proof body of the final-payment part of `Lending.regularPayment_schedule`. -/
lemma Loan.regularPayment_final_proof (pc : PaymentComponents) (pp' : Number)
    (hpp : STAmount.roundToNumericType loan.broker.numericType loan.periodicPayment .upward (some loan.loanScale) =
      .ok pp')
    (hfinal : loan.paymentRemaining = 1 ∨ loan.totalValueOutstanding.operator_le pp' = true)
    (hpc : loan.paymentComponents .regular now = .ok pc) :
    pc.totalValueDelta = loan.totalValueOutstanding ∧
      ∀ r : LoanWithAmounts Vault, (loan.regularPayment v amount now).run = .ok (.ok r) →
        r.loan'.paymentRemaining = 0 := by
  simp only [Loan.paymentComponents, bind, Except.bind] at hpc
  rcases hsc : Loan.scheduledComponents loan with e | pc0 <;> rw [hsc] at hpc <;> simp only at hpc
  · cases hpc
  obtain rfl := Except.ok.inj hpc
  have hpc0 := Loan.scheduledComponents_final loan pc0 pp' hpp hfinal hsc
  refine ⟨by rw [hpc0], fun r hok => ?_⟩
  obtain ⟨p, hp, hs⟩ := Loan.pay_ok loan v .regular amount now r hok
  obtain ⟨si, -, hloop, hcount⟩ := Loan.payScheduled_loop loan v amount now p hp
  have hsc' : Loan.scheduledComponents loan.unimpaired = .ok pc0 := by
    rw [Loan.scheduledComponents_unimpaired]; exact hsc
  have hf : pc0.isFinal = true := by rw [hpc0]
  rcases UnsettledPayment.payInstalments_first_final
    { loan := loan.unimpaired, pool := p.pool, amounts := PaymentAmounts.zero, totalPaid := Number.zero,
      count := 0, scheduledInterest := si } p 99 amount pc0 hsc' hf hloop with heq | hpr
  · rw [heq] at hcount; exact absurd rfl hcount
  · obtain ⟨_, _, _, _, _, _, _, -, -, -, -, hloan, -, -⟩ := UnsettledPayment.settle_ok p r hs
    rw [show r.loan'.paymentRemaining = r.loan'.toRawLoan.paymentRemaining from rfl, (RawLoan.to_lawful_ok hloan).1]
    exact hpr

/-- Proof body of `latePayment_single`. -/
lemma Loan.latePayment_single_proof (pc : PaymentComponents) (totalDue a₁ a₂ : Number)
    (hpc : loan.paymentComponents .late now = .ok pc) (hdue : pc.totalDue = .ok totalDue)
    (h₁ : a₁.operator_lt totalDue = false) (h₂ : a₂.operator_lt totalDue = false) :
    (loan.latePayment v a₁ now).run = (loan.latePayment v a₂ now).run ∧
      ∀ r : LoanWithAmounts Vault, (loan.latePayment v a₁ now).run = .ok (.ok r) →
        r.loan'.paymentRemaining = if pc.isFinal then 0 else loan.paymentRemaining - 1 := by
  have hlate : Loan.lateComponents loan now = .ok pc := hpc
  refine ⟨?_, fun r hok => ?_⟩
  · have e₁ := Loan.pay_run loan v .late a₁ now
    have e₂ := Loan.pay_run loan v .late a₂ now
    have h : loan.payInstalments v .late a₁ now = loan.payInstalments v .late a₂ now :=
      Loan.latePayInstalments_amount loan v now pc totalDue a₁ a₂ hlate hdue h₁ h₂
    simp only [Loan.pay] at e₁ e₂
    rw [e₁, e₂, h]
  · obtain ⟨p, hp, hs⟩ := Loan.pay_ok loan v .late a₁ now r hok
    obtain ⟨pc', hpc', -, hdo⟩ := Loan.latePayInstalments_ok loan v a₁ now p hp
    rw [hlate] at hpc'
    obtain rfl := Except.ok.inj hpc'
    obtain ⟨_, _, _, _, _, _, _, -, -, -, -, hloan, -, -⟩ := UnsettledPayment.settle_ok p r hs
    rw [show r.loan'.paymentRemaining = r.loan'.toRawLoan.paymentRemaining from rfl, (RawLoan.to_lawful_ok hloan).1]
    show p.loan.paymentRemaining = _
    cases hf : pc.isFinal
    · exact (Loan.doPayment_notFinal _ _ _ hf hdo).1
    · exact Loan.doPayment_final _ _ _ hf hdo

/-- Proof body of the count part of `Lending.regularPayment_schedule`. -/
lemma Loan.regularPayment_count_proof (payment : UnsettledPayment Vault)
    (hpay : (loan.payInstalments v .regular amount now).run = .ok (.ok payment)) :
    1 ≤ payment.count ∧ payment.count ≤ min 100 loan.paymentRemaining.toNat ∧
      amount.operator_lt payment.totalPaid = false ∧
      (payment.count = 100 ∨ payment.loan.paymentRemaining = 0 ∨
        ∀ pc due s, payment.loan.paymentComponents .regular now = .ok pc → pc.totalDue = .ok due →
          payment.totalPaid.operator_add due .to_nearest = .ok s → amount.operator_lt s = true) := by
  obtain ⟨si, -, hloop, hcount⟩ := Loan.payScheduled_loop loan v amount now payment hpay
  obtain ⟨h1, h2, h3, h4⟩ := UnsettledPayment.payInstalments_count _ _ _ _ hloop
  simp only [maxPaymentsPerTransaction] at h1 h4
  have hpr : loan.unimpaired.paymentRemaining = loan.paymentRemaining := rfl
  simp only [hpr] at h2
  refine ⟨by omega, by omega, ?_, ?_⟩
  · rcases h3 with h3 | h3
    · rw [h3] at hcount; exact absurd rfl hcount
    · exact h3
  · rcases h4 with h4 | h4 | h4
    · exact Or.inl (by omega)
    · exact Or.inr (Or.inl h4)
    · refine Or.inr (Or.inr fun pc due s hpc hdue hs => ?_)
      simp only [Loan.paymentComponents, bind, Except.bind] at hpc
      rcases hsc : Loan.scheduledComponents payment.loan with e | pc0 <;> rw [hsc] at hpc <;> simp only at hpc
      · cases hpc
      obtain rfl := Except.ok.inj hpc
      exact h4 pc0 due s hsc hdue hs

/-- The paid loan keeps PaymentRemaining through the settlement. -/
private lemma UnsettledPayment.settle_paymentRemaining (p : UnsettledPayment Vault)
    (hs : (Loan.settlePayment p.loan p.pool p.amounts p.scheduledInterest).run = .ok (.ok r)) :
    r.loan'.paymentRemaining = p.loan.paymentRemaining := by
  obtain ⟨_, _, _, _, _, _, _, -, -, -, -, hloan, -, -⟩ := UnsettledPayment.settle_ok p r hs
  rw [show r.loan'.paymentRemaining = r.loan'.toRawLoan.paymentRemaining from rfl, (RawLoan.to_lawful_ok hloan).1]

/-- The scheduled instalments of a payment take at least one payment off the loan. -/
private lemma Loan.regularPayInstalments_decreases (p : UnsettledPayment Vault)
    (hp : (loan.payInstalments v .regular amount now).run = .ok (.ok p)) :
    p.loan.paymentRemaining < loan.paymentRemaining := by
  obtain ⟨si, -, hloop, hcount⟩ := Loan.payScheduled_loop loan v amount now p hp
  obtain ⟨-, h2, -, -⟩ := UnsettledPayment.payInstalments_count _ _ _ _ hloop
  have hpr : loan.unimpaired.paymentRemaining = loan.paymentRemaining := rfl
  simp only [hpr] at h2
  rw [UInt32.lt_iff_toNat_lt]
  omega

/-- A late or full instalment takes at least one payment off the loan. -/
private lemma Loan.doPayment_decreases (pc : PaymentComponents) (l' : Loan) (hr : loan.paymentRemaining ≠ 0)
    (hdo : Loan.doPayment loan.unimpaired pc = .ok l') : l'.paymentRemaining < loan.paymentRemaining := by
  have hpos : 0 < loan.paymentRemaining.toNat := by
    have := UInt32.toNat_inj.not.mpr hr
    simp at this; omega
  rw [UInt32.lt_iff_toNat_lt]
  cases hf : pc.isFinal
  · rw [(Loan.doPayment_notFinal _ _ _ hf hdo).1]
    have hpr : loan.unimpaired.paymentRemaining = loan.paymentRemaining := rfl
    rw [hpr, UInt32.toNat_sub_of_le _ _ (by rw [UInt32.le_iff_toNat_le]; simpa using hpos)]
    simp; omega
  · rw [Loan.doPayment_final _ _ _ hf hdo]
    simpa using hpos

/-- A successful payment takes at least one payment off the loan. This is the PaymentRemaining half of
`payment_decreases`. -/
lemma Loan.payment_paymentRemaining_decreases (hok : (loan.pay v paymentType amount now).run = .ok (.ok r)) :
    r.loan'.paymentRemaining < loan.paymentRemaining := by
  obtain ⟨p, hp, hs⟩ := Loan.pay_ok loan v paymentType amount now r hok
  rw [UnsettledPayment.settle_paymentRemaining r p hs]
  obtain ⟨hchecks, -, -, -, -⟩ := Loan.payInstalments_ok loan v paymentType amount now p hp
  cases paymentType
  · exact Loan.regularPayInstalments_decreases loan v amount now p hp
  · obtain ⟨pc, -, -, hdo⟩ := Loan.latePayInstalments_ok loan v amount now p hp
    exact Loan.doPayment_decreases loan pc _ hchecks.remaining hdo
  · obtain ⟨pc, -, -, hdo⟩ := Loan.fullPayInstalments_ok loan v amount now p hp
    exact Loan.doPayment_decreases loan pc _ hchecks.remaining hdo
  · obtain ⟨p0, h0, h1⟩ := Loan.overPayInstalments_ok loan v amount now p hp
    obtain ⟨-, -, -, -, hpr, -⟩ := UnsettledPayment.applyOverpayment_sameTerms _ _ _ h1
    rw [hpr]
    exact Loan.regularPayInstalments_decreases loan v amount now p0 h0

end XRPL.Model.Lending
