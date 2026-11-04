import XRPL.Properties.Lending.Loan.Common.Twin
import XRPL.Properties.Lending.Loan.Common.PaySteps
import XRPL.Properties.Lending.Loan.Common.PayoffPay
import XRPL.Properties.Lending.Loan.Common.PayBounds
import XRPL.Properties.Lending.Ledger.Common.ClosedLoans

/-! # Twin loans pay the same instalments

The instalments of a payment read the broker only for its asset and management fee rate, so twin loans pay the same
instalments, tail and amounts and leave twins. Only the unimpair before the payment touches the vault. -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault (Vault)

open private Loan.scheduledComponents Loan.lateComponents Loan.fullComponents Loan.overpaymentComponents
  Loan.tryOverpayment Loan.unimpairIfImpaired Loan.payScheduledInstalments UnsettledPayment.applyOverpayment
  UnsettledPayment.payInstalments Loan.doPayment from XRPL.Model.Lending.Loan.LoanPay
open private Loan.scheduledComponents_twin Loan.lateComponents_twin Loan.fullComponents_twin
  from XRPL.Properties.Lending.Loan.Common.Twin
open private Loan.unimpairIfImpaired_loan from XRPL.Properties.Lending.Loan.Common.PaySteps
open private Loan.overPayInstalments_run from XRPL.Properties.Lending.Loan.Common.PayBounds

/-- Twins compute the same overpayment split. -/
private lemma Loan.overpaymentComponents_twin {l l' : Loan} (h : Loan.Twin l l') (x : Number) :
    Loan.overpaymentComponents l' x = Loan.overpaymentComponents l x := by
  obtain ⟨hraw, hnt, hm⟩ := h
  generalize hb : l'.toRawLoan.broker = b at hraw
  have hnt' : b.numericType = l.broker.numericType := by rw [← hb]; exact hnt
  have hm' : b.managementFeeRate = l.broker.managementFeeRate := by rw [← hb]; exact hm
  unfold Loan.overpaymentComponents
  rw [hraw]
  simp only [hnt', hm']

/-- Twins re-amortize an overpayment the same way. -/
private lemma Loan.tryOverpayment_twin {l l' : Loan} (h : Loan.Twin l l') (opc : PaymentComponents) :
    Loan.tryOverpayment l' opc = Loan.tryOverpayment l opc := by
  obtain ⟨hraw, hnt, hm⟩ := h
  generalize hb : l'.toRawLoan.broker = b at hraw
  have hnt' : b.numericType = l.broker.numericType := by rw [← hb]; exact hnt
  have hm' : b.managementFeeRate = l.broker.managementFeeRate := by rw [← hb]; exact hm
  unfold Loan.tryOverpayment Loan.state Loan.periodicRate
  rw [hraw]
  simp only [hnt', hm']

/-- Twins owe the same interest. -/
lemma Loan.Twin.interestDue {l l' : Loan} (h : Loan.Twin l l') : l'.interestDue = l.interestDue := by
  show RawLoan.interestDue l'.toRawLoan = RawLoan.interestDue l.toRawLoan
  rw [h.raw]
  rfl

/-- A loan record re-checked on a broker of the same asset and management fee rate gives a twin. -/
private lemma RawLoan.to_lawful_twin {raw : RawLoan} {r : Loan} (h : raw.to_lawful = .ok r) (b : LoanBroker)
    (hnt : b.numericType = raw.broker.numericType) (hm : b.managementFeeRate = raw.broker.managementFeeRate) :
    ∃ r', ({ raw with broker := b } : RawLoan).to_lawful = .ok r' ∧ Loan.Twin r r' := by
  have hr := (RawLoan.to_lawful_ok h).1
  have hrb : r.broker = raw.broker := by rw [show r.broker = r.toRawLoan.broker from rfl, hr]
  obtain ⟨r', hw⟩ := Loan.withBroker_ok r b (by rw [hrb]; exact hnt)
  have hw' := Loan.withBroker_eq hw
  have hb' : r'.broker = b := by rw [show r'.broker = r'.toRawLoan.broker from rfl, hw']
  refine ⟨r', ?_, ⟨by rw [hw'], by rw [hb', hrb]; exact hnt, by rw [hb', hrb]; exact hm⟩⟩
  have : ({ raw with broker := b } : RawLoan) = { r.toRawLoan with broker := b } := by rw [hr]
  rw [this]
  exact hw

/-- A twin advances by the same instalment to a twin of the loan it leaves. -/
private lemma Loan.doPayment_twin_ok {l l' r : Loan} (h : Loan.Twin l l') (pc : PaymentComponents)
    (hr : Loan.doPayment l pc = .ok r) : ∃ r', Loan.doPayment l' pc = .ok r' ∧ Loan.Twin r r' := by
  by_cases hf : pc.isFinal = true
  · obtain ⟨r', hr', -⟩ := Loan.doPayment_final_ok l' pc hf
    exact ⟨r', hr', Loan.doPayment_twin h pc hr hr'⟩
  simp only [Bool.not_eq_true] at hf
  have hr0 := hr
  obtain ⟨hraw, hnt, hm⟩ := h
  generalize hb : l'.toRawLoan.broker = b at hraw
  have hnt' : b.numericType = l.broker.numericType := by rw [← hb]; exact hnt
  have hm' : b.managementFeeRate = l.broker.managementFeeRate := by rw [← hb]; exact hm
  simp only [Loan.doPayment, hf, Bool.false_eq_true, ↓reduceIte] at hr
  unfold_ter at hr
  walk_ok
  rename_i _ t ht _ p hp _ m hmf hlaw
  obtain ⟨r', h1, -⟩ := RawLoan.to_lawful_twin hlaw b hnt' hm'
  have hd : Loan.doPayment l' pc = .ok r' := by
    unfold Loan.doPayment
    simp only [hf, Bool.false_eq_true, ↓reduceIte]
    rw [hraw]
    simp only [bind, Except.bind, *]
    rfl
  exact ⟨r', hd, Loan.doPayment_twin ⟨by rw [hraw], hnt, hm⟩ pc hr0 hd⟩

/-- Twins pay the same instalments in the loop, and the loans they leave are twins. The pools ride along. -/
private lemma UnsettledPayment.payInstalments_twin {α β : Type} (n : Nat) (amount : Number) :
    ∀ (p : UnsettledPayment α) (q : UnsettledPayment β) (p' : UnsettledPayment α),
      Loan.Twin p.loan q.loan → q.amounts = p.amounts → q.totalPaid = p.totalPaid → q.count = p.count →
      UnsettledPayment.payInstalments p n amount = .ok p' →
      ∃ q', UnsettledPayment.payInstalments q n amount = .ok q' ∧ Loan.Twin p'.loan q'.loan ∧
        q'.amounts = p'.amounts ∧ q'.totalPaid = p'.totalPaid ∧ q'.count = p'.count ∧ q'.pool = q.pool ∧
        q'.scheduledInterest = q.scheduledInterest := by
  induction n with
  | zero =>
    intro p q p' ht ha htp hc h
    rw [UnsettledPayment.payInstalments] at h
    obtain rfl := Except.ok.inj h
    exact ⟨q, by rw [UnsettledPayment.payInstalments]; rfl, ht, ha, htp, hc, rfl, rfl⟩
  | succ n ih =>
    intro p q p' ht ha htp hc h
    have hpr : q.loan.paymentRemaining = p.loan.paymentRemaining := (congrArg RawLoan.paymentRemaining ht.raw :)
    have hfees : q.loan.fees = p.loan.fees := (congrArg RawLoan.fees ht.raw :)
    have hsc := Loan.scheduledComponents_twin ht
    rw [UnsettledPayment.payInstalments] at h ⊢
    unfold_ter at h
    unfold_ter
    simp only [hpr, hsc, hfees, htp, ha, hc]
    walk_ok
    · exact ⟨q, by simp [*], ht, ha, htp, hc, rfl, rfl⟩
    · exact ⟨q, by simp [*], ht, ha, htp, hc, rfl, rfl⟩
    · clear ih
      obtain ⟨r', hr', htw⟩ := Loan.doPayment_twin_ok ht _ ‹Loan.doPayment p.loan _ = _›
      simp only [*] at hr'
      refine ⟨⟨r', q.pool, _, _, p.count + 1, q.scheduledInterest⟩, ?_, htw, rfl, rfl, rfl, rfl, rfl⟩
      simp [*]
    · obtain ⟨r', hr', htw⟩ := Loan.doPayment_twin_ok ht _ ‹Loan.doPayment p.loan _ = _›
      obtain ⟨q', hq', h1, h2, h3, h4, h5, h6⟩ :=
        ih _ ⟨r', q.pool, _, _, p.count + 1, q.scheduledInterest⟩ _ htw
        rfl rfl rfl ‹UnsettledPayment.payInstalments _ n amount = _›
      clear ih
      simp only [*] at hr'
      refine ⟨q', ?_, h1, h2, h3, h4, h5, h6⟩
      simp [*]

/-- Twins pay the same overpayment tail, and the loans they leave are twins. -/
private lemma UnsettledPayment.applyOverpayment_twin {α β : Type} (p : UnsettledPayment α) (q : UnsettledPayment β)
    (amount : Number) (p' : UnsettledPayment α) (ht : Loan.Twin p.loan q.loan) (ha : q.amounts = p.amounts)
    (htp : q.totalPaid = p.totalPaid) (hc : q.count = p.count)
    (h : UnsettledPayment.applyOverpayment p amount = .ok p') :
    ∃ q', UnsettledPayment.applyOverpayment q amount = .ok q' ∧ Loan.Twin p'.loan q'.loan ∧
      q'.amounts = p'.amounts ∧ q'.totalPaid = p'.totalPaid ∧ q'.count = p'.count ∧ q'.pool = q.pool ∧
      q'.scheduledInterest = q.scheduledInterest := by
  have hoc := Loan.overpaymentComponents_twin ht
  have htry := Loan.tryOverpayment_twin ht
  obtain ⟨hraw, hnt, hm⟩ := ht
  generalize hb : q.loan.toRawLoan.broker = b at hraw
  have hnt' : b.numericType = p.loan.broker.numericType := by rw [← hb]; exact hnt
  have hm' : b.managementFeeRate = p.loan.broker.managementFeeRate := by rw [← hb]; exact hm
  have ht : Loan.Twin p.loan q.loan := ⟨by rw [hraw], hnt, hm⟩
  simp only [UnsettledPayment.applyOverpayment] at h ⊢
  unfold_ter at h
  unfold_ter
  rw [hraw]
  simp only [hoc, htry, hnt', htp, hc, ha]
  walk_ok
  · exact ⟨q, by simp [*], ht, ha, htp, hc, rfl, rfl⟩
  · exact ⟨q, by simp [*], ht, ha, htp, hc, rfl, rfl⟩
  · exact ⟨q, by simp [*], ht, ha, htp, hc, rfl, rfl⟩
  · have hlaw := ‹RawLoan.to_lawful _ = Except.ok _›
    obtain ⟨r', h1, htw⟩ := RawLoan.to_lawful_twin hlaw b hnt' hm'
    simp only at h1
    refine ⟨⟨r', q.pool, _, p.totalPaid, p.count, q.scheduledInterest⟩, ?_, htw, rfl, rfl, rfl, rfl, rfl⟩
    simp [*]
  · exact ⟨q, by simp [*], ht, ha, htp, hc, rfl, rfl⟩

/-- Twins pay the same single instalment. -/
private lemma Loan.payInstalment_twin {l l' : Loan} (ht : Loan.Twin l l') (v v' : Vault) (pc : PaymentComponents)
    (amount : Number) (p : UnsettledPayment Vault) (h : (l.payInstalment v pc amount).run = .ok (.ok p)) :
    ∃ p', (l'.payInstalment v' pc amount).run = .ok (.ok p') ∧ Loan.Twin p.loan p'.loan ∧
      p'.amounts = p.amounts ∧ p'.totalPaid = p.totalPaid ∧ p'.count = p.count ∧ p'.pool = v' ∧
      p'.scheduledInterest = p.scheduledInterest := by
  have hid := ht.interestDue
  simp only [Loan.payInstalment] at h ⊢
  unfold_ter at h
  unfold_ter
  walk_ok
  obtain ⟨r', hr', htw⟩ := Loan.doPayment_twin_ok ht _ ‹Loan.doPayment l _ = _›
  exact ⟨⟨r', v', _, _, 1, _⟩, by simp [*], htw, rfl, rfl, rfl, rfl, rfl⟩

/-- Twins stay twins without the impaired flag. -/
private lemma Loan.Twin.unimpaired {l l' : Loan} (h : Loan.Twin l l') : Loan.Twin l.unimpaired l'.unimpaired :=
  ⟨by show ({ l'.toRawLoan with isImpaired := false } : RawLoan) = _; rw [h.raw]; rfl, h.numericType,
    h.managementFeeRate⟩

/-- What twins share for a payment: the payment checks, and the interestDue without the impaired flag. -/
private lemma Loan.Twin.pay_fields {l l' : Loan} (ht : Loan.Twin l l') :
    l'.paymentRemaining = l.paymentRemaining ∧ l'.principalOutstanding = l.principalOutstanding ∧
      l'.nextPaymentDueDate = l.nextPaymentDueDate ∧ l'.unimpaired.interestDue = l.unimpaired.interestDue ∧
      (∀ now, l'.isPaymentLate now = l.isPaymentLate now) := by
  have hraw := ht.raw
  have hnd : l'.nextPaymentDueDate = l.nextPaymentDueDate := (congrArg RawLoan.nextPaymentDueDate hraw :)
  exact ⟨(congrArg RawLoan.paymentRemaining hraw :), (congrArg RawLoan.principalOutstanding hraw :), hnd,
    ht.unimpaired.interestDue, fun now => by unfold Loan.isPaymentLate; rw [hnd]⟩

/-- Twins pay the same regular instalments. -/
private lemma Loan.payRegular_twin {l l' : Loan} (ht : Loan.Twin l l') (v v' v1' : Vault) (amount : Number)
    (now : UInt32) (p : UnsettledPayment Vault)
    (hu : Loan.unimpairIfImpaired l' v' = .ok (.ok { loan' := l'.unimpaired, pool' := v1' }))
    (h : (l.payInstalments v .regular amount now).run = .ok (.ok p)) :
    ∃ p', (l'.payInstalments v' .regular amount now).run = .ok (.ok p') ∧ Loan.Twin p.loan p'.loan ∧
      p'.amounts = p.amounts ∧ p'.totalPaid = p.totalPaid ∧ p'.count = p.count ∧ p'.pool = v1' ∧
      p'.scheduledInterest = p.scheduledInterest := by
  have hchk := (Loan.payInstalments_ok l v .regular amount now p h).1
  obtain ⟨hpr, hpo, hnd, hid, hlt⟩ := ht.pay_fields
  obtain ⟨si, hsi, hloop, hcnt⟩ := Loan.payScheduled_loop l v amount now p h
  obtain ⟨q, hq, htw, ha, htp, hc, hpool, hsiq⟩ := UnsettledPayment.payInstalments_twin
    maxPaymentsPerTransaction amount ⟨l.unimpaired, p.pool, PaymentAmounts.zero, Number.zero, 0, si⟩
    ⟨l'.unimpaired, v1', PaymentAmounts.zero, Number.zero, 0, si⟩ p ht.unimpaired rfl rfl rfl hloop
  have hsi' : si = p.scheduledInterest := by
    have := (Loan.payInstalments_ok l v .regular amount now p h).2.2.2.1
    rw [hsi] at this; exact Except.ok.inj this
  refine ⟨q, ?_, htw, ha, htp, hc, hpool, hsiq.trans hsi'⟩
  have hlate : l'.isPaymentLate now = false := by
    rw [hlt]; unfold Loan.isPaymentLate; exact decide_eq_false (hchk.not_late (by decide))
  have hqc : (q.count == 0) = false := by rw [hc]; simpa using hcnt
  simp only [Loan.payInstalments, Loan.payScheduledInstalments]
  unfold_ter
  rw [hpr, hpo, hnd, Loan.not_paid_off l hchk.remaining hchk.principal, Loan.nextPaymentDueDate_ne_zero l hchk.due]
  simp only [hlate, hu, hid, Loan.interestDue_unimpaired, hsi, hq, hqc, Bool.false_eq_true, ↓reduceIte]

/-- Twins pay the same instalments when the unimpair of the second passes on its vault. The amounts, the
total, the count and the interestDue before the payment are the same, and the paid loans are twins. -/
lemma Loan.payInstalments_twin {l l' : Loan} (ht : Loan.Twin l l') (v v' v1' : Vault) (pt : LoanPaymentType)
    (amount : Number) (now : UInt32) (p : UnsettledPayment Vault)
    (hu : (Loan.unimpairIfImpaired l' v').run = .ok (.ok { loan' := l'.unimpaired, pool' := v1' }))
    (h : (l.payInstalments v pt amount now).run = .ok (.ok p)) :
    ∃ p', (l'.payInstalments v' pt amount now).run = .ok (.ok p') ∧ Loan.Twin p.loan p'.loan ∧
      p'.amounts = p.amounts ∧ p'.totalPaid = p.totalPaid ∧ p'.count = p.count ∧ p'.pool = v1' ∧
      p'.scheduledInterest = p.scheduledInterest := by
  have hchk := (Loan.payInstalments_ok l v pt amount now p h).1
  obtain ⟨hpr, hpo, hnd, hid, hlt⟩ := ht.pay_fields
  simp only [ExceptT.run] at hu
  cases pt
  · exact Loan.payRegular_twin ht v v' v1' amount now p hu h
  · have hlate : l'.isPaymentLate now = true := by
      rw [hlt]; unfold Loan.isPaymentLate; exact decide_eq_true (hchk.date.mp rfl)
    simp only [Loan.payInstalments] at h ⊢
    unfold_ter at h
    unfold_ter
    rw [hpr, hpo, hnd, Loan.not_paid_off l hchk.remaining hchk.principal, Loan.nextPaymentDueDate_ne_zero l hchk.due]
    simp only [hlate, hu, Bool.false_eq_true, ↓reduceIte, Bool.not_true]
    walk_ok
    rename_i a hua _ _ pc hpc _ hpi
    have hal := Loan.unimpairIfImpaired_loan l v a (by simp only [ExceptT.run]; exact hua)
    rw [hal] at hpc hpi
    obtain ⟨p', hp', htw, h1, h2, h3, h4, h5⟩ := Loan.payInstalment_twin ht.unimpaired a.pool' v1' pc amount p hpi
    refine ⟨p', ?_, htw, h1, h2, h3, h4, h5⟩
    rw [Loan.lateComponents_twin ht.unimpaired, hpc]
    simpa [ExceptT.run] using hp'
  · have hlate : l'.isPaymentLate now = false := by
      rw [hlt]; unfold Loan.isPaymentLate; exact decide_eq_false (hchk.not_late (by decide))
    have hone := hchk.more_than_one
    simp only [Loan.payInstalments] at h ⊢
    unfold_ter at h
    unfold_ter
    rw [hpr, hpo, hnd, Loan.not_paid_off l hchk.remaining hchk.principal, Loan.nextPaymentDueDate_ne_zero l hchk.due]
    simp only [hlate, hu, hone, Bool.false_eq_true, ↓reduceIte]
    walk_ok
    rename_i a hua _ _ pc hpc _ hpi
    have hal := Loan.unimpairIfImpaired_loan l v a (by simp only [ExceptT.run]; exact hua)
    rw [hal] at hpc hpi
    obtain ⟨p', hp', htw, h1, h2, h3, h4, h5⟩ := Loan.payInstalment_twin ht.unimpaired a.pool' v1' pc amount p hpi
    refine ⟨p', ?_, htw, h1, h2, h3, h4, h5⟩
    rw [Loan.fullComponents_twin ht.unimpaired, hpc]
    simpa [ExceptT.run] using hp'
  · rw [Loan.overPayInstalments_run] at h
    rcases h0 : (l.payInstalments v .regular amount now).run with e | t | p0
    · rw [h0] at h; cases h
    · rw [h0] at h; cases h
    rw [h0] at h
    simp only at h
    obtain ⟨p1, h1⟩ : ∃ p1, UnsettledPayment.applyOverpayment p0 amount = .ok p1 ∧ p1 = p := by
      revert h
      cases UnsettledPayment.applyOverpayment p0 amount with
      | error e => intro h; cases h
      | ok p1 => intro h; exact ⟨p1, rfl, by injection h with h; injection h⟩
    obtain ⟨h1, rfl⟩ := h1
    obtain ⟨q0, hq0, htw0, ha0, htp0, hc0, hpool0, hsi0⟩ := Loan.payRegular_twin ht v v' v1' amount now p0 hu h0
    obtain ⟨q, hq, htw, ha, htp, hc, hpool, hsi⟩ := UnsettledPayment.applyOverpayment_twin p0 q0 amount p1 htw0 ha0
      htp0 hc0 h1
    have hsp := (UnsettledPayment.applyOverpayment_sameTerms p0 p1 amount h1)
    refine ⟨q, ?_, htw, ha, htp, hc, by rw [hpool, hpool0], by rw [hsi, hsi0, hsp.2.2.1]⟩
    rw [Loan.overPayInstalments_run, hq0]
    simp [hq, Except.map]

end XRPL.Model.Lending
