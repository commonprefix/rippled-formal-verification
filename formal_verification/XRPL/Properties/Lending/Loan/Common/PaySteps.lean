import XRPL.Properties.Lending.Loan.Common.PayExits
import XRPL.Properties.Lending.Loan.Common.SetUpdates

/-! # What a successful payment computed

Read-back lemmas for a payment that passes: the instalments it paid, the loan they leave, and the
amounts the settlement computed. -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault (Vault RawVault)

open private Loan.scheduledComponents Loan.lateComponents Loan.fullComponents Loan.unimpairIfImpaired
  Loan.payScheduledInstalments UnsettledPayment.applyOverpayment UnsettledPayment.payInstalments
  Loan.doPayment Loan.settlePayment validatePostPayment
  from XRPL.Model.Lending.Loan.LoanPay

/-- A passing step passes its value on. -/
private lemma TerExcept.bind_ok {α β : Type} (x : TerExcept α) (f : α → TerExcept β) (b : β)
    (h : (x >>= f).run = .ok (.ok b)) : ∃ a, x.run = .ok (.ok a) ∧ (f a).run = .ok (.ok b) := by
  simp only [ExceptT.run, bind, ExceptT.bind, ExceptT.mk, ExceptT.bindCont, Except.bind] at h ⊢
  rcases hx : x with e | t' | a
  · rw [hx] at h; exact absurd h (by simp)
  · rw [hx] at h; exact absurd h (by simp)
  · rw [hx] at h; exact ⟨a, rfl, h⟩

lemma Loan.pay_ok (loan : Loan) (v : Vault) (pt : LoanPaymentType) (amount : Number) (now : UInt32)
    (r : LoanWithAmounts Vault) (h : (loan.pay v pt amount now).run = .ok (.ok r)) :
    ∃ p, (loan.payInstalments v pt amount now).run = .ok (.ok p) ∧
      (Loan.settlePayment p.loan p.pool p.amounts p.scheduledInterest).run = .ok (.ok r) := by
  rw [Loan.pay_run] at h
  exact TerExcept.bind_ok _ _ r h

private lemma validatePostPayment_ok (v : Vault) (r0 r : LoanWithAmounts Vault)
    (h : validatePostPayment v r0 = .ok (.ok r)) : r = r0 := by
  simp only [validatePostPayment] at h
  unfold_ter at h
  walk_ok
  rfl

/-- A settlement that passes computed its amounts, updated the vault and the broker, and put the paid
loan on the updated broker. -/
lemma UnsettledPayment.settle_ok (p : UnsettledPayment Vault) (r : LoanWithAmounts Vault)
    (h : (Loan.settlePayment p.loan p.pool p.amounts p.scheduledInterest).run = .ok (.ok r)) :
    ∃ toPool yieldDelta toBroker cover' debtTotal' raw broker',
      p.SettleSums toPool yieldDelta toBroker cover' debtTotal' ∧
      (p.pool.adjustBalances (p.change toPool yieldDelta)).run = .ok (.ok raw) ∧ raw.to_lawful = .ok r.pool' ∧
      ({ p.loan.broker.toRawLoanBroker with debtTotal := debtTotal', coverAvailable := cover' }
        : RawLoanBroker).to_lawful = .ok broker' ∧
      ({ p.loan.toRawLoan with broker := broker' } : RawLoan).to_lawful = .ok r.loan' ∧
      r.amountToPool = toPool ∧ r.amountToBroker = toBroker := by
  simp only [Loan.settlePayment] at h
  unfold_ter at h
  walk_ok
  all_goals
    obtain ⟨raw, hraw, hlaw⟩ := Vault.poolAdjust_ok_inv _ _ _ ‹AssetPool.adjustBalances _ _ = _›
    obtain rfl := validatePostPayment_ok _ _ _ ‹validatePostPayment _ _ = _›
    simp only [Vault.pool_baseExponent, Vault.pool_amounts] at *
  · refine ⟨_, _, _, _, _, raw, _, ⟨Bool.eq_false_iff.mpr ‹¬(_ || _ || _) = true›, ⟨_, ‹_›, ‹_›⟩, ⟨_, _, ‹_›, ‹_›, ‹_›⟩,
      Or.inr ⟨?_, _, ‹_›, ‹_›, ‹_›⟩, ‹_›⟩,
      hraw, hlaw, ‹_›, ‹_›, rfl, rfl⟩
    have h := ‹(!_) = true›
    simp only [Bool.not_eq_true'] at h
    subst h; assumption
  · refine ⟨_, _, _, _, _, raw, _, ⟨Bool.eq_false_iff.mpr ‹¬(_ || _ || _) = true›, ⟨_, ‹_›, ‹_›⟩, ⟨_, _, ‹_›, ‹_›, ‹_›⟩,
      Or.inl ⟨?_, rfl, rfl⟩, ‹_›⟩,
      hraw, hlaw, ‹_›, ‹_›, rfl, rfl⟩
    have h := ‹¬(!_) = true›
    simp only [Bool.not_eq_true', Bool.not_eq_false] at h
    subst h; assumption

/-- Two loans with the same broker and terms. The outstanding amounts, PeriodicPayment, the schedule position and
the pending and defaulted flags may differ. -/
structure Loan.SameTerms (l l' : Loan) : Prop where
  broker : l'.broker = l.broker
  rates : l'.rates = l.rates
  fees : l'.fees = l.fees
  schedule : l'.schedule = l.schedule
  loanScale : l'.loanScale = l.loanScale
  isImpaired : l'.isImpaired = l.isImpaired
  allowsOverpayment : l'.allowsOverpayment = l.allowsOverpayment

lemma Loan.SameTerms.refl (l : Loan) : Loan.SameTerms l l := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

lemma Loan.SameTerms.trans {l l' l'' : Loan} (h1 : Loan.SameTerms l l') (h2 : Loan.SameTerms l' l'') :
    Loan.SameTerms l l'' :=
  ⟨h2.broker.trans h1.broker, h2.rates.trans h1.rates, h2.fees.trans h1.fees, h2.schedule.trans h1.schedule,
    h2.loanScale.trans h1.loanScale, h2.isImpaired.trans h1.isImpaired,
    h2.allowsOverpayment.trans h1.allowsOverpayment⟩

/-- Advancing the loan by one instalment keeps its broker and terms. -/
lemma Loan.doPayment_sameTerms (l l' : Loan) (pc : PaymentComponents) (h : Loan.doPayment l pc = .ok l') :
    Loan.SameTerms l l' := by
  simp only [Loan.doPayment] at h
  split at h
  · unfold_ter at h
    walk_ok
    have h1 := (RawLoan.to_lawful_ok ‹_›).1
    exact ⟨(congrArg RawLoan.broker h1 :), (congrArg RawLoan.rates h1 :), (congrArg RawLoan.fees h1 :),
      (congrArg RawLoan.schedule h1 :), (congrArg RawLoan.loanScale h1 :), (congrArg RawLoan.isImpaired h1 :),
      (congrArg RawLoan.allowsOverpayment h1 :)⟩
  · unfold_ter at h
    walk_ok
    have h1 := (RawLoan.to_lawful_ok ‹_›).1
    exact ⟨(congrArg RawLoan.broker h1 :), (congrArg RawLoan.rates h1 :), (congrArg RawLoan.fees h1 :),
      (congrArg RawLoan.schedule h1 :), (congrArg RawLoan.loanScale h1 :), (congrArg RawLoan.isImpaired h1 :),
      (congrArg RawLoan.allowsOverpayment h1 :)⟩

/-- The instalment loop keeps the broker, the terms, the pool and the interestDue before the payment. -/
private lemma UnsettledPayment.payInstalments_sameTerms {α : Type} (payment : UnsettledPayment α) (n : Nat)
    (amount : Number) (p' : UnsettledPayment α) (h : UnsettledPayment.payInstalments payment n amount = .ok p') :
    Loan.SameTerms payment.loan p'.loan ∧ p'.pool = payment.pool ∧
      p'.scheduledInterest = payment.scheduledInterest ∧ payment.count ≤ p'.count := by
  induction n generalizing payment with
  | zero =>
    rw [UnsettledPayment.payInstalments] at h
    obtain rfl := Except.ok.inj h
    exact ⟨Loan.SameTerms.refl _, rfl, rfl, le_refl _⟩
  | succ n ih =>
    rw [UnsettledPayment.payInstalments] at h
    unfold_ter at h
    walk_ok
    all_goals first
      | exact ⟨Loan.SameTerms.refl _, rfl, rfl, le_refl _⟩
      | exact ⟨Loan.doPayment_sameTerms _ _ _ ‹_›, rfl, rfl, Nat.le_succ _⟩
      | (obtain ⟨h1, h2, h3, h4⟩ := ih _ ‹_›
         exact ⟨(Loan.doPayment_sameTerms _ _ _ ‹_›).trans h1, h2, h3, le_trans (Nat.le_succ _) h4⟩)

/-- The overpayment tail keeps the broker, the terms, the schedule position, the pool and the instalment
count. -/
lemma UnsettledPayment.applyOverpayment_sameTerms (payment p' : UnsettledPayment Vault) (amount : Number)
    (h : UnsettledPayment.applyOverpayment payment amount = .ok p') :
    Loan.SameTerms payment.loan p'.loan ∧ p'.pool = payment.pool ∧
      p'.scheduledInterest = payment.scheduledInterest ∧ p'.count = payment.count ∧
      p'.loan.paymentRemaining = payment.loan.paymentRemaining ∧
      p'.loan.nextPaymentDueDate = payment.loan.nextPaymentDueDate := by
  simp only [UnsettledPayment.applyOverpayment] at h
  unfold_ter at h
  walk_ok
  all_goals first
    | exact ⟨Loan.SameTerms.refl _, rfl, rfl, rfl, rfl, rfl⟩
    | (have h1 := (RawLoan.to_lawful_ok ‹RawLoan.to_lawful _ = Except.ok _›).1
       refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, rfl, rfl, rfl, ?_, ?_⟩
       · exact (congrArg RawLoan.broker h1 :)
       · exact (congrArg RawLoan.rates h1 :)
       · exact (congrArg RawLoan.fees h1 :)
       · exact (congrArg RawLoan.schedule h1 :)
       · exact (congrArg RawLoan.loanScale h1 :)
       · exact (congrArg RawLoan.isImpaired h1 :)
       · exact (congrArg RawLoan.allowsOverpayment h1 :)
       · exact (congrArg RawLoan.paymentRemaining h1 :)
       · exact (congrArg RawLoan.nextPaymentDueDate h1 :))

/-- An unimpair that passes hands on the loan without the impaired flag. -/
private lemma Loan.unimpairIfImpaired_loan (loan : Loan) (v : Vault) (r : LoanWithPool Vault)
    (h : (Loan.unimpairIfImpaired loan v).run = .ok (.ok r)) : r.loan' = loan.unimpaired := by
  cases himp : loan.isImpaired
  · rw [Loan.unimpairIfImpaired_not loan v himp] at h
    obtain rfl : { loan' := loan, pool' := v } = r := by injection h with h; injection h
    exact (Loan.unimpaired_of_not loan himp).symm
  · rw [Loan.unimpairIfImpaired_impaired loan v himp] at h
    split at h
    · cases h
    · cases h
    · obtain rfl : { loan' := loan.unimpaired, pool' := _ } = r := by injection h with h; injection h
      rfl

private lemma Loan.payChecks_of (loan : Loan) (pt : LoanPaymentType) (now : UInt32)
    (h1 : ¬(loan.paymentRemaining == 0 || loan.principalOutstanding.operator_eq Number.zero) = true)
    (hdue : ¬(loan.nextPaymentDueDate == 0) = true)
    (hdate : pt = .late ↔ loan.nextPaymentDueDate < now) (hfull : pt = .full → loan.paymentRemaining ≠ 1) :
    loan.PayChecks pt now := by
  have h1' : ¬(loan.paymentRemaining = 0 ∨ loan.principalOutstanding = Number.zero) := fun h =>
    h1 ((Loan.paid_off_iff loan).mpr h)
  exact ⟨fun h => h1' (Or.inl h), fun h => h1' (Or.inr h), by simpa using hdue, hdate, hfull⟩

/-- The unimpair and the loop of the scheduled instalments, read back from a passing payment. -/
private lemma Loan.scheduled_ok (loan : Loan) (v : Vault) (amount : Number) (p : UnsettledPayment Vault)
    (a : LoanWithPool Vault) (si : Number)
    (hu : Loan.unimpairIfImpaired loan v = .ok (.ok a)) (hi : a.loan'.interestDue = .ok si)
    (hloop : UnsettledPayment.payInstalments
      { loan := a.loan', pool := a.pool', amounts := PaymentAmounts.zero, totalPaid := Number.zero, count := 0,
        scheduledInterest := si } maxPaymentsPerTransaction amount = .ok p)
    (hc : ¬(p.count == 0) = true) :
    (Loan.unimpairIfImpaired loan v).run = .ok (.ok { loan' := loan.unimpaired, pool' := p.pool }) ∧
      Loan.SameTerms loan.unimpaired p.loan ∧ loan.interestDue = .ok p.scheduledInterest ∧ 1 ≤ p.count := by
  obtain ⟨hst, hpool, hsi, -⟩ := UnsettledPayment.payInstalments_sameTerms _ _ _ _ hloop
  have hl := Loan.unimpairIfImpaired_loan loan v a (by simp only [ExceptT.run]; exact hu)
  simp only at hpool hsi hst
  rw [hl] at hst hi
  refine ⟨?_, hst, by rw [hsi]; exact hi, ?_⟩
  · simp only [ExceptT.run]
    rw [hu, hpool, ← hl]
  · simp only [beq_iff_eq] at hc; omega

/-- The scheduled instalments that pass, read back. -/
private lemma Loan.payScheduled_ok (loan : Loan) (v : Vault) (amount : Number) (now : UInt32)
    (p : UnsettledPayment Vault) (h : (Loan.payScheduledInstalments loan v amount now).run = .ok (.ok p)) :
    (¬(loan.paymentRemaining == 0 || loan.principalOutstanding.operator_eq Number.zero) = true ∧
      ¬(loan.nextPaymentDueDate == 0) = true ∧ ¬ loan.nextPaymentDueDate < now) ∧
      (Loan.unimpairIfImpaired loan v).run = .ok (.ok { loan' := loan.unimpaired, pool' := p.pool }) ∧
      Loan.SameTerms loan.unimpaired p.loan ∧ loan.interestDue = .ok p.scheduledInterest ∧ 1 ≤ p.count := by
  simp only [Loan.payScheduledInstalments] at h
  unfold_ter at h
  walk_ok
  have hnl : ¬ loan.nextPaymentDueDate < now := by
    simpa [Loan.isPaymentLate] using ‹¬loan.isPaymentLate now = true›
  exact ⟨⟨‹_›, ‹¬(loan.nextPaymentDueDate == 0) = true›, hnl⟩, Loan.scheduled_ok loan v amount p _ _ ‹_› ‹_› ‹_› ‹_›⟩

/-- A payment's instalments that pass: the loan passed the checks and the unimpair, and the paid loan keeps
the broker and the terms. -/
lemma Loan.payInstalments_ok (loan : Loan) (v : Vault) (pt : LoanPaymentType) (amount : Number) (now : UInt32)
    (p : UnsettledPayment Vault) (h : (loan.payInstalments v pt amount now).run = .ok (.ok p)) :
    loan.PayChecks pt now ∧
      (Loan.unimpairIfImpaired loan v).run = .ok (.ok { loan' := loan.unimpaired, pool' := p.pool }) ∧
      Loan.SameTerms loan.unimpaired p.loan ∧ loan.interestDue = .ok p.scheduledInterest ∧ 1 ≤ p.count := by
  cases pt
  · obtain ⟨⟨h1, hd, hnl⟩, hrest⟩ := Loan.payScheduled_ok loan v amount now p h
    exact ⟨Loan.payChecks_of loan _ now h1 hd ⟨(fun h => by cases h), (fun h => absurd h hnl)⟩
      (fun h => by cases h), hrest⟩
  · simp only [Loan.payInstalments, Loan.payInstalment] at h
    unfold_ter at h
    walk_ok
    have hl : loan.nextPaymentDueDate < now := by
      have h := ‹¬(!loan.isPaymentLate now) = true›
      simpa [Loan.isPaymentLate] using h
    refine ⟨Loan.payChecks_of loan _ now ‹_› ‹¬(loan.nextPaymentDueDate == 0) = true›
      ⟨(fun _ => hl), (fun _ => rfl)⟩ (fun h => by cases h), ?_⟩
    have hu := Loan.unimpairIfImpaired_loan loan v _
      (by simp only [ExceptT.run]; exact ‹Loan.unimpairIfImpaired loan v = _›)
    have hst := Loan.doPayment_sameTerms _ _ _ ‹Loan.doPayment _ _ = _›
    rw [hu] at hst
    refine ⟨?_, hst, by rw [← Loan.interestDue_unimpaired, ← hu]; assumption, le_refl _⟩
    simp only [ExceptT.run]
    rw [‹Loan.unimpairIfImpaired loan v = _›, ← hu]
  · simp only [Loan.payInstalments, Loan.payInstalment] at h
    unfold_ter at h
    walk_ok
    have hnl : ¬ loan.nextPaymentDueDate < now := by
      simpa [Loan.isPaymentLate] using ‹¬loan.isPaymentLate now = true›
    have hr : loan.paymentRemaining ≠ 0 := fun h0 =>
      ‹¬(loan.paymentRemaining == 0 || loan.principalOutstanding.operator_eq Number.zero) = true›
        ((Loan.paid_off_iff loan).mpr (Or.inl h0))
    have h1 : loan.paymentRemaining ≠ 1 := by
      intro h1; apply ‹¬loan.paymentRemaining ≤ 1›; rw [h1]; decide
    refine ⟨Loan.payChecks_of loan _ now ‹_› ‹¬(loan.nextPaymentDueDate == 0) = true›
      ⟨(fun h => by cases h), (fun h => absurd h hnl)⟩
      (fun _ => h1), ?_⟩
    have hu := Loan.unimpairIfImpaired_loan loan v _
      (by simp only [ExceptT.run]; exact ‹Loan.unimpairIfImpaired loan v = _›)
    have hst := Loan.doPayment_sameTerms _ _ _ ‹Loan.doPayment _ _ = _›
    rw [hu] at hst
    refine ⟨?_, hst, by rw [← Loan.interestDue_unimpaired, ← hu]; assumption, le_refl _⟩
    simp only [ExceptT.run]
    rw [‹Loan.unimpairIfImpaired loan v = _›, ← hu]
  · simp only [Loan.payInstalments] at h
    obtain ⟨p0, h0, h1⟩ := TerExcept.bind_ok _ _ p h
    obtain ⟨⟨hc, hd, hnl⟩, hu, hst, hi, hn⟩ := Loan.payScheduled_ok loan v amount now p0 h0
    simp only [ExceptT.run, liftM, monadLift, MonadLift.monadLift, MonadLiftT.monadLift, ExceptT.lift, ExceptT.mk,
      Functor.map, Except.map] at h1
    split at h1
    · cases h1
    · rename_i p' hp'
      obtain rfl : p' = p := by injection h1 with h1; injection h1
      obtain ⟨hst', hpool, hsi, hcount, -, -⟩ := UnsettledPayment.applyOverpayment_sameTerms _ _ _ hp'
      refine ⟨Loan.payChecks_of loan _ now hc hd ⟨(fun h => by cases h), (fun h => absurd h hnl)⟩ (fun h => by cases h),
        by rw [hpool]; exact hu, hst.trans hst', by rw [hsi]; exact hi, by rw [hcount]; exact hn⟩

/-- An overpayment's instalments that pass: the scheduled instalments, then the overpayment tail. -/
lemma Loan.overPayInstalments_ok (loan : Loan) (v : Vault) (amount : Number) (now : UInt32)
    (p : UnsettledPayment Vault) (h : (loan.payInstalments v .overpayment amount now).run = .ok (.ok p)) :
    ∃ p0, (loan.payInstalments v .regular amount now).run = .ok (.ok p0) ∧
      UnsettledPayment.applyOverpayment p0 amount = .ok p := by
  simp only [Loan.payInstalments] at h
  obtain ⟨p0, h0, h1⟩ := TerExcept.bind_ok _ _ p h
  simp only [ExceptT.run, liftM, monadLift, MonadLift.monadLift, MonadLiftT.monadLift, ExceptT.lift, ExceptT.mk,
    Functor.map, Except.map] at h1
  split at h1
  · cases h1
  rename_i p' hp'
  obtain rfl : p' = p := by injection h1 with h1; injection h1
  exact ⟨p0, h0, hp'⟩

/-- The vault update keeps the asset and the scale, so the base exponent. -/
private lemma Vault.poolAdjust_baseExponent (v v' : Vault) (c : PoolBalanceChange)
    (h : AssetPool.adjustBalances v c = .ok (.ok v')) : v'.baseExponent = v.baseExponent := by
  obtain ⟨raw, hadj, hv'⟩ := Vault.poolAdjust_ok_inv v c v' h
  simp only [ExceptT.run, XRPL.Model.SingleAssetVault.Vault.adjustBalances] at hadj
  unfold_ter at hadj
  walk_ok
  have h1 := (RawVault.to_lawful_ok hv').1
  simp only [XRPL.Model.SingleAssetVault.Vault.baseExponent]
  rw [show v'.numericType = v'.toRawVault.numericType from rfl, show v'.scale = v'.toRawVault.scale from rfl, h1]

/-- The unimpair keeps the vault's base exponent. -/
lemma Loan.unimpairIfImpaired_baseExponent (loan : Loan) (v v1 : Vault) (l1 : Loan)
    (h : (Loan.unimpairIfImpaired loan v).run = .ok (.ok { loan' := l1, pool' := v1 })) :
    v1.baseExponent = v.baseExponent := by
  cases himp : loan.isImpaired
  · rw [Loan.unimpairIfImpaired_not loan v himp] at h
    obtain rfl : v = v1 := by injection h with h; injection h with h; injection h
    rfl
  · rw [Loan.unimpairIfImpaired_impaired loan v himp] at h
    split at h
    · cases h
    · cases h
    · rename_i v2 hadj
      obtain rfl : v2 = v1 := by injection h with h; injection h with h; injection h
      exact Vault.poolAdjust_baseExponent v v2 _ hadj

variable (loan : Loan) (v : Vault) (amount : Number) (now : UInt32)

/-- The last instalment clears the whole outstanding value. -/
lemma Loan.scheduledComponents_final (l : Loan) (pc : PaymentComponents) (pp' : Number)
    (hpp : STAmount.roundToNumericType l.broker.numericType l.periodicPayment .upward (some l.loanScale) = .ok pp')
    (hfinal : l.paymentRemaining = 1 ∨ l.totalValueOutstanding.operator_le pp' = true)
    (h : Loan.scheduledComponents l = .ok pc) :
    pc = { totalValueDelta := l.totalValueOutstanding, principalDelta := l.principalOutstanding,
           managementFeeDelta := l.managementFeeOutstanding, isFinal := true } := by
  have hc : (l.paymentRemaining == 1 || l.totalValueOutstanding.operator_le pp') = true := by
    rcases hfinal with h1 | h1 <;> simp [h1]
  unfold Loan.scheduledComponents at h
  simp only [bind, Except.bind] at h
  split at h
  · cases h
  · simp only [hpp, hc, ↓reduceIte, pure, Except.pure] at h
    exact (Except.ok.inj h).symm

private lemma Loan.scheduled_loop (loan : Loan) (v : Vault) (amount : Number) (p : UnsettledPayment Vault)
    (a : LoanWithPool Vault) (si : Number)
    (hu : Loan.unimpairIfImpaired loan v = .ok (.ok a)) (hi : a.loan'.interestDue = .ok si)
    (hloop : UnsettledPayment.payInstalments
      { loan := a.loan', pool := a.pool', amounts := PaymentAmounts.zero, totalPaid := Number.zero, count := 0,
        scheduledInterest := si } maxPaymentsPerTransaction amount = .ok p)
    (hc : ¬(p.count == 0) = true) :
    ∃ si, loan.interestDue = .ok si ∧
      UnsettledPayment.payInstalments
        { loan := loan.unimpaired, pool := p.pool, amounts := PaymentAmounts.zero, totalPaid := Number.zero,
          count := 0, scheduledInterest := si } maxPaymentsPerTransaction amount = .ok p ∧ p.count ≠ 0 := by
  have hl := Loan.unimpairIfImpaired_loan loan v a (by simp only [ExceptT.run]; exact hu)
  obtain ⟨-, hpool, -, -⟩ := UnsettledPayment.payInstalments_sameTerms _ _ _ _ hloop
  obtain ⟨l, pool⟩ := a
  simp only at hl hpool hi hloop
  subst hl
  rw [← hpool] at hloop
  exact ⟨si, hi, hloop, by simpa using hc⟩

/-- The scheduled instalments that pass ran the loop on the loan without the impaired flag. -/
lemma Loan.payScheduled_loop (loan : Loan) (v : Vault) (amount : Number) (now : UInt32)
    (p : UnsettledPayment Vault) (h : (Loan.payScheduledInstalments loan v amount now).run = .ok (.ok p)) :
    ∃ si, loan.interestDue = .ok si ∧
      UnsettledPayment.payInstalments
        { loan := loan.unimpaired, pool := p.pool, amounts := PaymentAmounts.zero, totalPaid := Number.zero,
          count := 0, scheduledInterest := si } maxPaymentsPerTransaction amount = .ok p ∧ p.count ≠ 0 := by
  simp only [Loan.payScheduledInstalments] at h
  unfold_ter at h
  walk_ok
  exact Loan.scheduled_loop loan v amount p _ _ ‹_› ‹_› ‹_› ‹_›

/-- When the next instalment is the last, the loop stops before it or pays the loan off. -/
lemma UnsettledPayment.payInstalments_first_final {α : Type} (payment p' : UnsettledPayment α) (n : Nat)
    (amount : Number)
    (pc : PaymentComponents) (hpc : Loan.scheduledComponents payment.loan = .ok pc) (hf : pc.isFinal = true)
    (h : UnsettledPayment.payInstalments payment (n + 1) amount = .ok p') :
    p' = payment ∨ p'.loan.paymentRemaining = 0 := by
  rw [UnsettledPayment.payInstalments] at h
  unfold_ter at h
  simp only [hpc] at h
  walk_ok
  · exact Or.inl rfl
  · exact Or.inl rfl
  · exact Or.inr (Loan.doPayment_final _ _ _ hf ‹_›)
  · exact absurd hf ‹_›

/-- An instalment that isn't the last takes one payment off the loan and moves its due date one interval on. -/
lemma Loan.doPayment_notFinal (l l' : Loan) (pc : PaymentComponents) (hf : pc.isFinal = false)
    (h : Loan.doPayment l pc = .ok l') :
    l'.paymentRemaining = l.paymentRemaining - 1 ∧
      l'.nextPaymentDueDate = l.nextPaymentDueDate + l.schedule.paymentInterval := by
  simp only [Loan.doPayment, hf, Bool.false_eq_true, ↓reduceIte] at h
  unfold_ter at h
  walk_ok
  have h1 := (RawLoan.to_lawful_ok ‹_›).1
  exact ⟨(congrArg RawLoan.paymentRemaining h1 :), (congrArg RawLoan.nextPaymentDueDate h1 :)⟩

/-- The late instalments read the amount only in the amount check. -/
lemma Loan.latePayInstalments_amount (pc : PaymentComponents) (totalDue a b : Number)
    (hpc : Loan.lateComponents loan now = .ok pc) (hdue : pc.totalDue = .ok totalDue)
    (ha : a.operator_lt totalDue = false) (hb : b.operator_lt totalDue = false) :
    (loan.payInstalments v .late a now).run = (loan.payInstalments v .late b now).run := by
  simp only [Loan.payInstalments, Loan.payInstalment]
  unfold_ter
  split_ifs
  · rfl
  · rfl
  · rfl
  · rcases hu : Loan.unimpairIfImpaired loan v with e | t | a1
    · rfl
    · rfl
    · have hl := Loan.unimpairIfImpaired_loan loan v a1 (by simp only [ExceptT.run]; exact hu)
      obtain ⟨l1, p1⟩ := a1
      simp only at hl
      subst hl
      have hpc' : Loan.lateComponents loan.unimpaired now = .ok pc := by
        rw [Loan.lateComponents_unimpaired]; exact hpc
      simp only [hpc', hdue, ha, hb, Bool.false_eq_true, ↓reduceIte]

private lemma Loan.single_ok (loan : Loan) (v : Vault) (amount : Number) (p : UnsettledPayment Vault)
    (a : LoanWithPool Vault) (pc : PaymentComponents) (comps : Loan → Except Error PaymentComponents)
    (hu : Loan.unimpairIfImpaired loan v = .ok (.ok a)) (hpc : comps a.loan' = .ok pc)
    (hp : (a.loan'.payInstalment a.pool' pc amount).run = .ok (.ok p)) :
    comps loan.unimpaired = .ok pc ∧ pc.paidAmounts = .ok p.amounts ∧
      Loan.doPayment loan.unimpaired pc = .ok p.loan := by
  have hl := Loan.unimpairIfImpaired_loan loan v a (by simp only [ExceptT.run]; exact hu)
  obtain ⟨l1, p1⟩ := a
  simp only at hl hpc hp
  subst hl
  simp only [Loan.payInstalment] at hp
  unfold_ter at hp
  walk_ok
  exact ⟨hpc, ‹_›, ‹_›⟩

/-- A late payment's instalment that passes, read back: the late instalment of the loan, and the loan it
leaves. -/
lemma Loan.latePayInstalments_ok (p : UnsettledPayment Vault)
    (h : (loan.payInstalments v .late amount now).run = .ok (.ok p)) :
    ∃ pc, Loan.lateComponents loan now = .ok pc ∧ pc.paidAmounts = .ok p.amounts ∧
      Loan.doPayment loan.unimpaired pc = .ok p.loan := by
  simp only [Loan.payInstalments] at h
  unfold_ter at h
  walk_ok
  obtain ⟨h1, h2, h3⟩ := Loan.single_ok loan v amount p _ _ (fun l => Loan.lateComponents l now) ‹_› ‹_›
    (by simp only [ExceptT.run]; exact ‹_›)
  exact ⟨_, by rw [← Loan.lateComponents_unimpaired]; exact h1, h2, h3⟩

/-- A full payment's instalment that passes, read back. -/
lemma Loan.fullPayInstalments_ok (p : UnsettledPayment Vault)
    (h : (loan.payInstalments v .full amount now).run = .ok (.ok p)) :
    ∃ pc, Loan.fullComponents loan now = .ok pc ∧ pc.paidAmounts = .ok p.amounts ∧
      Loan.doPayment loan.unimpaired pc = .ok p.loan := by
  simp only [Loan.payInstalments] at h
  unfold_ter at h
  walk_ok
  obtain ⟨h1, h2, h3⟩ := Loan.single_ok loan v amount p _ _ (fun l => Loan.fullComponents l now) ‹_› ‹_›
    (by simp only [ExceptT.run]; exact ‹_›)
  exact ⟨_, by rw [← Loan.fullComponents_unimpaired]; exact h1, h2, h3⟩

/-- The next scheduled instalment isn't covered by the amount. -/
private def UnsettledPayment.NextNotCovered {α : Type} (payment : UnsettledPayment α) (amount : Number) : Prop :=
  ∀ pc due s, Loan.scheduledComponents payment.loan = .ok pc →
    ({ pc with untrackedManagementFee := payment.loan.fees.serviceFee } : PaymentComponents).totalDue = .ok due →
    payment.totalPaid.operator_add due .to_nearest = .ok s → amount.operator_lt s = true

/-- What the instalment loop pays: at most one covered instalment per step and per payment left. It stops
only at the step cap, when the loan is paid off, or when the next instalment isn't covered. -/
lemma UnsettledPayment.payInstalments_count {α : Type} (payment : UnsettledPayment α) (n : Nat) (amount : Number)
    (p' : UnsettledPayment α) (h : UnsettledPayment.payInstalments payment n amount = .ok p') :
    p'.count ≤ payment.count + n ∧
      p'.count + p'.loan.paymentRemaining.toNat ≤ payment.count + payment.loan.paymentRemaining.toNat ∧
      (p' = payment ∨ amount.operator_lt p'.totalPaid = false) ∧
      (p'.count = payment.count + n ∨ p'.loan.paymentRemaining = 0 ∨ p'.NextNotCovered amount) := by
  induction n generalizing payment with
  | zero =>
    rw [UnsettledPayment.payInstalments] at h
    obtain rfl := Except.ok.inj h
    exact ⟨le_refl _, le_refl _, Or.inl rfl, Or.inl rfl⟩
  | succ n ih =>
    rw [UnsettledPayment.payInstalments] at h
    unfold_ter at h
    walk_ok
    · -- the loan is paid off
      exact ⟨by omega, le_refl _, Or.inl rfl,
        Or.inr (Or.inl (by simpa using ‹(p'.loan.paymentRemaining == 0) = true›))⟩
    · -- the next instalment is not covered
      rename_i hlt _ hsc hdue₀ hs₀
      refine ⟨by omega, le_refl _, Or.inl rfl, Or.inr (Or.inr ?_)⟩
      intro pc due s hpc hdue hs
      rw [hsc] at hpc
      obtain rfl := Except.ok.inj hpc
      rw [hdue₀] at hdue
      obtain rfl := Except.ok.inj hdue
      rw [hs₀] at hs
      obtain rfl := Except.ok.inj hs
      exact hlt
    · -- the last instalment
      have hpr : (payment.loan.paymentRemaining == 0) = false := by
        simpa using ‹¬(payment.loan.paymentRemaining == 0) = true›
      have hpos : 1 ≤ payment.loan.paymentRemaining.toNat := by
        have : payment.loan.paymentRemaining ≠ 0 := by simpa using hpr
        have := UInt32.toNat_inj.not.mpr this
        simp at this; omega
      have h0 := Loan.doPayment_final _ _ _ ‹_› ‹Loan.doPayment _ _ = _›
      refine ⟨by dsimp only; omega, by dsimp only; rw [h0]; simp; omega, Or.inr (by simpa using ‹¬_ = true›),
        Or.inr (Or.inl h0)⟩
    · -- one instalment, then the rest of the loop
      have hpr : (payment.loan.paymentRemaining == 0) = false := by
        simpa using ‹¬(payment.loan.paymentRemaining == 0) = true›
      have hne : payment.loan.paymentRemaining ≠ 0 := by simpa using hpr
      have hpos : 1 ≤ payment.loan.paymentRemaining.toNat := by
        have := UInt32.toNat_inj.not.mpr hne
        simp at this; omega
      obtain ⟨hpr', -⟩ := Loan.doPayment_notFinal _ _ _ (Bool.eq_false_iff.mpr ‹_›) ‹Loan.doPayment _ _ = _›
      obtain ⟨h1, h2, h3, h4⟩ := ih _ ‹_›
      have hsub : (payment.loan.paymentRemaining - 1).toNat = payment.loan.paymentRemaining.toNat - 1 := by
        rw [UInt32.toNat_sub_of_le _ _ (by rw [UInt32.le_iff_toNat_le]; simpa using hpos)]; rfl
      simp only [hpr', hsub] at h1 h2 h4
      refine ⟨by omega, by omega, Or.inr ?_, ?_⟩
      · rcases h3 with rfl | h3
        · simpa using ‹¬amount.operator_lt _ = true›
        · exact h3
      · rcases h4 with h4 | h4 | h4
        · exact Or.inl (by omega)
        · exact Or.inr (Or.inl h4)
        · exact Or.inr (Or.inr h4)

end XRPL.Model.Lending
