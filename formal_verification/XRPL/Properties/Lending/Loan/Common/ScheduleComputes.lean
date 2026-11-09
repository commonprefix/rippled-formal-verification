import XRPL.Properties.Lending.Loan.Common.PaymentCount

/-! # A reachable loan's schedule computes

The periodic rate, the theoretical principal of the payments left and the rounded PeriodicPayment all compute:
LoanSet, each instalment and each re-amortization computed them for the loan they leave. -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault (Vault RawVault)

open private Loan.scheduledComponents Loan.lateComponents Loan.doPayment UnsettledPayment.payInstalments
  UnsettledPayment.applyOverpayment Loan.tryOverpayment Loan.settlePayment from XRPL.Model.Lending.Loan.LoanPay
open private Loan.changeImpairment from XRPL.Model.Lending.Loan.LoanManage
open private Loan.lateComponents_scheduled from XRPL.Properties.Lending.Loan.Common.PayMonotone

/-- The loan's schedule computes: its periodic rate, the theoretical principal of the payments left, and its
PeriodicPayment rounded up at LoanScale while payments are left. -/
structure Loan.ScheduleComputes (loan : Loan) : Prop where
  rate : ∃ rate, loan.periodicRate = .ok rate
  principal : ∀ rate, loan.periodicRate = .ok rate →
    ∃ tpo, loanPrincipalFromPeriodicPayment loan.periodicPayment rate loan.paymentRemaining = .ok tpo
  payment : loan.paymentRemaining ≠ 0 → ∃ pp', STAmount.roundToNumericType loan.broker.numericType
    loan.periodicPayment .upward (some loan.loanScale) = .ok pp'

/-- A loan with the same rate, interval, PeriodicPayment, count, asset and LoanScale computes the same. -/
lemma Loan.ScheduleComputes.of_same {l l' : Loan} (h : l.ScheduleComputes)
    (h1 : l'.rates.interestRate = l.rates.interestRate)
    (h2 : l'.schedule.paymentInterval = l.schedule.paymentInterval) (h3 : l'.periodicPayment = l.periodicPayment)
    (h4 : l'.paymentRemaining = l.paymentRemaining) (h5 : l'.broker.numericType = l.broker.numericType)
    (h6 : l'.loanScale = l.loanScale) : l'.ScheduleComputes := by
  have hr : l'.periodicRate = l.periodicRate := by unfold Loan.periodicRate; rw [h1, h2]
  refine ⟨by rw [hr]; exact h.rate, fun rate hrate => ?_, fun h0 => ?_⟩
  · rw [hr] at hrate; rw [h3, h4]; exact h.principal rate hrate
  · rw [h4] at h0; rw [h3, h5, h6]; exact h.payment h0

/-- A loan rebuilt with the same terms, PeriodicPayment and count computes the same. -/
lemma Loan.ScheduleComputes.of_raw {l l' : Loan} {raw : RawLoan} (h : l.ScheduleComputes)
    (hl : raw.to_lawful = .ok l') (h1 : raw.rates = l.rates) (h2 : raw.schedule = l.schedule)
    (h3 : raw.periodicPayment = l.periodicPayment) (h4 : raw.paymentRemaining = l.paymentRemaining)
    (h5 : raw.broker.numericType = l.broker.numericType) (h6 : raw.loanScale = l.loanScale) :
    l'.ScheduleComputes := by
  have hr := (RawLoan.to_lawful_ok hl).1
  exact h.of_same (by rw [← h1, ← hr]) (by rw [← h2, ← hr]) (by rw [← h3, ← hr]) (by rw [← h4, ← hr])
    (by rw [← h5, ← hr]) (by rw [← h6, ← hr])

/-- A loan with no payments left computes when it has the InterestRate and PaymentInterval of a loan that computes. -/
lemma Loan.ScheduleComputes.of_paid {l l' : Loan} (h : l.ScheduleComputes) (h0 : l'.paymentRemaining = 0)
    (h1 : l'.rates.interestRate = l.rates.interestRate)
    (h2 : l'.schedule.paymentInterval = l.schedule.paymentInterval) : l'.ScheduleComputes := by
  have hr : l'.periodicRate = l.periodicRate := by unfold Loan.periodicRate; rw [h1, h2]
  exact ⟨by rw [hr]; exact h.rate, fun _ _ => ⟨_, by rw [h0]; exact loanPrincipalFromPeriodicPayment_zero _ _⟩,
    fun h' => absurd h0 h'⟩

/-- When the theoretical state computes, its theoretical principal computes too. -/
private lemma LoanState.buildTheoretical_principal (pp rate : Number) (n : UInt32) (m : TenthBips16) (th : LoanState)
    (h : LoanState.buildTheoretical pp rate n m = .ok th) :
    ∃ tpo, loanPrincipalFromPeriodicPayment pp rate n = .ok tpo := by
  unfold LoanState.buildTheoretical at h
  split at h
  · rename_i h0
    simp only [beq_iff_eq] at h0
    subst h0
    exact ⟨_, loanPrincipalFromPeriodicPayment_zero _ _⟩
  obtain ⟨_, -, h⟩ := bind_ok_peel _ _ _ h
  obtain ⟨_, -, h⟩ := bind_ok_peel _ _ _ h
  obtain ⟨tpo, htpo, -⟩ := bind_ok_peel _ _ _ h
  exact ⟨tpo, htpo⟩

/-- An instalment that isn't the last computed the theoretical principal of one payment fewer. -/
private lemma Loan.scheduledComponents_theory {l : Loan} {pc : PaymentComponents}
    (hpc : Loan.scheduledComponents l = .ok pc) (hf : pc.isFinal = false) :
    ∀ rate, l.periodicRate = .ok rate →
      ∃ tpo, loanPrincipalFromPeriodicPayment l.periodicPayment rate (l.paymentRemaining - 1) = .ok tpo := by
  intro rate hrate
  unfold Loan.scheduledComponents at hpc
  obtain ⟨rate', hrate', hpc⟩ := bind_ok_peel _ _ _ hpc
  rw [hrate] at hrate'
  obtain rfl := Except.ok.inj hrate'
  obtain ⟨_, -, hpc⟩ := bind_ok_peel _ _ _ hpc
  dsimp only at hpc
  split at hpc
  · obtain rfl := (Except.ok.inj hpc).symm
    simp at hf
  obtain ⟨_, -, hpc⟩ := bind_ok_peel _ _ _ hpc
  obtain ⟨_, -, hpc⟩ := bind_ok_peel _ _ _ hpc
  obtain ⟨_, hpr1, hpc⟩ := bind_ok_peel _ _ _ hpc
  obtain ⟨-, rfl⟩ := UInt32.subChecked_eq_ok.mp hpr1
  obtain ⟨th, hth, -⟩ := bind_ok_peel _ _ _ hpc
  exact LoanState.buildTheoretical_principal _ _ _ _ th hth

/-- One instalment keeps the loan's schedule computing. The last leaves no payments, another leaves one
payment fewer, whose theoretical principal the instalment computed. -/
lemma Loan.doPayment_computes (l l' : Loan) (pc0 pc : PaymentComponents) (hn : l.ScheduleComputes)
    (hpr0 : l.paymentRemaining ≠ 0) (hpc0 : Loan.scheduledComponents l = .ok pc0) (hdo : Loan.doPayment l pc = .ok l')
    (e4 : pc.isFinal = pc0.isFinal) : l'.ScheduleComputes := by
  have hst := Loan.doPayment_sameTerms _ _ _ hdo
  cases hf : pc.isFinal
  · have hf0 : pc0.isFinal = false := by rw [← e4]; exact hf
    have hpr' := (Loan.doPayment_notFinal _ _ _ hf hdo).1
    have hpp' : l'.periodicPayment = l.periodicPayment := by
      unfold Loan.doPayment at hdo
      simp only [hf, Bool.false_eq_true, ↓reduceIte] at hdo
      unfold_ter at hdo
      walk_ok
      exact (congrArg RawLoan.periodicPayment (RawLoan.to_lawful_ok ‹_›).1 :)
    have hr : l'.periodicRate = l.periodicRate := by unfold Loan.periodicRate; rw [hst.rates, hst.schedule]
    refine ⟨by rw [hr]; exact hn.rate, fun rate hrate => ?_, fun h0 => ?_⟩
    · rw [hr] at hrate
      rw [hpp', hpr']
      exact Loan.scheduledComponents_theory hpc0 hf0 rate hrate
    · rw [hpp', hst.broker, hst.loanScale]
      exact hn.payment hpr0
  · exact hn.of_paid (Loan.doPayment_final _ _ _ hf hdo) (by rw [hst.rates]) (by rw [hst.schedule])

/-- The instalment loop keeps the loan's schedule computing. -/
private lemma UnsettledPayment.payInstalments_computes {α : Type} (amount : Number) :
    ∀ (n : Nat) (payment p' : UnsettledPayment α), UnsettledPayment.payInstalments payment n amount = .ok p' →
      payment.loan.ScheduleComputes → p'.loan.ScheduleComputes := by
  intro n
  induction n with
  | zero =>
    intro payment p' h hn
    rw [UnsettledPayment.payInstalments] at h
    obtain rfl := Except.ok.inj h
    exact hn
  | succ n ih =>
    intro payment p' h hn
    rw [UnsettledPayment.payInstalments] at h
    unfold_ter at h
    walk_ok
    · exact hn
    · exact hn
    all_goals
      have hpr0 : payment.loan.paymentRemaining ≠ 0 := by
        simpa using ‹¬(payment.loan.paymentRemaining == 0) = true›
      have hstep := Loan.doPayment_computes _ _ _ _ hn hpr0 ‹Loan.scheduledComponents payment.loan = _›
        ‹Loan.doPayment _ _ = _› rfl
    · exact hstep
    · exact ih _ p' ‹UnsettledPayment.payInstalments _ n amount = _› hstep

/-- When a LoanSet's properties compute from a periodic rate, the theoretical principal of their PeriodicPayment
computes too. -/
private lemma computeLoanPropertiesFromPeriodicRate_principal (p rate : Number) (n : UInt32) (m : TenthBips16)
    (nt : NumericType) (s : Int) (props : LoanProperties)
    (h : computeLoanPropertiesFromPeriodicRate p rate n m nt s = .ok props) :
    ∃ tpo, loanPrincipalFromPeriodicPayment props.periodicPayment rate n = .ok tpo := by
  unfold computeLoanPropertiesFromPeriodicRate at h
  obtain ⟨pp, -, h⟩ := bind_ok_peel _ _ _ h
  iterate 6 obtain ⟨_, -, h⟩ := bind_ok_peel _ _ _ h
  obtain ⟨tpo, htpo, h⟩ := bind_ok_peel _ _ _ h
  iterate 3 obtain ⟨_, -, h⟩ := bind_ok_peel _ _ _ h
  obtain rfl := (Except.ok.inj h).symm
  exact ⟨tpo, htpo⟩

/-- Amortization guards that pass rounded the PeriodicPayment up at LoanScale. -/
private lemma LoanProperties.amortizationGuards_payment (props : LoanProperties) (principal : Number)
    (expect : Bool) (n : UInt32) (nt : NumericType)
    (h : props.amortizationGuards principal expect n nt = .ok .tesSUCCESS) :
    ∃ pp', STAmount.roundToNumericType nt props.periodicPayment .upward (some props.loanScale) = .ok pp' := by
  unfold LoanProperties.amortizationGuards at h
  obtain ⟨_, -, h⟩ := bind_ok_peel _ _ _ h
  simp only [bind, Except.bind, pure, Except.pure] at h
  split at h
  · exact absurd h (by decide)
  split at h
  · exact absurd h (by decide)
  split at h
  · exact absurd h (by decide)
  split at h
  · cases h
  · exact ⟨_, ‹_›⟩

/-- A re-amortization that passes computed the theoretical principal and the rounded payment of its new
PeriodicPayment. -/
private lemma Loan.tryOverpayment_computes (l : Loan) (opc : PaymentComponents) (re : Reamortization)
    (h : Loan.tryOverpayment l opc = .ok (some re)) :
    (∀ rate, l.periodicRate = .ok rate →
      ∃ tpo, loanPrincipalFromPeriodicPayment re.periodicPayment rate l.paymentRemaining = .ok tpo) ∧
    ∃ pp', STAmount.roundToNumericType l.broker.numericType re.periodicPayment .upward (some l.loanScale) =
      .ok pp' := by
  unfold Loan.tryOverpayment at h
  simp only [bind, Except.bind] at h
  walk_ok
  all_goals first
    | (have hn := Except.ok.inj ‹pure none = Except.ok (some re)›; cases hn)
    | skip
  obtain rfl := Option.some.inj (Except.ok.inj ‹pure (some _) = Except.ok (some re)›)
  have hrate := ‹l.periodicRate = Except.ok _›
  have hprops := ‹computeLoanPropertiesFromPeriodicRate _ _ _ _ _ _ = Except.ok _›
  have hg := ‹LoanProperties.amortizationGuards _ _ _ _ _ = Except.ok _›
  have hgs := ‹¬(!TER.isTesSuccess _) = true›
  refine ⟨fun rate' hrate' => ?_, ?_⟩
  · rw [hrate] at hrate'
    obtain rfl := Except.ok.inj hrate'
    exact computeLoanPropertiesFromPeriodicRate_principal _ _ _ _ _ _ _ hprops
  · simp only [Bool.not_eq_true, Bool.not_eq_false'] at hgs
    rw [(TER.isTesSuccess_iff _).mp hgs] at hg
    exact LoanProperties.amortizationGuards_payment _ _ _ _ _ hg

/-- The overpayment tail keeps the loan's schedule computing. -/
private lemma UnsettledPayment.applyOverpayment_computes (payment p' : UnsettledPayment Vault) (amount : Number)
    (hn : payment.loan.ScheduleComputes) (h : UnsettledPayment.applyOverpayment payment amount = .ok p') :
    p'.loan.ScheduleComputes := by
  unfold UnsettledPayment.applyOverpayment at h
  unfold_ter at h
  walk_ok
  all_goals first
    | exact hn
    | skip
  rename_i re hre _ _ _ _ loan' hl
  obtain ⟨he, -, -⟩ := RawLoan.to_lawful_ok hl
  obtain ⟨hth, hpp⟩ := Loan.tryOverpayment_computes _ _ _ hre
  have h1 : loan'.rates = payment.loan.rates := by rw [show loan'.rates = loan'.toRawLoan.rates from rfl, he]
  have h2 : loan'.schedule = payment.loan.schedule := by
    rw [show loan'.schedule = loan'.toRawLoan.schedule from rfl, he]
  have hr : loan'.periodicRate = payment.loan.periodicRate := by unfold Loan.periodicRate; rw [h1, h2]
  have hn' : loan'.paymentRemaining = payment.loan.paymentRemaining := by
    rw [show loan'.paymentRemaining = loan'.toRawLoan.paymentRemaining from rfl, he]
  have hpp' : loan'.periodicPayment = re.periodicPayment := by
    rw [show loan'.periodicPayment = loan'.toRawLoan.periodicPayment from rfl, he]
  have hls : loan'.loanScale = payment.loan.loanScale := by
    rw [show loan'.loanScale = loan'.toRawLoan.loanScale from rfl, he]
  have hb : loan'.broker = payment.loan.broker := by
    rw [show loan'.broker = loan'.toRawLoan.broker from rfl, he]
  refine ⟨by rw [hr]; exact hn.rate, fun rate hrate => ?_, fun _ => ?_⟩
  · rw [hr] at hrate
    rw [hpp', hn']
    exact hth rate hrate
  · rw [hpp', hb, hls]
    exact hpp

/-- A payment of any type keeps the loan's schedule computing. -/
lemma Loan.pay_computes (loan : Loan) (v : Vault) (pt : LoanPaymentType) (amount : Number) (now : UInt32)
    (r : LoanWithAmounts Vault) (hn : loan.ScheduleComputes) (h : (loan.pay v pt amount now).run = .ok (.ok r)) :
    r.loan'.ScheduleComputes := by
  obtain ⟨p, hp, hsettle⟩ := Loan.pay_ok loan v pt amount now r h
  obtain ⟨_, _, _, _, _, _, broker', -, -, -, hbroker, hloan, -, -⟩ := UnsettledPayment.settle_ok p r hsettle
  suffices hp' : p.loan.ScheduleComputes by
    refine hp'.of_raw hloan rfl rfl rfl rfl ?_ rfl
    show broker'.toRawLoanBroker.numericType = _
    rw [(RawLoanBroker.to_lawful_ok hbroker).1]
  have hu : loan.unimpaired.ScheduleComputes := hn.of_same rfl rfl rfl rfl rfl rfl
  cases pt
  · obtain ⟨si, -, hloop, -⟩ := Loan.payScheduled_loop loan v amount now p hp
    exact UnsettledPayment.payInstalments_computes amount _ _ p hloop hu
  · obtain ⟨pc, hpc, -, hdo⟩ := Loan.latePayInstalments_ok loan v amount now p hp
    obtain ⟨pc0, hpc0, -, -, -, e4⟩ := Loan.lateComponents_scheduled loan now pc hpc
    exact Loan.doPayment_computes loan.unimpaired p.loan pc0 pc hu
      (Loan.payInstalments_ok loan v .late amount now p hp).1.remaining
      (by rw [Loan.scheduledComponents_unimpaired]; exact hpc0) hdo e4
  · obtain ⟨-, -, hst, -, -⟩ := Loan.payInstalments_ok loan v .full amount now p hp
    exact hn.of_paid (Loan.fullPayInstalments_paid loan v amount now p hp) (by rw [hst.rates]; rfl)
      (by rw [hst.schedule]; rfl)
  · obtain ⟨p0, h0, h1⟩ := Loan.overPayInstalments_ok loan v amount now p hp
    obtain ⟨si, -, hloop, -⟩ := Loan.payScheduled_loop loan v amount now p0 h0
    exact UnsettledPayment.applyOverpayment_computes p0 p amount
      (UnsettledPayment.payInstalments_computes amount _ _ p0 hloop hu) h1

/-- An accept keeps the loan's schedule computing. -/
private lemma Loan.accept_computes (loan : Loan) (v : Vault) (r : LoanWithDisbursement Vault)
    (hn : loan.ScheduleComputes) (h : (loan.accept v).run = .ok (.ok r)) : r.loan'.ScheduleComputes := by
  simp only [Loan.accept] at h
  unfold_ter at h
  walk_ok
  have hl := ‹RawLoan.to_lawful _ = Except.ok _›
  exact hn.of_raw hl rfl rfl rfl rfl rfl rfl

/-- Changing the impairment keeps the loan's schedule computing. -/
private lemma Loan.changeImpairment_computes (loan : Loan) (v : Vault) (b : Bool) (r : LoanWithPool Vault)
    (hn : loan.ScheduleComputes) (h : (Loan.changeImpairment loan v b).run = .ok (.ok r)) :
    r.loan'.ScheduleComputes := by
  simp only [Loan.changeImpairment] at h
  unfold_ter at h
  walk_ok
  all_goals
    have hl := ‹RawLoan.to_lawful _ = Except.ok _›
    exact hn.of_raw hl rfl rfl rfl rfl rfl rfl

/-- A default keeps the rates and the schedule. -/
private lemma Loan.manageDefault_terms (loan : Loan) (v : Vault) (r : LoanWithAmounts Vault)
    (h : (loan.manageDefault v).run = .ok (.ok r)) :
    r.loan'.rates = loan.rates ∧ r.loan'.schedule = loan.schedule := by
  simp only [Loan.manageDefault] at h
  unfold_ter at h
  walk_ok
  all_goals
    have h1 := (RawLoan.to_lawful_ok ‹RawLoan.to_lawful _ = Except.ok _›).1
    exact ⟨(congrArg RawLoan.rates h1 :), (congrArg RawLoan.schedule h1 :)⟩

/-- A loan a LoanSet creates has a schedule that computes. -/
lemma Loan.Created.scheduleComputes {start : Loan} {t₀ : UInt32} (h : Loan.Created start t₀) :
    start.ScheduleComputes := by
  obtain ⟨broker, v, principal, rates, fees, pi, pt, gp, sd, twoStep, allowsOverpayment, r, -, hok, rfl⟩ := h
  obtain ⟨props, _, _, _, broker', _, _, _, _, _, hchecks, -, -, -, hl, hb⟩ :=
    Loan.create_pool_sums broker v principal rates fees _ allowsOverpayment twoStep r hok
  have hPP : r.loan'.periodicPayment = props.periodicPayment := by
    show r.loan'.toRawLoan.periodicPayment = _; rw [hl]; rfl
  have hLS : r.loan'.loanScale = props.loanScale := by
    show r.loan'.toRawLoan.loanScale = _; rw [hl]; rfl
  have hN : r.loan'.paymentRemaining = (LoanSchedule.build pi pt gp sd t₀ twoStep).paymentTotal := by
    show r.loan'.toRawLoan.paymentRemaining = _; rw [hl]; rfl
  have hNT : r.loan'.broker.numericType = broker.numericType := by
    show r.loan'.toRawLoan.broker.toRawLoanBroker.numericType = _; rw [hl]
    show broker'.toRawLoanBroker.numericType = _; rw [hb]
  have hR : r.loan'.periodicRate = loanPeriodicRate rates.interestRate
      (LoanSchedule.build pi pt gp sd t₀ twoStep).paymentInterval := by
    have hRt : r.loan'.rates = rates := by show r.loan'.toRawLoan.rates = _; rw [hl]; rfl
    have hSc : r.loan'.schedule = LoanSchedule.build pi pt gp sd t₀ twoStep := by
      show r.loan'.toRawLoan.schedule = _; rw [hl]; rfl
    unfold Loan.periodicRate
    rw [hRt, hSc]
  have hprops := hchecks.properties_ok
  unfold computeLoanProperties at hprops
  obtain ⟨rate, hrate, hprops⟩ := bind_ok_peel _ _ _ hprops
  refine ⟨⟨rate, by rw [hR]; exact hrate⟩, fun rate' hrate' => ?_, fun _ => ?_⟩
  · rw [hR, hrate] at hrate'
    obtain rfl := Except.ok.inj hrate'
    rw [hPP, hN]
    exact computeLoanPropertiesFromPeriodicRate_principal _ _ _ _ _ _ _ hprops
  · rw [hPP, hNT, hLS]
    exact LoanProperties.amortizationGuards_payment _ _ _ _ _
      (LoanProperties.checkGuards_amortization _ _ _ _ _ hchecks.guards)

/-- Every loan reachable from a LoanSet has a schedule that computes. -/
lemma Loan.ReachableFrom.scheduleComputes {start : Loan} {t₀ : UInt32} {loan : Loan} {t : UInt32}
    (hc : Loan.Created start t₀) (hr : Loan.ReachableFrom start t₀ loan t) : loan.ScheduleComputes := by
  induction hr with
  | refl => exact Loan.Created.scheduleComputes hc
  | refresh _ _ _ _ _ hnt h ih => exact ih.of_raw h rfl rfl rfl rfl hnt rfl
  | accept _ _ _ _ _ _ _ _ h ih => exact Loan.accept_computes _ _ _ ih h
  | regularPayment _ _ _ _ _ _ _ _ _ h ih => exact Loan.pay_computes _ _ .regular _ _ _ ih h
  | latePayment _ _ _ _ _ _ _ _ _ h ih => exact Loan.pay_computes _ _ .late _ _ _ ih h
  | fullPayment _ _ _ _ _ _ _ _ _ h ih => exact Loan.pay_computes _ _ .full _ _ _ ih h
  | overpayment _ _ _ _ _ _ _ _ _ h ih => exact Loan.pay_computes _ _ .overpayment _ _ _ ih h
  | impair _ _ _ _ _ _ _ _ h ih =>
    simp only [Loan.manageImpair] at h
    unfold_ter at h
    walk_ok
    exact Loan.changeImpairment_computes _ _ true _ ih ‹_›
  | unimpair _ _ _ _ _ _ _ _ h ih => exact Loan.changeImpairment_computes _ _ false _ ih h
  | default _ _ _ _ _ _ _ _ h ih =>
    obtain ⟨h1, h2⟩ := Loan.manageDefault_terms _ _ _ h
    exact ih.of_paid (Loan.manageDefault_paid _ _ _ h) (by rw [h1]) (by rw [h2])

/-- Every reachable loan has a schedule that computes. -/
lemma Loan.Reachable.scheduleComputes {loan : Loan} {t : UInt32} (hr : loan.Reachable t) :
    loan.ScheduleComputes := by
  obtain ⟨start, t₀, hc, hr'⟩ := hr
  exact hr'.scheduleComputes hc

end XRPL.Model.Lending
