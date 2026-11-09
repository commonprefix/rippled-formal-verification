import XRPL.Properties.Lending.Loan.Common.Frame
import XRPL.Properties.Lending.Loan.Common.GuardProofs
import XRPL.Properties.Lending.Loan.Common.ReachableProofs
import XRPL.Properties.Lending.Loan.Common.SetUpdates

/-! # The payment schedule of a loan

A loan with payments left is due at the instalment its count says. An instalment takes one payment and moves the due
date one interval on, the last one and a default clear both, the other transactions leave them alone. -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault (Vault RawVault)

open private Loan.changeImpairment from XRPL.Model.Lending.Loan.LoanManage
open private Loan.doPayment Loan.settlePayment validatePostPayment UnsettledPayment.payInstalments
  Loan.unimpairIfImpaired Loan.payScheduledInstalments UnsettledPayment.applyOverpayment Loan.paySingleInstalment
  from XRPL.Model.Lending.Loan.LoanPay

/-- The payments left and the due dates, which only a payment or a default changes. -/
structure Loan.KeepsDueDate (loan loan' : Loan) : Prop where
  paymentRemaining : loan'.paymentRemaining = loan.paymentRemaining
  nextPaymentDueDate : loan'.nextPaymentDueDate = loan.nextPaymentDueDate
  previousPaymentDueDate : loan'.previousPaymentDueDate = loan.previousPaymentDueDate

lemma Loan.KeepsDueDate.refl (loan : Loan) : Loan.KeepsDueDate loan loan := ⟨rfl, rfl, rfl⟩

lemma Loan.KeepsDueDate.trans {a b c : Loan} (h₁ : Loan.KeepsDueDate a b) (h₂ : Loan.KeepsDueDate b c) :
    Loan.KeepsDueDate a c :=
  ⟨h₂.paymentRemaining.trans h₁.paymentRemaining, h₂.nextPaymentDueDate.trans h₁.nextPaymentDueDate,
    h₂.previousPaymentDueDate.trans h₁.previousPaymentDueDate⟩

lemma Loan.KeepsDueDate.of_lawful {loan loan' : Loan} {raw : RawLoan} (h : raw.to_lawful = .ok loan')
    (hp : raw.paymentRemaining = loan.paymentRemaining) (hn : raw.nextPaymentDueDate = loan.nextPaymentDueDate)
    (hq : raw.previousPaymentDueDate = loan.previousPaymentDueDate) : Loan.KeepsDueDate loan loan' := by
  obtain ⟨he, -, -⟩ := RawLoan.to_lawful_ok h
  subst he
  exact ⟨hp, hn, hq⟩

lemma Loan.accept_keepsDueDate (loan : Loan) (v : Vault) (r : LoanWithDisbursement Vault)
    (h : (loan.accept v).run = .ok (.ok r)) : Loan.KeepsDueDate loan r.loan' := by
  simp only [Loan.accept] at h
  unfold_ter at h
  walk_ok
  have hl := ‹RawLoan.to_lawful _ = Except.ok _›
  exact Loan.KeepsDueDate.of_lawful hl rfl rfl rfl

private lemma Loan.changeImpairment_keepsDueDate {α : Type} [AssetPool α] (loan : Loan) (pool : α) (b : Bool)
    (r : LoanWithPool α) (h : (Loan.changeImpairment loan pool b).run = .ok (.ok r)) :
    Loan.KeepsDueDate loan r.loan' := by
  simp only [Loan.changeImpairment] at h
  unfold_ter at h
  walk_ok
  all_goals
    have hl := ‹RawLoan.to_lawful _ = Except.ok _›
    exact Loan.KeepsDueDate.of_lawful hl rfl rfl rfl

lemma Loan.manageImpair_keepsDueDate (loan : Loan) (v : Vault) (now : UInt32) (r : LoanWithPool Vault)
    (h : (loan.manageImpair v now).run = .ok (.ok r)) : Loan.KeepsDueDate loan r.loan' := by
  simp only [Loan.manageImpair] at h
  unfold_ter at h
  walk_ok
  exact Loan.changeImpairment_keepsDueDate loan v true r ‹_›

private lemma Loan.settlePayment_keepsDueDate {α : Type} [AssetPool α] (loan : Loan) (pool : α)
    (amounts : PaymentAmounts) (si : Number) (r : LoanWithAmounts α)
    (h : (Loan.settlePayment loan pool amounts si).run = .ok (.ok r)) :
    Loan.KeepsDueDate loan r.loan' := by
  simp only [Loan.settlePayment] at h
  unfold_ter at h
  walk_ok
  all_goals
    have hv := validatePostPayment_eq _ _ r ‹_›
    subst hv
    have hl := ‹RawLoan.to_lawful _ = Except.ok _›
    exact Loan.KeepsDueDate.of_lawful hl rfl rfl rfl

private lemma UnsettledPayment.applyOverpayment_keepsDueDate {α : Type} (payment p : UnsettledPayment α)
    (amount : Number) (h : UnsettledPayment.applyOverpayment payment amount = .ok p) :
    Loan.KeepsDueDate payment.loan p.loan := by
  unfold UnsettledPayment.applyOverpayment at h
  unfold_ter at h
  walk_ok
  all_goals first
    | exact Loan.KeepsDueDate.refl _
    | (have hl := ‹RawLoan.to_lawful _ = Except.ok _›
       exact Loan.KeepsDueDate.of_lawful hl rfl rfl rfl)

private lemma Loan.unimpairIfImpaired_keepsDueDate {α : Type} [AssetPool α] (loan : Loan) (pool : α)
    (r : LoanWithPool α) (h : (Loan.unimpairIfImpaired loan pool).run = .ok (.ok r)) :
    Loan.KeepsDueDate loan r.loan' := by
  unfold Loan.unimpairIfImpaired at h
  split at h
  · exact Loan.changeImpairment_keepsDueDate loan pool false r h
  · unfold_ter at h
    walk_ok
    exact Loan.KeepsDueDate.refl _

/-- One instalment: the final one clears the payments left, any other takes one and moves the due date
one interval on, with the paid due date as the previous one. -/
private lemma Loan.doPayment_dueDate (loan : Loan) (pc : PaymentComponents) (loan' : Loan)
    (h : Loan.doPayment loan pc = .ok loan') :
    loan'.paymentRemaining = 0 ∨
      (loan'.paymentRemaining = loan.paymentRemaining - 1 ∧
        loan'.nextPaymentDueDate = loan.nextPaymentDueDate + loan.schedule.paymentInterval ∧
        loan'.previousPaymentDueDate = loan.nextPaymentDueDate) := by
  unfold Loan.doPayment at h
  dsimp only at h
  split at h
  · obtain ⟨l, hl, h⟩ := bind_ok_peel _ _ _ h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    obtain ⟨he, -, -⟩ := RawLoan.to_lawful_ok hl
    left; rw [he]
  · obtain ⟨_, -, h⟩ := bind_ok_peel _ _ _ h
    obtain ⟨_, -, h⟩ := bind_ok_peel _ _ _ h
    obtain ⟨_, -, h⟩ := bind_ok_peel _ _ _ h
    obtain ⟨_, -, h⟩ := bind_ok_peel _ _ _ h
    obtain ⟨_, hc1, h⟩ := bind_ok_peel _ _ _ h
    obtain ⟨-, rfl⟩ := UInt32.subChecked_eq_ok.mp hc1
    obtain ⟨_, hc2, h⟩ := bind_ok_peel _ _ _ h
    obtain ⟨-, rfl⟩ := UInt32.addChecked_eq_ok.mp hc2
    obtain ⟨he, -, -⟩ := RawLoan.to_lawful_ok h
    right; rw [he]; exact ⟨rfl, rfl, rfl⟩
/-- A loan has at most PaymentTotal payments left, and with payments left it is due at the instalment its count
of payments left says, after its previous due date. -/
private def Loan.OnSchedule (loan : Loan) : Prop :=
  loan.paymentRemaining ≤ loan.schedule.paymentTotal ∧
    (loan.paymentRemaining ≠ 0 →
      loan.nextPaymentDueDate.toNat = loan.schedule.startDate.toNat +
        (loan.schedule.paymentTotal.toNat - loan.paymentRemaining.toNat + 1) * loan.schedule.paymentInterval.toNat ∧
      loan.previousPaymentDueDate < loan.nextPaymentDueDate)

/-- The schedule's last payment is due by the largest ledger time. -/
private def LoanSchedule.EndsInTime (s : LoanSchedule) : Prop :=
  s.startDate.toNat + s.paymentTotal.toNat * s.paymentInterval.toNat ≤ maxTime.toNat

private lemma Loan.OnSchedule.of_keepsDueDate {loan loan' : Loan} (hon : loan.OnSchedule)
    (ht : Loan.KeepsTerms loan loan') (hd : Loan.KeepsDueDate loan loan') : loan'.OnSchedule := by
  refine ⟨by rw [hd.paymentRemaining, ht.schedule]; exact hon.1, fun hpr => ?_⟩
  rw [hd.paymentRemaining] at hpr ⊢
  rw [hd.nextPaymentDueDate, hd.previousPaymentDueDate, ht.schedule]
  exact hon.2 hpr

/-- An instalment keeps a loan on its schedule. -/
private lemma Loan.doPayment_onSchedule (loan : Loan) (pc : PaymentComponents) (loan' : Loan)
    (hend : loan.schedule.EndsInTime) (hon : loan.OnSchedule) (hpr : loan.paymentRemaining ≠ 0)
    (h : Loan.doPayment loan pc = .ok loan') : loan'.OnSchedule := by
  have hs := (Loan.doPayment_keepsTerms loan pc loan' h).schedule
  have hle : loan.paymentRemaining.toNat ≤ loan.schedule.paymentTotal.toNat := UInt32.le_iff_toNat_le.mp hon.1
  have hP1 : 1 ≤ loan.paymentRemaining.toNat := by
    have : loan.paymentRemaining.toNat ≠ 0 := fun h0 => hpr (UInt32.toNat_inj.mp (by simpa using h0))
    omega
  have hsub : (loan.paymentRemaining - 1).toNat = loan.paymentRemaining.toNat - 1 := by
    rw [UInt32.toNat_sub_of_le _ _ (by rw [UInt32.le_iff_toNat_le]; simpa using hP1)]; rfl
  -- the instalment leaves no payment, or one less
  have hcount : loan'.paymentRemaining ≤ loan'.schedule.paymentTotal := by
    rw [hs]
    rcases Loan.doPayment_dueDate loan pc loan' h with h0 | ⟨hp, -⟩
    · rw [h0]; exact UInt32.zero_le
    · rw [hp, UInt32.le_iff_toNat_le, hsub]; omega
  refine ⟨hcount, fun hpr' => ?_⟩
  rcases Loan.doPayment_dueDate loan pc loan' h with h0 | ⟨hp, hn, hq⟩
  · exact absurd h0 hpr'
  rw [hs]
  have hP2 : 2 ≤ loan.paymentRemaining.toNat := by
    have : (loan.paymentRemaining - 1).toNat ≠ 0 := fun h0 =>
      hpr' (by rw [hp]; exact UInt32.toNat_inj.mp (by simpa using h0))
    omega
  rw [hp, hsub]
  have hnext := (hon.2 hpr).1
  have hI := UInt32.le_iff_toNat_le.mp loan.valid.paymentInterval_min
  have h60 : minPaymentInterval.toNat = 60 := rfl
  set T := loan.schedule.paymentTotal.toNat
  set P := loan.paymentRemaining.toNat
  set i := loan.schedule.paymentInterval.toNat
  set st := loan.schedule.startDate.toNat
  have hbound : (T - P + 2) * i ≤ T * i := Nat.mul_le_mul_right _ (by omega)
  have hend' : st + T * i ≤ maxTime.toNat := hend
  have hM : maxTime.toNat = 4294967295 := rfl
  have hk : T - (P - 1) + 1 = (T - P + 1) + 1 := by omega
  have hsum : (loan.nextPaymentDueDate + loan.schedule.paymentInterval).toNat =
      loan.nextPaymentDueDate.toNat + i := by
    rw [UInt32.toNat_add]
    apply Nat.mod_eq_of_lt
    have : (T - P + 1) * i + i = (T - P + 2) * i := by ring
    omega
  refine ⟨by rw [hn, hsum, hnext, hk]; ring, ?_⟩
  -- the paid due date becomes the previous one
  rw [hq, hn, UInt32.lt_iff_toNat_lt, hsum]
  omega
private lemma UnsettledPayment.payInstalments_onSchedule {α : Type} (amount : Number) :
    ∀ (n : Nat) (payment p : UnsettledPayment α), payment.loan.schedule.EndsInTime → payment.loan.OnSchedule →
      UnsettledPayment.payInstalments payment n amount = .ok p → p.loan.OnSchedule := by
  intro n
  induction n with
  | zero =>
    intro payment p _ hon h
    unfold UnsettledPayment.payInstalments at h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    exact hon
  | succ k ih =>
    intro payment p hend hon h
    unfold UnsettledPayment.payInstalments at h
    dsimp only at h
    split at h
    · simp only [pure, Except.pure, Except.ok.injEq] at h; subst h; exact hon
    · rename_i hpr
      have hpr' : payment.loan.paymentRemaining ≠ 0 := by simpa using hpr
      obtain ⟨_, -, h⟩ := bind_ok_peel _ _ _ h
      obtain ⟨pc, -, h⟩ := bind_ok_peel _ _ _ h
      try dsimp only at h
      obtain ⟨_, -, h⟩ := bind_ok_peel _ _ _ h
      obtain ⟨_, -, h⟩ := bind_ok_peel _ _ _ h
      split at h
      · simp only [pure, Except.pure, Except.ok.injEq] at h; subst h; exact hon
      · obtain ⟨_, -, h⟩ := bind_ok_peel _ _ _ h
        obtain ⟨_, -, h⟩ := bind_ok_peel _ _ _ h
        obtain ⟨loan', hl, h⟩ := bind_ok_peel _ _ _ h
        obtain ⟨_, -, h⟩ := bind_ok_peel _ _ _ h
        obtain ⟨_, -, h⟩ := bind_ok_peel _ _ _ h
        try dsimp only at h
        have hon' := Loan.doPayment_onSchedule _ _ _ hend hon hpr' hl
        have hend' : loan'.schedule.EndsInTime := by
          rw [(Loan.doPayment_keepsTerms _ _ _ hl).schedule]; exact hend
        split at h
        · simp only [pure, Except.pure, Except.ok.injEq] at h; subst h; exact hon'
        · exact ih _ _ hend' hon' h
private lemma Loan.payScheduledInstalments_onSchedule {α : Type} [AssetPool α] (loan : Loan) (pool : α)
    (amount : Number) (now : UInt32) (p : UnsettledPayment α) (hend : loan.schedule.EndsInTime)
    (hon : loan.OnSchedule) (h : (Loan.payScheduledInstalments loan pool amount now).run = .ok (.ok p)) :
    p.loan.OnSchedule := by
  simp only [Loan.payScheduledInstalments] at h
  unfold_ter at h
  walk_ok
  all_goals
    have hu := ‹(Loan.unimpairIfImpaired _ _) = Except.ok (Except.ok _)›
    have ht := Loan.unimpairIfImpaired_keepsTerms _ _ _ hu
    have hd := Loan.unimpairIfImpaired_keepsDueDate _ _ _ hu
    have hi := ‹UnsettledPayment.payInstalments _ _ _ = Except.ok _›
    exact UnsettledPayment.payInstalments_onSchedule amount _ _ _ (by rw [← ht.schedule] at hend; exact hend)
      (hon.of_keepsDueDate ht hd) hi

private lemma Loan.paySingleInstalment_onSchedule {α : Type} [AssetPool α] (loan : Loan) (pool : α)
    (pc : PaymentComponents) (amount : Number) (r : LoanWithAmounts α) (hend : loan.schedule.EndsInTime)
    (hon : loan.OnSchedule) (hpr : loan.paymentRemaining ≠ 0)
    (h : (Loan.paySingleInstalment loan pool pc amount).run = .ok (.ok r)) : r.loan'.OnSchedule := by
  simp only [Loan.paySingleInstalment] at h
  unfold_ter at h
  walk_ok
  all_goals
    have hl := ‹Loan.doPayment _ _ = Except.ok _›
    have hs := ‹(Loan.settlePayment _ _ _ _) = Except.ok (Except.ok _)›
    exact (Loan.doPayment_onSchedule _ _ _ hend hon hpr hl).of_keepsDueDate
      (Loan.settlePayment_keepsTerms _ _ _ _ _ hs) (Loan.settlePayment_keepsDueDate _ _ _ _ _ hs)

private lemma Loan.regularPayment_onSchedule {α : Type} [AssetPool α] (loan : Loan) (pool : α) (amount : Number)
    (now : UInt32) (r : LoanWithAmounts α) (hend : loan.schedule.EndsInTime) (hon : loan.OnSchedule)
    (h : (loan.regularPayment pool amount now).run = .ok (.ok r)) : r.loan'.OnSchedule := by
  simp only [Loan.regularPayment] at h
  unfold_ter at h
  walk_ok
  all_goals
    have hp := ‹(Loan.payScheduledInstalments _ _ _ _) = Except.ok (Except.ok _)›
    have hs := ‹(Loan.settlePayment _ _ _ _) = Except.ok (Except.ok _)›
    exact (Loan.payScheduledInstalments_onSchedule _ _ _ _ _ hend hon hp).of_keepsDueDate
      (Loan.settlePayment_keepsTerms _ _ _ _ _ hs) (Loan.settlePayment_keepsDueDate _ _ _ _ _ hs)

private lemma Loan.overpayment_onSchedule {α : Type} [AssetPool α] (loan : Loan) (pool : α) (amount : Number)
    (now : UInt32) (r : LoanWithAmounts α) (hend : loan.schedule.EndsInTime) (hon : loan.OnSchedule)
    (h : (loan.overpayment pool amount now).run = .ok (.ok r)) : r.loan'.OnSchedule := by
  simp only [Loan.overpayment] at h
  unfold_ter at h
  walk_ok
  all_goals
    have hp := ‹(Loan.payScheduledInstalments _ _ _ _) = Except.ok (Except.ok _)›
    have ho := ‹UnsettledPayment.applyOverpayment _ _ = Except.ok _›
    have hs := ‹(Loan.settlePayment _ _ _ _) = Except.ok (Except.ok _)›
    exact ((Loan.payScheduledInstalments_onSchedule _ _ _ _ _ hend hon hp).of_keepsDueDate
      (UnsettledPayment.applyOverpayment_keepsTerms _ _ _ ho)
      (UnsettledPayment.applyOverpayment_keepsDueDate _ _ _ ho)).of_keepsDueDate
      (Loan.settlePayment_keepsTerms _ _ _ _ _ hs) (Loan.settlePayment_keepsDueDate _ _ _ _ _ hs)

private lemma Loan.latePayment_onSchedule {α : Type} [AssetPool α] (loan : Loan) (pool : α) (amount : Number)
    (now : UInt32) (r : LoanWithAmounts α) (hend : loan.schedule.EndsInTime) (hon : loan.OnSchedule)
    (h : (loan.latePayment pool amount now).run = .ok (.ok r)) : r.loan'.OnSchedule := by
  simp only [Loan.latePayment] at h
  unfold_ter at h
  walk_ok
  all_goals
    have hk := ‹¬ (_ || _) = true›
    have hpr : loan.paymentRemaining ≠ 0 := by simp only [Bool.or_eq_true, beq_iff_eq, not_or] at hk; exact hk.1
    have hu := ‹(Loan.unimpairIfImpaired _ _) = Except.ok (Except.ok _)›
    have ht := Loan.unimpairIfImpaired_keepsTerms _ _ _ hu
    have hd := Loan.unimpairIfImpaired_keepsDueDate _ _ _ hu
    have hi := ‹(Loan.paySingleInstalment _ _ _ _) = Except.ok (Except.ok _)›
    exact Loan.paySingleInstalment_onSchedule _ _ _ _ _ (by rw [← ht.schedule] at hend; exact hend)
      (hon.of_keepsDueDate ht hd) (by rw [hd.paymentRemaining]; exact hpr) hi

private lemma Loan.fullPayment_onSchedule {α : Type} [AssetPool α] (loan : Loan) (pool : α) (amount : Number)
    (now : UInt32) (r : LoanWithAmounts α) (hend : loan.schedule.EndsInTime) (hon : loan.OnSchedule)
    (h : (loan.fullPayment pool amount now).run = .ok (.ok r)) : r.loan'.OnSchedule := by
  simp only [Loan.fullPayment] at h
  unfold_ter at h
  walk_ok
  all_goals
    have hk := ‹¬ (_ || _) = true›
    have hpr : loan.paymentRemaining ≠ 0 := by simp only [Bool.or_eq_true, beq_iff_eq, not_or] at hk; exact hk.1
    have hu := ‹(Loan.unimpairIfImpaired _ _) = Except.ok (Except.ok _)›
    have ht := Loan.unimpairIfImpaired_keepsTerms _ _ _ hu
    have hd := Loan.unimpairIfImpaired_keepsDueDate _ _ _ hu
    have hi := ‹(Loan.paySingleInstalment _ _ _ _) = Except.ok (Except.ok _)›
    exact Loan.paySingleInstalment_onSchedule _ _ _ _ _ (by rw [← ht.schedule] at hend; exact hend)
      (hon.of_keepsDueDate ht hd) (by rw [hd.paymentRemaining]; exact hpr) hi

lemma Loan.manageDefault_paid (loan : Loan) (v : Vault) (r : LoanWithAmounts Vault)
    (h : (loan.manageDefault v).run = .ok (.ok r)) : r.loan'.paymentRemaining = 0 := by
  simp only [Loan.manageDefault] at h
  unfold_ter at h
  walk_ok
  all_goals
    have hl := ‹RawLoan.to_lawful _ = Except.ok _›
    rw [(RawLoan.to_lawful_ok hl).1]
/-- The loan a LoanSet creates is due one interval after its StartDate, and its schedule ends by the
largest ledger time. -/
private lemma Loan.Created.onSchedule {start : Loan} {t₀ : UInt32} (hc : Loan.Created start t₀) :
    start.schedule.EndsInTime ∧ start.OnSchedule := by
  obtain ⟨broker, v, principal, rates, fees, pi, pt, gp, sd, twoStep, ao, r, hcan, hok, rfl⟩ := hc
  set schedule := LoanSchedule.build pi pt gp sd t₀ twoStep
  obtain ⟨props, _, _, _, broker', -, -, -, -, hloan⟩ :=
    Loan.create_ok_inv broker v principal rates fees schedule ao twoStep r hok
  obtain ⟨hraw, -, -⟩ := RawLoan.to_lawful_ok hloan
  have hs : r.loan'.schedule = schedule := (congrArg RawLoan.schedule hraw :)
  have hp : r.loan'.paymentRemaining = schedule.paymentTotal := (congrArg RawLoan.paymentRemaining hraw :)
  have hn : r.loan'.nextPaymentDueDate = schedule.startDate + schedule.paymentInterval :=
    (congrArg RawLoan.nextPaymentDueDate hraw :)
  have hq : r.loan'.previousPaymentDueDate = 0 := (congrArg RawLoan.previousPaymentDueDate hraw :)
  have hT : 1 ≤ schedule.paymentTotal.toNat := by
    have := r.loan'.valid.paymentTotal_pos
    rw [hs, UInt32.lt_iff_toNat_lt] at this; simpa using this
  have hI : 1 ≤ schedule.paymentInterval.toNat := by
    have := r.loan'.valid.paymentInterval_min
    rw [hs, UInt32.le_iff_toNat_le] at this
    have h60 : minPaymentInterval.toNat = 60 := rfl
    omega
  have hfit : schedule.startDate.toNat + schedule.gracePeriod.toNat +
      schedule.paymentTotal.toNat * schedule.paymentInterval.toNat ≤ maxTime.toNat := by
    by_contra hlong
    rw [Loan.canCreate_schedule_too_long_proof broker v principal fees schedule t₀ twoStep (by omega)] at hcan
    exact absurd hcan (by decide)
  have hend : schedule.EndsInTime := by unfold LoanSchedule.EndsInTime; omega
  refine ⟨by rw [hs]; exact hend, by rw [hp, hs]; exact UInt32.le_refl _, fun _ => ?_⟩
  have hM : maxTime.toNat = 4294967295 := rfl
  have hle : schedule.paymentInterval.toNat ≤ schedule.paymentTotal.toNat * schedule.paymentInterval.toNat :=
    Nat.le_mul_of_pos_left _ (by omega)
  have hsum : (schedule.startDate + schedule.paymentInterval).toNat =
      schedule.startDate.toNat + schedule.paymentInterval.toNat := by
    rw [UInt32.toNat_add]; apply Nat.mod_eq_of_lt; unfold LoanSchedule.EndsInTime at hend; omega
  refine ⟨by rw [hn, hs, hp, hsum, Nat.sub_self, Nat.zero_add, Nat.one_mul], ?_⟩
  -- a new loan has no previous due date
  rw [hq, hn, UInt32.lt_iff_toNat_lt, hsum, UInt32.toNat_zero]
  omega

/-- Every transaction keeps a reachable loan on its schedule. -/
private lemma Loan.ReachableFrom.onSchedule {start : Loan} {t₀ : UInt32} {loan : Loan} {t : UInt32}
    (hr : Loan.ReachableFrom start t₀ loan t) (hend : start.schedule.EndsInTime) (hon : start.OnSchedule) :
    loan.schedule.EndsInTime ∧ loan.OnSchedule := by
  refine ⟨by rw [hr.keepsTerms.schedule]; exact hend, ?_⟩
  induction hr with
  | refl => exact hon
  | refresh _ _ _ _ hr _ h ih =>
    exact ih.of_keepsDueDate (Loan.KeepsTerms.of_lawful h rfl rfl rfl rfl rfl)
      (Loan.KeepsDueDate.of_lawful h rfl rfl rfl)
  | accept loan _ _ _ r hr _ _ h ih =>
    exact ih.of_keepsDueDate (Loan.accept_keepsTerms _ _ _ h) (Loan.accept_keepsDueDate _ _ _ h)
  | regularPayment loan _ _ _ _ r hr _ _ h ih =>
    exact Loan.regularPayment_onSchedule _ _ _ _ _ (by rw [hr.keepsTerms.schedule]; exact hend)
      ih h
  | latePayment loan _ _ _ _ r hr _ _ h ih =>
    exact Loan.latePayment_onSchedule _ _ _ _ _ (by rw [hr.keepsTerms.schedule]; exact hend)
      ih h
  | fullPayment loan _ _ _ _ r hr _ _ h ih =>
    exact Loan.fullPayment_onSchedule _ _ _ _ _ (by rw [hr.keepsTerms.schedule]; exact hend)
      ih h
  | overpayment loan _ _ _ _ r hr _ _ h ih =>
    exact Loan.overpayment_onSchedule _ _ _ _ _ (by rw [hr.keepsTerms.schedule]; exact hend)
      ih h
  | impair loan _ _ _ r hr _ _ h ih =>
    exact ih.of_keepsDueDate (Loan.manageImpair_keepsTerms _ _ _ _ h)
      (Loan.manageImpair_keepsDueDate _ _ _ _ h)
  | unimpair loan _ _ _ r hr _ _ h ih =>
    exact ih.of_keepsDueDate (Loan.manageUnimpair_keepsTerms _ _ _ h)
      (Loan.changeImpairment_keepsDueDate _ _ _ _ h)
  | default loan _ _ _ r hr _ _ h ih =>
    exact ⟨by rw [Loan.manageDefault_paid _ _ _ h]; exact UInt32.zero_le,
      fun hpr => absurd (Loan.manageDefault_paid _ _ _ h) hpr⟩

/-- A reachable loan with payments left is due at the instalment its count of payments left says. -/
lemma Loan.Reachable.dueDate_proof (loan : Loan) (t : UInt32) (hr : loan.Reachable t)
    (hpr : loan.paymentRemaining ≠ 0) :
    loan.nextPaymentDueDate.toNat = loan.schedule.startDate.toNat +
      (loan.schedule.paymentTotal.toNat - loan.paymentRemaining.toNat + 1) * loan.schedule.paymentInterval.toNat := by
  obtain ⟨start, t₀, hc, hr⟩ := hr
  obtain ⟨hend, hon⟩ := hc.onSchedule
  exact ((hr.onSchedule hend hon).2.2 hpr).1

/-- A reachable loan has at most PaymentTotal payments left. -/
lemma Loan.Reachable.paymentRemaining_le (loan : Loan) (t : UInt32) (hr : loan.Reachable t) :
    loan.paymentRemaining ≤ loan.schedule.paymentTotal := by
  obtain ⟨start, t₀, hc, hr⟩ := hr
  obtain ⟨hend, hon⟩ := hc.onSchedule
  exact (hr.onSchedule hend hon).2.1

/-- A reachable loan with payments left has a due date, at least one PaymentInterval after StartDate. -/
lemma Loan.Reachable.nextPaymentDueDate_ne_zero (loan : Loan) (t : UInt32) (hr : loan.Reachable t)
    (hpr : loan.paymentRemaining ≠ 0) : loan.nextPaymentDueDate ≠ 0 := by
  have hdue := Loan.Reachable.dueDate_proof loan t hr hpr
  have hle := UInt32.le_iff_toNat_le.mp (Loan.Reachable.paymentRemaining_le loan t hr)
  have hI := UInt32.le_iff_toNat_le.mp loan.valid.paymentInterval_min
  have h60 : minPaymentInterval.toNat = 60 := rfl
  have hk : loan.schedule.paymentInterval.toNat ≤
      (loan.schedule.paymentTotal.toNat - loan.paymentRemaining.toNat + 1) * loan.schedule.paymentInterval.toNat :=
    Nat.le_mul_of_pos_left _ (by omega)
  intro h0
  rw [h0] at hdue
  simp only [UInt32.toNat_zero] at hdue
  omega

/-- A reachable loan with payments left is due after its previous due date. -/
lemma Loan.Reachable.dueDates_ordered (loan : Loan) (t : UInt32) (hr : loan.Reachable t)
    (hpr : loan.paymentRemaining ≠ 0) : loan.previousPaymentDueDate < loan.nextPaymentDueDate := by
  obtain ⟨start, t₀, hc, hr⟩ := hr
  obtain ⟨hend, hon⟩ := hc.onSchedule
  exact ((hr.onSchedule hend hon).2.2 hpr).2

end XRPL.Model.Lending
