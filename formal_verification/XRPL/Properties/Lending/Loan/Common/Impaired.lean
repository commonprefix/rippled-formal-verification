import XRPL.Properties.Lending.Loan.Common.Schedule
import XRPL.Properties.Lending.Common.Walk

/-! # Impaired loans stay late

Impair needs a late loan and keeps its due date. Every payment clears the impaired flag first, and the
close time never goes back, so an impaired loan with payments left stays late. -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault (Vault RawVault)

open private Loan.changeImpairment from XRPL.Model.Lending.Loan.LoanManage
open private Loan.doPayment Loan.settlePayment validatePostPayment UnsettledPayment.payInstalments
  Loan.unimpairIfImpaired Loan.payScheduledInstalments UnsettledPayment.applyOverpayment Loan.paySingleInstalment
  from XRPL.Model.Lending.Loan.LoanPay

/-- Setting or clearing the impaired flag sets it to the requested value. -/
lemma Loan.changeImpairment_flag {α : Type} [AssetPool α] (loan : Loan) (pool : α) (b : Bool)
    (r : LoanWithPool α) (h : (Loan.changeImpairment loan pool b).run = .ok (.ok r)) : r.loan'.isImpaired = b := by
  simp only [Loan.changeImpairment] at h
  unfold_ter at h
  walk_ok'
  all_goals
    have hl := ‹RawLoan.to_lawful _ = Except.ok _›
    rw [(congrArg RawLoan.isImpaired (RawLoan.to_lawful_ok hl).1 :)]

/-- A payment first clears the impaired flag. -/
private lemma Loan.unimpairIfImpaired_flag {α : Type} [AssetPool α] (loan : Loan) (pool : α)
    (r : LoanWithPool α) (h : (Loan.unimpairIfImpaired loan pool).run = .ok (.ok r)) : r.loan'.isImpaired = false := by
  unfold Loan.unimpairIfImpaired at h
  split at h
  · exact Loan.changeImpairment_flag loan pool false r h
  · unfold_ter at h
    walk_ok'
    simpa using ‹¬ _ = true›

/-- An instalment keeps the impaired flag. -/
private lemma Loan.doPayment_flag (loan : Loan) (pc : PaymentComponents) (loan' : Loan)
    (h : Loan.doPayment loan pc = .ok loan') : loan'.isImpaired = loan.isImpaired := by
  unfold Loan.doPayment at h
  dsimp only at h
  split at h
  · obtain ⟨l, hl, h⟩ := bind_ok_peel _ _ _ h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    rw [(congrArg RawLoan.isImpaired (RawLoan.to_lawful_ok hl).1 :)]
  · obtain ⟨_, -, h⟩ := bind_ok_peel _ _ _ h
    obtain ⟨_, -, h⟩ := bind_ok_peel _ _ _ h
    obtain ⟨_, -, h⟩ := bind_ok_peel _ _ _ h
    obtain ⟨_, -, h⟩ := bind_ok_peel _ _ _ h
    rw [(congrArg RawLoan.isImpaired (RawLoan.to_lawful_ok h).1 :)]

/-- The settlement keeps the impaired flag. -/
private lemma Loan.settlePayment_flag {α : Type} [AssetPool α] (loan : Loan) (pool : α) (amounts : PaymentAmounts)
    (si : Number) (r : LoanWithAmounts α) (h : (Loan.settlePayment loan pool amounts si).run = .ok (.ok r)) :
    r.loan'.isImpaired = loan.isImpaired := by
  simp only [Loan.settlePayment] at h
  unfold_ter at h
  walk_ok'
  all_goals
    have hv := validatePostPayment_eq _ _ r ‹_›
    subst hv
    have hl := ‹RawLoan.to_lawful _ = Except.ok _›
    rw [(congrArg RawLoan.isImpaired (RawLoan.to_lawful_ok hl).1 :)]

/-- The scheduled instalments keep the impaired flag. -/
private lemma UnsettledPayment.payInstalments_flag {α : Type} (amount : Number) :
    ∀ (n : Nat) (payment p : UnsettledPayment α), UnsettledPayment.payInstalments payment n amount = .ok p →
      p.loan.isImpaired = payment.loan.isImpaired := by
  intro n
  induction n with
  | zero =>
    intro payment p h
    unfold UnsettledPayment.payInstalments at h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    rw [h]
  | succ k ih =>
    intro payment p h
    unfold UnsettledPayment.payInstalments at h
    unfold_ter at h
    walk_ok'
    all_goals first
      | rfl
      | (have hd := Loan.doPayment_flag _ _ _ ‹Loan.doPayment _ _ = _›; exact hd)
      | (rename_i hrec
         have hp := ih _ _ hrec
         rw [hp]
         exact Loan.doPayment_flag _ _ _ ‹Loan.doPayment _ _ = _›)

/-- The re-amortization keeps the impaired flag. -/
private lemma UnsettledPayment.applyOverpayment_flag {α : Type} (payment p : UnsettledPayment α) (amount : Number)
    (h : UnsettledPayment.applyOverpayment payment amount = .ok p) : p.loan.isImpaired = payment.loan.isImpaired := by
  unfold UnsettledPayment.applyOverpayment at h
  unfold_ter at h
  walk_ok'
  all_goals first
    | rfl
    | (have hl := ‹RawLoan.to_lawful _ = Except.ok _›
       rw [(congrArg RawLoan.isImpaired (RawLoan.to_lawful_ok hl).1 :)])
/-- The scheduled part of a payment leaves the loan not impaired. -/
private lemma Loan.payScheduledInstalments_flag {α : Type} [AssetPool α] (loan : Loan) (pool : α) (amount : Number)
    (now : UInt32) (p : UnsettledPayment α)
    (h : (Loan.payScheduledInstalments loan pool amount now).run = .ok (.ok p)) :
    p.loan.isImpaired = false := by
  simp only [Loan.payScheduledInstalments] at h
  unfold_ter at h
  walk_ok'
  all_goals
    have hu := Loan.unimpairIfImpaired_flag _ _ _ ‹(Loan.unimpairIfImpaired _ _) = _›
    have hi := ‹UnsettledPayment.payInstalments _ _ _ = _›
    rw [UnsettledPayment.payInstalments_flag amount _ _ _ hi]
    exact hu

/-- A single settled instalment keeps the impaired flag. -/
private lemma Loan.paySingleInstalment_flag {α : Type} [AssetPool α] (loan : Loan) (pool : α) (pc : PaymentComponents)
    (amount : Number) (r : LoanWithAmounts α) (h : (Loan.paySingleInstalment loan pool pc amount).run = .ok (.ok r)) :
    r.loan'.isImpaired = loan.isImpaired := by
  simp only [Loan.paySingleInstalment] at h
  unfold_ter at h
  walk_ok'
  all_goals
    rw [Loan.settlePayment_flag _ _ _ _ _ ‹(Loan.settlePayment _ _ _ _) = _›]
    exact Loan.doPayment_flag _ _ _ ‹Loan.doPayment _ _ = _›

/-- A payment of any type leaves the loan not impaired. -/
lemma Loan.payment_unimpaired {α : Type} [AssetPool α] (loan : Loan) (pool : α) (paymentType : LoanPaymentType)
    (amount : Number) (now : UInt32) (r : LoanWithAmounts α)
    (h : (match paymentType with
      | .regular => loan.regularPayment pool amount now
      | .late => loan.latePayment pool amount now
      | .full => loan.fullPayment pool amount now
      | .overpayment => loan.overpayment pool amount now).run = .ok (.ok r)) :
    r.loan'.isImpaired = false := by
  cases paymentType <;>
    simp only [Loan.regularPayment, Loan.latePayment, Loan.fullPayment, Loan.overpayment] at h <;>
    unfold_ter at h <;> walk_ok'
  all_goals first
    | (rw [Loan.settlePayment_flag _ _ _ _ _ ‹(Loan.settlePayment _ _ _ _) = _›]
       first
       | exact Loan.payScheduledInstalments_flag _ _ _ _ _ ‹(Loan.payScheduledInstalments _ _ _ _) = _›
       | (rw [UnsettledPayment.applyOverpayment_flag _ _ _ ‹UnsettledPayment.applyOverpayment _ _ = _›]
          exact Loan.payScheduledInstalments_flag _ _ _ _ _ ‹(Loan.payScheduledInstalments _ _ _ _) = _›))
    | (rw [Loan.paySingleInstalment_flag _ _ _ _ _ ‹(Loan.paySingleInstalment _ _ _ _) = _›]
       exact Loan.unimpairIfImpaired_flag _ _ _ ‹(Loan.unimpairIfImpaired _ _) = _›)
/-- Accept keeps the impaired flag. -/
private lemma Loan.accept_flag (loan : Loan) (v : Vault) (r : LoanWithPool Vault)
    (h : (loan.accept v).run = .ok (.ok r)) : r.loan'.isImpaired = loan.isImpaired := by
  simp only [Loan.accept] at h
  unfold_ter at h
  walk_ok'
  have hl := ‹RawLoan.to_lawful _ = Except.ok _›
  rw [(congrArg RawLoan.isImpaired (RawLoan.to_lawful_ok hl).1 :)]

/-- Impair succeeds only on a late loan. -/
private lemma Loan.manageImpair_late (loan : Loan) (v : Vault) (now : UInt32) (r : LoanWithPool Vault)
    (h : (loan.manageImpair v now).run = .ok (.ok r)) : loan.isPaymentLate now = true := by
  simp only [Loan.manageImpair] at h
  unfold_ter at h
  walk_ok'
  have hc := ‹¬ (!loan.isPaymentLate now) = true›
  cases hx : loan.isPaymentLate now
  · rw [hx] at hc; exact absurd rfl hc
  · rfl

/-- An impaired loan with payments left is past its due date at the close time `t` of its last
transaction. -/
private def Loan.LateIfImpaired (loan : Loan) (t : UInt32) : Prop :=
  loan.isImpaired = true → loan.paymentRemaining ≠ 0 → loan.nextPaymentDueDate < t

/-- Every transaction keeps an impaired loan late. -/
private lemma Loan.ReachableFrom.lateIfImpaired {start : Loan} {t₀ : UInt32} {loan : Loan} {t : UInt32}
    (hr : Loan.ReachableFrom start t₀ loan t) (h0 : start.LateIfImpaired t₀) : loan.LateIfImpaired t := by
  induction hr with
  | refl => exact h0
  | refresh loan loan' _ _ _ _ h ih =>
    intro hi hp
    obtain ⟨he, -, -⟩ := RawLoan.to_lawful_ok h
    have hi' : loan.isImpaired = true := by rw [← hi, he]
    have hp' : loan.paymentRemaining ≠ 0 := by rw [he] at hp; exact hp
    rw [he]; exact ih hi' hp'
  | accept loan _ _ _ r _ hle _ h ih =>
    intro hi hp
    have hd := Loan.accept_keepsDueDate _ _ _ h
    rw [Loan.accept_flag _ _ _ h] at hi
    rw [hd.paymentRemaining] at hp
    rw [hd.nextPaymentDueDate]
    have h1 := ih hi hp
    rw [UInt32.lt_iff_toNat_lt] at h1 ⊢
    rw [UInt32.le_iff_toNat_le] at hle
    omega
  | regularPayment loan _ _ _ _ r _ _ _ h _ =>
    intro hi; rw [Loan.payment_unimpaired loan _ .regular _ _ r h] at hi; cases hi
  | latePayment loan _ _ _ _ r _ _ _ h _ =>
    intro hi; rw [Loan.payment_unimpaired loan _ .late _ _ r h] at hi; cases hi
  | fullPayment loan _ _ _ _ r _ _ _ h _ =>
    intro hi; rw [Loan.payment_unimpaired loan _ .full _ _ r h] at hi; cases hi
  | overpayment loan _ _ _ _ r _ _ _ h _ =>
    intro hi; rw [Loan.payment_unimpaired loan _ .overpayment _ _ r h] at hi; cases hi
  | impair loan _ t' _ r _ _ _ h _ =>
    intro _ hp
    have hd := Loan.manageImpair_keepsDueDate _ _ _ _ h
    have hl := Loan.manageImpair_late _ _ _ _ h
    rw [hd.nextPaymentDueDate]
    simpa [Loan.isPaymentLate] using hl
  | unimpair loan _ _ _ r _ _ _ h _ =>
    intro hi; rw [Loan.changeImpairment_flag loan _ false r h] at hi; cases hi
  | default loan _ _ _ r _ _ _ h _ =>
    intro _ hp; exact absurd (Loan.manageDefault_paid _ _ _ h) hp

/-- A created loan is not impaired. -/
private lemma Loan.Created.not_impaired {start : Loan} {t₀ : UInt32} (hc : Loan.Created start t₀) :
    start.isImpaired = false := by
  obtain ⟨broker, v, principal, rates, fees, pi, pt, gp, sd, twoStep, ao, r, -, hok, rfl⟩ := hc
  obtain ⟨_, _, _, _, _, -, -, -, -, hloan⟩ := Loan.create_ok_inv broker v principal rates fees _ ao twoStep r hok
  rw [(congrArg RawLoan.isImpaired (RawLoan.to_lawful_ok hloan).1 :)]
  rfl

/-- An impaired reachable loan with payments left is late at the close time `t` of its last transaction. -/
lemma Loan.Reachable.impaired_late_proof (loan : Loan) (t : UInt32) (hr : loan.Reachable t)
    (hi : loan.isImpaired = true) (hp : loan.paymentRemaining ≠ 0) : loan.isPaymentLate t = true := by
  obtain ⟨start, t₀, hc, hr⟩ := hr
  have h0 : start.LateIfImpaired t₀ := by intro hi'; rw [hc.not_impaired] at hi'; cases hi'
  simpa [Loan.isPaymentLate] using hr.lateIfImpaired h0 hi hp
end XRPL.Model.Lending
