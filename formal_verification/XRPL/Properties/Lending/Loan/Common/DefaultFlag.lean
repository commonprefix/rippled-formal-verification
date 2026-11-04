import XRPL.Properties.Lending.Loan.Common.Frame
import XRPL.Properties.Lending.Loan.Common.ReachableDefs
import XRPL.Properties.Lending.Loan.Common.SetUpdates
import XRPL.Properties.Lending.Loan.Common.ManageProofs

/-! # Only a default marks a loan defaulted, and it leaves no payment

Accept, the payments, impair and unimpair rebuild the loan from the old record, so they keep its defaulted flag.
A default zeroes PaymentRemaining, so a defaulted reachable loan has no payment left. -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault (Vault RawVault)

open private Loan.changeImpairment from XRPL.Model.Lending.Loan.LoanManage
open private Loan.doPayment Loan.settlePayment validatePostPayment UnsettledPayment.payInstalments
  Loan.unimpairIfImpaired Loan.payScheduledInstalments UnsettledPayment.applyOverpayment Loan.paySingleInstalment
  from XRPL.Model.Lending.Loan.LoanPay

/-- A transaction keeps the defaulted flag. -/
structure Loan.KeepsDefault (loan loan' : Loan) : Prop where
  isDefault : loan'.isDefault = loan.isDefault

private lemma Loan.KeepsDefault.refl (loan : Loan) : Loan.KeepsDefault loan loan := ⟨rfl⟩

private lemma Loan.KeepsDefault.trans {a b c : Loan} (h₁ : Loan.KeepsDefault a b) (h₂ : Loan.KeepsDefault b c) :
    Loan.KeepsDefault a c :=
  ⟨h₂.isDefault.trans h₁.isDefault⟩

/-- A re-checked record with the same flag keeps it. -/
private lemma Loan.KeepsDefault.of_lawful {loan loan' : Loan} {raw : RawLoan} (h : raw.to_lawful = .ok loan')
    (hd : raw.isDefault = loan.isDefault) : Loan.KeepsDefault loan loan' := by
  obtain ⟨he, -, -⟩ := RawLoan.to_lawful_ok h
  subst he
  exact ⟨hd⟩

private lemma Loan.changeImpairment_keepsDefault (loan : Loan) (v : Vault) (b : Bool) (r : LoanWithPool Vault)
    (h : (Loan.changeImpairment loan v b).run = .ok (.ok r)) : Loan.KeepsDefault loan r.loan' := by
  simp only [Loan.changeImpairment] at h
  unfold_ter at h
  walk_ok
  all_goals
    have hl := ‹RawLoan.to_lawful _ = Except.ok _›
    exact Loan.KeepsDefault.of_lawful hl rfl

private lemma Loan.doPayment_keepsDefault (loan : Loan) (pc : PaymentComponents) (loan' : Loan)
    (h : Loan.doPayment loan pc = .ok loan') : Loan.KeepsDefault loan loan' := by
  unfold Loan.doPayment at h
  dsimp only at h
  split at h
  · obtain ⟨l, hl, h⟩ := bind_ok_peel _ _ _ h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    exact Loan.KeepsDefault.of_lawful hl rfl
  · obtain ⟨_, -, h⟩ := bind_ok_peel _ _ _ h
    obtain ⟨_, -, h⟩ := bind_ok_peel _ _ _ h
    obtain ⟨_, -, h⟩ := bind_ok_peel _ _ _ h
    obtain ⟨_, -, h⟩ := bind_ok_peel _ _ _ h
    exact Loan.KeepsDefault.of_lawful h rfl

private lemma Loan.settlePayment_keepsDefault {α : Type} [AssetPool α] (loan : Loan) (pool : α)
    (amounts : PaymentAmounts) (si : Number) (r : LoanWithAmounts α)
    (h : (Loan.settlePayment loan pool amounts si).run = .ok (.ok r)) : Loan.KeepsDefault loan r.loan' := by
  simp only [Loan.settlePayment] at h
  unfold_ter at h
  walk_ok
  all_goals
    have hv := validatePostPayment_eq _ _ r ‹_›
    subst hv
    have hl := ‹RawLoan.to_lawful _ = Except.ok _›
    exact Loan.KeepsDefault.of_lawful hl rfl

private lemma UnsettledPayment.payInstalments_keepsDefault {α : Type} (amount : Number) :
    ∀ (n : Nat) (payment p : UnsettledPayment α), UnsettledPayment.payInstalments payment n amount = .ok p →
      Loan.KeepsDefault payment.loan p.loan := by
  intro n
  induction n with
  | zero =>
    intro payment p h
    unfold UnsettledPayment.payInstalments at h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    exact Loan.KeepsDefault.refl _
  | succ k ih =>
    intro payment p h
    unfold UnsettledPayment.payInstalments at h
    dsimp only at h
    split at h
    · simp only [pure, Except.pure, Except.ok.injEq] at h; subst h; exact Loan.KeepsDefault.refl _
    · obtain ⟨_, -, h⟩ := bind_ok_peel _ _ _ h
      obtain ⟨pc, -, h⟩ := bind_ok_peel _ _ _ h
      try dsimp only at h
      obtain ⟨_, -, h⟩ := bind_ok_peel _ _ _ h
      obtain ⟨_, -, h⟩ := bind_ok_peel _ _ _ h
      split at h
      · simp only [pure, Except.pure, Except.ok.injEq] at h; subst h; exact Loan.KeepsDefault.refl _
      · obtain ⟨_, -, h⟩ := bind_ok_peel _ _ _ h
        obtain ⟨_, -, h⟩ := bind_ok_peel _ _ _ h
        obtain ⟨loan', hl, h⟩ := bind_ok_peel _ _ _ h
        obtain ⟨_, -, h⟩ := bind_ok_peel _ _ _ h
        obtain ⟨_, -, h⟩ := bind_ok_peel _ _ _ h
        try dsimp only at h
        have hk := Loan.doPayment_keepsDefault _ _ _ hl
        split at h
        · simp only [pure, Except.pure, Except.ok.injEq] at h; subst h; exact hk
        · exact hk.trans (ih _ _ h)

private lemma UnsettledPayment.applyOverpayment_keepsDefault {α : Type} (payment p : UnsettledPayment α)
    (amount : Number) (h : UnsettledPayment.applyOverpayment payment amount = .ok p) :
    Loan.KeepsDefault payment.loan p.loan := by
  unfold UnsettledPayment.applyOverpayment at h
  unfold_ter at h
  walk_ok
  all_goals first
    | exact Loan.KeepsDefault.refl _
    | (have hl := ‹RawLoan.to_lawful _ = Except.ok _›
       exact Loan.KeepsDefault.of_lawful hl rfl)

private lemma Loan.unimpairIfImpaired_keepsDefault {α : Type} [AssetPool α] (loan : Loan) (pool : α)
    (r : LoanWithPool α) (h : (Loan.unimpairIfImpaired loan pool).run = .ok (.ok r)) :
    Loan.KeepsDefault loan r.loan' := by
  unfold Loan.unimpairIfImpaired at h
  split at h
  · simp only [Loan.manageUnimpair, Loan.changeImpairment] at h
    unfold_ter at h
    walk_ok
    all_goals
      have hl := ‹RawLoan.to_lawful _ = Except.ok _›
      exact Loan.KeepsDefault.of_lawful hl rfl
  · unfold_ter at h
    walk_ok
    exact Loan.KeepsDefault.refl _

private lemma Loan.payScheduledInstalments_keepsDefault {α : Type} [AssetPool α] (loan : Loan) (pool : α)
    (amount : Number) (now : UInt32) (p : UnsettledPayment α)
    (h : (Loan.payScheduledInstalments loan pool amount now).run = .ok (.ok p)) :
    Loan.KeepsDefault loan p.loan := by
  simp only [Loan.payScheduledInstalments] at h
  unfold_ter at h
  walk_ok
  all_goals
    have hu := Loan.unimpairIfImpaired_keepsDefault _ _ _ ‹_›
    have hp := UnsettledPayment.payInstalments_keepsDefault amount _ _ _ ‹_›
    exact hu.trans hp

private lemma Loan.paySingleInstalment_keepsDefault {α : Type} [AssetPool α] (loan : Loan) (pool : α)
    (pc : PaymentComponents) (amount : Number) (r : LoanWithAmounts α)
    (h : (Loan.paySingleInstalment loan pool pc amount).run = .ok (.ok r)) : Loan.KeepsDefault loan r.loan' := by
  simp only [Loan.paySingleInstalment] at h
  unfold_ter at h
  walk_ok
  all_goals
    have hd := Loan.doPayment_keepsDefault _ _ _ ‹_›
    have hs := Loan.settlePayment_keepsDefault _ _ _ _ _ ‹_›
    exact hd.trans hs

private lemma Loan.regularPayment_keepsDefault {α : Type} [AssetPool α] (loan : Loan) (pool : α) (amount : Number)
    (now : UInt32) (r : LoanWithAmounts α) (h : (loan.regularPayment pool amount now).run = .ok (.ok r)) :
    Loan.KeepsDefault loan r.loan' := by
  simp only [Loan.regularPayment] at h
  unfold_ter at h
  walk_ok
  all_goals
    have hp := Loan.payScheduledInstalments_keepsDefault _ _ _ _ _ ‹_›
    have hs := Loan.settlePayment_keepsDefault _ _ _ _ _ ‹_›
    exact hp.trans hs

private lemma Loan.overpayment_keepsDefault {α : Type} [AssetPool α] (loan : Loan) (pool : α) (amount : Number)
    (now : UInt32) (r : LoanWithAmounts α) (h : (loan.overpayment pool amount now).run = .ok (.ok r)) :
    Loan.KeepsDefault loan r.loan' := by
  simp only [Loan.overpayment] at h
  unfold_ter at h
  walk_ok
  all_goals
    have hp := Loan.payScheduledInstalments_keepsDefault _ _ _ _ _ ‹_›
    have ho := UnsettledPayment.applyOverpayment_keepsDefault _ _ _ ‹_›
    have hs := Loan.settlePayment_keepsDefault _ _ _ _ _ ‹_›
    exact (hp.trans ho).trans hs

private lemma Loan.latePayment_keepsDefault {α : Type} [AssetPool α] (loan : Loan) (pool : α) (amount : Number)
    (now : UInt32) (r : LoanWithAmounts α) (h : (loan.latePayment pool amount now).run = .ok (.ok r)) :
    Loan.KeepsDefault loan r.loan' := by
  simp only [Loan.latePayment] at h
  unfold_ter at h
  walk_ok
  all_goals
    have hu := Loan.unimpairIfImpaired_keepsDefault _ _ _ ‹_›
    have hs := Loan.paySingleInstalment_keepsDefault _ _ _ _ _ ‹_›
    exact hu.trans hs

private lemma Loan.fullPayment_keepsDefault {α : Type} [AssetPool α] (loan : Loan) (pool : α) (amount : Number)
    (now : UInt32) (r : LoanWithAmounts α) (h : (loan.fullPayment pool amount now).run = .ok (.ok r)) :
    Loan.KeepsDefault loan r.loan' := by
  simp only [Loan.fullPayment] at h
  unfold_ter at h
  walk_ok
  all_goals
    have hu := Loan.unimpairIfImpaired_keepsDefault _ _ _ ‹_›
    have hs := Loan.paySingleInstalment_keepsDefault _ _ _ _ _ ‹_›
    exact hu.trans hs

/-- A loan that passes the payment checks has a payment left. -/
private lemma Loan.canPay_remaining (loan : Loan) (pt : LoanPaymentType) (h : loan.canPay pt = .tesSUCCESS) :
    loan.paymentRemaining ≠ 0 := by
  intro h0
  unfold Loan.canPay at h
  simp [h0] at h
  split_ifs at h

/-- A loan that passes the impair or unimpair checks is not defaulted. -/
private lemma Loan.canManage_not_default (loan : Loan) (action : LoanManageAction) (now : UInt32)
    (h : loan.canManage action now = .tesSUCCESS) : loan.isDefault = false := by
  unfold Loan.canManage at h
  cases hd : loan.isDefault
  · rfl
  · simp only [hd, if_true] at h
    split_ifs at h

/-- A defaulted loan reachable from create has no payment left. -/
lemma Loan.ReachableFrom.default_paidOff {start loan : Loan} {t₀ t : UInt32} (hs : start.isDefault = false)
    (h : Loan.ReachableFrom start t₀ loan t) : loan.isDefault = true → loan.paymentRemaining = 0 := by
  induction h with
  | refl => intro hd; rw [hs] at hd; cases hd
  | refresh loan loan' t broker _ _ hl ih =>
    obtain ⟨he, -, -⟩ := RawLoan.to_lawful_ok hl
    intro hd
    have hd' : loan.isDefault = true := by
      rw [show loan'.isDefault = loan'.toRawLoan.isDefault from rfl, he] at hd; exact hd
    rw [show loan'.paymentRemaining = loan'.toRawLoan.paymentRemaining from rfl, he]
    exact ih hd'
  | accept loan t t' v r _ _ _ hok ih =>
    have hacc : ({ loan.toRawLoan with isPending := false } : RawLoan).to_lawful = .ok r.loan' := by
      simp only [Loan.accept] at hok
      unfold_ter at hok
      walk_ok
      exact ‹RawLoan.to_lawful _ = Except.ok _›
    obtain ⟨he, -, -⟩ := RawLoan.to_lawful_ok hacc
    intro hd
    rw [show r.loan'.isDefault = r.loan'.toRawLoan.isDefault from rfl, he] at hd
    rw [show r.loan'.paymentRemaining = r.loan'.toRawLoan.paymentRemaining from rfl, he]
    exact ih hd
  | regularPayment loan t t' v amount r _ _ hc hok ih =>
    intro hd
    rw [(Loan.regularPayment_keepsDefault _ _ _ _ _ hok).isDefault] at hd
    exact absurd (ih hd) (Loan.canPay_remaining _ _ hc)
  | latePayment loan t t' v amount r _ _ hc hok ih =>
    intro hd
    rw [(Loan.latePayment_keepsDefault _ _ _ _ _ hok).isDefault] at hd
    exact absurd (ih hd) (Loan.canPay_remaining _ _ hc)
  | fullPayment loan t t' v amount r _ _ hc hok ih =>
    intro hd
    rw [(Loan.fullPayment_keepsDefault _ _ _ _ _ hok).isDefault] at hd
    exact absurd (ih hd) (Loan.canPay_remaining _ _ hc)
  | overpayment loan t t' v amount r _ _ hc hok ih =>
    intro hd
    rw [(Loan.overpayment_keepsDefault _ _ _ _ _ hok).isDefault] at hd
    exact absurd (ih hd) (Loan.canPay_remaining _ _ hc)
  | impair loan t t' v r _ _ hc hok ih =>
    intro hd
    simp only [Loan.manageImpair] at hok
    unfold_ter at hok
    walk_ok
    rw [(Loan.changeImpairment_keepsDefault _ _ _ _ ‹_›).isDefault, Loan.canManage_not_default _ _ _ hc] at hd
    cases hd
  | unimpair loan t t' v r _ _ hc hok ih =>
    intro hd
    rw [(Loan.changeImpairment_keepsDefault _ _ _ _ hok).isDefault, Loan.canManage_not_default _ _ _ hc] at hd
    cases hd
  | default loan t t' v r _ _ _ hok _ =>
    intro _
    exact (Loan.manageDefault_closes_proof loan v r hok).2.2.2.1

/-- A defaulted reachable loan has no payment left. -/
lemma Loan.Reachable.default_paidOff {loan : Loan} {t : UInt32} (h : loan.Reachable t)
    (hd : loan.isDefault = true) : loan.paymentRemaining = 0 := by
  obtain ⟨start, t₀, ⟨broker, v, principal, rates, fees, pi, pt, gp, sd, ts, ao, r, -, hok, hr⟩, hreach⟩ := h
  obtain ⟨_, _, _, _, _, -, -, -, -, hl⟩ := Loan.create_ok_inv broker v principal rates fees _ ao ts r hok
  obtain ⟨he, -, -⟩ := RawLoan.to_lawful_ok hl
  have hs : start.isDefault = false := by
    rw [← hr, show r.loan'.isDefault = r.loan'.toRawLoan.isDefault from rfl, he]; rfl
  exact hreach.default_paidOff hs hd

end XRPL.Model.Lending
