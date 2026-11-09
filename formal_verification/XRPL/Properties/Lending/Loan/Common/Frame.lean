import XRPL.Properties.Lending.Common.PoolBalances
import XRPL.Properties.Lending.Loan.LoanValid
import XRPL.Model.Lending.Loan.LoanAccept
import XRPL.Model.Lending.Loan.LoanManage
import XRPL.Model.Lending.Loan.LoanPay

/-! # What a loan transaction never changes

Accept, the payments and the management actions rebuild the loan from the old record, so its
rates, fees, schedule, LoanScale and overpayment flag stay as they were. -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault (Vault RawVault)

open private Loan.changeImpairment from XRPL.Model.Lending.Loan.LoanManage
open private Loan.doPayment Loan.settlePayment validatePostPayment UnsettledPayment.payInstalments
  Loan.unimpairIfImpaired Loan.payScheduledInstalments UnsettledPayment.applyOverpayment Loan.paySingleInstalment
  from XRPL.Model.Lending.Loan.LoanPay

/-- The loan terms a transaction never changes. -/
structure Loan.KeepsTerms (loan loan' : Loan) : Prop where
  rates : loan'.rates = loan.rates
  fees : loan'.fees = loan.fees
  schedule : loan'.schedule = loan.schedule
  loanScale : loan'.loanScale = loan.loanScale
  allowsOverpayment : loan'.allowsOverpayment = loan.allowsOverpayment

/-- A loan keeps its own terms. -/
lemma Loan.KeepsTerms.refl (loan : Loan) : Loan.KeepsTerms loan loan := ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- Keeping the terms over two steps keeps them over both. -/
lemma Loan.KeepsTerms.trans {a b c : Loan} (h₁ : Loan.KeepsTerms a b) (h₂ : Loan.KeepsTerms b c) :
    Loan.KeepsTerms a c :=
  ⟨h₂.rates.trans h₁.rates, h₂.fees.trans h₁.fees, h₂.schedule.trans h₁.schedule,
    h₂.loanScale.trans h₁.loanScale, h₂.allowsOverpayment.trans h₁.allowsOverpayment⟩

/-- A re-checked record with the same terms keeps them. -/
lemma Loan.KeepsTerms.of_lawful {loan loan' : Loan} {raw : RawLoan} (h : raw.to_lawful = .ok loan')
    (hr : raw.rates = loan.rates) (hf : raw.fees = loan.fees) (hs : raw.schedule = loan.schedule)
    (hl : raw.loanScale = loan.loanScale) (ho : raw.allowsOverpayment = loan.allowsOverpayment) :
    Loan.KeepsTerms loan loan' := by
  obtain ⟨he, -, -⟩ := RawLoan.to_lawful_ok h
  subst he
  exact ⟨hr, hf, hs, hl, ho⟩

/-- Accept keeps the terms. -/
lemma Loan.accept_keepsTerms (loan : Loan) (v : Vault) (r : LoanWithDisbursement Vault)
    (h : (loan.accept v).run = .ok (.ok r)) : Loan.KeepsTerms loan r.loan' := by
  simp only [Loan.accept] at h
  unfold_ter at h
  walk_ok
  all_goals
    have hl := ‹RawLoan.to_lawful _ = Except.ok _›
    exact Loan.KeepsTerms.of_lawful hl rfl rfl rfl rfl rfl
/-- Setting or clearing the impaired flag keeps the terms. -/
private lemma Loan.changeImpairment_keepsTerms (loan : Loan) (v : Vault) (b : Bool) (r : LoanWithPool Vault)
    (h : (Loan.changeImpairment loan v b).run = .ok (.ok r)) : Loan.KeepsTerms loan r.loan' := by
  simp only [Loan.changeImpairment] at h
  unfold_ter at h
  walk_ok
  all_goals
    have hl := ‹RawLoan.to_lawful _ = Except.ok _›
    exact Loan.KeepsTerms.of_lawful hl rfl rfl rfl rfl rfl

/-- Impair keeps the terms. -/
lemma Loan.manageImpair_keepsTerms (loan : Loan) (v : Vault) (now : UInt32) (r : LoanWithPool Vault)
    (h : (loan.manageImpair v now).run = .ok (.ok r)) : Loan.KeepsTerms loan r.loan' := by
  simp only [Loan.manageImpair] at h
  unfold_ter at h
  walk_ok
  exact Loan.changeImpairment_keepsTerms loan v true r ‹_›

/-- Unimpair keeps the terms. -/
lemma Loan.manageUnimpair_keepsTerms (loan : Loan) (v : Vault) (r : LoanWithPool Vault)
    (h : (loan.manageUnimpair v).run = .ok (.ok r)) : Loan.KeepsTerms loan r.loan' :=
  Loan.changeImpairment_keepsTerms loan v false r h

/-- Default keeps the terms. -/
lemma Loan.manageDefault_keepsTerms (loan : Loan) (v : Vault) (r : LoanWithAmounts Vault)
    (h : (loan.manageDefault v).run = .ok (.ok r)) : Loan.KeepsTerms loan r.loan' := by
  simp only [Loan.manageDefault] at h
  unfold_ter at h
  walk_ok
  all_goals
    have hl := ‹RawLoan.to_lawful _ = Except.ok _›
    exact Loan.KeepsTerms.of_lawful hl rfl rfl rfl rfl rfl

/-- Advancing the loan by one instalment keeps the terms. -/
lemma Loan.doPayment_keepsTerms (loan : Loan) (pc : PaymentComponents) (loan' : Loan)
    (h : Loan.doPayment loan pc = .ok loan') : Loan.KeepsTerms loan loan' := by
  unfold Loan.doPayment at h
  dsimp only at h
  split at h
  · obtain ⟨l, hl, h⟩ := bind_ok_peel _ _ _ h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    exact Loan.KeepsTerms.of_lawful hl rfl rfl rfl rfl rfl
  · obtain ⟨_, -, h⟩ := bind_ok_peel _ _ _ h
    obtain ⟨_, -, h⟩ := bind_ok_peel _ _ _ h
    obtain ⟨_, -, h⟩ := bind_ok_peel _ _ _ h
    obtain ⟨_, -, h⟩ := bind_ok_peel _ _ _ h
    obtain ⟨_, -, h⟩ := bind_ok_peel _ _ _ h
    obtain ⟨_, -, h⟩ := bind_ok_peel _ _ _ h
    exact Loan.KeepsTerms.of_lawful h rfl rfl rfl rfl rfl
/-- The post-payment check returns the result it checked. -/
lemma validatePostPayment_eq {α : Type} [AssetPool α] (pool : α) (result r : LoanWithAmounts α)
    (h : (validatePostPayment pool result).run = .ok (.ok r)) : r = result := by
  simp only [validatePostPayment] at h
  unfold_ter at h
  walk_ok
  all_goals rfl

/-- Settling a payment against the broker and the vault keeps the terms. -/
lemma Loan.settlePayment_keepsTerms {α : Type} [AssetPool α] (loan : Loan) (pool : α) (amounts : PaymentAmounts)
    (si : Number) (r : LoanWithAmounts α) (h : (Loan.settlePayment loan pool amounts si).run = .ok (.ok r)) :
    Loan.KeepsTerms loan r.loan' := by
  simp only [Loan.settlePayment] at h
  unfold_ter at h
  walk_ok
  all_goals
    have hv := validatePostPayment_eq _ _ r ‹_›
    subst hv
    have hl := ‹RawLoan.to_lawful _ = Except.ok _›
    exact Loan.KeepsTerms.of_lawful hl rfl rfl rfl rfl rfl
/-- Paying scheduled instalments one at a time keeps the terms. -/
private lemma UnsettledPayment.payInstalments_keepsTerms {α : Type} (amount : Number) :
    ∀ (n : Nat) (payment p : UnsettledPayment α), UnsettledPayment.payInstalments payment n amount = .ok p →
      Loan.KeepsTerms payment.loan p.loan := by
  intro n
  induction n with
  | zero =>
    intro payment p h
    unfold UnsettledPayment.payInstalments at h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    exact Loan.KeepsTerms.refl _
  | succ k ih =>
    intro payment p h
    unfold UnsettledPayment.payInstalments at h
    dsimp only at h
    split at h
    · simp only [pure, Except.pure, Except.ok.injEq] at h; subst h; exact Loan.KeepsTerms.refl _
    · obtain ⟨_, -, h⟩ := bind_ok_peel _ _ _ h
      obtain ⟨pc, -, h⟩ := bind_ok_peel _ _ _ h
      try dsimp only at h
      obtain ⟨_, -, h⟩ := bind_ok_peel _ _ _ h
      obtain ⟨_, -, h⟩ := bind_ok_peel _ _ _ h
      split at h
      · simp only [pure, Except.pure, Except.ok.injEq] at h; subst h; exact Loan.KeepsTerms.refl _
      · obtain ⟨_, -, h⟩ := bind_ok_peel _ _ _ h
        obtain ⟨_, -, h⟩ := bind_ok_peel _ _ _ h
        obtain ⟨loan', hl, h⟩ := bind_ok_peel _ _ _ h
        obtain ⟨_, -, h⟩ := bind_ok_peel _ _ _ h
        obtain ⟨_, -, h⟩ := bind_ok_peel _ _ _ h
        try dsimp only at h
        have hk := Loan.doPayment_keepsTerms _ _ _ hl
        split at h
        · simp only [pure, Except.pure, Except.ok.injEq] at h; subst h; exact hk
        · exact hk.trans (ih _ _ h)
/-- Re-amortizing after an overpayment keeps the terms. -/
lemma UnsettledPayment.applyOverpayment_keepsTerms {α : Type} (payment p : UnsettledPayment α) (amount : Number)
    (h : UnsettledPayment.applyOverpayment payment amount = .ok p) : Loan.KeepsTerms payment.loan p.loan := by
  unfold UnsettledPayment.applyOverpayment at h
  unfold_ter at h
  walk_ok
  all_goals first
    | exact Loan.KeepsTerms.refl _
    | (have hl := ‹RawLoan.to_lawful _ = Except.ok _›
       exact Loan.KeepsTerms.of_lawful hl rfl rfl rfl rfl rfl)

/-- Clearing an impairment before a payment keeps the terms. -/
lemma Loan.unimpairIfImpaired_keepsTerms {α : Type} [AssetPool α] (loan : Loan) (pool : α)
    (r : LoanWithPool α) (h : (Loan.unimpairIfImpaired loan pool).run = .ok (.ok r)) :
    Loan.KeepsTerms loan r.loan' := by
  unfold Loan.unimpairIfImpaired at h
  split at h
  · simp only [Loan.manageUnimpair, Loan.changeImpairment] at h
    unfold_ter at h
    walk_ok
    all_goals
      have hl := ‹RawLoan.to_lawful _ = Except.ok _›
      exact Loan.KeepsTerms.of_lawful hl rfl rfl rfl rfl rfl
  · unfold_ter at h
    walk_ok
    exact Loan.KeepsTerms.refl _
/-- The scheduled part of a payment keeps the terms. -/
private lemma Loan.payScheduledInstalments_keepsTerms {α : Type} [AssetPool α] (loan : Loan) (pool : α)
    (amount : Number) (now : UInt32) (p : UnsettledPayment α)
    (h : (Loan.payScheduledInstalments loan pool amount now).run = .ok (.ok p)) : Loan.KeepsTerms loan p.loan := by
  simp only [Loan.payScheduledInstalments] at h
  unfold_ter at h
  walk_ok
  all_goals
    have hu := Loan.unimpairIfImpaired_keepsTerms _ _ _ ‹_›
    have hp := UnsettledPayment.payInstalments_keepsTerms amount _ _ _ ‹_›
    exact hu.trans hp

/-- A single settled instalment keeps the terms. -/
private lemma Loan.paySingleInstalment_keepsTerms {α : Type} [AssetPool α] (loan : Loan) (pool : α)
    (pc : PaymentComponents) (amount : Number) (r : LoanWithAmounts α)
    (h : (Loan.paySingleInstalment loan pool pc amount).run = .ok (.ok r)) : Loan.KeepsTerms loan r.loan' := by
  simp only [Loan.paySingleInstalment] at h
  unfold_ter at h
  walk_ok
  all_goals
    have hd := Loan.doPayment_keepsTerms _ _ _ ‹_›
    have hs := Loan.settlePayment_keepsTerms _ _ _ _ _ ‹_›
    exact hd.trans hs

/-- A regular payment keeps the terms. -/
lemma Loan.regularPayment_keepsTerms {α : Type} [AssetPool α] (loan : Loan) (pool : α) (amount : Number)
    (now : UInt32) (r : LoanWithAmounts α) (h : (loan.regularPayment pool amount now).run = .ok (.ok r)) :
    Loan.KeepsTerms loan r.loan' := by
  simp only [Loan.regularPayment] at h
  unfold_ter at h
  walk_ok
  all_goals
    have hp := Loan.payScheduledInstalments_keepsTerms _ _ _ _ _ ‹_›
    have hs := Loan.settlePayment_keepsTerms _ _ _ _ _ ‹_›
    exact hp.trans hs

/-- An overpayment keeps the terms. -/
lemma Loan.overpayment_keepsTerms {α : Type} [AssetPool α] (loan : Loan) (pool : α) (amount : Number)
    (now : UInt32) (r : LoanWithAmounts α) (h : (loan.overpayment pool amount now).run = .ok (.ok r)) :
    Loan.KeepsTerms loan r.loan' := by
  simp only [Loan.overpayment] at h
  unfold_ter at h
  walk_ok
  all_goals
    have hp := Loan.payScheduledInstalments_keepsTerms _ _ _ _ _ ‹_›
    have ho := UnsettledPayment.applyOverpayment_keepsTerms _ _ _ ‹_›
    have hs := Loan.settlePayment_keepsTerms _ _ _ _ _ ‹_›
    exact (hp.trans ho).trans hs

/-- A late payment keeps the terms. -/
lemma Loan.latePayment_keepsTerms {α : Type} [AssetPool α] (loan : Loan) (pool : α) (amount : Number)
    (now : UInt32) (r : LoanWithAmounts α) (h : (loan.latePayment pool amount now).run = .ok (.ok r)) :
    Loan.KeepsTerms loan r.loan' := by
  simp only [Loan.latePayment] at h
  unfold_ter at h
  walk_ok
  all_goals
    have hu := Loan.unimpairIfImpaired_keepsTerms _ _ _ ‹_›
    have hs := Loan.paySingleInstalment_keepsTerms _ _ _ _ _ ‹_›
    exact hu.trans hs

/-- A full payment keeps the terms. -/
lemma Loan.fullPayment_keepsTerms {α : Type} [AssetPool α] (loan : Loan) (pool : α) (amount : Number)
    (now : UInt32) (r : LoanWithAmounts α) (h : (loan.fullPayment pool amount now).run = .ok (.ok r)) :
    Loan.KeepsTerms loan r.loan' := by
  simp only [Loan.fullPayment] at h
  unfold_ter at h
  walk_ok
  all_goals
    have hu := Loan.unimpairIfImpaired_keepsTerms _ _ _ ‹_›
    have hs := Loan.paySingleInstalment_keepsTerms _ _ _ _ _ ‹_›
    exact hu.trans hs
end XRPL.Model.Lending
