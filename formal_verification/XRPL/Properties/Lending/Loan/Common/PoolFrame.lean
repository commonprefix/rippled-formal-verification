import XRPL.Properties.Lending.Loan.Common.SetUpdates
import XRPL.Properties.Lending.Loan.Common.Frame
import XRPL.Model.Lending.Loan.LoanDelete

/-! # What a loan transaction never changes in the vault

Every loan transaction moves only the five balances of the vault, through its balance update, so
SharesTotal, AssetsMaximum, the schedule and the other settings stay as they were. -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault (Vault RawVault)

open private Loan.changeImpairment from XRPL.Model.Lending.Loan.LoanManage
open private Loan.doPayment Loan.settlePayment validatePostPayment UnsettledPayment.payInstalments
  Loan.unimpairIfImpaired Loan.payScheduledInstalments UnsettledPayment.applyOverpayment Loan.paySingleInstalment
  from XRPL.Model.Lending.Loan.LoanPay

/-- The vault fields a loan transaction never changes: everything but the five balances. -/
structure Vault.KeepsSettings (v v' : Vault) : Prop where
  numericType : v'.numericType = v.numericType
  scale : v'.scale = v.scale
  sharesTotal : v'.sharesTotal = v.sharesTotal
  assetsMaximum : v'.assetsMaximum = v.assetsMaximum
  schedule : v'.schedule = v.schedule
  earlyExitFeeRate : v'.earlyExitFeeRate = v.earlyExitFeeRate
  ownerCanBlockDeposit : v'.ownerCanBlockDeposit = v.ownerCanBlockDeposit
  depositBlocked : v'.depositBlocked = v.depositBlocked

/-- A vault keeps its own settings. -/
lemma Vault.KeepsSettings.refl (v : Vault) : Vault.KeepsSettings v v := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Keeping the settings over two steps keeps them over both. -/
lemma Vault.KeepsSettings.trans {a b c : Vault} (h₁ : Vault.KeepsSettings a b) (h₂ : Vault.KeepsSettings b c) :
    Vault.KeepsSettings a c :=
  ⟨h₂.1.trans h₁.1, h₂.2.trans h₁.2, h₂.3.trans h₁.3, h₂.4.trans h₁.4, h₂.5.trans h₁.5, h₂.6.trans h₁.6,
    h₂.7.trans h₁.7, h₂.8.trans h₁.8⟩

/-- The vault settings a loan operation keeps fix the base exponent. -/
lemma Vault.KeepsSettings.baseExponent_eq {v v' : Vault} (h : Vault.KeepsSettings v v') :
    v'.baseExponent = v.baseExponent := by
  unfold XRPL.Model.SingleAssetVault.Vault.baseExponent; rw [h.numericType, h.scale]

/-- A balance change keeps the vault settings. -/
private lemma Vault.poolAdjust_keepsSettings (v v' : Vault) (c : PoolBalanceChange)
    (h : AssetPool.adjustBalances v c = .ok (.ok v')) : Vault.KeepsSettings v v' := by
  obtain ⟨raw, hadj, hv'⟩ := Vault.poolAdjust_ok_inv v c v' h
  obtain ⟨he, -, -⟩ := XRPL.Model.SingleAssetVault.RawVault.to_lawful_ok hv'
  simp only [XRPL.Model.SingleAssetVault.Vault.adjustBalances] at hadj
  unfold_ter at hadj
  walk_ok
  all_goals
    open XRPL.Model.SingleAssetVault in
    exact ⟨(congrArg RawVault.numericType he :), (congrArg RawVault.scale he :),
      (congrArg RawVault.sharesTotal he :), (congrArg RawVault.assetsMaximum he :),
      (congrArg RawVault.schedule he :), (congrArg RawVault.earlyExitFeeRate he :),
      (congrArg RawVault.ownerCanBlockDeposit he :), (congrArg RawVault.depositBlocked he :)⟩
/-- A new loan keeps the vault settings. -/
lemma Loan.create_keepsSettings (broker : LoanBroker) (v : Vault) (principal : Number) (rates : LoanRates)
    (fees : LoanFees) (schedule : LoanSchedule) (ao pending : Bool) (r : LoanWithDisbursement Vault)
    (h : (Loan.create broker v principal rates fees schedule ao pending).run = .ok (.ok r)) :
    Vault.KeepsSettings v r.pool' := by
  obtain ⟨_, _, _, _, _, -, -, hpool, -, -⟩ := Loan.create_ok_inv broker v principal rates fees schedule ao pending r h
  exact Vault.poolAdjust_keepsSettings _ _ _ hpool

/-- Accept keeps the vault settings. -/
lemma Loan.accept_keepsSettings (loan : Loan) (v : Vault) (r : LoanWithDisbursement Vault)
    (h : (loan.accept v).run = .ok (.ok r)) : Vault.KeepsSettings v r.pool' := by
  simp only [Loan.accept] at h
  unfold_ter at h
  walk_ok
  exact Vault.poolAdjust_keepsSettings _ _ _ ‹_›

/-- Setting or clearing the impaired flag keeps the vault settings. -/
lemma Loan.changeImpairment_keepsSettings (loan : Loan) (v : Vault) (b : Bool) (r : LoanWithPool Vault)
    (h : (Loan.changeImpairment loan v b).run = .ok (.ok r)) : Vault.KeepsSettings v r.pool' := by
  simp only [Loan.changeImpairment] at h
  unfold_ter at h
  walk_ok
  all_goals exact Vault.poolAdjust_keepsSettings _ _ _ ‹_›

/-- Impair keeps the vault settings. -/
lemma Loan.manageImpair_keepsSettings (loan : Loan) (v : Vault) (now : UInt32) (r : LoanWithPool Vault)
    (h : (loan.manageImpair v now).run = .ok (.ok r)) : Vault.KeepsSettings v r.pool' := by
  simp only [Loan.manageImpair] at h
  unfold_ter at h
  walk_ok
  exact Loan.changeImpairment_keepsSettings loan v true r ‹_›

/-- Default keeps the vault settings. -/
lemma Loan.manageDefault_keepsSettings (loan : Loan) (v : Vault) (r : LoanWithAmounts Vault)
    (h : (loan.manageDefault v).run = .ok (.ok r)) : Vault.KeepsSettings v r.pool' := by
  simp only [Loan.manageDefault] at h
  unfold_ter at h
  walk_ok
  all_goals exact Vault.poolAdjust_keepsSettings _ _ _ ‹AssetPool.adjustBalances _ _ = _›

/-- Delete keeps the vault settings. -/
lemma Loan.delete_keepsSettings (loan : Loan) (v : Vault) (r : LoanBrokerWithPool Vault)
    (h : (loan.delete v).run = .ok (.ok r)) : Vault.KeepsSettings v r.pool' := by
  unfold Loan.delete at h
  split at h
  · simp only [Loan.deletePending] at h
    unfold_ter at h
    walk_ok
    exact Vault.poolAdjust_keepsSettings _ _ _ ‹AssetPool.adjustBalances _ _ = _›
  · unfold_ter at h
    walk_ok
    exact Vault.KeepsSettings.refl _

/-- Settling a payment keeps the vault settings. -/
private lemma Loan.settlePayment_keepsSettings (loan : Loan) (v : Vault) (amounts : PaymentAmounts) (si : Number)
    (r : LoanWithAmounts Vault) (h : (Loan.settlePayment loan v amounts si).run = .ok (.ok r)) :
    Vault.KeepsSettings v r.pool' := by
  simp only [Loan.settlePayment] at h
  unfold_ter at h
  walk_ok
  all_goals
    have hv := validatePostPayment_eq _ _ r ‹_›
    subst hv
    exact Vault.poolAdjust_keepsSettings _ _ _ ‹AssetPool.adjustBalances _ _ = _›

/-- Clearing an impairment before a payment keeps the vault settings. -/
private lemma Loan.unimpairIfImpaired_keepsSettings (loan : Loan) (v : Vault) (r : LoanWithPool Vault)
    (h : (Loan.unimpairIfImpaired loan v).run = .ok (.ok r)) : Vault.KeepsSettings v r.pool' := by
  unfold Loan.unimpairIfImpaired at h
  split at h
  · exact Loan.changeImpairment_keepsSettings loan v false r h
  · unfold_ter at h
    walk_ok
    exact Vault.KeepsSettings.refl _

/-- Paying scheduled instalments leaves the pool for the settlement. -/
lemma UnsettledPayment.payInstalments_pool {α : Type} (amount : Number) :
    ∀ (n : Nat) (payment p : UnsettledPayment α), UnsettledPayment.payInstalments payment n amount = .ok p →
      p.pool = payment.pool := by
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
    walk_ok
    all_goals first
      | rfl
      | (rename_i hrec; have hp := ih _ _ hrec; exact hp)

/-- Re-amortizing after an overpayment leaves the pool for the settlement. -/
lemma UnsettledPayment.applyOverpayment_pool {α : Type} (payment p : UnsettledPayment α) (amount : Number)
    (h : UnsettledPayment.applyOverpayment payment amount = .ok p) : p.pool = payment.pool := by
  unfold UnsettledPayment.applyOverpayment at h
  unfold_ter at h
  walk_ok
  all_goals rfl

/-- The scheduled part of a payment keeps the vault settings. -/
private lemma Loan.payScheduledInstalments_keepsSettings (loan : Loan) (v : Vault) (amount : Number) (now : UInt32)
    (p : UnsettledPayment Vault) (h : (Loan.payScheduledInstalments loan v amount now).run = .ok (.ok p)) :
    Vault.KeepsSettings v p.pool := by
  simp only [Loan.payScheduledInstalments] at h
  unfold_ter at h
  walk_ok
  all_goals
    have hu := Loan.unimpairIfImpaired_keepsSettings _ _ _ ‹(Loan.unimpairIfImpaired _ _) = _›
    rw [UnsettledPayment.payInstalments_pool amount _ _ _ ‹UnsettledPayment.payInstalments _ _ _ = _›]
    exact hu

/-- A single settled instalment keeps the vault settings. -/
private lemma Loan.paySingleInstalment_keepsSettings (loan : Loan) (v : Vault) (pc : PaymentComponents)
    (amount : Number) (r : LoanWithAmounts Vault) (h : (Loan.paySingleInstalment loan v pc amount).run = .ok (.ok r)) :
    Vault.KeepsSettings v r.pool' := by
  simp only [Loan.paySingleInstalment] at h
  unfold_ter at h
  walk_ok
  all_goals exact Loan.settlePayment_keepsSettings _ _ _ _ _ ‹(Loan.settlePayment _ _ _ _) = _›

/-- A regular payment keeps the vault settings. -/
lemma Loan.regularPayment_keepsSettings (loan : Loan) (v : Vault) (amount : Number) (now : UInt32)
    (r : LoanWithAmounts Vault) (h : (loan.regularPayment v amount now).run = .ok (.ok r)) :
    Vault.KeepsSettings v r.pool' := by
  simp only [Loan.regularPayment] at h
  unfold_ter at h
  walk_ok
  all_goals
    have hp := Loan.payScheduledInstalments_keepsSettings _ _ _ _ _ ‹(Loan.payScheduledInstalments _ _ _ _) = _›
    have hs := Loan.settlePayment_keepsSettings _ _ _ _ _ ‹(Loan.settlePayment _ _ _ _) = _›
    exact hp.trans hs

/-- An overpayment keeps the vault settings. -/
lemma Loan.overpayment_keepsSettings (loan : Loan) (v : Vault) (amount : Number) (now : UInt32)
    (r : LoanWithAmounts Vault) (h : (loan.overpayment v amount now).run = .ok (.ok r)) :
    Vault.KeepsSettings v r.pool' := by
  simp only [Loan.overpayment] at h
  unfold_ter at h
  walk_ok
  all_goals
    have hp := Loan.payScheduledInstalments_keepsSettings _ _ _ _ _ ‹(Loan.payScheduledInstalments _ _ _ _) = _›
    have hs := Loan.settlePayment_keepsSettings _ _ _ _ _ ‹(Loan.settlePayment _ _ _ _) = _›
    rw [UnsettledPayment.applyOverpayment_pool _ _ _ ‹UnsettledPayment.applyOverpayment _ _ = _›] at hs
    exact hp.trans hs

/-- A late payment keeps the vault settings. -/
lemma Loan.latePayment_keepsSettings (loan : Loan) (v : Vault) (amount : Number) (now : UInt32)
    (r : LoanWithAmounts Vault) (h : (loan.latePayment v amount now).run = .ok (.ok r)) :
    Vault.KeepsSettings v r.pool' := by
  simp only [Loan.latePayment] at h
  unfold_ter at h
  walk_ok
  all_goals
    have hu := Loan.unimpairIfImpaired_keepsSettings _ _ _ ‹(Loan.unimpairIfImpaired _ _) = _›
    have hs := Loan.paySingleInstalment_keepsSettings _ _ _ _ _ ‹(Loan.paySingleInstalment _ _ _ _) = _›
    exact hu.trans hs

/-- A full payment keeps the vault settings. -/
lemma Loan.fullPayment_keepsSettings (loan : Loan) (v : Vault) (amount : Number) (now : UInt32)
    (r : LoanWithAmounts Vault) (h : (loan.fullPayment v amount now).run = .ok (.ok r)) :
    Vault.KeepsSettings v r.pool' := by
  simp only [Loan.fullPayment] at h
  unfold_ter at h
  walk_ok
  all_goals
    have hu := Loan.unimpairIfImpaired_keepsSettings _ _ _ ‹(Loan.unimpairIfImpaired _ _) = _›
    have hs := Loan.paySingleInstalment_keepsSettings _ _ _ _ _ ‹(Loan.paySingleInstalment _ _ _ _) = _›
    exact hu.trans hs

end XRPL.Model.Lending
