import XRPL.Properties.Lending.Ledger.Common.LoanSteps
import XRPL.Properties.Lending.Ledger.Common.VaultSteps
import XRPL.Properties.Vault.Proofs.AssociateAssetPreserve
import XRPL.Properties.Lending.Ledger.Common.WithdrawHolder

/-! # The lending ledger stores AssetsAvailable exactly

Every update of AssetsAvailable rounds the new value to the vault's asset, so on a reachable ledger the
asset stores AssetsAvailable exactly. On an XRP or MPT vault this needs the asset's maximum to fit an int64. -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault (Vault RawVault)

open private Loan.changeImpairment from XRPL.Model.Lending.Loan.LoanManage
open private Loan.settlePayment validatePostPayment UnsettledPayment.payInstalments Loan.unimpairIfImpaired
  Loan.payScheduledInstalments UnsettledPayment.applyOverpayment Loan.paySingleInstalment
  from XRPL.Model.Lending.Loan.LoanPay

/-- The asset stores the vault's AssetsAvailable exactly. On an XRP or MPT vault this needs the asset's maximum to
fit an int64. -/
private def Vault.StoresAvailable (v : Vault) : Prop :=
  (v.numericType.isIntegral = true → v.numericType.maxValue.toNat ≤ maxRep.toNat) →
    STAmount.isRounded v.numericType v.assetsAvailable = false

/-- A step that keeps AssetsAvailable stored exactly. -/
private def Vault.KeepsAvailableStored (v v' : Vault) : Prop := Vault.StoresAvailable v → Vault.StoresAvailable v'

/-- A vault keeps its own AssetsAvailable stored exactly. -/
private lemma Vault.KeepsAvailableStored.refl (v : Vault) : Vault.KeepsAvailableStored v v := id

/-- Two steps that keep AssetsAvailable stored exactly keep it over both. -/
private lemma Vault.KeepsAvailableStored.trans {a b c : Vault} (h₁ : Vault.KeepsAvailableStored a b)
    (h₂ : Vault.KeepsAvailableStored b c) :
    Vault.KeepsAvailableStored a c := fun h => h₂ (h₁ h)

/-- A balance change rounds the new AssetsAvailable to the asset, so the asset stores it exactly. -/
private lemma Vault.poolAdjust_keepsStored (v v' : Vault) (c : PoolBalanceChange)
    (h : AssetPool.adjustBalances v c = .ok (.ok v')) : Vault.KeepsAvailableStored v v' := by
  intro _ hmax
  obtain ⟨raw, hadj, hv'⟩ := Vault.poolAdjust_ok_inv v c v' h
  have he := (XRPL.Model.SingleAssetVault.RawVault.to_lawful_ok hv').1
  simp only [XRPL.Model.SingleAssetVault.Vault.adjustBalances] at hadj
  unfold_ter at hadj
  walk_ok
  all_goals
    have hnt : v'.numericType = v.numericType := (congrArg RawVault.numericType he :)
    have haa : v'.assetsAvailable = _ := (congrArg RawVault.assetsAvailable he :)
    rw [hnt] at hmax ⊢
    rw [haa]
    exact STAmount.isRounded_eq_false_of_rounded _ _ _ hmax ‹_› (by rw [← haa]; exact v'.exact.assetsAvailable_nonneg)

/-- A new loan keeps AssetsAvailable stored exactly. -/
private lemma Loan.create_keepsStored (broker : LoanBroker) (v : Vault) (principal : Number) (rates : LoanRates)
    (fees : LoanFees) (schedule : LoanSchedule) (ao pending : Bool) (r : LoanWithDisbursement Vault)
    (h : (Loan.create broker v principal rates fees schedule ao pending).run = .ok (.ok r)) :
    Vault.KeepsAvailableStored v r.pool' := by
  obtain ⟨_, _, _, _, _, -, -, hpool, -, -⟩ := Loan.create_ok_inv broker v principal rates fees schedule ao pending r h
  exact Vault.poolAdjust_keepsStored _ _ _ hpool

/-- Accept keeps AssetsAvailable stored exactly. -/
private lemma Loan.accept_keepsStored (loan : Loan) (v : Vault) (r : LoanWithDisbursement Vault)
    (h : (loan.accept v).run = .ok (.ok r)) : Vault.KeepsAvailableStored v r.pool' := by
  simp only [Loan.accept] at h
  unfold_ter at h
  walk_ok
  exact Vault.poolAdjust_keepsStored _ _ _ ‹_›

/-- Setting or clearing the impaired flag keeps AssetsAvailable stored exactly. -/
private lemma Loan.changeImpairment_keepsStored (loan : Loan) (v : Vault) (b : Bool) (r : LoanWithPool Vault)
    (h : (Loan.changeImpairment loan v b).run = .ok (.ok r)) : Vault.KeepsAvailableStored v r.pool' := by
  simp only [Loan.changeImpairment] at h
  unfold_ter at h
  walk_ok
  all_goals exact Vault.poolAdjust_keepsStored _ _ _ ‹_›

/-- Default keeps AssetsAvailable stored exactly. -/
private lemma Loan.manageDefault_keepsStored (loan : Loan) (v : Vault) (r : LoanWithAmounts Vault)
    (h : (loan.manageDefault v).run = .ok (.ok r)) : Vault.KeepsAvailableStored v r.pool' := by
  simp only [Loan.manageDefault] at h
  unfold_ter at h
  walk_ok
  all_goals exact Vault.poolAdjust_keepsStored _ _ _ ‹AssetPool.adjustBalances _ _ = _›

/-- Delete keeps AssetsAvailable stored exactly. -/
private lemma Loan.delete_keepsStored (loan : Loan) (v : Vault) (r : LoanBrokerWithPool Vault)
    (h : (loan.delete v).run = .ok (.ok r)) : Vault.KeepsAvailableStored v r.pool' := by
  unfold Loan.delete at h
  split at h
  · simp only [Loan.deletePending] at h
    unfold_ter at h
    walk_ok
    exact Vault.poolAdjust_keepsStored _ _ _ ‹AssetPool.adjustBalances _ _ = _›
  · unfold_ter at h
    walk_ok
    exact Vault.KeepsAvailableStored.refl _

/-- Settling a payment keeps AssetsAvailable stored exactly. -/
private lemma Loan.settlePayment_keepsStored (loan : Loan) (v : Vault) (amounts : PaymentAmounts) (si : Number)
    (r : LoanWithAmounts Vault) (h : (Loan.settlePayment loan v amounts si).run = .ok (.ok r)) :
    Vault.KeepsAvailableStored v r.pool' := by
  simp only [Loan.settlePayment] at h
  unfold_ter at h
  walk_ok
  all_goals
    have hv := validatePostPayment_eq _ _ r ‹_›
    subst hv
    exact Vault.poolAdjust_keepsStored _ _ _ ‹AssetPool.adjustBalances _ _ = _›

/-- Clearing an impairment before a payment keeps AssetsAvailable stored exactly. -/
private lemma Loan.unimpairIfImpaired_keepsStored (loan : Loan) (v : Vault) (r : LoanWithPool Vault)
    (h : (Loan.unimpairIfImpaired loan v).run = .ok (.ok r)) : Vault.KeepsAvailableStored v r.pool' := by
  unfold Loan.unimpairIfImpaired at h
  split at h
  · exact Loan.changeImpairment_keepsStored loan v false r h
  · unfold_ter at h
    walk_ok
    exact Vault.KeepsAvailableStored.refl _

/-- The scheduled part of a payment keeps AssetsAvailable stored exactly. -/
private lemma Loan.payScheduledInstalments_keepsStored (loan : Loan) (v : Vault) (amount : Number) (now : UInt32)
    (p : UnsettledPayment Vault) (h : (Loan.payScheduledInstalments loan v amount now).run = .ok (.ok p)) :
    Vault.KeepsAvailableStored v p.pool := by
  simp only [Loan.payScheduledInstalments] at h
  unfold_ter at h
  walk_ok
  all_goals
    have hu := Loan.unimpairIfImpaired_keepsStored _ _ _ ‹(Loan.unimpairIfImpaired _ _) = _›
    rw [UnsettledPayment.payInstalments_pool amount _ _ _ ‹UnsettledPayment.payInstalments _ _ _ = _›]
    exact hu

/-- A single settled instalment keeps AssetsAvailable stored exactly. -/
private lemma Loan.paySingleInstalment_keepsStored (loan : Loan) (v : Vault) (pc : PaymentComponents)
    (amount : Number) (r : LoanWithAmounts Vault)
    (h : (Loan.paySingleInstalment loan v pc amount).run = .ok (.ok r)) : Vault.KeepsAvailableStored v r.pool' := by
  simp only [Loan.paySingleInstalment] at h
  unfold_ter at h
  walk_ok
  all_goals exact Loan.settlePayment_keepsStored _ _ _ _ _ ‹(Loan.settlePayment _ _ _ _) = _›

/-- A payment of any type keeps AssetsAvailable stored exactly. -/
private lemma Loan.pay_keepsStored (loan : Loan) (paymentType : LoanPaymentType) (v : Vault) (amount : Number)
    (now : UInt32) (r : LoanWithAmounts Vault) (h : (loan.pay v paymentType amount now).run = .ok (.ok r)) :
    Vault.KeepsAvailableStored v r.pool' := by
  cases paymentType with
  | regular =>
    simp only [Loan.pay, Loan.regularPayment] at h
    unfold_ter at h
    walk_ok
    all_goals
      have hp := Loan.payScheduledInstalments_keepsStored _ _ _ _ _ ‹(Loan.payScheduledInstalments _ _ _ _) = _›
      have hs := Loan.settlePayment_keepsStored _ _ _ _ _ ‹(Loan.settlePayment _ _ _ _) = _›
      exact hp.trans hs
  | late =>
    simp only [Loan.pay, Loan.latePayment] at h
    unfold_ter at h
    walk_ok
    all_goals
      have hu := Loan.unimpairIfImpaired_keepsStored _ _ _ ‹(Loan.unimpairIfImpaired _ _) = _›
      have hs := Loan.paySingleInstalment_keepsStored _ _ _ _ _ ‹(Loan.paySingleInstalment _ _ _ _) = _›
      exact hu.trans hs
  | full =>
    simp only [Loan.pay, Loan.fullPayment] at h
    unfold_ter at h
    walk_ok
    all_goals
      have hu := Loan.unimpairIfImpaired_keepsStored _ _ _ ‹(Loan.unimpairIfImpaired _ _) = _›
      have hs := Loan.paySingleInstalment_keepsStored _ _ _ _ _ ‹(Loan.paySingleInstalment _ _ _ _) = _›
      exact hu.trans hs
  | overpayment =>
    simp only [Loan.pay, Loan.overpayment] at h
    unfold_ter at h
    walk_ok
    all_goals
      have hp := Loan.payScheduledInstalments_keepsStored _ _ _ _ _ ‹(Loan.payScheduledInstalments _ _ _ _) = _›
      have hs := Loan.settlePayment_keepsStored _ _ _ _ _ ‹(Loan.settlePayment _ _ _ _) = _›
      rw [UnsettledPayment.applyOverpayment_pool _ _ _ ‹UnsettledPayment.applyOverpayment _ _ = _›] at hs
      exact hp.trans hs

/-- A management action keeps AssetsAvailable stored exactly. -/
private lemma Loan.manage_keepsStored (loan : Loan) (action : LoanManageAction) (v : Vault) (now : UInt32)
    (r : LoanWithPool Vault) (h : (loan.manage action v now).run = .ok (.ok r)) :
    Vault.KeepsAvailableStored v r.pool' := by
  cases action with
  | impair =>
    simp only [Loan.manage, Loan.manageImpair] at h
    unfold_ter at h
    walk_ok
    exact Loan.changeImpairment_keepsStored loan v true r ‹_›
  | unimpair => exact Loan.changeImpairment_keepsStored loan v false r h
  | default =>
    simp only [Loan.manage] at h
    unfold_ter at h
    walk_ok'
    exact Loan.manageDefault_keepsStored loan v _ ‹_›

/-- A loan transaction keeps AssetsAvailable stored exactly. -/
private lemma LendingLedger.applyLoan_keepsStored (l : LendingLedger) (tx : LendingTx) (u : LoanEffect)
    (h : (l.applyLoan tx).run = .ok (.ok u)) : Vault.KeepsAvailableStored l.vault u.vault := by
  cases tx with
  | loanSet i principal rates fees pi pt gp sd twoStep ao =>
    simp only [LendingLedger.applyLoan] at h
    obtain ⟨broker, r, -, -, hcr, rfl⟩ := l.applyLoanSet_inv _ _ _ _ _ _ _ _ h
    exact Loan.create_keepsStored _ _ _ _ _ _ _ _ _ hcr
  | loanAccept i =>
    obtain ⟨e, broker, loan, r, -, -, -, -, hr, rfl⟩ := l.applyLoan_accept_inv u i h
    exact Loan.accept_keepsStored _ _ _ hr
  | loanDelete i =>
    obtain ⟨e, broker, loan, r, -, -, -, -, hr, rfl⟩ := l.applyLoan_delete_inv u i h
    exact Loan.delete_keepsStored _ _ _ hr
  | loanManage i action =>
    obtain ⟨e, broker, loan, r, -, -, -, -, hr, rfl⟩ := l.applyLoan_manage_inv u i action h
    exact Loan.manage_keepsStored _ _ _ _ _ hr
  | loanPay i paymentType amount =>
    obtain ⟨e, broker, loan, r, -, -, -, -, hr, rfl⟩ := l.applyLoan_pay_inv u i paymentType amount h
    exact Loan.pay_keepsStored _ _ _ _ _ _ hr
  | _ => simp only [LendingLedger.applyLoan] at h; cases h

/-- A vault transaction keeps AssetsAvailable stored exactly. -/
private lemma LendingLedger.applyVault_keepsStored (l : LendingLedger) (tx : LendingTx) (u : VaultEffect)
    (h : (l.applyVault tx).run = .ok (.ok u)) : Vault.KeepsAvailableStored l.vault u.vault := by
  have hk := l.applyVault_keepsLending tx u h
  intro hst hmax
  rw [hk.numericType] at hmax ⊢
  cases tx with
  | vaultDeposit hd amount isDonation =>
    simp only [LendingLedger.applyVault] at h
    split at h
    · unfold_ter at h
      walk_ok
      exact (Vault.deposit_associateAsset_noop_proof _ _ _ _ _ hmax _ ‹_›).1
    · cases h
  | vaultWithdraw hd amount =>
    simp only [LendingLedger.applyVault] at h
    split at h
    · unfold_ter at h
      walk_ok
      all_goals exact (Vault.withdraw_associateAsset_noop_proof _ _ _ _ _ hmax _
        (Vault.withdraw_holder_ok _ _ _ _ _ _ _ ‹_›).1).1
    · cases h
  | vaultClawback hd assets =>
    simp only [LendingLedger.applyVault] at h
    split at h
    · unfold_ter at h
      walk_ok
      all_goals exact (Vault.clawback_associateAsset_noop_proof _ _ _ _ _ hmax _ ‹_›).1
    · cases h
  | vaultBurnShares hd amount =>
    simp only [LendingLedger.applyVault] at h
    unfold_ter at h
    walk_ok
    obtain ⟨_, hf⟩ := Vault.burnShares_frame _ _ _ ‹_›
    rw [(congrArg RawVault.assetsAvailable hf :)]
    exact hst hmax
  | vaultSet m b =>
    simp only [LendingLedger.applyVault] at h
    unfold_ter at h
    walk_ok
    obtain ⟨_, _, hf⟩ := Vault.update_frame _ _ _ _ ‹_›
    rw [(congrArg RawVault.assetsAvailable hf :)]
    exact hst hmax
  | _ => simp only [LendingLedger.applyVault] at h; cases h

/-- Every transaction keeps AssetsAvailable stored exactly. -/
private lemma LendingLedger.apply_keepsStored {l l' : LendingLedger} {tx : LendingTx}
    (h : (l.apply tx).run = .ok (.ok l')) (hst : Vault.StoresAvailable l.vault) : Vault.StoresAvailable l'.vault := by
  by_cases hv : tx.isVault = true
  · obtain ⟨u, hu, rfl⟩ := LendingLedger.apply_vault hv h
    have hvault : (l.commitVault u).vault = u.vault := by
      unfold LendingLedger.commitVault; split <;> simp [LendingLedger.setShares]
    rw [hvault]
    exact l.applyVault_keepsStored tx u hu hst
  by_cases hb : tx.isBroker = true
  · obtain ⟨u, -, rfl⟩ := LendingLedger.apply_broker hb h
    exact hst
  by_cases hl : tx.isLoan = true
  · obtain ⟨u, hu, rfl⟩ := LendingLedger.apply_loan hl h
    exact l.applyLoan_keepsStored tx u hu hst
  have hc := (LendingLedger.apply_checked h).2
  cases tx <;> simp only [LendingTx.isVault, LendingTx.isBroker, LendingTx.isLoan, Bool.false_eq_true,
    not_false_eq_true, not_true_eq_false] at hv hb hl
  · -- vaultDelete only sets the deleted flag
    simp only [LendingLedger.applyChecked, LendingLedger.applyVaultDelete] at hc
    unfold_ter at hc
    walk_ok
    exact hst
  · -- close moves the close time forward
    simp only [LendingLedger.applyChecked] at hc
    cases hc
    exact hst

/-- A new vault holds nothing, which every asset stores exactly. -/
lemma LendingLedger.Genesis.storesAvailable {g : LendingLedger} (hg : g.Genesis) : Vault.StoresAvailable g.vault := by
  obtain ⟨scale, m, s, eer, ocb, nt, -, hcreate⟩ := hg.created
  unfold XRPL.Model.SingleAssetVault.Vault.create at hcreate
  have hraw := (XRPL.Model.SingleAssetVault.RawVault.to_lawful_ok hcreate).1
  intro _
  rw [show g.vault.assetsAvailable = Number.zero from (congrArg RawVault.assetsAvailable hraw :)]
  exact STAmount.isRounded_zero _

/-- On a reachable ledger the asset stores AssetsAvailable exactly. -/
lemma LendingLedger.Reachable.storesAvailable {l : LendingLedger} (hr : l.Reachable) : Vault.StoresAvailable l.vault :=
  LendingLedger.Reachable.invariant (Inv := fun l => Vault.StoresAvailable l.vault) (fun _ hg => hg.storesAvailable)
    (fun _ _ _ hi ha => LendingLedger.apply_keepsStored ha hi) hr

/-- On a reachable ledger the asset stores AssetsAvailable exactly. -/
lemma LendingLedger.Reachable.availableStored {l : LendingLedger} (hr : l.Reachable) :
    STAmount.isRounded l.vault.numericType l.vault.assetsAvailable = false :=
  hr.storesAvailable hr.holdsAsset.maxValue_le

end XRPL.Model.Lending
