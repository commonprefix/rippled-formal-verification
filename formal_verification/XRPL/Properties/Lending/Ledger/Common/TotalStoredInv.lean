import Batteries.Tactic.OpenPrivate
import XRPL.Properties.Lending.Ledger.Common.LoanSteps
import XRPL.Properties.Lending.Ledger.Common.VaultSteps
import XRPL.Properties.Lending.Ledger.Common.WithdrawHolder
import XRPL.Properties.Vault.Proofs.TotalStored

/-! # The lending ledger keeps a total the asset stores

C++ `syncAssetsTotal` stores AssetsAvailable + AssetsDeployed as an amount of the asset and fails when it can't, so on
a reachable ledger the sum fits the asset, up to the last digit the `Number` sum drops. -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault (Vault RawVault TotalStores)

open private Loan.changeImpairment from XRPL.Model.Lending.Loan.LoanManage
open private Loan.settlePayment validatePostPayment UnsettledPayment.payInstalments Loan.unimpairIfImpaired
  Loan.payScheduledInstalments UnsettledPayment.applyOverpayment Loan.paySingleInstalment
  from XRPL.Model.Lending.Loan.LoanPay

/-- A step that keeps the vault's total an amount of the asset. -/
private def Vault.KeepsTotalStored (v v' : Vault) : Prop := v.TotalStored → v'.TotalStored

/-- A vault keeps its own total. -/
private lemma Vault.KeepsTotalStored.refl (v : Vault) : Vault.KeepsTotalStored v v := id

/-- Two steps that keep the total an amount of the asset keep it over both. -/
private lemma Vault.KeepsTotalStored.trans {a b c : Vault} (h₁ : Vault.KeepsTotalStored a b)
    (h₂ : Vault.KeepsTotalStored b c) :
    Vault.KeepsTotalStored a c := fun h => h₂ (h₁ h)

/-- A balance change the vault takes leaves a total that is an amount of the asset. -/
lemma Vault.poolAdjust_totalStored (v v' : Vault) (c : PoolBalanceChange)
    (h : AssetPool.adjustBalances v c = .ok (.ok v')) : v'.TotalStored := by
  obtain ⟨raw, hadj, hv'⟩ := Vault.poolAdjust_ok_inv v c v' h
  have he := (XRPL.Model.SingleAssetVault.RawVault.to_lawful_ok hv').1
  have hts := XRPL.Model.SingleAssetVault.Vault.adjustBalances_totalStores v c raw hadj
  obtain ⟨_, _, _, _, _, -, -, -, hraw⟩ := Vault.adjustBalances_ok_parts v c raw hadj
  have hnt : v'.numericType = v.numericType := by
    show v'.toRawVault.numericType = _
    rw [he, hraw]
  unfold XRPL.Model.SingleAssetVault.Vault.TotalStored
  rw [hnt]
  show TotalStores v.numericType v'.toRawVault.assetsAvailable v'.toRawVault.assetsDeployed
  rw [he]
  exact hts

/-- A balance change keeps the total an amount of the asset. -/
private lemma Vault.poolAdjust_keepsTotal (v v' : Vault) (c : PoolBalanceChange)
    (h : AssetPool.adjustBalances v c = .ok (.ok v')) : Vault.KeepsTotalStored v v' :=
  fun _ => Vault.poolAdjust_totalStored v v' c h

/-- A new loan keeps the total an amount of the asset. -/
private lemma Loan.create_keepsTotal (broker : LoanBroker) (v : Vault) (principal : Number) (rates : LoanRates)
    (fees : LoanFees) (schedule : LoanSchedule) (ao pending : Bool) (r : LoanWithDisbursement Vault)
    (h : (Loan.create broker v principal rates fees schedule ao pending).run = .ok (.ok r)) :
    Vault.KeepsTotalStored v r.pool' := by
  obtain ⟨_, _, _, _, _, -, -, hpool, -, -⟩ := Loan.create_ok_inv broker v principal rates fees schedule ao pending r h
  exact Vault.poolAdjust_keepsTotal _ _ _ hpool

/-- Accept keeps the total an amount of the asset. -/
private lemma Loan.accept_keepsTotal (loan : Loan) (v : Vault) (r : LoanWithDisbursement Vault)
    (h : (loan.accept v).run = .ok (.ok r)) : Vault.KeepsTotalStored v r.pool' := by
  simp only [Loan.accept] at h
  unfold_ter at h
  walk_ok
  exact Vault.poolAdjust_keepsTotal _ _ _ ‹_›

/-- Setting or clearing the impaired flag keeps the total an amount of the asset. -/
private lemma Loan.changeImpairment_keepsTotal (loan : Loan) (v : Vault) (b : Bool) (r : LoanWithPool Vault)
    (h : (Loan.changeImpairment loan v b).run = .ok (.ok r)) : Vault.KeepsTotalStored v r.pool' := by
  simp only [Loan.changeImpairment] at h
  unfold_ter at h
  walk_ok
  all_goals exact Vault.poolAdjust_keepsTotal _ _ _ ‹_›

/-- Default keeps the total an amount of the asset. -/
private lemma Loan.manageDefault_keepsTotal (loan : Loan) (v : Vault) (r : LoanWithAmounts Vault)
    (h : (loan.manageDefault v).run = .ok (.ok r)) : Vault.KeepsTotalStored v r.pool' := by
  simp only [Loan.manageDefault] at h
  unfold_ter at h
  walk_ok
  all_goals exact Vault.poolAdjust_keepsTotal _ _ _ ‹AssetPool.adjustBalances _ _ = _›

/-- Delete keeps the total an amount of the asset. -/
private lemma Loan.delete_keepsTotal (loan : Loan) (v : Vault) (r : LoanBrokerWithPool Vault)
    (h : (loan.delete v).run = .ok (.ok r)) : Vault.KeepsTotalStored v r.pool' := by
  unfold Loan.delete at h
  split at h
  · simp only [Loan.deletePending] at h
    unfold_ter at h
    walk_ok
    exact Vault.poolAdjust_keepsTotal _ _ _ ‹AssetPool.adjustBalances _ _ = _›
  · unfold_ter at h
    walk_ok
    exact Vault.KeepsTotalStored.refl _

/-- Settling a payment keeps the total an amount of the asset. -/
private lemma Loan.settlePayment_keepsTotal (loan : Loan) (v : Vault) (amounts : PaymentAmounts) (si : Number)
    (r : LoanWithAmounts Vault) (h : (Loan.settlePayment loan v amounts si).run = .ok (.ok r)) :
    Vault.KeepsTotalStored v r.pool' := by
  simp only [Loan.settlePayment] at h
  unfold_ter at h
  walk_ok
  all_goals
    have hv := validatePostPayment_eq _ _ r ‹_›
    subst hv
    exact Vault.poolAdjust_keepsTotal _ _ _ ‹AssetPool.adjustBalances _ _ = _›

/-- Clearing an impairment before a payment keeps the total an amount of the asset. -/
private lemma Loan.unimpairIfImpaired_keepsTotal (loan : Loan) (v : Vault) (r : LoanWithPool Vault)
    (h : (Loan.unimpairIfImpaired loan v).run = .ok (.ok r)) : Vault.KeepsTotalStored v r.pool' := by
  unfold Loan.unimpairIfImpaired at h
  split at h
  · exact Loan.changeImpairment_keepsTotal loan v false r h
  · unfold_ter at h
    walk_ok
    exact Vault.KeepsTotalStored.refl _

/-- The scheduled part of a payment keeps the total an amount of the asset. -/
private lemma Loan.payScheduledInstalments_keepsTotal (loan : Loan) (v : Vault) (amount : Number) (now : UInt32)
    (p : UnsettledPayment Vault) (h : (Loan.payScheduledInstalments loan v amount now).run = .ok (.ok p)) :
    Vault.KeepsTotalStored v p.pool := by
  simp only [Loan.payScheduledInstalments] at h
  unfold_ter at h
  walk_ok
  all_goals
    have hu := Loan.unimpairIfImpaired_keepsTotal _ _ _ ‹(Loan.unimpairIfImpaired _ _) = _›
    rw [UnsettledPayment.payInstalments_pool amount _ _ _ ‹UnsettledPayment.payInstalments _ _ _ = _›]
    exact hu

/-- A single settled instalment keeps the total an amount of the asset. -/
private lemma Loan.paySingleInstalment_keepsTotal (loan : Loan) (v : Vault) (pc : PaymentComponents)
    (amount : Number) (r : LoanWithAmounts Vault)
    (h : (Loan.paySingleInstalment loan v pc amount).run = .ok (.ok r)) : Vault.KeepsTotalStored v r.pool' := by
  simp only [Loan.paySingleInstalment] at h
  unfold_ter at h
  walk_ok
  all_goals exact Loan.settlePayment_keepsTotal _ _ _ _ _ ‹(Loan.settlePayment _ _ _ _) = _›

/-- A payment of any type keeps the total an amount of the asset. -/
private lemma Loan.pay_keepsTotal (loan : Loan) (paymentType : LoanPaymentType) (v : Vault) (amount : Number)
    (now : UInt32) (r : LoanWithAmounts Vault) (h : (loan.pay v paymentType amount now).run = .ok (.ok r)) :
    Vault.KeepsTotalStored v r.pool' := by
  cases paymentType with
  | regular =>
    simp only [Loan.pay, Loan.regularPayment] at h
    unfold_ter at h
    walk_ok
    all_goals
      have hp := Loan.payScheduledInstalments_keepsTotal _ _ _ _ _ ‹(Loan.payScheduledInstalments _ _ _ _) = _›
      have hs := Loan.settlePayment_keepsTotal _ _ _ _ _ ‹(Loan.settlePayment _ _ _ _) = _›
      exact hp.trans hs
  | late =>
    simp only [Loan.pay, Loan.latePayment] at h
    unfold_ter at h
    walk_ok
    all_goals
      have hu := Loan.unimpairIfImpaired_keepsTotal _ _ _ ‹(Loan.unimpairIfImpaired _ _) = _›
      have hs := Loan.paySingleInstalment_keepsTotal _ _ _ _ _ ‹(Loan.paySingleInstalment _ _ _ _) = _›
      exact hu.trans hs
  | full =>
    simp only [Loan.pay, Loan.fullPayment] at h
    unfold_ter at h
    walk_ok
    all_goals
      have hu := Loan.unimpairIfImpaired_keepsTotal _ _ _ ‹(Loan.unimpairIfImpaired _ _) = _›
      have hs := Loan.paySingleInstalment_keepsTotal _ _ _ _ _ ‹(Loan.paySingleInstalment _ _ _ _) = _›
      exact hu.trans hs
  | overpayment =>
    simp only [Loan.pay, Loan.overpayment] at h
    unfold_ter at h
    walk_ok
    all_goals
      have hp := Loan.payScheduledInstalments_keepsTotal _ _ _ _ _ ‹(Loan.payScheduledInstalments _ _ _ _) = _›
      have hs := Loan.settlePayment_keepsTotal _ _ _ _ _ ‹(Loan.settlePayment _ _ _ _) = _›
      rw [UnsettledPayment.applyOverpayment_pool _ _ _ ‹UnsettledPayment.applyOverpayment _ _ = _›] at hs
      exact hp.trans hs

/-- A management action keeps the total an amount of the asset. -/
private lemma Loan.manage_keepsTotal (loan : Loan) (action : LoanManageAction) (v : Vault) (now : UInt32)
    (r : LoanWithPool Vault) (h : (loan.manage action v now).run = .ok (.ok r)) :
    Vault.KeepsTotalStored v r.pool' := by
  cases action with
  | impair =>
    simp only [Loan.manage, Loan.manageImpair] at h
    unfold_ter at h
    walk_ok
    exact Loan.changeImpairment_keepsTotal loan v true r ‹_›
  | unimpair => exact Loan.changeImpairment_keepsTotal loan v false r h
  | default =>
    simp only [Loan.manage] at h
    unfold_ter at h
    walk_ok'
    exact Loan.manageDefault_keepsTotal loan v _ ‹_›

/-- A loan transaction keeps the total an amount of the asset. -/
private lemma LendingLedger.applyLoan_keepsTotal (l : LendingLedger) (tx : LendingTx) (u : LoanEffect)
    (h : (l.applyLoan tx).run = .ok (.ok u)) : Vault.KeepsTotalStored l.vault u.vault := by
  cases tx with
  | loanSet i principal rates fees pi pt gp sd twoStep ao =>
    simp only [LendingLedger.applyLoan] at h
    obtain ⟨broker, r, -, -, hcr, rfl⟩ := l.applyLoanSet_inv _ _ _ _ _ _ _ _ h
    exact Loan.create_keepsTotal _ _ _ _ _ _ _ _ _ hcr
  | loanAccept i =>
    obtain ⟨e, broker, loan, r, -, -, -, -, hr, rfl⟩ := l.applyLoan_accept_inv u i h
    exact Loan.accept_keepsTotal _ _ _ hr
  | loanDelete i =>
    obtain ⟨e, broker, loan, r, -, -, -, -, hr, rfl⟩ := l.applyLoan_delete_inv u i h
    exact Loan.delete_keepsTotal _ _ _ hr
  | loanManage i action =>
    obtain ⟨e, broker, loan, r, -, -, -, -, hr, rfl⟩ := l.applyLoan_manage_inv u i action h
    exact Loan.manage_keepsTotal _ _ _ _ _ hr
  | loanPay i paymentType amount =>
    obtain ⟨e, broker, loan, r, -, -, -, -, hr, rfl⟩ := l.applyLoan_pay_inv u i paymentType amount h
    exact Loan.pay_keepsTotal _ _ _ _ _ _ hr
  | _ => simp only [LendingLedger.applyLoan] at h; cases h

/-- A vault transaction keeps the total an amount of the asset. -/
private lemma LendingLedger.applyVault_keepsTotal (l : LendingLedger) (tx : LendingTx) (u : VaultEffect)
    (h : (l.applyVault tx).run = .ok (.ok u)) : Vault.KeepsTotalStored l.vault u.vault := by
  intro hst
  cases tx with
  | vaultDeposit hd amount isDonation =>
    simp only [LendingLedger.applyVault] at h
    split at h
    · unfold_ter at h
      walk_ok
      exact XRPL.Model.SingleAssetVault.Vault.deposit_totalStored _ _ _ _ _ _ ‹_›
    · cases h
  | vaultWithdraw hd amount =>
    simp only [LendingLedger.applyVault] at h
    split at h
    · unfold_ter at h
      walk_ok
      all_goals exact (XRPL.Model.SingleAssetVault.Vault.withdraw_totalStored _ _ _ _ _ _
        (Vault.withdraw_holder_ok _ _ _ _ _ _ _ ‹_›).1)
    · cases h
  | vaultClawback hd assets =>
    simp only [LendingLedger.applyVault] at h
    split at h
    · unfold_ter at h
      walk_ok
      all_goals exact XRPL.Model.SingleAssetVault.Vault.clawback_totalStored _ _ _ _ _ _ ‹_›
    · cases h
  | vaultBurnShares hd amount =>
    simp only [LendingLedger.applyVault] at h
    unfold_ter at h
    walk_ok
    exact XRPL.Model.SingleAssetVault.Vault.burnShares_totalStored _ _ _ ‹_› hst
  | vaultSet m b =>
    simp only [LendingLedger.applyVault] at h
    unfold_ter at h
    walk_ok
    exact XRPL.Model.SingleAssetVault.Vault.update_totalStored _ _ _ _ ‹_› hst
  | _ => simp only [LendingLedger.applyVault] at h; cases h

/-- Every transaction keeps the total an amount of the asset. -/
private lemma LendingLedger.apply_keepsTotal {l l' : LendingLedger} {tx : LendingTx}
    (h : (l.apply tx).run = .ok (.ok l')) (hst : l.vault.TotalStored) : l'.vault.TotalStored := by
  by_cases hv : tx.isVault = true
  · obtain ⟨u, hu, rfl⟩ := LendingLedger.apply_vault hv h
    have hvault : (l.commitVault u).vault = u.vault := by
      unfold LendingLedger.commitVault; split <;> simp [LendingLedger.setShares]
    rw [hvault]
    exact l.applyVault_keepsTotal tx u hu hst
  by_cases hb : tx.isBroker = true
  · obtain ⟨u, -, rfl⟩ := LendingLedger.apply_broker hb h
    exact hst
  by_cases hl : tx.isLoan = true
  · obtain ⟨u, hu, rfl⟩ := LendingLedger.apply_loan hl h
    exact l.applyLoan_keepsTotal tx u hu hst
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

/-- A new vault holds nothing, and every asset stores a total of zero. -/
lemma LendingLedger.Genesis.totalStored {g : LendingLedger} (hg : g.Genesis) : g.vault.TotalStored := by
  obtain ⟨scale, m, s, eer, ocb, nt, -, hcreate⟩ := hg.created
  unfold XRPL.Model.SingleAssetVault.Vault.create at hcreate
  have hraw := (XRPL.Model.SingleAssetVault.RawVault.to_lawful_ok hcreate).1
  unfold XRPL.Model.SingleAssetVault.Vault.TotalStored
  rw [show g.vault.assetsAvailable = Number.zero from (congrArg RawVault.assetsAvailable hraw :),
    show g.vault.assetsDeployed = Number.zero from (congrArg RawVault.assetsDeployed hraw :)]
  exact TotalStores.of_zero_deployed _ Number.zero Number.zero_isNormalized (by rw [Number.toRat_zero])
    (STAmount.isRounded_zero _)

/-- On a reachable ledger AssetsAvailable + AssetsDeployed is an amount of the asset (C++ `syncAssetsTotal`). -/
lemma LendingLedger.Reachable.totalStored {l : LendingLedger} (hr : l.Reachable) : l.vault.TotalStored :=
  LendingLedger.Reachable.invariant (Inv := fun l => l.vault.TotalStored) (fun _ hg => hg.totalStored)
    (fun _ _ _ hi ha => LendingLedger.apply_keepsTotal ha hi) hr

end XRPL.Model.Lending
