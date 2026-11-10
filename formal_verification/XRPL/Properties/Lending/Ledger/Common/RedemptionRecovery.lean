import XRPL.Properties.Lending.Ledger.Common.VaultOutflow
import XRPL.Properties.Lending.Loan.Common.DeleteExits
import XRPL.Properties.Lending.Loan.Common.SetPhase
import XRPL.Properties.Lending.Loan.Common.GuardProofs

/-! # Where AssetsAvailable comes from in the redemption phase

A LoanSet, an accept and a deposit that is not a donation need an earlier phase. A withdrawal or a clawback
only pays out, and an impairment change moves nothing into AssetsAvailable. -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault (Vault RawVault)

open private Loan.changeImpairment from XRPL.Model.Lending.Loan.LoanManage

/-- A deposit that is not a donation needs the subscription phase or no phase at all. -/
private lemma Vault.deposit_not_redemption (v : Vault) (amount : STAmount) (t : UInt32) (hpos : 0 < amount.toRat)
    (hred : v.phase t = .redemption) (r : XRPL.Model.SingleAssetVault.VaultWithAmounts)
    (h : (v.deposit amount false t hpos).run = .ok (.ok r)) : False := by
  simp only [XRPL.Model.SingleAssetVault.Vault.deposit, hred] at h
  unfold_ter at h
  simp at h

/-- A change of the impaired flag moves only LossUnrealized, so a vault that stores AssetsAvailable
exactly keeps it. -/
private lemma Loan.changeImpairment_assetsAvailable (loan : Loan) (v : Vault) (b : Bool) (r : LoanWithPool Vault)
    (hst : STAmount.isRounded v.numericType v.assetsAvailable = false)
    (h : (Loan.changeImpairment loan v b).run = .ok (.ok r)) :
    r.pool'.assetsAvailable.toRat = v.assetsAvailable.toRat := by
  simp only [Loan.changeImpairment] at h
  unfold_ter at h
  walk_ok
  all_goals
    obtain ⟨raw, hadj, hv'⟩ := Vault.poolAdjust_ok_inv v _ _ ‹AssetPool.adjustBalances _ _ = _›
    have he := (XRPL.Model.SingleAssetVault.RawVault.to_lawful_ok hv').1
    simp only [XRPL.Model.SingleAssetVault.Vault.adjustBalances] at hadj
    unfold_ter at hadj
    walk_ok
    simp only [Number.operator_add_zero_right, Except.ok.injEq] at *
    subst_vars
    rw [(congrArg RawVault.assetsAvailable he :)]
    exact STAmount.roundToNumericType_of_isRounded_false _ _ _ v.wf.assetsAvailable_norm hst ‹_›

/-- Impairing or unimpairing a loan keeps AssetsAvailable when the asset stores it exactly. -/
private lemma Loan.manage_impairment_assetsAvailable (loan : Loan) (action : LoanManageAction) (v : Vault)
    (now : UInt32) (r : LoanWithPool Vault) (hst : STAmount.isRounded v.numericType v.assetsAvailable = false)
    (hact : action ≠ .default) (h : (loan.manage action v now).run = .ok (.ok r)) :
    r.pool'.assetsAvailable.toRat = v.assetsAvailable.toRat := by
  cases action with
  | impair =>
    simp only [Loan.manage, Loan.manageImpair] at h
    unfold_ter at h
    walk_ok
    exact Loan.changeImpairment_assetsAvailable loan v true _ hst ‹_›
  | unimpair => exact Loan.changeImpairment_assetsAvailable loan v false r hst h
  | default => exact absurd rfl hact

/-- A vault transaction writes its vault. -/
private lemma LendingLedger.commitVault_vault (l : LendingLedger) (u : VaultEffect) :
    (l.commitVault u).vault = u.vault := by
  unfold LendingLedger.commitVault; split <;> simp [LendingLedger.setShares]

/-- Proof body of the AssetsAvailable line of `Lending.redemption_recovery`. -/
lemma LendingLedger.redemption_recovery_proof (l l' : LendingLedger) (tx : LendingTx) (hr : l.Reachable)
    (hmax : l.vault.numericType.isIntegral = true → l.vault.numericType.maxValue.toNat ≤ maxRep.toNat)
    (hred : l.vault.phase l.now = .redemption) (h : (l.apply tx).run = .ok (.ok l'))
    (hup : l.vault.assetsAvailable.toRat < l'.vault.assetsAvailable.toRat) :
    (∃ i paymentType amount, tx = .loanPay i paymentType amount) ∨ (∃ i, tx = .loanManage i .default) ∨
      (∃ i e, tx = .loanDelete i ∧ l.loan? i = some e ∧ e.loan.isPending = true) ∨
      (∃ holder amount, tx = .vaultDeposit holder amount true) := by
  have hst := hr.storesAvailable hmax
  cases tx with
  | vaultDeposit holder amount isDonation =>
    cases isDonation
    · -- a deposit that is not a donation is refused in the redemption phase
      exfalso
      obtain ⟨u, hu, rfl⟩ := LendingLedger.apply_vault rfl h
      simp only [LendingLedger.applyVault] at hu
      split at hu
      · unfold_ter at hu
        walk_ok
        exact Vault.deposit_not_redemption _ _ _ _ hred _ ‹_›
      · cases hu
    · exact Or.inr (Or.inr (Or.inr ⟨holder, amount, rfl⟩))
  | vaultWithdraw holder amount =>
    exfalso
    have := (LendingLedger.lent_out_protected_proof l l' _ hr hmax (Or.inl ⟨_, _, rfl⟩) h).2.1
    linarith
  | vaultClawback holder assets =>
    exfalso
    have := (LendingLedger.lent_out_protected_proof l l' _ hr hmax (Or.inr ⟨_, _, rfl⟩) h).2.1
    linarith
  | vaultBurnShares holder amount =>
    exfalso
    obtain ⟨u, hu, rfl⟩ := LendingLedger.apply_vault rfl h
    rw [LendingLedger.commitVault_vault] at hup
    simp only [LendingLedger.applyVault] at hu
    unfold_ter at hu
    walk_ok
    obtain ⟨_, hf⟩ := Vault.burnShares_frame _ _ _ ‹_›
    rw [show RawVault.assetsAvailable _ = _ from (congrArg RawVault.assetsAvailable hf :)] at hup
    exact lt_irrefl _ hup
  | vaultSet m b =>
    exfalso
    obtain ⟨u, hu, rfl⟩ := LendingLedger.apply_vault rfl h
    rw [LendingLedger.commitVault_vault] at hup
    simp only [LendingLedger.applyVault] at hu
    unfold_ter at hu
    walk_ok
    obtain ⟨_, _, hf⟩ := Vault.update_frame _ _ _ _ _ ‹_›
    rw [show RawVault.assetsAvailable _ = _ from (congrArg RawVault.assetsAvailable hf :)] at hup
    exact lt_irrefl _ hup
  | vaultDelete =>
    exfalso
    have hc := (LendingLedger.apply_checked h).2
    simp only [LendingLedger.applyChecked, LendingLedger.applyVaultDelete] at hc
    unfold_ter at hc
    walk_ok
    exact lt_irrefl _ hup
  | loanBrokerCreate _ | loanBrokerUpdate _ _ | loanBrokerCoverDeposit _ _ | loanBrokerCoverWithdraw _ _
  | loanBrokerCoverClawback _ _ | loanBrokerDelete _ =>
    exfalso
    rw [(LendingLedger.broker_ops_scope_proof l l' _ rfl h).2.2.1] at hup
    exact lt_irrefl _ hup
  | loanSet i principal rates fees pi pt gp sd twoStep ao =>
    exfalso
    obtain ⟨u, hu, rfl⟩ := LendingLedger.apply_loan rfl h
    simp only [LendingLedger.applyLoan] at hu
    obtain ⟨broker, r, -, hc, -⟩ := l.applyLoanSet_inv _ _ _ _ _ _ _ _ hu
    rcases Loan.canCreate_fitsVault _ _ _ _ _ _ _ hc with h | ⟨h, -⟩ <;> rw [hred] at h <;> cases h
  | loanAccept i =>
    exfalso
    obtain ⟨u, hu, rfl⟩ := LendingLedger.apply_loan rfl h
    obtain ⟨e, broker, loan, r, -, -, -, hc, -⟩ := l.applyLoan_accept_inv u i hu
    exact Loan.canAccept_not_redemption loan l.vault l.now hred hc
  | loanDelete i =>
    obtain ⟨u, hu, rfl⟩ := LendingLedger.apply_loan rfl h
    obtain ⟨e, broker, loan, r, he, -, hw, -, hdel, rfl⟩ := l.applyLoan_delete_inv u i hu
    by_cases hp : e.loan.isPending = true
    · exact Or.inr (Or.inr (Or.inl ⟨i, e, rfl, he, hp⟩))
    · -- a closed loan's delete leaves the vault as it was
      exfalso
      have hlp : loan.isPending = false := by
        rw [show loan.isPending = e.loan.isPending from (congrArg RawLoan.isPending (Loan.withBroker_eq hw) :)]
        simpa using hp
      obtain ⟨-, hpool⟩ := Loan.delete_active_ok_inv loan l.vault r hlp hdel
      rw [hpool] at hup
      exact lt_irrefl _ hup
  | loanManage i action =>
    by_cases hact : action = .default
    · subst hact; exact Or.inr (Or.inl ⟨i, rfl⟩)
    · exfalso
      obtain ⟨u, hu, rfl⟩ := LendingLedger.apply_loan rfl h
      obtain ⟨e, broker, loan, r, -, -, -, -, hr', rfl⟩ := l.applyLoan_manage_inv u i action hu
      have hc := Loan.manage_impairment_assetsAvailable loan action l.vault l.now r hst hact hr'
      change l.vault.assetsAvailable.toRat < r.pool'.assetsAvailable.toRat at hup
      rw [hc] at hup
      exact lt_irrefl _ hup
  | loanPay i paymentType amount => exact Or.inl ⟨i, paymentType, amount, rfl⟩
  | close t =>
    exfalso
    have hc := (LendingLedger.apply_checked h).2
    simp only [LendingLedger.applyChecked] at hc
    cases hc
    exact lt_irrefl _ hup

end XRPL.Model.Lending
