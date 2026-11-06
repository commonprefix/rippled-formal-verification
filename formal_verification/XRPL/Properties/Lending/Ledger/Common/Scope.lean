import XRPL.Properties.Lending.Common.Walk
import XRPL.Properties.Lending.Ledger.Common.ReachableProofs
import XRPL.Properties.Lending.Loan.Common.PoolFrame

/-! # What each kind of ledger transaction changes

A vault transaction writes only the vault and one holder, a broker transaction one broker slot, and
a loan transaction the vault balances, one broker and one loan slot. -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault (Vault)

/-- Storing into one slot leaves every other slot as it was. -/
private lemma storeSlot_other {α : Type} (xs : List (Option α)) (i : Nat) (x : Option α) :
    ∃ k : ℕ, ∀ j : ℕ, j ≠ k → (storeSlot xs i x)[j]? = xs[j]? := by
  unfold storeSlot
  split
  · exact ⟨i, fun j hj => List.getElem?_set_ne (Ne.symm hj)⟩
  · refine ⟨xs.length, fun j hj => ?_⟩
    rw [List.getElem?_append]
    split
    · rfl
    · rename_i hlt
      have h1 : xs[j]? = none := List.getElem?_eq_none (by omega)
      have h2 : j - xs.length ≠ 0 := by omega
      rw [h1, List.getElem?_cons]
      simp [h2]

/-- Setting one slot leaves every other slot as it was. -/
private lemma set_other {α : Type} (xs : List α) (i : Nat) (x : α) :
    ∀ j, j ≠ i → (xs.set i x)[j]? = xs[j]? :=
  fun _ hj => List.getElem?_set_ne (Ne.symm hj)

/-- A management action keeps the vault settings. -/
private lemma Loan.manage_keepsSettings (loan : Loan) (action : LoanManageAction) (v : Vault) (now : UInt32)
    (r : LoanWithPool Vault) (h : (loan.manage action v now).run = .ok (.ok r)) : Vault.KeepsSettings v r.pool' := by
  cases action with
  | impair => exact Loan.manageImpair_keepsSettings loan v now r h
  | unimpair => exact Loan.changeImpairment_keepsSettings loan v false r h
  | default =>
    simp only [Loan.manage] at h
    unfold_ter at h
    walk_ok'
    exact Loan.manageDefault_keepsSettings loan v _ ‹_›

/-- A payment of any type keeps the vault settings. -/
private lemma Loan.pay_keepsSettings (loan : Loan) (paymentType : LoanPaymentType) (v : Vault) (amount : Number)
    (now : UInt32) (r : LoanWithAmounts Vault) (h : (loan.pay v paymentType amount now).run = .ok (.ok r)) :
    Vault.KeepsSettings v r.pool' := by
  cases paymentType with
  | regular => exact Loan.regularPayment_keepsSettings loan v amount now r h
  | late => exact Loan.latePayment_keepsSettings loan v amount now r h
  | full => exact Loan.fullPayment_keepsSettings loan v amount now r h
  | overpayment => exact Loan.overpayment_keepsSettings loan v amount now r h

/-- The create step of a LoanSet keeps the vault settings. -/
private lemma LendingLedger.loanSetChecked_keepsSettings (l : LendingLedger) (u : LoanEffect) (i : Nat)
    (broker : LoanBroker) (a : Number) (r : LoanRates) (f : LoanFees) (schedule : LoanSchedule) (b1 b2 : Bool)
    (checks : Except Error TER) (h : (l.loanSetChecked i broker a r f schedule b1 b2 checks).run = .ok (.ok u)) :
    Vault.KeepsSettings l.vault u.vault := by
  unfold LendingLedger.loanSetChecked at h
  cases checks with
  | error e => cases h
  | ok ter =>
    dsimp only at h
    split at h
    · cases h
    obtain ⟨res, hres, rfl⟩ := TerExcept.map_ok h
    exact Loan.create_keepsSettings _ _ _ _ _ _ _ _ _ hres

/-- A LoanSet keeps the vault settings. -/
private lemma LendingLedger.applyLoanSet_keepsSettings (l : LendingLedger) (u : LoanEffect) (i : Nat) (a : Number)
    (r : LoanRates) (f : LoanFees) (schedule : LoanSchedule) (b1 b2 : Bool)
    (h : (l.applyLoanSet i a r f schedule b1 b2).run = .ok (.ok u)) : Vault.KeepsSettings l.vault u.vault := by
  unfold LendingLedger.applyLoanSet at h
  dsimp only at h
  split at h
  · simp [ExceptT.run, ExceptT.mk] at h
  split at h
  · cases h
  generalize l.broker? i = ob at h
  cases ob with
  | none => cases h
  | some broker => exact l.loanSetChecked_keepsSettings _ _ _ _ _ _ _ _ _ _ h

/-- A loan transaction keeps the vault settings. -/
lemma LendingLedger.applyLoan_keepsSettings (l : LendingLedger) (tx : LendingTx) (u : LoanEffect)
    (h : (l.applyLoan tx).run = .ok (.ok u)) : Vault.KeepsSettings l.vault u.vault := by
  cases tx with
  | loanSet i principal rates fees pi pt gp sd twoStep ao =>
    exact l.applyLoanSet_keepsSettings _ _ _ _ _ _ _ _ h
  | loanAccept i =>
    simp only [LendingLedger.applyLoan] at h
    unfold_ter at h
    walk_ok'
    exact Loan.accept_keepsSettings _ _ _ ‹_›
  | loanDelete i =>
    simp only [LendingLedger.applyLoan] at h
    unfold_ter at h
    walk_ok'
    exact Loan.delete_keepsSettings _ _ _ ‹_›
  | loanManage i action =>
    simp only [LendingLedger.applyLoan] at h
    unfold_ter at h
    walk_ok'
    exact Loan.manage_keepsSettings _ _ _ _ _ ‹_›
  | loanPay i paymentType amount =>
    simp only [LendingLedger.applyLoan] at h
    unfold_ter at h
    walk_ok'
    exact Loan.pay_keepsSettings _ _ _ _ _ _ ‹_›
  | _ => simp only [LendingLedger.applyLoan] at h; cases h

/-- A vault transaction other than VaultDelete keeps the loans and the brokers. -/
lemma LendingLedger.vault_ops_scope_proof (l l' : LendingLedger) (tx : LendingTx) (hv : tx.isVault = true)
    (h : (l.apply tx).run = .ok (.ok l')) : l'.loans = l.loans ∧ l'.brokers = l.brokers := by
  obtain ⟨u, -, rfl⟩ := LendingLedger.apply_vault hv h
  unfold LendingLedger.commitVault
  split <;> simp [LendingLedger.setShares]

/-- A successful VaultDelete keeps the loans and the brokers. -/
lemma LendingLedger.vaultDelete_scope (l l' : LendingLedger) (h : (l.apply .vaultDelete).run = .ok (.ok l')) :
    l'.loans = l.loans ∧ l'.brokers = l.brokers := by
  have h := (LendingLedger.apply_checked h).2
  simp only [LendingLedger.applyChecked, LendingLedger.applyVaultDelete] at h
  unfold_ter at h
  walk_ok'
  all_goals exact ⟨rfl, rfl⟩

/-- Proof body of the vault line of `Lending.ops_scope`, VaultDelete included. -/
lemma LendingLedger.vault_ops_scope_all_proof (l l' : LendingLedger) (tx : LendingTx)
    (hv : tx.isVault = true ∨ tx = .vaultDelete) (h : (l.apply tx).run = .ok (.ok l')) :
    l'.loans = l.loans ∧ l'.brokers = l.brokers := by
  rcases hv with hv | rfl
  · exact LendingLedger.vault_ops_scope_proof l l' tx hv h
  · exact LendingLedger.vaultDelete_scope l l' h

/-- Proof body of the LoanBroker line of `Lending.ops_scope`. -/
lemma LendingLedger.broker_ops_scope_proof (l l' : LendingLedger) (tx : LendingTx) (hb : tx.isBroker = true)
    (h : (l.apply tx).run = .ok (.ok l')) :
    l'.loans = l.loans ∧ l'.shares = l.shares ∧ l'.vault = l.vault ∧
      ∃ k : ℕ, ∀ j : ℕ, j ≠ k → l'.brokers[j]? = l.brokers[j]? := by
  obtain ⟨u, -, rfl⟩ := LendingLedger.apply_broker hb h
  exact ⟨rfl, rfl, rfl, storeSlot_other l.brokers u.index u.broker⟩

/-- Proof body of the loan line of `Lending.ops_scope`. -/
lemma LendingLedger.loan_ops_scope_proof (l l' : LendingLedger) (tx : LendingTx) (hl : tx.isLoan = true)
    (h : (l.apply tx).run = .ok (.ok l')) :
    (∃ k : ℕ, ∀ j : ℕ, j ≠ k → l'.loans[j]? = l.loans[j]?) ∧
      (∃ k : ℕ, ∀ j : ℕ, j ≠ k → l'.brokers[j]? = l.brokers[j]?) ∧
      l'.shares = l.shares ∧ l'.vault.sharesTotal = l.vault.sharesTotal ∧
      l'.vault.assetsMaximum = l.vault.assetsMaximum := by
  obtain ⟨u, hu, rfl⟩ := LendingLedger.apply_loan hl h
  have hs := l.applyLoan_keepsSettings tx u hu
  exact ⟨storeSlot_other l.loans u.loanIndex u.loan, ⟨u.brokerIndex, set_other l.brokers u.brokerIndex _⟩, rfl,
    hs.sharesTotal, hs.assetsMaximum⟩

end XRPL.Model.Lending
