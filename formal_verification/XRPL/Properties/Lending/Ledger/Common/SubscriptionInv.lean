import XRPL.Properties.Lending.Ledger.Common.BrokerSteps
import XRPL.Properties.Lending.Ledger.Common.LoanCountInv
import XRPL.Properties.Lending.Ledger.Common.LoanSteps
import XRPL.Properties.Lending.Ledger.Common.Scope
import XRPL.Properties.Lending.Ledger.Common.VaultSteps
import XRPL.Properties.Lending.Ledger.Common.YieldSum
import XRPL.Properties.Lending.Loan.Common.SetPhase
import XRPL.Properties.Protocol.Number.Totality

/-! # The lending ledger in the subscription phase

A LoanSet needs the investment phase, so until SubscriptionDate the ledger has no loans, no broker
owes the vault anything, and the vault has nothing lent out, reserved or lost. -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault (Vault RawVault VaultSchedule)

/-- The vault is in the subscription phase exactly until SubscriptionDate. -/
private lemma Vault.phase_subscription_iff (v : Vault) (t : UInt32) (s : VaultSchedule) (hs : v.schedule = some s) :
    v.phase t = .subscription ↔ t.toNat ≤ s.subscriptionDate.toNat := by
  unfold XRPL.Model.SingleAssetVault.Vault.phase
  rw [hs]
  dsimp only
  by_cases hc : t > s.subscriptionDate
  · have hc' := UInt32.lt_iff_toNat_lt.mp hc
    simp only [hc, decide_true, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    constructor
    · intro h; split at h <;> cases h
    · intro h; omega
  · have hc' : ¬ s.subscriptionDate.toNat < t.toNat := fun h => hc (UInt32.lt_iff_toNat_lt.mpr h)
    simp only [hc, decide_false, Bool.not_false, ↓reduceIte, true_iff]
    omega

/-- A ledger that has not lent anything: no loans, no broker debt, and nothing lent out, reserved or
lost in the vault. -/
structure LendingLedger.Idle (l : LendingLedger) : Prop where
  no_loans : ∀ j, l.loan? j = none
  no_debt : ∀ (j : Nat) (b : LoanBroker), l.broker? j = some b → b.debtTotal = Number.zero
  assetsDeployed : l.vault.assetsDeployed = Number.zero
  assetsReserved : l.vault.assetsReserved = Number.zero
  lossUnrealized : l.vault.lossUnrealized = Number.zero

/-- What every reachable ledger keeps about the subscription phase: the vault keeps the schedule it was
created with, and up to SubscriptionDate the ledger is idle. -/
structure LendingLedger.SubscriptionInv (l : LendingLedger) (s : VaultSchedule) : Prop where
  schedule : l.vault.schedule = some s
  idle : l.now.toNat ≤ s.subscriptionDate.toNat → l.Idle

/-- A loan transaction fails in the subscription phase. -/
private lemma LendingLedger.Idle.applyLoan_fails {l : LendingLedger} (hidle : l.Idle) {s : VaultSchedule}
    (hs : l.vault.schedule = some s) (hsub : l.now.toNat ≤ s.subscriptionDate.toNat) {tx : LendingTx}
    {u : LoanEffect} (hu : (l.applyLoan tx).run = .ok (.ok u)) : False := by
  cases tx with
  | loanSet i principal rates fees pi pt gp sd twoStep ao =>
    simp only [LendingLedger.applyLoan] at hu
    obtain ⟨broker, r, -, hc, -⟩ := l.applyLoanSet_inv _ _ _ _ _ _ _ _ hu
    have hph := (Vault.phase_subscription_iff l.vault l.now s hs).mpr hsub
    rcases Loan.canCreate_fitsVault _ _ _ _ _ _ _ hc with h | ⟨h, -⟩ <;> rw [hph] at h <;> cases h
  | loanAccept i =>
    obtain ⟨e, -, -, -, he, -⟩ := l.applyLoan_accept_inv u i hu
    rw [hidle.no_loans] at he; cases he
  | loanDelete i =>
    obtain ⟨e, -, -, -, he, -⟩ := l.applyLoan_delete_inv u i hu
    rw [hidle.no_loans] at he; cases he
  | loanManage i action =>
    obtain ⟨e, -, -, -, he, -⟩ := l.applyLoan_manage_inv u i action hu
    rw [hidle.no_loans] at he; cases he
  | loanPay i paymentType amount =>
    obtain ⟨e, -, -, -, he, -⟩ := l.applyLoan_pay_inv u i paymentType amount hu
    rw [hidle.no_loans] at he; cases he
  | _ => simp only [LendingLedger.applyLoan] at hu; cases hu

/-- Every transaction keeps the invariant. -/
lemma LendingLedger.SubscriptionInv.step {l l' : LendingLedger} {s : VaultSchedule} (hinv : l.SubscriptionInv s)
    {tx : LendingTx} (h : (l.apply tx).run = .ok (.ok l')) : l'.SubscriptionInv s := by
  by_cases hv : tx.isVault = true
  · obtain ⟨u, hu, rfl⟩ := LendingLedger.apply_vault hv h
    have hk := l.applyVault_keepsLending tx u hu
    have hvault : (l.commitVault u).vault = u.vault := by
      unfold LendingLedger.commitVault; split <;> simp [LendingLedger.setShares]
    have hrest : (l.commitVault u).loans = l.loans ∧ (l.commitVault u).brokers = l.brokers ∧
        (l.commitVault u).now = l.now := by
      unfold LendingLedger.commitVault; split <;> simp [LendingLedger.setShares]
    refine ⟨by rw [hvault, hk.schedule]; exact hinv.schedule, fun hsub => ?_⟩
    rw [hrest.2.2] at hsub
    have hidle := hinv.idle hsub
    refine ⟨fun j => ?_, fun j b hb => ?_, ?_, ?_, ?_⟩
    · unfold LendingLedger.loan?; rw [hrest.1]; exact hidle.no_loans j
    · unfold LendingLedger.broker? at hb; rw [hrest.2.1] at hb; exact hidle.no_debt j b hb
    · rw [hvault, hk.assetsDeployed]; exact hidle.assetsDeployed
    · rw [hvault, hk.assetsReserved]; exact hidle.assetsReserved
    · rw [hvault, hk.lossUnrealized]; exact hidle.lossUnrealized
  by_cases hb : tx.isBroker = true
  · obtain ⟨u, hu, rfl⟩ := LendingLedger.apply_broker hb h
    refine ⟨hinv.schedule, fun hsub => ?_⟩
    have hidle := hinv.idle hsub
    refine ⟨hidle.no_loans, fun j b' hb' => ?_, hidle.assetsDeployed, hidle.assetsReserved,
      hidle.lossUnrealized⟩
    rw [LendingLedger.broker?_commitBroker] at hb'
    by_cases hj : j = (if u.index < l.brokers.length then u.index else l.brokers.length)
    · rw [if_pos hj] at hb'
      rcases LendingLedger.applyBroker_debt l tx u hu b' hb' with h0 | ⟨b, hb, hd⟩
      · exact h0
      · rw [hd]; exact hidle.no_debt _ b hb
    · rw [if_neg hj] at hb'
      exact hidle.no_debt j b' hb'
  by_cases hl : tx.isLoan = true
  · obtain ⟨u, hu, rfl⟩ := LendingLedger.apply_loan hl h
    have hs := l.applyLoan_keepsSettings tx u hu
    exact ⟨by rw [← hinv.schedule]; exact hs.schedule, fun hsub =>
      ((hinv.idle hsub).applyLoan_fails hinv.schedule hsub hu).elim⟩
  have hc := (LendingLedger.apply_checked h).2
  cases tx <;> simp only [LendingTx.isVault, LendingTx.isBroker, LendingTx.isLoan, Bool.false_eq_true,
    not_false_eq_true, not_true_eq_false] at hv hb hl
  · -- vaultDelete only sets the deleted flag
    simp only [LendingLedger.applyChecked, LendingLedger.applyVaultDelete] at hc
    unfold_ter at hc
    walk_ok
    exact ⟨hinv.schedule, fun hsub => let hidle := hinv.idle hsub
      ⟨hidle.no_loans, hidle.no_debt, hidle.assetsDeployed, hidle.assetsReserved, hidle.lossUnrealized⟩⟩
  · -- close moves the close time forward
    simp only [LendingLedger.applyChecked] at hc
    cases hc
    refine ⟨hinv.schedule, fun hsub => ?_⟩
    have hle : l.now.toNat ≤ s.subscriptionDate.toNat := by
      simp only [max, UInt32.le_iff_toNat_le] at hsub
      split at hsub <;> omega
    have hidle := hinv.idle hle
    exact ⟨hidle.no_loans, hidle.no_debt, hidle.assetsDeployed, hidle.assetsReserved, hidle.lossUnrealized⟩

/-- A genesis ledger satisfies the invariant with the schedule its vault was created with. -/
private lemma LendingLedger.Genesis.subscriptionInv {g : LendingLedger} (hg : g.Genesis) :
    ∃ s, g.SubscriptionInv s := by
  obtain ⟨scale, m, s, eer, ocb, nt, -, hcreate⟩ := hg.created
  unfold Vault.create at hcreate
  have hraw := (XRPL.Model.SingleAssetVault.RawVault.to_lawful_ok hcreate).1
  refine ⟨s, (congrArg RawVault.schedule hraw :), fun _ => ⟨fun j => ?_, fun j b hb => ?_,
    (congrArg RawVault.assetsDeployed hraw :), (congrArg RawVault.assetsReserved hraw :),
    (congrArg RawVault.lossUnrealized hraw :)⟩⟩
  · unfold LendingLedger.loan?; rw [hg.no_loans]; rfl
  · unfold LendingLedger.broker? at hb; rw [hg.no_brokers] at hb; cases hb

/-- Every reachable ledger satisfies the invariant. -/
private lemma LendingLedger.Reachable.subscriptionInv {l : LendingLedger} (hr : l.Reachable) :
    ∃ s, l.SubscriptionInv s := by
  obtain ⟨g, txs, hg, hreach, -⟩ := hr
  obtain ⟨s, hs⟩ := hg.subscriptionInv
  exact ⟨s, hreach.invariant (Inv := fun l => l.SubscriptionInv s) hs fun _ _ _ _ hi ha => hi.step ha⟩

/-- Proof body of `Lending.Reachable.subscription_no_loans`. -/
lemma LendingLedger.subscription_no_loans_proof (l : LendingLedger) (hr : l.Reachable)
    (hsub : l.vault.phase l.now = .subscription) :
    (∀ j, l.loan? j = none) ∧
      (∀ (j : Nat) (b : LoanBroker), l.broker? j = some b → b.debtTotal = Number.zero ∧ b.loanCount = 0) ∧
      l.vault.assetsTotal = .ok l.vault.assetsAvailable ∧ l.vault.assetsDeployed = Number.zero ∧
      l.vault.lossUnrealized = Number.zero ∧ l.vault.assetsReserved = Number.zero ∧
      l.vault.yieldUnrealized = Number.zero := by
  obtain ⟨s, hinv⟩ := hr.subscriptionInv
  have hidle := hinv.idle ((Vault.phase_subscription_iff l.vault l.now s hinv.schedule).mp hsub)
  refine ⟨hidle.no_loans, fun j b hb => ⟨hidle.no_debt j b hb, ?_⟩, ?_, hidle.assetsDeployed,
    hidle.lossUnrealized, hidle.assetsReserved, ?_⟩
  · have hc := LendingLedger.loanCount_proof l hr j b hb
    rw [LendingLedger.loansOf_none hidle.no_loans j] at hc
    exact UInt32.toNat_inj.mp (by simpa using hc)
  · unfold RawVault.assetsTotal
    rw [hidle.assetsDeployed, Number.operator_add_zero_right]
  · exact (Number.toRat_eq_zero_iff_eq_zero l.vault.wf.yieldUnrealized_norm).mp (by
      rw [LendingLedger.yield_scheduled_proof l hr,
        l.interestSum_eq_zero _ fun j e he => by rw [hidle.no_loans j] at he; cases he])

end XRPL.Model.Lending
