import XRPL.Properties.Lending.Ledger.Common.DebtInv
import XRPL.Properties.Lending.Loan.Common.YieldGrid

/-! # YieldUnrealized on the base grid

Every loan operation adds to YieldUnrealized a whole number of base units, or leaves it, and a sum of two
whole numbers of base units rounds to one, so YieldUnrealized stays a whole number of base units. -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault (Vault RawVault)

/-- What every reachable ledger keeps about YieldUnrealized: it is a whole number of base units. -/
structure LendingLedger.YieldGridInv (l : LendingLedger) : Prop where
  reserved : l.ReservedInv
  grid : Number.OnGrid l.vault.baseExponent l.vault.yieldUnrealized

/-- A loan transaction keeps the invariant. -/
lemma LendingLedger.YieldGridInv.loan_step {l : LendingLedger} (hinv : l.YieldGridInv) {tx : LendingTx}
    (hpre : (tx.preflight l).isTesSuccess = true) {u : LoanEffect} (hu : (l.applyLoan tx).run = .ok (.ok u)) :
    (l.commitLoan u).YieldGridInv := by
  have hs := l.applyLoan_keepsSettings tx u hu
  have hres := hinv.reserved.loan_step hpre hu
  have hscale := hinv.reserved.scale
  have hbase := Vault.baseExponent_scale_range l.vault
  have hsb : minExponent + 18 ≤ l.vault.baseExponent ∧ l.vault.baseExponent ≤ maxExponent - 1 := by
    unfold minExponent maxExponent; omega
  have hv : (l.commitLoan u).vault = u.vault := rfl
  suffices h : (∃ y, Number.OnGrid l.vault.baseExponent y ∧
      l.vault.yieldUnrealized.operator_add y .to_nearest = .ok u.vault.yieldUnrealized) ∨
      u.vault.yieldUnrealized = l.vault.yieldUnrealized by
    refine ⟨hres, ?_⟩
    rw [hv, hs.baseExponent_eq]
    rcases h with ⟨y, hy, hadd⟩ | heq
    · exact Number.OnGrid.add hinv.grid hy hsb hadd
    · rw [heq]; exact hinv.grid
  have hls : ∀ (i : Nat) (e : LoanEntry) (broker : LoanBroker) (loan : Loan), l.loan? i = some e →
      e.loan.withBroker broker = .ok loan → loan.loanScale = l.vault.baseExponent := fun i e broker loan he hw => by
    rw [show loan.loanScale = e.loan.loanScale from (congrArg RawLoan.loanScale (Loan.withBroker_eq hw) :)]
    exact hscale.loanScale i e he
  cases tx with
  | loanSet i principal rates fees pi pt gp sd twoStep ao =>
    obtain ⟨hpn, hpos⟩ := LendingTx.preflight_loanSet_principal l i principal rates fees pi pt gp sd twoStep ao hpre
    simp only [LendingLedger.applyLoan] at hu
    obtain ⟨broker, r, hb, hc, hcr, rfl⟩ := l.applyLoanSet_inv _ _ _ _ _ _ _ _ hu
    have hst := Loan.canCreate_exact _ _ _ _ _ _ _ hc principal (List.mem_cons_self ..)
    exact Or.inl (Loan.create_yieldStep broker l.vault principal rates fees _ ao twoStep r hpn hpos hst
      (hscale.brokers i broker hb) hinv.reserved.grid hcr)
  | loanAccept i =>
    obtain ⟨e, broker, loan, r, he, hb, hw, -, hr, rfl⟩ := l.applyLoan_accept_inv u i hu
    obtain ⟨y, hy, hadd⟩ := Loan.accept_yieldStep loan l.vault r hr
    rw [hls i e broker loan he hw] at hy
    exact Or.inl ⟨y, hy, hadd⟩
  | loanManage i action =>
    obtain ⟨e, broker, loan, r, he, hb, hw, -, hr, rfl⟩ := l.applyLoan_manage_inv u i action hu
    cases action with
    | impair => exact Or.inr (Loan.manageImpair_yield loan l.vault l.now r hr)
    | unimpair => exact Or.inr (Loan.manageUnimpair_yield loan l.vault r hr)
    | default =>
      simp only [Loan.manage] at hr
      unfold_ter at hr
      walk_ok
      rename_i rd hd
      obtain ⟨y, hy, hadd⟩ := Loan.manageDefault_yieldStep loan l.vault rd hd
      rw [hls i e broker loan he hw] at hy
      exact Or.inl ⟨y, hy, hadd⟩
  | loanPay i paymentType amount =>
    obtain ⟨e, broker, loan, r, he, hb, hw, -, hr, rfl⟩ := l.applyLoan_pay_inv u i paymentType amount hu
    obtain ⟨y, hy, hadd⟩ := Loan.pay_yieldStep loan l.vault paymentType amount l.now r hr
    rw [hls i e broker loan he hw] at hy
    exact Or.inl ⟨y, hy, hadd⟩
  | loanDelete i =>
    obtain ⟨e, broker, loan, r, he, hb, hw, -, hr, rfl⟩ := l.applyLoan_delete_inv u i hu
    exact Or.inr (Loan.delete_yield loan l.vault r hr)
  | _ => simp only [LendingLedger.applyLoan] at hu; cases hu

/-- Every transaction keeps the invariant. -/
lemma LendingLedger.YieldGridInv.step {l l' : LendingLedger} (hinv : l.YieldGridInv) {tx : LendingTx}
    (h : (l.apply tx).run = .ok (.ok l')) : l'.YieldGridInv := by
  have hpre := (LendingLedger.apply_checked h).1
  have hres := hinv.reserved.step h
  by_cases hv : tx.isVault = true
  · obtain ⟨u, hu, rfl⟩ := LendingLedger.apply_vault hv h
    have hk := l.applyVault_keepsLending tx u hu
    have hvault : (l.commitVault u).vault = u.vault := by
      unfold LendingLedger.commitVault; split <;> simp [LendingLedger.setShares]
    have hbe : u.vault.baseExponent = l.vault.baseExponent := by
      unfold XRPL.Model.SingleAssetVault.Vault.baseExponent; rw [hk.numericType, hk.scale]
    refine ⟨hres, ?_⟩
    rw [hvault, hbe, hk.yieldUnrealized]; exact hinv.grid
  by_cases hb : tx.isBroker = true
  · obtain ⟨u, -, rfl⟩ := LendingLedger.apply_broker hb h
    exact ⟨hres, hinv.grid⟩
  by_cases hl : tx.isLoan = true
  · obtain ⟨u, hu, rfl⟩ := LendingLedger.apply_loan hl h
    exact hinv.loan_step hpre hu
  have hc := (LendingLedger.apply_checked h).2
  cases tx <;> simp only [LendingTx.isVault, LendingTx.isBroker, LendingTx.isLoan, Bool.false_eq_true,
    not_false_eq_true, not_true_eq_false] at hv hb hl
  · -- vaultDelete only sets the deleted flag
    simp only [LendingLedger.applyChecked, LendingLedger.applyVaultDelete] at hc
    unfold_ter at hc
    walk_ok
    exact ⟨hres, hinv.grid⟩
  · -- close only moves the close time
    simp only [LendingLedger.applyChecked] at hc
    cases hc
    exact ⟨hres, hinv.grid⟩

/-- A genesis ledger has no yield. -/
lemma LendingLedger.Genesis.yieldGridInv {g : LendingLedger} (hg : g.Genesis) : g.YieldGridInv := by
  obtain ⟨scale, m, s, eer, ocb, nt, -, hcreate⟩ := hg.created
  unfold Vault.create at hcreate
  have hraw := (XRPL.Model.SingleAssetVault.RawVault.to_lawful_ok hcreate).1
  have hyu : g.vault.yieldUnrealized = Number.zero := (congrArg RawVault.yieldUnrealized hraw :)
  exact ⟨hg.reservedInv, by rw [hyu]; exact Number.OnGrid.zero _⟩

/-- Every reachable ledger satisfies the invariant. -/
lemma LendingLedger.Reachable.yieldGridInv {l : LendingLedger} (hr : l.Reachable) : l.YieldGridInv :=
  LendingLedger.Reachable.invariant (fun _ hg => hg.yieldGridInv) (fun _ _ _ hi ha => hi.step ha) hr

end XRPL.Model.Lending
