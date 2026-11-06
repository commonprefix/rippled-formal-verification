import XRPL.Properties.Lending.Ledger.Common.LoansInv

/-! # Every loan starts after SubscriptionDate

LoanSet needs the vault in its investment phase, so the close time is after SubscriptionDate, and a loan starts at
the close time or, for a two-step LoanSet, after it. Every stored loan of a reachable ledger keeps that StartDate. -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault (Vault RawVault VaultSchedule)

/-- A passing two-step LoanSet starts after the close time. -/
private lemma Loan.canCreate_startDate (broker : LoanBroker) (v : Vault) (p : Number) (fees : LoanFees)
    (schedule : LoanSchedule) (t : UInt32) (twoStep : Bool)
    (h : Loan.canCreate broker v p fees schedule t twoStep = .ok .tesSUCCESS) (ht : twoStep = true) :
    t < schedule.startDate := by
  unfold Loan.canCreate at h
  generalize schedule.checkTimeAvailability = st at h
  obtain ⟨st, rfl⟩ : ∃ t, st = .ok t := by
    cases st with
    | error e => simp [bind, Except.bind] at h
    | ok t => exact ⟨t, rfl⟩
  simp only [bind, Except.bind, pure, Except.pure] at h
  split at h
  · cases h; exact absurd ‹_› (by decide)
  · split at h
    · cases h
    · rename_i hexp
      simp only [ht, Bool.true_and, decide_eq_true_eq, ge_iff_le] at hexp
      rw [UInt32.le_iff_toNat_le] at hexp
      exact UInt32.lt_iff_toNat_lt.mpr (by omega)

/-- A vault in its investment phase is past SubscriptionDate. -/
private lemma Vault.phase_investment {v : Vault} {s : VaultSchedule} {t : UInt32} (hs : v.schedule = some s)
    (h : v.phase t = .investment) : s.subscriptionDate < t := by
  simp only [XRPL.Model.SingleAssetVault.Vault.phase, hs] at h
  split at h
  · cases h
  · rename_i hsub
    simpa using hsub

/-- What every reachable ledger keeps about its loans' start: the vault keeps its schedule, and every stored loan
starts after SubscriptionDate. -/
structure LendingLedger.StartsInv (l : LendingLedger) (s : VaultSchedule) : Prop where
  schedule : l.vault.schedule = some s
  starts : ∀ (j : Nat) (e : LoanEntry), l.loan? j = some e →
    s.subscriptionDate.toNat < e.loan.schedule.startDate.toNat

/-- A loan transaction keeps the invariant. -/
lemma LendingLedger.StartsInv.loan_step {l : LendingLedger} {s : VaultSchedule} (hinv : l.StartsInv s)
    {tx : LendingTx} {u : LoanEffect} (hu : (l.applyLoan tx).run = .ok (.ok u)) : (l.commitLoan u).StartsInv s := by
  have hs := l.applyLoan_keepsSettings tx u hu
  have hnew : ∀ e', u.loan = some e' → s.subscriptionDate.toNat < e'.loan.schedule.startDate.toNat := by
    intro e' he'
    cases tx with
    | loanSet i principal rates fees pi pt gp sd twoStep ao =>
      simp only [LendingLedger.applyLoan] at hu
      obtain ⟨broker, r, hb, hc, hcr, rfl⟩ := l.applyLoanSet_inv _ _ _ _ _ _ _ _ hu
      simp only [LoanEffect.ofCreate, Option.some.injEq] at he'
      subst he'
      obtain ⟨_, _, _, _, _, -, -, -, -, hloan⟩ := Loan.create_ok_inv _ _ _ _ _ _ _ _ r hcr
      have hsch := (congrArg RawLoan.schedule (RawLoan.to_lawful_ok hloan).1 :)
      dsimp only at hsch ⊢
      rw [hsch]
      have hsub : s.subscriptionDate < l.now := by
        rcases Loan.canCreate_fitsVault _ _ _ _ _ _ _ hc with hph | ⟨hph, -⟩
        · simp only [XRPL.Model.SingleAssetVault.Vault.phase, hinv.schedule, ge_iff_le] at hph
          split at hph <;> [skip; split at hph] <;> cases hph
        · exact Vault.phase_investment hinv.schedule hph
      rw [UInt32.lt_iff_toNat_lt] at hsub
      cases htwo : twoStep
      · simp only [RawLoan.build, LoanSchedule.build, Bool.false_eq_true, ↓reduceIte]
        exact hsub
      · have := UInt32.lt_iff_toNat_lt.mp (Loan.canCreate_startDate _ _ _ _ _ _ _ hc htwo)
        simp only [RawLoan.build, LoanSchedule.build, htwo, ↓reduceIte] at this ⊢
        omega
    | loanAccept i =>
      obtain ⟨e, broker, loan, r, he, hb, hw, hc, hr, rfl⟩ := l.applyLoan_accept_inv u i hu
      simp only [LoanEffect.ofLoan, Option.some.injEq] at he'
      subst he'
      have ht := (Loan.KeepsTerms.of_lawful hw rfl rfl rfl rfl rfl).trans (Loan.accept_keepsTerms _ _ _ hr)
      dsimp only
      rw [ht.schedule]
      exact hinv.starts i e he
    | loanDelete i =>
      obtain ⟨e, broker, loan, r, he, hb, hw, hc, hr, rfl⟩ := l.applyLoan_delete_inv u i hu
      cases he'
    | loanManage i action =>
      obtain ⟨e, broker, loan, r, he, hb, hw, hc, hr, rfl⟩ := l.applyLoan_manage_inv u i action hu
      simp only [LoanEffect.ofLoan, Option.some.injEq] at he'
      subst he'
      have ht := (Loan.KeepsTerms.of_lawful hw rfl rfl rfl rfl rfl).trans (Loan.manage_keepsTerms _ _ _ _ _ hr)
      dsimp only
      rw [ht.schedule]
      exact hinv.starts i e he
    | loanPay i paymentType amount =>
      obtain ⟨e, broker, loan, r, he, hb, hw, hc, hr, rfl⟩ := l.applyLoan_pay_inv u i paymentType amount hu
      simp only [LoanEffect.ofLoan, Option.some.injEq] at he'
      subst he'
      have ht := (Loan.KeepsTerms.of_lawful hw rfl rfl rfl rfl rfl).trans (Loan.pay_keepsTerms _ _ _ _ _ _ hr)
      dsimp only
      rw [ht.schedule]
      exact hinv.starts i e he
    | _ => simp only [LendingLedger.applyLoan] at hu; cases hu
  refine ⟨by rw [← hinv.schedule]; exact hs.schedule, fun j e he => ?_⟩
  rw [LendingLedger.loan?_commitLoan] at he
  by_cases hj : j = (if u.loanIndex < l.loans.length then u.loanIndex else l.loans.length)
  · rw [if_pos hj] at he
    exact hnew e he
  · rw [if_neg hj] at he
    exact hinv.starts j e he

/-- Every transaction keeps the invariant. -/
lemma LendingLedger.StartsInv.step {l l' : LendingLedger} {s : VaultSchedule} (hinv : l.StartsInv s)
    {tx : LendingTx} (h : (l.apply tx).run = .ok (.ok l')) : l'.StartsInv s := by
  by_cases hv : tx.isVault = true
  · obtain ⟨u, hu, rfl⟩ := LendingLedger.apply_vault hv h
    have hk := l.applyVault_keepsLending tx u hu
    have hloans : (l.commitVault u).loans = l.loans := by
      unfold LendingLedger.commitVault; split <;> simp [LendingLedger.setShares]
    have hvault : (l.commitVault u).vault = u.vault := by
      unfold LendingLedger.commitVault; split <;> simp [LendingLedger.setShares]
    have hloan : ∀ j, (l.commitVault u).loan? j = l.loan? j := fun j => by
      unfold LendingLedger.loan?; rw [hloans]
    refine ⟨by rw [hvault, hk.schedule]; exact hinv.schedule, fun j e he => ?_⟩
    rw [hloan] at he; exact hinv.starts j e he
  by_cases hb : tx.isBroker = true
  · obtain ⟨u, -, rfl⟩ := LendingLedger.apply_broker hb h
    exact ⟨hinv.schedule, hinv.starts⟩
  by_cases hl : tx.isLoan = true
  · obtain ⟨u, hu, rfl⟩ := LendingLedger.apply_loan hl h
    exact hinv.loan_step hu
  have hc := (LendingLedger.apply_checked h).2
  cases tx <;> simp only [LendingTx.isVault, LendingTx.isBroker, LendingTx.isLoan, Bool.false_eq_true,
    not_false_eq_true, not_true_eq_false] at hv hb hl
  · -- vaultDelete only sets the deleted flag
    simp only [LendingLedger.applyChecked, LendingLedger.applyVaultDelete] at hc
    unfold_ter at hc
    walk_ok
    exact ⟨hinv.schedule, hinv.starts⟩
  · -- close moves the close time forward
    simp only [LendingLedger.applyChecked] at hc
    cases hc
    exact ⟨hinv.schedule, hinv.starts⟩

/-- A genesis ledger satisfies the invariant with the schedule its vault was created with. -/
lemma LendingLedger.Genesis.startsInv {g : LendingLedger} (hg : g.Genesis) : ∃ s, g.StartsInv s := by
  obtain ⟨s, hs⟩ := hg.loansInv
  have hnone : ∀ j, g.loan? j = none := fun j => by unfold LendingLedger.loan?; rw [hg.no_loans]; rfl
  exact ⟨s, hs.schedule, fun j e he => by rw [hnone] at he; cases he⟩

/-- Every reachable ledger satisfies the invariant. -/
lemma LendingLedger.Reachable.startsInv {l : LendingLedger} (hr : l.Reachable) : ∃ s, l.StartsInv s := by
  obtain ⟨g, txs, hg, hreach, -⟩ := hr
  obtain ⟨s, hs⟩ := hg.startsInv
  exact ⟨s, hreach.invariant (Inv := fun l => l.StartsInv s) hs fun _ _ _ _ hi ha => hi.step ha⟩

end XRPL.Model.Lending
