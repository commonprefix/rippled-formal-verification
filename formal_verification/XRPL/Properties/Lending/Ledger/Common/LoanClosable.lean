import XRPL.Properties.Lending.Ledger.Common.ClosedLoans
import XRPL.Properties.Lending.Ledger.Common.LoansInv
import XRPL.Properties.Lending.Ledger.Common.ManageTotal
import XRPL.Properties.Lending.Ledger.Common.PaymentShareValue
import XRPL.Properties.Lending.Ledger.Common.PendingDelete
import XRPL.Properties.Lending.Ledger.Common.YieldSum
import XRPL.Properties.Lending.Loan.Common.DefaultFlag

/-! # Every loan can be deleted

A pending loan is deleted directly, a closed one too. An active loan waits for its grace period to end, is
defaulted, and then deleted as a closed loan. -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault (Vault RawVault)

/-- A close time one second after `x` passes `x`, while `x` is before the clock's last second. -/
private lemma UInt32.lt_max_succ (x a : UInt32) (h : x < maxTime) : x < max a (x + 1) := by
  have hm : maxTime.toNat = 4294967295 := rfl
  have hx : x.toNat < 4294967295 := by rw [← hm]; exact UInt32.lt_iff_toNat_lt.mp h
  have h1 : (x + 1).toNat = x.toNat + 1 := by rw [UInt32.toNat_add]; simp; omega
  rw [UInt32.lt_iff_toNat_lt]
  show x.toNat < (if a ≤ x + 1 then x + 1 else a).toNat
  split <;> rename_i hle
  · omega
  · rw [UInt32.le_iff_toNat_le] at hle; omega

/-- A close moves only the clock. -/
private lemma LendingLedger.apply_close (l : LendingLedger) (T : UInt32) :
    (l.apply (.close T)).run = .ok (.ok { l with now := max l.now T }) := rfl

/-- A default leaves a closed loan at its slot. The stored loan has no payment left and is not pending. -/
private lemma LendingLedger.default_slot (l l' : LendingLedger) (i : Nat)
    (h : (l.apply (.loanManage i .default)).run = .ok (.ok l')) :
    ∃ e', l'.loan? i = some e' ∧ e'.loan.paymentRemaining = 0 ∧ e'.loan.isPending = false ∧
      l'.vaultDeleted = l.vaultDeleted := by
  obtain ⟨u, hu, rfl⟩ := LendingLedger.apply_loan rfl h
  obtain ⟨e, b, loan, r, he, -, hw, hc, hok, rfl⟩ := LendingLedger.applyLoan_manage_inv l u i .default hu
  have hraw := Loan.withBroker_eq hw
  have hpend : loan.isPending = false := by
    cases hp : loan.isPending
    · rfl
    · unfold Loan.canManage at hc; simp [hp] at hc
  have hdef : ∃ r₀ : LoanWithAmounts Vault, (loan.manageDefault l.vault).run = .ok (.ok r₀) ∧ r.loan' = r₀.loan' := by
    simp only [Loan.manage] at hok
    unfold_ter at hok
    walk_ok
    exact ⟨_, ‹_›, rfl⟩
  obtain ⟨r₀, hok₀, hr⟩ := hdef
  obtain ⟨_, _, _, _, _, -, -, -, -, -, -, -, hloan, -⟩ := Loan.manageDefault_ok_parts loan l.vault r₀ hok₀
  have hpr := (Loan.manageDefault_closes_proof loan l.vault r₀ hok₀).2.2.2.1
  refine ⟨{ e with loan := r.loan' }, ?_, by rw [hr]; exact hpr, ?_, rfl⟩
  · rw [LendingLedger.loan?_commitLoan]
    simp [LoanEffect.ofLoan, LendingLedger.loan?_lt he]
  · show r.loan'.toRawLoan.isPending = false
    rw [hr, hloan]
    exact hpend

/-- Proof body of the delete line of `Lending.Reachable.loan_resolvable`. -/
lemma LendingLedger.loan_closable_proof (l : LendingLedger) (hr : l.Reachable) (hnd : l.vaultDeleted = false)
    (i : Nat) (e : LoanEntry) (he : l.loan? i = some e)
    (hfit : e.loan.isPending = true → STAmount.Representable l.vault.numericType
      (l.vault.assetsAvailable.toRat + e.loan.principalOutstanding.toRat))
    (htime : e.loan.isPending = false → e.loan.paymentRemaining ≠ 0 →
      e.loan.nextPaymentDueDate + e.loan.schedule.gracePeriod < maxTime)
    (htotal : e.loan.isPending = false → e.loan.paymentRemaining ≠ 0 →
      l.vault.assetsAvailable.toRat + l.vault.assetsDeployed.toRat < 10 ^ 16 * (10 : ℚ) ^ l.vault.baseExponent)
    (hca : e.loan.isPending = false → e.loan.paymentRemaining ≠ 0 →
      ∀ b, l.broker? e.brokerIndex = some b → b.coverAvailable.toRat < 10 ^ 96) :
    ∃ (txs : List LendingTx) (l' l'' : LendingLedger), LendingLedger.Reaches l txs l' ∧
      (∀ tx ∈ txs, (∃ t, tx = .close t) ∨ tx = .loanManage i .default) ∧
      (l'.apply (.loanDelete i)).run = .ok (.ok l'') := by
  by_cases hp : e.loan.isPending = true
  · -- a pending loan is deleted directly
    obtain ⟨l'', h⟩ := LendingLedger.pending_resolvable_proof l hr hr.holdsAsset.maxValue_le hnd i e he hp (hfit hp)
    exact ⟨[], l, l'', .refl, (fun _ h => by cases h), h⟩
  have hnp : e.loan.isPending = false := by simpa using hp
  by_cases hrem : e.loan.paymentRemaining = 0
  · -- a closed loan too
    obtain ⟨l'', h⟩ := LendingLedger.closed_loan_deletable l hr hnd i e he hrem hnp
    exact ⟨[], l, l'', .refl, (fun _ h => by cases h), h⟩
  -- an active loan is not defaulted: a defaulted reachable loan has no payment left
  have hd : e.loan.isDefault = false := by
    obtain ⟨s, hinv⟩ := hr.loansInv
    obtain ⟨t, -, hreach⟩ := hinv.reachable i e he
    cases hdf : e.loan.isDefault
    · rfl
    · exact absurd (hreach.default_paidOff hdf) hrem

  -- the ledger closes after the grace period, then the loan is defaulted
  set T := e.loan.nextPaymentDueDate + e.loan.schedule.gracePeriod + 1
  set l₁ : LendingLedger := { l with now := max l.now T }
  have hc₁ := LendingLedger.apply_close l T
  have hr₁ : l₁.Reachable := hr.apply hc₁
  have hlate : e.loan.nextPaymentDueDate + e.loan.schedule.gracePeriod < l₁.now :=
    UInt32.lt_max_succ _ l.now (htime hnp hrem)
  obtain ⟨l₂, hd₂⟩ := LendingLedger.default_possible_proof l₁ hr₁ hnd hr₁.holdsAsset i e he hnp hd hrem hlate
    (htotal hnp hrem) (hr₁.assetsAvailable_units hr₁.holdsAsset) hr₁.yield_lt (hr₁.interest_le_yield he hnp)
    (hca hnp hrem)
  have hr₂ : l₂.Reachable := hr₁.apply hd₂

  -- and deleted as a closed loan
  obtain ⟨e₂, he₂, hrem₂, hnp₂, hnd₂⟩ := LendingLedger.default_slot l₁ l₂ i hd₂
  obtain ⟨l₃, h₃⟩ := LendingLedger.closed_loan_deletable l₂ hr₂ (by rw [hnd₂]; exact hnd) i e₂ he₂ hrem₂ hnp₂
  exact ⟨[.close T, .loanManage i .default], l₂, l₃, by
    simpa using (LendingLedger.Reaches.single hc₁).step _ hd₂, by simp, h₃⟩

end XRPL.Model.Lending
