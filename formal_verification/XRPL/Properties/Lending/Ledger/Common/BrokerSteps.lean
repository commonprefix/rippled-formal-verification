import XRPL.Properties.Lending.Common.Walk
import XRPL.Properties.Lending.Ledger.Common.ReachableProofs
import XRPL.Properties.Lending.LoanBroker.LoanBrokerValid
import XRPL.Model.Lending.LoanBroker.LoanBrokerDelete

/-! # What a broker transaction does to the broker slots

A broker transaction writes one slot. The broker it writes keeps the debt and loan count it had, or is
a new broker without either, or the slot is emptied for a broker without loans. -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol

/-- A cover transaction keeps the debt. -/
private lemma LoanBroker.applyCoverTransaction_debt (lb : LoanBroker) (d : CoverDirection) (a : STAmount)
    (r : LoanBrokerCoverResult) (h : lb.applyCoverTransaction d a = .ok r) :
    r.loanBroker'.debtTotal = lb.debtTotal := by
  unfold LoanBroker.applyCoverTransaction at h
  obtain ⟨_, -, h⟩ := bind_ok_peel _ _ _ h
  dsimp only at h
  cases d <;>
  · obtain ⟨_, -, h⟩ := bind_ok_peel _ _ _ h
    obtain ⟨b, hb, h⟩ := bind_ok_peel _ _ _ h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    exact (congrArg RawLoanBroker.debtTotal (RawLoanBroker.to_lawful_ok hb).1 :)

/-- A broker transaction writes a broker with the debt it had, or a new broker without debt. -/
lemma LendingLedger.applyBroker_debt (l : LendingLedger) (tx : LendingTx) (u : BrokerEffect)
    (h : (l.applyBroker tx).run = .ok (.ok u)) (b' : LoanBroker) (hb' : u.broker = some b') :
    b'.debtTotal = Number.zero ∨ ∃ b, l.broker? u.index = some b ∧ b'.debtTotal = b.debtTotal := by
  cases tx with
  | loanBrokerCreate ctx =>
    simp only [LendingLedger.applyBroker] at h
    unfold_ter at h
    walk_ok
    simp only [Option.some.injEq] at hb'
    subst hb'
    left
    exact (congrArg RawLoanBroker.debtTotal (RawLoanBroker.to_lawful_ok ‹_›).1 :)
  | loanBrokerUpdate i dm =>
    simp only [LendingLedger.applyBroker] at h
    unfold_ter at h
    walk_ok
    simp only [Option.some.injEq] at hb'
    subst hb'
    right
    exact ⟨_, ‹_›, (congrArg RawLoanBroker.debtTotal (RawLoanBroker.to_lawful_ok ‹_›).1 :)⟩
  | loanBrokerCoverDeposit i a =>
    simp only [LendingLedger.applyBroker, LoanBroker.coverDeposit] at h
    unfold_ter at h
    walk_ok
    simp only [Option.some.injEq] at hb'
    subst hb'
    right
    exact ⟨_, ‹_›, LoanBroker.applyCoverTransaction_debt _ _ _ _ ‹_›⟩
  | loanBrokerCoverWithdraw i a =>
    simp only [LendingLedger.applyBroker, LoanBroker.coverWithdraw] at h
    unfold_ter at h
    walk_ok
    simp only [Option.some.injEq] at hb'
    subst hb'
    right
    exact ⟨_, ‹_›, LoanBroker.applyCoverTransaction_debt _ _ _ _ ‹_›⟩
  | loanBrokerCoverClawback i a =>
    simp only [LendingLedger.applyBroker, LoanBroker.coverClawback] at h
    unfold_ter at h
    walk_ok
    simp only [Option.some.injEq] at hb'
    subst hb'
    right
    exact ⟨_, ‹_›, LoanBroker.applyCoverTransaction_debt _ _ _ _ ‹_›⟩
  | loanBrokerDelete i =>
    simp only [LendingLedger.applyBroker] at h
    unfold_ter at h
    walk_ok
    cases hb'
  | _ => simp only [LendingLedger.applyBroker] at h; cases h

/-- A cover transaction keeps the loan count. -/
private lemma LoanBroker.applyCoverTransaction_loanCount (lb : LoanBroker) (d : CoverDirection) (a : STAmount)
    (r : LoanBrokerCoverResult) (h : lb.applyCoverTransaction d a = .ok r) :
    r.loanBroker'.loanCount = lb.loanCount := by
  unfold LoanBroker.applyCoverTransaction at h
  obtain ⟨_, -, h⟩ := bind_ok_peel _ _ _ h
  dsimp only at h
  cases d <;>
  · obtain ⟨_, -, h⟩ := bind_ok_peel _ _ _ h
    obtain ⟨b, hb, h⟩ := bind_ok_peel _ _ _ h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    exact (congrArg RawLoanBroker.loanCount (RawLoanBroker.to_lawful_ok hb).1 :)

/-- A deletable broker has no loans. -/
private lemma LoanBroker.canDelete_loanCount {α : Type} [AssetPool α] (lb : LoanBroker) (pool : α)
    (h : lb.canDelete pool = .ok .tesSUCCESS) : lb.loanCount = 0 := by
  unfold LoanBroker.canDelete at h
  by_contra hne
  rw [if_pos (by simpa using hne)] at h
  cases h

/-- A broker transaction adds a broker without debt or loans at the end, rewrites a broker keeping its
debt and loan count, or deletes a broker without loans. -/
lemma LendingLedger.applyBroker_cases (l : LendingLedger) (tx : LendingTx) (u : BrokerEffect)
    (h : (l.applyBroker tx).run = .ok (.ok u)) :
    (u.index = l.brokers.length ∧ ∃ b', u.broker = some b' ∧ b'.debtTotal = Number.zero ∧ b'.loanCount = 0) ∨
      (∃ b b', l.broker? u.index = some b ∧ u.broker = some b' ∧ b'.debtTotal = b.debtTotal ∧
        b'.loanCount = b.loanCount) ∨
      (∃ b, l.broker? u.index = some b ∧ u.broker = none ∧ b.loanCount = 0) := by
  cases tx with
  | loanBrokerCreate ctx =>
    simp only [LendingLedger.applyBroker] at h
    unfold_ter at h
    walk_ok
    have hraw := (RawLoanBroker.to_lawful_ok ‹_›).1
    exact Or.inl ⟨rfl, _, rfl, (congrArg RawLoanBroker.debtTotal hraw :), (congrArg RawLoanBroker.loanCount hraw :)⟩
  | loanBrokerUpdate i dm =>
    simp only [LendingLedger.applyBroker] at h
    unfold_ter at h
    walk_ok
    have hraw := (RawLoanBroker.to_lawful_ok ‹_›).1
    exact Or.inr (Or.inl ⟨_, _, ‹_›, rfl, (congrArg RawLoanBroker.debtTotal hraw :),
      (congrArg RawLoanBroker.loanCount hraw :)⟩)
  | loanBrokerCoverDeposit i a =>
    simp only [LendingLedger.applyBroker, LoanBroker.coverDeposit] at h
    unfold_ter at h
    walk_ok
    exact Or.inr (Or.inl ⟨_, _, ‹_›, rfl, LoanBroker.applyCoverTransaction_debt _ _ _ _ ‹_›,
      LoanBroker.applyCoverTransaction_loanCount _ _ _ _ ‹_›⟩)
  | loanBrokerCoverWithdraw i a =>
    simp only [LendingLedger.applyBroker, LoanBroker.coverWithdraw] at h
    unfold_ter at h
    walk_ok
    exact Or.inr (Or.inl ⟨_, _, ‹_›, rfl, LoanBroker.applyCoverTransaction_debt _ _ _ _ ‹_›,
      LoanBroker.applyCoverTransaction_loanCount _ _ _ _ ‹_›⟩)
  | loanBrokerCoverClawback i a =>
    simp only [LendingLedger.applyBroker, LoanBroker.coverClawback] at h
    unfold_ter at h
    walk_ok
    exact Or.inr (Or.inl ⟨_, _, ‹_›, rfl, LoanBroker.applyCoverTransaction_debt _ _ _ _ ‹_›,
      LoanBroker.applyCoverTransaction_loanCount _ _ _ _ ‹_›⟩)
  | loanBrokerDelete i =>
    simp only [LendingLedger.applyBroker] at h
    unfold_ter at h
    walk_ok
    simp only [Bool.not_eq_eq_eq_not, Bool.not_true, Bool.not_eq_false, TER.isTesSuccess_iff] at *
    subst_vars
    exact Or.inr (Or.inr ⟨_, ‹_›, trivial, LoanBroker.canDelete_loanCount _ _ ‹_›⟩)
  | _ => simp only [LendingLedger.applyBroker] at h; cases h

/-- A stored broker sits at an index inside the list. -/
lemma LendingLedger.broker?_lt {l : LendingLedger} {i : Nat} {b : LoanBroker} (h : l.broker? i = some b) :
    i < l.brokers.length := by
  unfold LendingLedger.broker? at h
  by_contra hc
  rw [List.getElem?_eq_none (by omega)] at h
  cases h


/-- The broker slots after a broker effect: the written slot holds the effect's broker, the others are as
they were. -/
lemma LendingLedger.broker?_commitBroker (l : LendingLedger) (u : BrokerEffect) (j : Nat) :
    (l.commitBroker u).broker? j =
      if j = (if u.index < l.brokers.length then u.index else l.brokers.length) then u.broker
      else l.broker? j := by
  unfold LendingLedger.commitBroker LendingLedger.broker? storeSlot
  dsimp only
  split
  · rename_i hlt
    split
    · subst_vars; rw [List.getElem?_set_self hlt]; rfl
    · rw [List.getElem?_set_ne (Ne.symm ‹_›)]
  · split
    · subst_vars; rw [List.getElem?_append_right (le_refl _)]; simp
    · rename_i hge hne
      rw [List.getElem?_append]
      split
      · rfl
      · rename_i hlt
        have h1 : l.brokers[j]? = none := List.getElem?_eq_none (by omega)
        have h2 : j - l.brokers.length ≠ 0 := by omega
        rw [h1, List.getElem?_cons]
        simp [h2]

/-- The broker slots after a loan effect on a stored broker: its slot holds the effect's broker. -/
lemma LendingLedger.broker?_commitLoan (l : LendingLedger) (u : LoanEffect) (b : LoanBroker)
    (hb : l.broker? u.brokerIndex = some b) (j : Nat) :
    (l.commitLoan u).broker? j = if j = u.brokerIndex then some u.broker else l.broker? j := by
  have hlt := LendingLedger.broker?_lt hb
  unfold LendingLedger.commitLoan LendingLedger.broker?
  dsimp only
  split
  · subst_vars; rw [List.getElem?_set_self hlt]; rfl
  · rw [List.getElem?_set_ne (Ne.symm ‹_›)]

end XRPL.Model.Lending
