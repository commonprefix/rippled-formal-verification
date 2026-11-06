import XRPL.Properties.Lending.Ledger.Common.Scope

/-! # What a successful ledger loan transaction ran

Each successful loan transaction found its loan and broker, refreshed the loan's broker, passed its
checks and ran its operation. These lemmas let invariants follow one loan through the ledger. -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault (Vault RawVault)

/-- The create step of a LoanSet succeeds only when the checks returned success. -/
private lemma LendingLedger.loanSetChecked_inv (l : LendingLedger) (u : LoanEffect) (i : Nat) (broker : LoanBroker)
    (principal : Number) (rates : LoanRates) (fees : LoanFees) (schedule : LoanSchedule) (twoStep ao : Bool)
    (checks : Except Error TER)
    (h : (l.loanSetChecked i broker principal rates fees schedule twoStep ao checks).run = .ok (.ok u)) :
    ∃ r, checks = .ok .tesSUCCESS ∧
      (Loan.create broker l.vault principal rates fees schedule ao twoStep).run = .ok (.ok r) ∧
      u = LoanEffect.ofCreate i l.loans.length r := by
  unfold LendingLedger.loanSetChecked at h
  cases checks with
  | error e => cases h
  | ok ter =>
    dsimp only at h
    split at h
    · cases h
    rename_i hter
    have hter' : ter = .tesSUCCESS := (TER.isTesSuccess_iff ter).mp (by simpa using hter)
    subst hter'
    obtain ⟨r, hr, rfl⟩ := TerExcept.map_ok h
    exact ⟨r, rfl, hr, rfl⟩

/-- A successful LoanSet passed its checks and created the loan it stores at the end of the list. -/
lemma LendingLedger.applyLoanSet_inv (l : LendingLedger) (u : LoanEffect) (i : Nat) (principal : Number)
    (rates : LoanRates) (fees : LoanFees) (schedule : LoanSchedule) (twoStep ao : Bool)
    (h : (l.applyLoanSet i principal rates fees schedule twoStep ao).run = .ok (.ok u)) :
    ∃ broker r, l.broker? i = some broker ∧
      Loan.canCreate broker l.vault principal fees schedule l.now twoStep = .ok .tesSUCCESS ∧
      (Loan.create broker l.vault principal rates fees schedule ao twoStep).run = .ok (.ok r) ∧
      u = LoanEffect.ofCreate i l.loans.length r := by
  unfold LendingLedger.applyLoanSet at h
  dsimp only at h
  split at h
  · simp [ExceptT.run, ExceptT.mk] at h
  split at h
  · cases h
  generalize hb : l.broker? i = ob at h
  cases ob with
  | none => cases h
  | some broker =>
    obtain ⟨r, hc, hr, rfl⟩ := l.loanSetChecked_inv _ _ _ _ _ _ _ _ _ _ h
    exact ⟨broker, r, rfl, hc, hr, rfl⟩

/-- A successful LoanAccept ran on a stored loan with its broker refreshed. -/
lemma LendingLedger.applyLoan_accept_inv (l : LendingLedger) (u : LoanEffect) (i : Nat)
    (h : (l.applyLoan (.loanAccept i)).run = .ok (.ok u)) :
    ∃ e broker loan r, l.loan? i = some e ∧ l.broker? e.brokerIndex = some broker ∧
      e.loan.withBroker broker = .ok loan ∧ loan.canAccept l.vault l.now = .ok .tesSUCCESS ∧
      (loan.accept l.vault).run = .ok (.ok r) ∧ u = LoanEffect.ofLoan i e r.loan' r.pool' := by
  simp only [LendingLedger.applyLoan] at h
  unfold_ter at h
  walk_ok
  simp only [Bool.not_eq_eq_eq_not, Bool.not_true] at *
  simp only [Bool.not_eq_false, TER.isTesSuccess_iff] at *
  subst_vars
  exact ⟨_, _, _, _, ‹_›, ‹_›, ‹_›, ‹_›, ‹_›, rfl⟩

/-- A successful LoanDelete ran on a stored loan with its broker refreshed. -/
lemma LendingLedger.applyLoan_delete_inv (l : LendingLedger) (u : LoanEffect) (i : Nat)
    (h : (l.applyLoan (.loanDelete i)).run = .ok (.ok u)) :
    ∃ e broker loan r, l.loan? i = some e ∧ l.broker? e.brokerIndex = some broker ∧
      e.loan.withBroker broker = .ok loan ∧ loan.canDelete = .tesSUCCESS ∧
      (loan.delete l.vault).run = .ok (.ok r) ∧
      u = { vault := r.pool', brokerIndex := e.brokerIndex, broker := r.broker', loanIndex := i, loan := none } := by
  simp only [LendingLedger.applyLoan] at h
  unfold_ter at h
  walk_ok
  simp only [Bool.not_eq_eq_eq_not, Bool.not_true] at *
  simp only [Bool.not_eq_false, TER.isTesSuccess_iff] at *
  exact ⟨_, _, _, _, ‹_›, ‹_›, ‹_›, ‹_›, ‹_›, rfl⟩

/-- A successful LoanManage ran on a stored loan with its broker refreshed. -/
lemma LendingLedger.applyLoan_manage_inv (l : LendingLedger) (u : LoanEffect) (i : Nat) (action : LoanManageAction)
    (h : (l.applyLoan (.loanManage i action)).run = .ok (.ok u)) :
    ∃ e broker loan r, l.loan? i = some e ∧ l.broker? e.brokerIndex = some broker ∧
      e.loan.withBroker broker = .ok loan ∧ loan.canManage action l.now = .ok .tesSUCCESS ∧
      (loan.manage action l.vault l.now).run = .ok (.ok r) ∧ u = LoanEffect.ofLoan i e r.loan' r.pool' := by
  simp only [LendingLedger.applyLoan] at h
  unfold_ter at h
  walk_ok
  simp only [Bool.not_eq_eq_eq_not, Bool.not_true] at *
  simp only [Bool.not_eq_false, TER.isTesSuccess_iff] at *
  subst_vars
  exact ⟨_, _, _, _, ‹_›, ‹_›, ‹_›, ‹_›, ‹_›, rfl⟩

/-- A successful LoanPay ran on a stored loan with its broker refreshed. -/
lemma LendingLedger.applyLoan_pay_inv (l : LendingLedger) (u : LoanEffect) (i : Nat) (paymentType : LoanPaymentType)
    (amount : Number) (h : (l.applyLoan (.loanPay i paymentType amount)).run = .ok (.ok u)) :
    ∃ e broker loan r, l.loan? i = some e ∧ l.broker? e.brokerIndex = some broker ∧
      e.loan.withBroker broker = .ok loan ∧ loan.canPay paymentType = .tesSUCCESS ∧
      (loan.pay l.vault paymentType amount l.now).run = .ok (.ok r) ∧
      u = LoanEffect.ofLoan i e r.loan' r.pool' := by
  simp only [LendingLedger.applyLoan] at h
  unfold_ter at h
  walk_ok
  simp only [Bool.not_eq_eq_eq_not, Bool.not_true] at *
  simp only [Bool.not_eq_false, TER.isTesSuccess_iff] at *
  exact ⟨_, _, _, _, ‹_›, ‹_›, ‹_›, ‹_›, ‹_›, rfl⟩

/-- A stored loan sits at an index inside the list. -/
lemma LendingLedger.loan?_lt {l : LendingLedger} {i : Nat} {e : LoanEntry} (h : l.loan? i = some e) :
    i < l.loans.length := by
  unfold LendingLedger.loan? at h
  by_contra hc
  rw [List.getElem?_eq_none (by omega)] at h
  cases h

/-- The loan slots after a loan effect: the written slot holds the effect's loan, the others are as
they were. -/
lemma LendingLedger.loan?_commitLoan (l : LendingLedger) (u : LoanEffect) (j : Nat) :
    (l.commitLoan u).loan? j =
      if j = (if u.loanIndex < l.loans.length then u.loanIndex else l.loans.length) then u.loan
      else l.loan? j := by
  unfold LendingLedger.commitLoan LendingLedger.loan? storeSlot
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
        have h1 : l.loans[j]? = none := List.getElem?_eq_none (by omega)
        have h2 : j - l.loans.length ≠ 0 := by omega
        rw [h1, List.getElem?_cons]
        simp [h2]

/-- An operation on the stored loan at `j` rewrites slot `j` and leaves the others. -/
lemma LendingLedger.loan?_commit_ofLoan (l : LendingLedger) {j : Nat} {e : LoanEntry}
    (he : l.loan? j = some e) (loan' : Loan) (v' : Vault) (k : Nat) :
    (l.commitLoan (LoanEffect.ofLoan j e loan' v')).loan? k =
      if k = j then some { e with loan := loan' } else l.loan? k := by
  rw [LendingLedger.loan?_commitLoan]
  have hj := LendingLedger.loan?_lt he
  simp only [LoanEffect.ofLoan, hj, ↓reduceIte]

/-- A management action keeps the loan terms. -/
lemma Loan.manage_keepsTerms (loan : Loan) (action : LoanManageAction) (v : Vault) (now : UInt32)
    (r : LoanWithPool Vault) (h : (loan.manage action v now).run = .ok (.ok r)) : Loan.KeepsTerms loan r.loan' := by
  cases action with
  | impair => exact Loan.manageImpair_keepsTerms loan v now r h
  | unimpair => exact Loan.manageUnimpair_keepsTerms loan v r h
  | default =>
    simp only [Loan.manage] at h
    unfold_ter at h
    walk_ok
    exact Loan.manageDefault_keepsTerms loan v _ ‹_›

/-- A payment of any type keeps the loan terms. -/
lemma Loan.pay_keepsTerms (loan : Loan) (paymentType : LoanPaymentType) (v : Vault) (amount : Number)
    (now : UInt32) (r : LoanWithAmounts Vault) (h : (loan.pay v paymentType amount now).run = .ok (.ok r)) :
    Loan.KeepsTerms loan r.loan' := by
  cases paymentType with
  | regular => exact Loan.regularPayment_keepsTerms loan v amount now r h
  | late => exact Loan.latePayment_keepsTerms loan v amount now r h
  | full => exact Loan.fullPayment_keepsTerms loan v amount now r h
  | overpayment => exact Loan.overpayment_keepsTerms loan v amount now r h

end XRPL.Model.Lending
