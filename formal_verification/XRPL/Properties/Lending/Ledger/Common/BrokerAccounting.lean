import XRPL.Properties.Lending.Ledger.Common.BrokerAccountingDefs
import XRPL.Properties.Lending.Ledger.Common.DebtInv
import XRPL.Properties.Lending.Ledger.Common.LoanCountInv
import XRPL.Properties.Lending.Ledger.Common.ShareSum
import XRPL.Properties.Lending.Ledger.Common.CoverOpenZone
import XRPL.Properties.Lending.LoanBroker.Common.CoverExact
import XRPL.Properties.Lending.Loan.Common.AcceptDeleteLedger
import XRPL.Properties.Lending.Loan.Common.ManageLedger
import XRPL.Properties.Lending.Loan.Common.PayLedgerFunds
import XRPL.Properties.Lending.Loan.Common.SetLedger

/-! # SharesTotal and one broker over a sequence of transactions

SharesTotal moves by the shares deposits issue and withdrawals, clawbacks and burns destroy. A broker's DebtTotal is
the principal of its loans, and its LoanCount the number of its loans, so both move by what the loan transactions on
the broker lend, pay, default and delete. CoverAvailable moves by the cover deposits, withdrawals, clawbacks, the fees
paid into it and the cover defaults take, exactly while the cover is not coarsened. -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault (Vault RawVault VaultWithAmounts)

open private LendingLedger.brokerPrincipal_commitLoan from XRPL.Properties.Lending.Ledger.Common.DebtInv
open private LendingLedger.loansOf_rewrite LendingLedger.loansOf_delete LendingLedger.loansOf_create
  from XRPL.Properties.Lending.Ledger.Common.LoanCountInv
open private Loan.pay_cover_sums from XRPL.Properties.Lending.Loan.Common.PayBounds

/-- A transaction reads the stored loan at `i` with its broker's current copy. -/
private lemma LendingLedger.LoanAt.read {l : LendingLedger} {i : Nat} {loan : Loan} (h : l.LoanAt i loan) :
    l.loanRead i = some loan := by
  obtain ⟨e, b, he, hb, hw⟩ := h
  simp only [LendingLedger.loanRead, he, hb, hw]

/-- A transaction other than a loan transaction keeps the loans. -/
private lemma LendingLedger.apply_loans {l l' : LendingLedger} {tx : LendingTx} (hl : ¬ tx.isLoan = true)
    (h : (l.apply tx).run = .ok (.ok l')) : l'.loans = l.loans := by
  by_cases hv : tx.isVault = true
  · obtain ⟨u, -, rfl⟩ := LendingLedger.apply_vault hv h
    unfold LendingLedger.commitVault; split <;> simp [LendingLedger.setShares]
  by_cases hb : tx.isBroker = true
  · exact (LendingLedger.broker_ops_scope_proof l l' tx hb h).1
  have hc := (LendingLedger.apply_checked h).2
  cases tx <;> simp only [LendingTx.isVault, LendingTx.isBroker, LendingTx.isLoan, Bool.false_eq_true,
    not_false_eq_true, not_true_eq_false] at hv hb hl
  · simp only [LendingLedger.applyChecked, LendingLedger.applyVaultDelete] at hc
    unfold_ter at hc
    walk_ok
    rfl
  · simp only [LendingLedger.applyChecked] at hc
    cases hc
    rfl

/-- A transaction other than a loan transaction is on no broker. -/
private lemma LendingLedger.onBroker_of_not_loan (l : LendingLedger) (j : Nat) {tx : LendingTx}
    (hl : ¬ tx.isLoan = true) : l.onBroker j tx = false := by
  cases tx <;> simp_all [LendingTx.isLoan, LendingLedger.onBroker]

/-- A transaction on the stored loan at `i` is on the broker the loan names. -/
private lemma LendingLedger.onBroker_loan (l : LendingLedger) (j : Nat) {i : Nat} {e : LoanEntry}
    (he : l.loan? i = some e) :
    l.onBroker j (.loanAccept i) = (e.brokerIndex == j) ∧ l.onBroker j (.loanDelete i) = (e.brokerIndex == j) ∧
      (∀ a, l.onBroker j (.loanManage i a) = (e.brokerIndex == j)) ∧
      ∀ pt amount, l.onBroker j (.loanPay i pt amount) = (e.brokerIndex == j) := by
  simp [LendingLedger.onBroker, he]

/-- One successful transaction moves the principal of broker `j`'s loans by what it lends on `j`, less what its
payments, defaults and pending deletes take off `j`'s loans. -/
private lemma LendingLedger.brokerPrincipal_step {l l' : LendingLedger} {tx : LendingTx} (hr : l.Reachable)
    (h : (l.apply tx).run = .ok (.ok l')) (j : Nat) :
    l'.brokerPrincipal j = l.brokerPrincipal j + l.brokerLentOf j tx - l.brokerPrincipalPaidOf j tx -
      l.brokerDefaultedOf j tx - l.brokerDeletedPendingOf j tx := by
  by_cases hl : tx.isLoan = true
  swap
  · have hloans := LendingLedger.apply_loans hl h
    have hon := l.onBroker_of_not_loan j hl
    simp only [LendingLedger.brokerLentOf, LendingLedger.brokerPrincipalPaidOf, LendingLedger.brokerDefaultedOf,
      LendingLedger.brokerDeletedPendingOf, hon, Bool.false_eq_true, ↓reduceIte]
    unfold LendingLedger.brokerPrincipal
    rw [hloans]
    ring
  cases tx with
  | loanSet i principal rates fees pi pt gp sd twoStep ao =>
    obtain ⟨broker, r, hb, hpre, -, hc, hcr, hl', -, -, -, -⟩ := LendingLedger.loanSet_ok h
    obtain ⟨hp, hpos⟩ := LendingTx.preflight_loanSet_principal l i principal rates fees pi pt gp sd twoStep ao
      (by rw [hpre]; rfl)
    have hst := Loan.canCreate_exact _ _ _ _ _ _ _ hc principal (List.mem_cons_self ..)
    obtain ⟨-, -, hPO, -, -⟩ := Loan.create_reserved broker l.vault principal rates fees _ ao twoStep r hp hpos hst
      (hr.scaleInv.brokers i broker hb) hr.reservedInv.grid hcr
    have hc' := LendingLedger.brokerPrincipal_commitLoan l (LoanEffect.ofCreate i l.loans.length r) j
    have hnone : l.loan? l.loans.length = none := by
      unfold LendingLedger.loan?; rw [List.getElem?_eq_none (le_refl _)]; rfl
    rw [← hl'] at hc'
    simp only [LoanEffect.ofCreate, hnone, LoanEntry.principalOn, add_zero] at hc'
    simp only [LendingLedger.brokerLentOf, LendingLedger.brokerPrincipalPaidOf, LendingLedger.brokerDefaultedOf,
      LendingLedger.brokerDeletedPendingOf, LendingLedger.onBroker, LendingLedger.lentOf,
      LendingLedger.principalPaidOf, LendingLedger.defaultedOf, LendingLedger.deletedPendingOf, beq_iff_eq]
    split_ifs at hc' ⊢ <;> linarith
  | loanAccept i =>
    obtain ⟨e, loan, r, he, hat, -, hok, hl', -, -, -, -⟩ := LendingLedger.loanAccept_ok h
    obtain ⟨e₀, he₀, -, hraw⟩ := hat.stored
    obtain rfl := Option.some.inj (he₀.symm.trans he)
    have hPO : r.loan'.principalOutstanding = e₀.loan.principalOutstanding := by
      rw [(Loan.accept_reserved loan l.vault r hok).2.2.1]; exact (congrArg RawLoan.principalOutstanding hraw :)
    have hc' := LendingLedger.brokerPrincipal_commitLoan l (LoanEffect.ofLoan i e₀ r.loan' r.pool') j
    rw [← hl'] at hc'
    simp only [LoanEffect.ofLoan, he₀, LoanEntry.principalOn, hPO] at hc'
    simp only [LendingLedger.brokerLentOf, LendingLedger.brokerPrincipalPaidOf, LendingLedger.brokerDefaultedOf,
      LendingLedger.brokerDeletedPendingOf, LendingLedger.lentOf, LendingLedger.principalPaidOf,
      LendingLedger.defaultedOf, LendingLedger.deletedPendingOf, ite_self]
    linarith
  | loanManage i action =>
    obtain ⟨e, loan, r, he, hat, -, hm, hl', -, -, -, -⟩ := LendingLedger.loanManage_ok h
    obtain ⟨e₀, he₀, -, hraw⟩ := hat.stored
    obtain rfl := Option.some.inj (he₀.symm.trans he)
    have hePO : loan.principalOutstanding = e₀.loan.principalOutstanding :=
      (congrArg RawLoan.principalOutstanding hraw :)
    have hc' := LendingLedger.brokerPrincipal_commitLoan l (LoanEffect.ofLoan i e₀ r.loan' r.pool') j
    rw [← hl'] at hc'
    simp only [LoanEffect.ofLoan, he₀, LoanEntry.principalOn] at hc'
    have hon := (l.onBroker_loan j he₀).2.2.1 action
    cases action with
    | impair =>
      have hPO := (Loan.manageImpair_lossStep loan l.vault l.now r hm).2.2.2
      rw [hPO, hePO] at hc'
      simp only [LendingLedger.brokerLentOf, LendingLedger.brokerPrincipalPaidOf, LendingLedger.brokerDefaultedOf,
        LendingLedger.brokerDeletedPendingOf, LendingLedger.lentOf, LendingLedger.principalPaidOf,
        LendingLedger.defaultedOf, LendingLedger.deletedPendingOf, ite_self]
      linarith
    | unimpair =>
      have hPO := (Loan.manageUnimpair_lossStep loan l.vault r hm).2.2.2
      rw [hPO, hePO] at hc'
      simp only [LendingLedger.brokerLentOf, LendingLedger.brokerPrincipalPaidOf, LendingLedger.brokerDefaultedOf,
        LendingLedger.brokerDeletedPendingOf, LendingLedger.lentOf, LendingLedger.principalPaidOf,
        LendingLedger.defaultedOf, LendingLedger.deletedPendingOf, ite_self]
      linarith
    | default =>
      obtain ⟨-, loan₂, r₂, -, hat₂, -, hdef, -, -, -, -, -⟩ := LendingLedger.loanDefault_ok h
      obtain rfl := hat.eq hat₂
      have hm' : r = r₂.toLoanWithPool := by
        simp only [Loan.manage] at hm
        unfold_ter at hm
        rw [show loan.manageDefault l.vault = .ok (.ok r₂) from hdef] at hm
        cases hm
        rfl
      subst hm'
      have hPO := (Loan.manageDefault_debtStep loan l.vault r₂ hdef).2.2
      rw [show r₂.toLoanWithPool.loan' = r₂.loan' from rfl, hPO, Number.toRat_zero] at hc'
      simp only [LendingLedger.brokerLentOf, LendingLedger.brokerPrincipalPaidOf, LendingLedger.brokerDefaultedOf,
        LendingLedger.brokerDeletedPendingOf, LendingLedger.lentOf, LendingLedger.principalPaidOf,
        LendingLedger.defaultedOf, LendingLedger.deletedPendingOf, ite_self, hon, hat.read, beq_iff_eq,
        hePO]
      split_ifs at hc' ⊢ <;> linarith
  | loanPay i pt amount =>
    obtain ⟨e, loan, r, he, hat, -, -, hok, hl', -, hat', -, -⟩ := LendingLedger.loanPay_ok h
    obtain ⟨e₀, he₀, -, hraw⟩ := hat.stored
    obtain rfl := Option.some.inj (he₀.symm.trans he)
    have hePO : loan.principalOutstanding = e₀.loan.principalOutstanding :=
      (congrArg RawLoan.principalOutstanding hraw :)
    obtain ⟨p, hp⟩ := LendingLedger.loanPay_instalments h hat
    have hpaid := (LendingLedger.payment_principal_proof l hr l' i pt amount h loan r.loan' hat hat' p hp).1
    have hc' := LendingLedger.brokerPrincipal_commitLoan l (LoanEffect.ofLoan i e₀ r.loan' r.pool') j
    rw [← hl'] at hc'
    simp only [LoanEffect.ofLoan, he₀, LoanEntry.principalOn] at hc'
    have hon := (l.onBroker_loan j he₀).2.2.2 pt amount
    simp only [LendingLedger.brokerLentOf, LendingLedger.brokerPrincipalPaidOf, LendingLedger.brokerDefaultedOf,
      LendingLedger.brokerDeletedPendingOf, LendingLedger.lentOf, LendingLedger.principalPaidOf,
      LendingLedger.defaultedOf, LendingLedger.deletedPendingOf, ite_self, hon, hat.read, hp, beq_iff_eq]
    rw [← hePO] at hc'
    split_ifs at hc' ⊢ <;> linarith
  | loanDelete i =>
    obtain ⟨e, loan, r, he, hat, hc, -, hl', -, -, -, -⟩ := LendingLedger.loanDelete_ok h
    obtain ⟨e₀, he₀, -, hraw⟩ := hat.stored
    obtain rfl := Option.some.inj (he₀.symm.trans he)
    have hePO : loan.principalOutstanding = e₀.loan.principalOutstanding :=
      (congrArg RawLoan.principalOutstanding hraw :)
    have hc' := LendingLedger.brokerPrincipal_commitLoan l
      { vault := r.pool', brokerIndex := e₀.brokerIndex, broker := r.broker', loanIndex := i, loan := none } j
    rw [← hl'] at hc'
    simp only [he₀, LoanEntry.principalOn, add_zero] at hc'
    have hon := (l.onBroker_loan j he₀).2.1
    -- an active loan that can be deleted owes nothing
    have hpaid : loan.isPending = false → loan.principalOutstanding.toRat = 0 := by
      intro hp
      have hz := (loan.valid.paid_zeroed (Loan.canDelete_active_paid loan hc hp)).2.1
      rw [show loan.principalOutstanding = loan.toRawLoan.principalOutstanding from rfl, hz, Number.toRat_zero]
    simp only [LendingLedger.brokerLentOf, LendingLedger.brokerPrincipalPaidOf, LendingLedger.brokerDefaultedOf,
      LendingLedger.brokerDeletedPendingOf, LendingLedger.lentOf, LendingLedger.principalPaidOf,
      LendingLedger.defaultedOf, LendingLedger.deletedPendingOf, ite_self, hon, hat.read, beq_iff_eq]
    rw [← hePO] at hc'
    cases hp : loan.isPending
    · have := hpaid hp
      simp only [Bool.false_eq_true, ↓reduceIte]
      split_ifs at hc' ⊢ <;> linarith
    · simp only [↓reduceIte]
      split_ifs at hc' ⊢ <;> linarith
  | _ => simp only [LendingTx.isLoan, Bool.false_eq_true] at hl

/-- Proof of the DebtTotal line: a broker present at both ends owes the principal of its loans, which moves by
what is lent on the broker, less what payments, defaults and pending deletes take off its loans. -/
private lemma LendingLedger.broker_debt_accounting {start l : LendingLedger} {txs : List LendingTx}
    (hr : start.Reachable) (hrun : LendingLedger.Reaches start txs l) (j : Nat) (b b' : LoanBroker)
    (hb : start.broker? j = some b) (hb' : l.broker? j = some b') :
    b'.debtTotal.toRat = b.debtTotal.toRat + start.brokerLent j txs - start.brokerPrincipalPaid j txs -
      start.brokerDefaulted j txs - start.brokerDeletedPending j txs := by
  have hsum := LendingLedger.Reaches.runSum_eq (F := fun l₀ => l₀.brokerPrincipal j)
    (d := fun l₀ tx => l₀.brokerLentOf j tx - l₀.brokerPrincipalPaidOf j tx - l₀.brokerDefaultedOf j tx -
      l₀.brokerDeletedPendingOf j tx) (P := fun _ _ _ => True)
    (fun l₁ tx l₂ hr₁ hok _ => by beta_reduce; rw [LendingLedger.brokerPrincipal_step hr₁ hok j]; ring) hr hrun
    (fun _ _ _ _ _ _ _ => trivial)
  beta_reduce at hsum
  rw [(hrun.reachable hr).debtInv.debt j b' hb', hr.debtInv.debt j b hb, hsum]
  simp only [LendingLedger.runSum_sub]
  unfold LendingLedger.brokerLent LendingLedger.brokerPrincipalPaid LendingLedger.brokerDefaulted
    LendingLedger.brokerDeletedPending
  ring

/-- One successful transaction moves the number of broker `j`'s loans by the LoanSet on `j` and the LoanDelete of
one of `j`'s loans. -/
private lemma LendingLedger.loansOf_step {l l' : LendingLedger} {tx : LendingTx} (h : (l.apply tx).run = .ok (.ok l'))
    (j : Nat) : (l'.loansOf j : ℚ) = l.loansOf j + l.newLoansOf j tx - l.deletedLoansOf j tx := by
  by_cases hl : tx.isLoan = true
  swap
  · have hloans := LendingLedger.apply_loans hl h
    have hon := l.onBroker_of_not_loan j hl
    simp only [LendingLedger.newLoansOf, LendingLedger.deletedLoansOf, hon, Bool.false_eq_true, ↓reduceIte]
    unfold LendingLedger.loansOf
    rw [hloans]
    ring
  -- an operation that keeps the loan's slot on the same broker keeps every count
  have hkeep : ∀ {i : Nat} {e : LoanEntry} (loan' : Loan) (v' : Vault), l.loan? i = some e →
      l' = l.commitLoan (LoanEffect.ofLoan i e loan' v') → l'.loansOf j = l.loansOf j := by
    intro i e loan' v' he hl'
    subst hl'
    exact LendingLedger.loansOf_rewrite l i e { e with loan := loan' } he rfl j
  cases tx with
  | loanSet i principal rates fees pi pt gp sd twoStep ao =>
    obtain ⟨-, r, -, -, -, -, -, hl', -, -, -, -⟩ := LendingLedger.loanSet_ok h
    have hc := LendingLedger.loansOf_create l { brokerIndex := i, loan := r.loan' } j
    rw [show (storeSlot l.loans l.loans.length (some { brokerIndex := i, loan := r.loan' })).countP
      (fun o => o.any (·.brokerIndex == j)) = l'.loansOf j by rw [hl']; rfl] at hc
    simp only [LendingLedger.newLoansOf, LendingLedger.deletedLoansOf, LendingLedger.onBroker, beq_iff_eq]
    rw [hc]
    split_ifs <;> push_cast <;> ring
  | loanAccept i =>
    obtain ⟨e, -, r, he, -, -, -, hl', -, -, -, -⟩ := LendingLedger.loanAccept_ok h
    rw [hkeep _ _ he hl']
    simp only [LendingLedger.newLoansOf, LendingLedger.deletedLoansOf, ite_self]
    ring
  | loanManage i action =>
    obtain ⟨e, -, r, he, -, -, -, hl', -, -, -, -⟩ := LendingLedger.loanManage_ok h
    rw [hkeep _ _ he hl']
    simp only [LendingLedger.newLoansOf, LendingLedger.deletedLoansOf, ite_self]
    ring
  | loanPay i pt amount =>
    obtain ⟨e, -, r, he, -, -, -, -, hl', -, -, -, -⟩ := LendingLedger.loanPay_ok h
    rw [hkeep _ _ he hl']
    simp only [LendingLedger.newLoansOf, LendingLedger.deletedLoansOf, ite_self]
    ring
  | loanDelete i =>
    obtain ⟨e, -, r, he, -, -, -, hl', -, -, -, -⟩ := LendingLedger.loanDelete_ok h
    have hc := LendingLedger.loansOf_delete l i e he j
    rw [show (storeSlot l.loans i none).countP (fun o => o.any (·.brokerIndex == j)) = l'.loansOf j by
      rw [hl']; rfl] at hc
    have hon := (l.onBroker_loan j he).2.1
    simp only [LendingLedger.newLoansOf, LendingLedger.deletedLoansOf, hon, beq_iff_eq]
    rw [← hc]
    split_ifs <;> push_cast <;> ring
  | _ => simp only [LendingTx.isLoan, Bool.false_eq_true] at hl

/-- Proof of the LoanCount line: a broker present at both ends counts its loans, which move by the new loans on
the broker and the deleted ones. -/
private lemma LendingLedger.broker_count_accounting {start l : LendingLedger} {txs : List LendingTx}
    (hr : start.Reachable) (hrun : LendingLedger.Reaches start txs l) (j : Nat) (b b' : LoanBroker)
    (hb : start.broker? j = some b) (hb' : l.broker? j = some b') :
    (b'.loanCount.toNat : ℚ) = b.loanCount.toNat + start.newLoans j txs - start.deletedLoans j txs := by
  have hsum := LendingLedger.Reaches.runSum_eq (F := fun l₀ => (l₀.loansOf j : ℚ))
    (d := fun l₀ tx => l₀.newLoansOf j tx - l₀.deletedLoansOf j tx) (P := fun _ _ _ => True)
    (fun l₁ tx l₂ _ hok _ => by beta_reduce; rw [LendingLedger.loansOf_step hok j]; ring) hr hrun
    (fun _ _ _ _ _ _ _ => trivial)
  beta_reduce at hsum
  rw [(hrun.reachable hr).loanCountInv.counted j b' hb', hr.loanCountInv.counted j b hb, hsum,
    LendingLedger.runSum_sub]
  unfold LendingLedger.newLoans LendingLedger.deletedLoans
  ring

/-- A negative `Int64` has a magnitude above zero. -/
private lemma Int64.natAbs_toUInt64_ne_zero (x : Int64) (h : x < 0) : x.toInt.natAbs.toUInt64 ≠ 0 := by
  have h1 : x.toInt < 0 := by simpa using Int64.lt_iff_toInt_lt.mp h
  have h2 : -2 ^ 63 ≤ x.toInt := Int64.le_toInt x
  intro h0
  have h3 := congrArg UInt64.toNat h0
  rw [Nat.toUInt64, UInt64.toNat_ofNat] at h3
  simp at h3
  omega

/-- An MPT amount of zero converted from a `Number` of at least zero is not marked negative. -/
private lemma STAmount.ofNumber_int64_zero_sign (n : Number) (hn : n.isNormalized) (h0 : 0 ≤ n.toRat) (s : STAmount)
    (hok : STAmount.ofNumber .int64 n .to_nearest = .ok s) (hm : s.mValue = 0) : s.mIsNegative = false := by
  have hnegf : n.negative_ = false := Number.negative_false_of_nonneg n hn h0
  have hsig : decide (n.signum < 0) = false := by
    unfold Number.signum
    rw [hnegf]
    simp only [Bool.false_eq_true, if_false]
    by_cases hm : (n.mantissa_ != 0) = true
    · rw [if_pos hm]; decide
    · rw [if_neg hm]; decide
  unfold STAmount.ofNumber at hok
  rw [hsig] at hok
  simp only [Bool.false_eq_true, if_false, show NumericType.int64.isIntegral = true from rfl, if_true] at hok
  split at hok
  · cases hok
  obtain ⟨vpeel, hvpeel, hok⟩ := bind_ok_peel _ _ _ hok
  obtain ⟨-, rfl⟩ := Int64.toUInt64Checked_eq_ok.mp hvpeel
  unfold STAmount.checked STAmount.canonicalize at hok
  rw [if_pos (show (STAmount.unchecked .int64 _ 0 false).integral = true from rfl)] at hok
  split at hok
  · cases hok; rfl
  split at hok
  · cases hok
  dsimp only at hok
  split at hok
  · cases hok
  rename_i i _
  split at hok
  · cases hok
  cases hok
  simp only at hm ⊢
  by_contra hne
  exact Int64.natAbs_toUInt64_ne_zero i.value (by simpa using hne) hm

/-- The holder's shares as an amount of shares: a canonical MPT amount of at least zero. -/
private lemma LendingLedger.holderShares_balance (l : LendingLedger) (hr : l.Reachable) (h : Nat) (hs : STAmount)
    (hof : STAmount.ofNumber .int64 (l.sharesOf h) .to_nearest = .ok hs) :
    hs.ShareBalance ∧ hs.IntegralCanonical ∧ 0 ≤ hs.toRat := by
  obtain ⟨hn, h0⟩ := hr.sharesNonneg.sharesOf h
  obtain ⟨hic, hty⟩ := STAmount.ofNumber_integral_canonical _ _ _ _ (by decide) hof
  have h0' := STAmount.ofNumber_nonneg _ _ _ _ hn (Number.negative_false_of_nonneg _ hn h0) hof
  have hneg : hs.mIsNegative = false := by
    by_cases hm : hs.mValue = 0
    · exact STAmount.ofNumber_int64_zero_sign _ hn h0 _ hof hm
    · exact STAmount.mIsNegative_false_of_nonneg hs h0' hm
  exact ⟨⟨hty, hic.canonical (by rw [hty]; decide), hneg⟩, hic, h0'⟩

/-- One successful transaction moves SharesTotal by the shares it issues less the shares it destroys, when a
deposit keeps SharesTotal within the share MPT maximum. -/
private lemma LendingLedger.sharesTotal_step {l l' : LendingLedger} {tx : LendingTx} (hr : l.Reachable)
    (hok : (l.apply tx).run = .ok (.ok l')) (hfit : l.vault.sharesTotal.toRat + l.sharesCreatedOf tx ≤ 2 ^ 63 - 1) :
    l'.vault.sharesTotal.toRat = l.vault.sharesTotal.toRat + l.sharesCreatedOf tx - l.sharesRemovedOf tx := by
  by_cases hv : tx.isVault = true
  · have hpre := (TER.isTesSuccess_iff _).mp (LendingLedger.apply_checked hok).1
    obtain ⟨u, hu, rfl⟩ := LendingLedger.apply_vault hv hok
    have hvault : (l.commitVault u).vault = u.vault := by
      unfold LendingLedger.commitVault; split <;> simp [LendingLedger.setShares]
    rw [hvault]
    have hcast := RawVault.WF.toExact_sharesTotal _ l.vault.wf
    cases tx with
    | vaultDeposit h amount isDonation =>
      obtain ⟨hc, hty⟩ := LendingTx.preflight_vaultDeposit_canonical l hr.holdsAsset h amount isDonation hpre
      simp only [LendingLedger.applyVault] at hu
      split at hu
      · rename_i hpos
        unfold_ter at hu
        walk_ok
        have hdep : (l.vault.deposit amount isDonation l.now hpos).run = .ok (.ok _) := ‹_›
        simp only [LendingLedger.sharesCreatedOf, LendingLedger.sharesRemovedOf, dif_pos hpos, hdep] at hfit ⊢
        have hST := Vault.deposit_exact_sharesTotal _ _ _ _ hpos hc hty _ hdep (by rw [hcast]; exact hfit)
        rw [RawVault.WF.toExact_sharesTotal _ (VaultWithAmounts.vault' _).wf, hcast] at hST
        rw [hST]; ring
      · cases hu
    | vaultWithdraw h amount =>
      obtain ⟨hc, hty⟩ := LendingTx.preflight_vaultWithdraw_canonical l hr.holdsAsset h amount hpre
      simp only [LendingLedger.applyVault] at hu
      split at hu
      · rename_i hpos
        unfold_ter at hu
        walk_ok
        have hwh : (l.vault.withdraw amount _ l.now hpos (some _)).run = .ok (.ok _) := ‹_›
        have hST := Vault.withdraw_sharesTotal _ _ _ _ hpos hc hty _ (Vault.withdraw_holder_ok _ _ _ _ _ _ _ hwh).1
        simp only [LendingLedger.sharesCreatedOf, LendingLedger.sharesRemovedOf, dif_pos hpos, hwh]
        rw [hST]; ring
      · cases hu
    | vaultClawback h assets =>
      have hc := LendingTx.preflight_vaultClawback_canonical l hr.holdsAsset h assets hpre
      simp only [LendingLedger.applyVault] at hu
      split at hu
      · rename_i hnn
        unfold_ter at hu
        walk_ok
        have hof : STAmount.ofNumber .int64 (l.sharesOf h) .to_nearest = .ok _ := ‹_›
        have hcl : (l.vault.clawback assets _ (l.isSoleShareholder h) hnn).run = .ok (.ok _) := ‹_›
        obtain ⟨hhs, -, -⟩ := l.holderShares_balance hr h _ hof
        have hST := Vault.clawback_exact_sharesTotal _ _ _ _ hnn hc hhs hr.holdsAsset.maxValue_le _ hcl
        rw [RawVault.WF.toExact_sharesTotal _ (VaultWithAmounts.vault' _).wf, hcast] at hST
        simp only [LendingLedger.sharesCreatedOf, LendingLedger.sharesRemovedOf, dif_pos hnn, hof, hcl]
        rw [hST]; ring
      · cases hu
    | vaultBurnShares h amount =>
      simp only [LendingLedger.applyVault] at hu
      unfold_ter at hu
      walk_ok
      have hof : STAmount.ofNumber .int64 (l.sharesOf h) .to_nearest = .ok _ := ‹_›
      have hb : (l.vault.burnShares _).run = .ok (.ok _) := ‹_›
      obtain ⟨hhs, hic, hs0⟩ := l.holderShares_balance hr h _ hof
      obtain ⟨-, n, st', hnum, hsub, hv'⟩ := Vault.burnShares_ok_reduces _ _ _ hb
      obtain ⟨hnv, hnn⟩ := STAmount.CanonicalOrZero.toNumber_exact (Or.inl hhs.canonical) n hnum
      have habs := abs_le.mp (hic.abs_le_int64 hhs.int64)
      have hS0 := l.vault.wf.sharesTotal_nonneg
      have hSle := l.vault.sharesTotal_le_maxRep
      have hnd : n.toRat.den = 1 := by rw [hnv]; exact hic.den_eq_one _
      obtain ⟨hst, -⟩ := operator_sub_exact_int _ _ _ l.vault.wf.sharesTotal_norm hnn l.vault.wf.sharesTotal_int hnd
        (Rat.num_natAbs_lt (Rat.den_one_sub _ _ l.vault.wf.sharesTotal_int hnd) (by rw [hnv]; linarith)
          (by rw [hnv]; linarith)) hsub
      simp only [LendingLedger.sharesCreatedOf, LendingLedger.sharesRemovedOf, hof]
      rw [show (_ : Vault).sharesTotal = st' from congrArg RawVault.sharesTotal hv', hst, hnv]
      ring
    | vaultSet assetsMaximum blockDeposit unblockDeposit =>
      simp only [LendingLedger.applyVault] at hu
      unfold_ter at hu
      walk_ok
      have hupd : l.vault.update assetsMaximum blockDeposit unblockDeposit = .ok _ := ‹_›
      unfold Vault.update at hupd
      have hraw := congrArg RawVault.sharesTotal (RawVault.to_lawful_ok hupd).1
      simp only [LendingLedger.sharesCreatedOf, LendingLedger.sharesRemovedOf]
      rw [show (_ : Vault).sharesTotal = l.vault.sharesTotal from hraw]
      ring
    | _ => simp only [LendingTx.isVault, Bool.false_eq_true] at hv
  have h0 : l.sharesCreatedOf tx = 0 ∧ l.sharesRemovedOf tx = 0 := by
    cases tx <;> simp_all [LendingTx.isVault, LendingLedger.sharesCreatedOf, LendingLedger.sharesRemovedOf]
  rw [h0.1, h0.2, add_zero, sub_zero]
  by_cases hb : tx.isBroker = true
  · rw [(LendingLedger.broker_ops_scope_proof l l' tx hb hok).2.2.1]
  by_cases hlo : tx.isLoan = true
  · rw [(LendingLedger.loan_ops_scope_proof l l' tx hlo hok).2.2.2.1]
  have hc := (LendingLedger.apply_checked hok).2
  cases tx <;> simp only [LendingTx.isVault, LendingTx.isBroker, LendingTx.isLoan, Bool.false_eq_true,
    not_false_eq_true, not_true_eq_false] at hv hb hlo
  · simp only [LendingLedger.applyChecked, LendingLedger.applyVaultDelete] at hc
    unfold_ter at hc
    walk_ok
    rfl
  · simp only [LendingLedger.applyChecked] at hc
    cases hc
    rfl

/-- Over any sequence of transactions from a reachable ledger, where every deposit keeps SharesTotal within the
share MPT maximum -> SharesTotal' = SharesTotal + Σ sharesCreated − Σ sharesRedeemed − Σ sharesDestroyed. -/
lemma LendingLedger.shares_accounting_proof {start l : LendingLedger} {txs : List LendingTx} (hr : start.Reachable)
    (hrun : LendingLedger.Reaches start txs l) :
    start.SharesFitAlong txs →
      l.vault.sharesTotal.toRat = start.vault.sharesTotal.toRat + start.sharesCreated txs - start.sharesRedeemed txs -
        start.sharesDestroyed txs := by
  intro hfit
  have hsum := LendingLedger.Reaches.runSum_eq (F := fun l₀ => l₀.vault.sharesTotal.toRat)
    (d := fun l₀ tx => l₀.sharesCreatedOf tx - l₀.sharesRemovedOf tx)
    (P := fun l₀ tx _ => l₀.vault.sharesTotal.toRat + l₀.sharesCreatedOf tx ≤ 2 ^ 63 - 1)
    (fun l₁ tx l₂ hr₁ hok hP => by beta_reduce; rw [LendingLedger.sharesTotal_step hr₁ hok hP]; ring) hr hrun
    (fun pre l₁ tx _ hp hr' _ => hfit pre l₁ tx hp hr')
  beta_reduce at hsum
  have hsplit : start.runSum LendingLedger.sharesRemovedOf txs =
      start.sharesRedeemed txs + start.sharesDestroyed txs := by
    unfold LendingLedger.sharesRedeemed LendingLedger.sharesDestroyed
    rw [← LendingLedger.runSum_add]
    congr 1
    funext l₀ tx
    exact LendingLedger.sharesRemovedOf_eq l₀ tx
  rw [hsum, LendingLedger.runSum_sub, hsplit]
  unfold LendingLedger.sharesCreated
  ring

/-- A cover deposit or withdrawal that passed its preflight moves a canonical amount above zero. -/
private lemma LendingTx.preflight_coverAmount (l : LendingLedger) (hasset : Vault.HoldsAsset l.vault)
    (amount : STAmount) (h : (isCanonicalAmount amount l.vault.numericType && isPositiveAmount amount) = true) :
    amount.Canonical ∧ 0 < amount.toRat := by
  rw [Bool.and_eq_true] at h
  have hpos := h.2
  simp only [isPositiveAmount, Bool.and_eq_true, Bool.not_eq_true', bne_iff_ne, ne_eq] at hpos
  exact ⟨(isCanonicalAmount_canonical amount _ hasset.maxValue_le h.1 hpos.2).1,
    lt_of_le_of_ne (STAmount.toRat_nonneg_of amount hpos.1) (Ne.symm (STAmount.toRat_ne_zero amount hpos.2))⟩

/-- A cover deposit adds its rounded amount to CoverAvailable, exactly while the sum stays below `2^63` base
units. -/
private lemma LoanBroker.coverDeposit_cover (lb : LoanBroker) (v : Vault) (amount : STAmount)
    (res : LoanBrokerCoverResult) (hc : Number.OnGrid v.baseExponent lb.coverAvailable)
    (hint : lb.numericType.isIntegral = true → v.baseExponent = 0) (ha : amount.Canonical) (hpos : 0 < amount.toRat)
    (hok : (lb.coverDeposit v amount).run = .ok (.ok res))
    (hlt : lb.coverAvailable.toRat + res.amount'.toRat < 2 ^ 63 * 10 ^ v.baseExponent) :
    res.loanBroker'.coverAvailable.toRat = lb.coverAvailable.toRat + res.amount'.toRat := by
  obtain ⟨hb, hs⟩ := Vault.baseExponent_grid v
  have hp : (0 : ℚ) < 10 ^ v.baseExponent := zpow_pos (by norm_num) _
  obtain ⟨r, hr, happ⟩ := LoanBroker.coverDeposit_ok_inv lb v amount res hok
  obtain ⟨m, c', hm, hadd, hamt, hraw⟩ := LoanBroker.applyCoverTransaction_credit_inv lb r res happ
  obtain ⟨aN, -, hsr, hrpos⟩ := LoanBroker.roundedCoverAmount_ok lb v amount r hr
  obtain ⟨-, hrnum⟩ := LoanBroker.roundedCoverAmount_le lb v amount r ha hpos.le v.baseExponent_range hr
  obtain ⟨hmv, hmn⟩ := hrnum m hm
  obtain ⟨-, k, hk⟩ := sumRoundAndSubtract_onGrid _ _ _ _ _ r m hc ⟨hb, v.baseExponent_bounds.2.1⟩ hint hsr hm
  obtain ⟨hcn, a, ha'⟩ := hc
  have hr0 := (STAmount.signum_pos_iff_toRat_pos r).mp hrpos
  rw [hamt] at hlt ⊢
  have ha0 : 0 ≤ a := by
    have : (0 : ℚ) ≤ (a : ℚ) * 10 ^ v.baseExponent := ha' ▸ lb.exact.coverAvailable_nonneg
    exact_mod_cast nonneg_of_mul_nonneg_left this hp
  have hk0 : 0 ≤ k := by
    have : (0 : ℚ) ≤ (k : ℚ) * 10 ^ v.baseExponent := by rw [← hk, hmv]; exact hr0.le
    exact_mod_cast nonneg_of_mul_nonneg_left this hp
  have hlt' : a + k < 2 ^ 63 := by
    have : ((a + k : ℤ) : ℚ) * 10 ^ v.baseExponent < (2 ^ 63 : ℚ) * 10 ^ v.baseExponent := by
      push_cast; rw [add_mul, ← ha', ← hk, hmv]; exact hlt
    exact_mod_cast lt_of_mul_lt_mul_right this hp.le
  have hv := Number.operator_add_toRat_of_grid _ _ _ a k _ hcn hmn ha' hk ⟨by omega, hlt'⟩ hs hadd
  rw [show res.loanBroker'.coverAvailable = c' from congrArg RawLoanBroker.coverAvailable hraw, hv, ha', ← hmv, hk]
  push_cast; ring

/-- A cover withdrawal takes its clamped amount off CoverAvailable, exactly while the cover is below `2^63` base
units. -/
private lemma LoanBroker.coverWithdraw_cover (lb : LoanBroker) (v : Vault) (amount : STAmount)
    (res : LoanBrokerCoverResult) (hc : Number.OnGrid v.baseExponent lb.coverAvailable) (ha : amount.Canonical)
    (hpos : 0 < amount.toRat) (hcan : lb.canCoverWithdraw v amount = .ok .tesSUCCESS)
    (hok : (lb.coverWithdraw v amount).run = .ok (.ok res))
    (hlt : lb.coverAvailable.toRat < 2 ^ 63 * 10 ^ v.baseExponent) :
    res.loanBroker'.coverAvailable.toRat = lb.coverAvailable.toRat - res.amount'.toRat := by
  obtain ⟨a, hcl, happ⟩ := LoanBroker.coverWithdraw_ok_inv lb v amount res hok
  obtain ⟨a2, aN, c2, hcl2, -, hnum, hge, -, -⟩ := LoanBroker.canCoverWithdraw_ok lb v amount hcan
  rw [hcl, Except.ok.injEq] at hcl2
  subst hcl2
  obtain ⟨m, c', hm, hsub, hamt, hraw⟩ := LoanBroker.applyCoverTransaction_debit_inv lb a res happ
  rw [hnum, Except.ok.injEq] at hm
  subst hm
  obtain ⟨hac, ha0, -, -⟩ := clampToSumExponent_debit_facts lb.coverAvailable amount a _ (Or.inl ha) hpos.le
    v.baseExponent_range (fun _ => v.baseExponent_bounds.2.1) hcl
  obtain ⟨hav, -⟩ := STAmount.CanonicalOrZero.toNumber_exact hac aN hnum
  have hng := Vault.clamp_onGrid v _ _ _ (STAmount.CanonicalOrZero.operator_neg (Or.inl ha)) hcl aN hnum
  have hle : aN.toRat ≤ lb.coverAvailable.toRat :=
    (operator_lt_eq_false_iff _ _ lb.wf.coverAvailable_norm hng.1).mp hge
  have hv := Number.OnGrid.sub_exact hc hng (by rw [hav]; exact ha0) hle hlt (Vault.baseExponent_grid v).2 hsub
  rw [hamt, show res.loanBroker'.coverAvailable = c' from congrArg RawLoanBroker.coverAvailable hraw, hv, hav]

/-- A cover clawback takes its amount off CoverAvailable, exactly while the cover is below `2^63` base units. -/
private lemma LoanBroker.coverClawback_cover (lb : LoanBroker) (v : Vault) (amount : Option STAmount)
    (res : LoanBrokerCoverResult) (hc : Number.OnGrid v.baseExponent lb.coverAvailable)
    (hmax : lb.numericType.isIntegral = true → lb.numericType.maxValue.toNat ≤ maxRep.toNat)
    (hok : (lb.coverClawback v amount).run = .ok (.ok res))
    (hlt : lb.coverAvailable.toRat < 2 ^ 63 * 10 ^ v.baseExponent) :
    res.loanBroker'.coverAvailable.toRat = lb.coverAvailable.toRat - res.amount'.toRat := by
  obtain ⟨c, hcr, happ⟩ := LoanBroker.coverClawback_ok_inv lb v amount res hok
  obtain ⟨_, _, claw, claw', _, _, _, _, hof, hcl, -⟩ := LoanBroker.roundedCoverClawback_ok lb v amount c hcr
  obtain ⟨m, c', hm, hsub, hamt, hraw⟩ := LoanBroker.applyCoverTransaction_debit_inv lb c res happ
  have hcv : res.loanBroker'.coverAvailable = c' := congrArg RawLoanBroker.coverAvailable hraw
  rw [hamt]
  have hneg := (STAmount.ofNumber_canonicalOrZero _ _ _ claw' hmax hof).1.operator_neg
  obtain ⟨hcc, -, hc0⟩ := clampToSumExponent_canonicalOrZero lb.coverAvailable _ c _ hneg
    v.baseExponent_range.1 v.baseExponent_range.2 hcl
  obtain ⟨hmv, -⟩ := STAmount.CanonicalOrZero.toNumber_exact hcc m hm
  have hng := Vault.clamp_onGrid v _ _ _ hneg hcl m hm
  -- the clawback leaves a lawful cover, so on the grid it cannot take more than the cover
  have hc'0 : 0 ≤ c'.toRat := by rw [← hcv]; exact res.loanBroker'.exact.coverAvailable_nonneg
  have hle : m.toRat ≤ lb.coverAvailable.toRat := by
    by_contra hgt
    push Not at hgt
    obtain ⟨-, jc, hjc⟩ := hc
    obtain ⟨hmn, jm, hjm⟩ := hng
    have hp : (0 : ℚ) < 10 ^ v.baseExponent := zpow_pos (by norm_num) _
    have hj : jc < jm := by
      have : (jc : ℚ) * 10 ^ v.baseExponent < (jm : ℚ) * 10 ^ v.baseExponent := hjc ▸ hjm ▸ hgt
      exact_mod_cast lt_of_mul_lt_mul_right this hp.le
    obtain ⟨w, hw, hwv⟩ := Number.exists_normalized_int_mul_pow (-1) v.baseExponent (by constructor <;> norm_num)
      (Vault.baseExponent_grid v).2
    have hR := operator_sub_rounded_to_nearest _ _ _ lb.wf.coverAvailable_norm hmn hsub
    have hwle : lb.coverAvailable.toRat - m.toRat ≤ w.toRat := by
      rw [hwv, hjc, hjm]
      have : ((jc - jm : ℤ) : ℚ) ≤ -1 := by exact_mod_cast (by omega : jc - jm ≤ -1)
      push_cast at this ⊢; nlinarith
    have := Number.RoundsToRepresentable.le_of_ge hR (Or.inl rfl) w hw hwle
    rw [hwv] at this
    push_cast at this
    linarith
  have hexact := Number.OnGrid.sub_exact hc hng (by rw [hmv]; exact hc0) hle hlt (Vault.baseExponent_grid v).2 hsub
  rw [hcv, hexact, hmv]

/-- A successful payment found the broker's cover at its minimum or below it. -/
private lemma Loan.pay_minimumCover (loan : Loan) (v : Vault) (pt : LoanPaymentType) (amount : Number) (now : UInt32)
    (r : LoanWithAmounts Vault) (hok : (loan.pay v pt amount now).run = .ok (.ok r)) :
    loan.broker.hasMinimumCover v.baseExponent = .ok true ∨ loan.broker.hasMinimumCover v.baseExponent = .ok false := by
  obtain ⟨p, hp, hs⟩ := Loan.pay_ok loan v pt amount now r hok
  obtain ⟨-, hu, hst, -, -⟩ := Loan.payInstalments_ok loan v pt amount now p hp
  obtain ⟨_, _, _, _, _, _, _, hsums, -⟩ := UnsettledPayment.settle_ok p r hs
  have hbe := Loan.unimpairIfImpaired_baseExponent loan v p.pool _ hu
  have hb : p.loan.broker = loan.broker := hst.broker
  rcases hsums.fee with ⟨h1, -⟩ | ⟨h1, -⟩
  · rw [hb, hbe] at h1; exact Or.inl h1
  · rw [hb, hbe] at h1; exact Or.inr h1

/-- A payment below the minimum cover adds its whole fee to CoverAvailable while the cover plus the fee stays below
`10^16` base units. -/
private lemma LendingLedger.pay_fee_cover {l : LendingLedger} (hr : l.Reachable) {i : Nat} {loan : Loan}
    (hat : l.LoanAt i loan) {pt : LoanPaymentType} {amount : Number} {r : LoanWithAmounts Vault}
    (hok : (loan.pay l.vault pt amount l.now).run = .ok (.ok r)) {p : UnsettledPayment Vault}
    (hp : (loan.payInstalments l.vault pt amount l.now).run = .ok (.ok p))
    (hcover : loan.broker.hasMinimumCover l.vault.baseExponent = .ok false)
    (hlt : loan.broker.coverAvailable.toRat + p.amounts.feePaid.toRat < 10 ^ 16 * 10 ^ l.vault.baseExponent) :
    r.loan'.broker.coverAvailable.toRat = loan.broker.coverAvailable.toRat + p.amounts.feePaid.toRat := by
  obtain ⟨p', fc, tb, hp', hfc, htb, -, hcov⟩ := Loan.pay_cover_sums loan l.vault amount l.now pt r hcover hok
  rw [show p' = p from Except.ok.inj (Except.ok.inj (hp'.symm.trans hp))] at hfc
  obtain ⟨hblo, hbhi, hbint⟩ := l.vault.baseExponent_bounds
  have hs := (Vault.baseExponent_grid l.vault).2
  have hpw : (0 : ℚ) < 10 ^ l.vault.baseExponent := zpow_pos (by norm_num) _
  obtain ⟨e, he, hbk, -⟩ := hat.stored
  obtain ⟨hcn, a, ha⟩ := hr.cover_onGrid hbk
  have hfee0 := (Loan.pay_parts_nonneg loan amount pt r l.vault l.now p hp hok).2.2
  obtain ⟨t, -, hreach⟩ := hr.loanAt_reachable hat
  obtain ⟨gs, gl, -⟩ := Loan.Reachable.fees_onGrid hreach
  have gfee := Loan.payInstalments_fee_onGrid loan l.vault pt amount l.now p (hr.loanScale_range hat) gs gl hp
  rw [(hr.loanAt_scale hat).1] at gfee
  obtain ⟨hfn, f, hf⟩ := gfee
  have hnt := (hr.loanAt_scale hat).2
  have ha0 : 0 ≤ a := by
    have : (0 : ℚ) ≤ (a : ℚ) * 10 ^ l.vault.baseExponent := ha ▸ loan.broker.exact.coverAvailable_nonneg
    exact_mod_cast nonneg_of_mul_nonneg_left this hpw
  have hf0 : 0 ≤ f := by
    have : (0 : ℚ) ≤ (f : ℚ) * 10 ^ l.vault.baseExponent := hf ▸ hfee0
    exact_mod_cast nonneg_of_mul_nonneg_left this hpw
  have haf : a + f < 10 ^ 16 := by
    have : ((a + f : ℤ) : ℚ) * 10 ^ l.vault.baseExponent < ((10 ^ 16 : ℤ) : ℚ) * 10 ^ l.vault.baseExponent := by
      push_cast; rw [add_mul, ← ha, ← hf]; exact hlt
    exact_mod_cast lt_of_mul_lt_mul_right this hpw.le
  -- the fee joins the cover whole: it is whole base units and the sum stays at the base exponent
  obtain ⟨-, htbv⟩ := sumRoundAndSubtract_downward_le _ _ _ _ fc loan.broker.wf.coverAvailable_norm
    loan.broker.exact.coverAvailable_nonneg hfn hfee0 (Vault.baseExponent_range l.vault) hfc
  have hfcv : fc.toRat = p.amounts.feePaid.toRat := by
    cases hint : loan.broker.numericType.isIntegral
    · have hfr := NumericType.eq_fractional_of_not_integral hint
      rw [hfr] at hfc
      have hroom : loan.broker.coverAvailable.toRat + p.amounts.feePaid.toRat ≤
          (10 : ℚ) ^ (16 + l.vault.baseExponent) - 10 ^ l.vault.baseExponent := by
        rw [zpow_add₀ (by norm_num), ha, hf]
        have : ((a + f : ℤ) : ℚ) ≤ 10 ^ 16 - 1 := by exact_mod_cast (by omega : a + f ≤ 10 ^ 16 - 1)
        push_cast at this
        norm_num
        nlinarith
      rw [sumRoundAndSubtract_at_base _ _ _ fc a.toNat loan.broker.wf.coverAvailable_norm
        (by rw [ha, show ((a.toNat : ℕ) : ℚ) = (a : ℚ) by exact_mod_cast Int.toNat_of_nonneg ha0])
        hfn hfee0 ⟨by omega, hbhi⟩ hroom hfc, floor_units_self _ _ f hf]
    · unfold sumRoundAndSubtract at hfc
      rw [if_pos hint] at hfc
      obtain ⟨x, hofn, hx⟩ := bind_ok_peel _ _ _ hfc
      simp only [pure, Except.pure, Except.ok.injEq] at hx
      subst hx
      refine STAmount.ofNumber_integral_exact _ _ _ _ hint hfn ?_ hofn
      have hb0 : l.vault.baseExponent = 0 := hbint (by rw [← hnt]; exact hint)
      rw [hf, hb0, zpow_zero, mul_one]
      exact Rat.den_intCast f
  obtain ⟨htbq, htbn⟩ := htbv tb htb
  rw [hfcv] at htbq
  have hv := Number.operator_add_toRat_of_grid _ _ _ a f _ hcn htbn ha (by rw [htbq, hf])
    ⟨by omega, lt_trans haf (by norm_num)⟩ hs hcov
  rw [hv, ha, hf]
  push_cast; ring

/-- A default takes its cover off CoverAvailable exactly while what it leaves stays below `10^16` base units. -/
private lemma LendingLedger.default_cover {l : LendingLedger} (hr : l.Reachable) {i : Nat} {loan : Loan}
    (hat : l.LoanAt i loan) {r : LoanWithAmounts Vault} (hdef : (loan.manageDefault l.vault).run = .ok (.ok r))
    (hlt : loan.broker.coverAvailable.toRat - r.amountToPool.toRat < 10 ^ 16 * 10 ^ l.vault.baseExponent) :
    r.loan'.broker.coverAvailable.toRat = loan.broker.coverAvailable.toRat - r.amountToPool.toRat := by
  obtain ⟨hblo, hbhi, hbint⟩ := l.vault.baseExponent_bounds
  have hs := (Vault.baseExponent_grid l.vault).2
  have hpw : (0 : ℚ) < 10 ^ l.vault.baseExponent := zpow_pos (by norm_num) _
  obtain ⟨e, he, hbk, -⟩ := hat.stored
  obtain ⟨-, a, ha⟩ := hr.cover_onGrid hbk
  obtain ⟨_, _, _, _, _, -, hdc, -⟩ := Loan.manageDefault_ok_parts loan l.vault r hdef
  -- the cover is floored onto the grid of AssetsAvailable, which is whole base units
  have hdcg : Number.OnGrid l.vault.baseExponent r.amountToPool := by
    have hdc' := hdc
    unfold Loan.defaultCover at hdc'
    obtain ⟨_, -, hdc'⟩ := bind_ok_peel _ _ _ hdc'
    obtain ⟨_, -, hdc'⟩ := bind_ok_peel _ _ _ hdc'
    obtain ⟨_, -, hdc'⟩ := bind_ok_peel _ _ _ hdc'
    obtain ⟨st, hst, hdc'⟩ := bind_ok_peel _ _ _ hdc'
    exact sumRoundAndSubtract_onGrid _ _ _ _ _ st _ (hr.assetsAvailable_onGrid hr.holdsAsset.maxValue_le)
      ⟨hblo, hbhi⟩ (fun hi => hbint (by rw [← (hr.loanAt_scale hat).2]; exact hi)) hst hdc'
  obtain ⟨-, d, hd⟩ := hdcg
  obtain ⟨mc, liq, hmin, hliq⟩ := Loan.manageDefault_cover_steps loan l.vault r hdef
  have hle := (Loan.defaultCover_le loan l.vault _ _ _ hdc hmin hliq).trans (min_le_right _ _)
  have had : 0 ≤ a - d := by
    have : (d : ℚ) * 10 ^ l.vault.baseExponent ≤ (a : ℚ) * 10 ^ l.vault.baseExponent := by rw [← hd, ← ha]; exact hle
    have := le_of_mul_le_mul_right this hpw
    have : d ≤ a := by exact_mod_cast this
    omega
  have had' : a - d < 2 ^ 63 := by
    have : ((a - d : ℤ) : ℚ) * 10 ^ l.vault.baseExponent < ((10 ^ 16 : ℤ) : ℚ) * 10 ^ l.vault.baseExponent := by
      push_cast; rw [sub_mul, ← ha, ← hd]; exact hlt
    have : a - d < 10 ^ 16 := by exact_mod_cast lt_of_mul_lt_mul_right this hpw.le
    exact lt_trans this (by norm_num)
  obtain ⟨w, hw, hwv⟩ := Number.exists_normalized_int_mul_pow (a - d) l.vault.baseExponent ⟨by omega, had'⟩ hs
  exact Loan.manageDefault_coverAvailable_proof loan l.vault r hdef ⟨w, hw, by rw [hwv, ha, hd]; push_cast; ring⟩

/-- A LoanDelete keeps the broker's cover. -/
private lemma Loan.delete_cover (loan : Loan) (v : Vault) (r : LoanBrokerWithPool Vault)
    (h : (loan.delete v).run = .ok (.ok r)) : r.broker'.coverAvailable = loan.broker.coverAvailable := by
  by_cases hp : loan.isPending = true
  · obtain ⟨_, _, _, -, -, -, -, hrel⟩ := Loan.delete_pending_ok_inv loan v r hp h
    exact LoanBroker.releaseLoan_cover _ _ _ hrel
  · simp only [Loan.delete, Bool.not_eq_true] at h hp
    rw [hp] at h
    unfold_ter at h
    walk_ok
    exact LoanBroker.releaseLoan_cover _ _ _ ‹Loan.deleteActive _ = Except.ok _›

/-- A transaction that is not a vault, broker or loan transaction is a VaultDelete, which only marks the vault
deleted, or a close, which only moves the close time. -/
private lemma LendingLedger.apply_other {l l' : LendingLedger} {tx : LendingTx} (hv : ¬ tx.isVault = true)
    (hb : ¬ tx.isBroker = true) (hl : ¬ tx.isLoan = true) (hok : (l.apply tx).run = .ok (.ok l')) :
    l'.vault = l.vault ∧ l'.brokers = l.brokers ∧ l'.loans = l.loans := by
  have hc := (LendingLedger.apply_checked hok).2
  cases tx <;> simp only [LendingTx.isVault, LendingTx.isBroker, LendingTx.isLoan, Bool.false_eq_true,
    not_false_eq_true, not_true_eq_false] at hv hb hl
  · simp only [LendingLedger.applyChecked, LendingLedger.applyVaultDelete] at hc
    unfold_ter at hc
    walk_ok
    exact ⟨rfl, rfl, rfl⟩
  · simp only [LendingLedger.applyChecked] at hc
    cases hc
    exact ⟨rfl, rfl, rfl⟩

/-- A transaction that is not a broker or loan transaction keeps the brokers. -/
private lemma LendingLedger.apply_brokers {l l' : LendingLedger} {tx : LendingTx} (hb : ¬ tx.isBroker = true)
    (hl : ¬ tx.isLoan = true) (hok : (l.apply tx).run = .ok (.ok l')) : l'.brokers = l.brokers := by
  by_cases hv : tx.isVault = true
  · obtain ⟨u, -, rfl⟩ := LendingLedger.apply_vault hv hok
    unfold LendingLedger.commitVault; split <;> simp [LendingLedger.setShares]
  · exact (LendingLedger.apply_other hv hb hl hok).2.1

/-- A loan transaction writes the broker of a stored broker slot. -/
private lemma LendingLedger.applyLoan_broker (l : LendingLedger) (tx : LendingTx) (u : LoanEffect)
    (hu : (l.applyLoan tx).run = .ok (.ok u)) : ∃ b, l.broker? u.brokerIndex = some b := by
  cases tx with
  | loanSet i principal rates fees pi pt gp sd twoStep ao =>
    simp only [LendingLedger.applyLoan] at hu
    obtain ⟨broker, r, hb, -, -, rfl⟩ := l.applyLoanSet_inv _ _ _ _ _ _ _ _ hu
    exact ⟨broker, hb⟩
  | loanAccept i =>
    obtain ⟨e, broker, -, -, -, hb, -, -, -, rfl⟩ := l.applyLoan_accept_inv u i hu
    exact ⟨broker, hb⟩
  | loanManage i action =>
    obtain ⟨e, broker, -, -, -, hb, -, -, -, rfl⟩ := l.applyLoan_manage_inv u i action hu
    exact ⟨broker, hb⟩
  | loanPay i pt amount =>
    obtain ⟨e, broker, -, -, -, hb, -, -, -, rfl⟩ := l.applyLoan_pay_inv u i pt amount hu
    exact ⟨broker, hb⟩
  | loanDelete i =>
    obtain ⟨e, broker, -, -, -, hb, -, -, -, rfl⟩ := l.applyLoan_delete_inv u i hu
    exact ⟨broker, hb⟩
  | _ => simp only [LendingLedger.applyLoan] at hu; cases hu

/-- The broker slots never shrink. -/
private lemma LendingLedger.apply_brokers_length {l l' : LendingLedger} {tx : LendingTx}
    (hok : (l.apply tx).run = .ok (.ok l')) : l.brokers.length ≤ l'.brokers.length := by
  by_cases hb : tx.isBroker = true
  · obtain ⟨u, -, rfl⟩ := LendingLedger.apply_broker hb hok
    unfold LendingLedger.commitBroker storeSlot
    split <;> simp
  by_cases hl : tx.isLoan = true
  · obtain ⟨u, -, rfl⟩ := LendingLedger.apply_loan hl hok
    simp [LendingLedger.commitLoan]
  rw [LendingLedger.apply_brokers hb hl hok]

/-- A broker slot a LoanBrokerDelete emptied stays empty: a new broker goes to a new slot. -/
private lemma LendingLedger.apply_broker_none {l l' : LendingLedger} {tx : LendingTx}
    (hok : (l.apply tx).run = .ok (.ok l')) {j : Nat} (hj : j < l.brokers.length) (hn : l.broker? j = none) :
    l'.broker? j = none := by
  by_cases hb : tx.isBroker = true
  · obtain ⟨u, hu, rfl⟩ := LendingLedger.apply_broker hb hok
    rw [LendingLedger.broker?_commitBroker]
    rcases LendingLedger.applyBroker_cases l tx u hu with ⟨hi, -⟩ | ⟨b, -, hbu, -⟩ | ⟨-, -, hnone, -⟩
    · rw [hi, if_neg (lt_irrefl _), if_neg (by omega)]
      exact hn
    · rw [if_pos (LendingLedger.broker?_lt hbu), if_neg (fun hji => by rw [← hji, hn] at hbu; cases hbu)]
      exact hn
    · split_ifs <;> first | exact hnone | exact hn
  by_cases hl : tx.isLoan = true
  · obtain ⟨u, hu, rfl⟩ := LendingLedger.apply_loan hl hok
    obtain ⟨b, hbu⟩ := l.applyLoan_broker tx u hu
    rw [LendingLedger.broker?_commitLoan l u b hbu, if_neg (fun hji => by rw [← hji, hn] at hbu; cases hbu)]
    exact hn
  unfold LendingLedger.broker?
  rw [LendingLedger.apply_brokers hb hl hok]
  exact hn

/-- A transaction other than a broker or loan transaction moves nothing in or out of a cover. -/
private lemma LendingLedger.coverFlows_of_other (l : LendingLedger) (j : Nat) {tx : LendingTx}
    (hb : ¬ tx.isBroker = true) (hl : ¬ tx.isLoan = true) :
    l.coverDepositsOf j tx = 0 ∧ l.coverWithdrawalsOf j tx = 0 ∧ l.coverClawbacksOf j tx = 0 ∧
      l.feesToCoverOf j tx = 0 ∧ l.brokerDefaultCoveredOf j tx = 0 := by
  have hon := l.onBroker_of_not_loan j hl
  simp only [LendingLedger.feesToCoverOf, LendingLedger.brokerDefaultCoveredOf, hon, Bool.false_eq_true,
    ↓reduceIte]
  cases tx <;> simp_all [LendingTx.isBroker, LendingLedger.coverDepositsOf, LendingLedger.coverWithdrawalsOf,
    LendingLedger.coverClawbacksOf]

/-- One successful transaction on a reachable ledger moves broker `j`'s CoverAvailable by what it pays into the cover
less what it takes out, while the broker is there before and after and its cover stays below `10^16` base units. -/
private lemma LendingLedger.cover_accounting_step {l l' : LendingLedger} {tx : LendingTx} (hr : l.Reachable)
    (hok : (l.apply tx).run = .ok (.ok l')) {j : Nat} {b b' : LoanBroker} (hb : l.broker? j = some b)
    (hb' : l'.broker? j = some b')
    (hin : b.coverAvailable.toRat + l.coverDepositsOf j tx + l.feesToCoverOf j tx <
      10 ^ 16 * 10 ^ l.vault.baseExponent)
    (hout : b.coverAvailable.toRat - l.brokerDefaultCoveredOf j tx < 10 ^ 16 * 10 ^ l.vault.baseExponent) :
    b'.coverAvailable.toRat = b.coverAvailable.toRat + l.coverDepositsOf j tx - l.coverWithdrawalsOf j tx -
      l.coverClawbacksOf j tx + l.feesToCoverOf j tx - l.brokerDefaultCoveredOf j tx := by
  have hpw : (0 : ℚ) < 10 ^ l.vault.baseExponent := zpow_pos (by norm_num) _
  have h63 : (10 : ℚ) ^ 16 * 10 ^ l.vault.baseExponent < 2 ^ 63 * 10 ^ l.vault.baseExponent :=
    mul_lt_mul_of_pos_right (by norm_num) hpw
  have hc := hr.cover_onGrid hb
  have hbnt := hr.scaleInv.brokers j b hb
  -- a step that keeps the broker's cover and moves nothing in or out of it
  have hsame : b'.coverAvailable = b.coverAvailable → l.coverDepositsOf j tx = 0 → l.coverWithdrawalsOf j tx = 0 →
      l.coverClawbacksOf j tx = 0 → l.feesToCoverOf j tx = 0 → l.brokerDefaultCoveredOf j tx = 0 →
      b'.coverAvailable.toRat = b.coverAvailable.toRat + l.coverDepositsOf j tx - l.coverWithdrawalsOf j tx -
        l.coverClawbacksOf j tx + l.feesToCoverOf j tx - l.brokerDefaultCoveredOf j tx := by
    intro h1 h2 h3 h4 h5 h6
    rw [h1, h2, h3, h4, h5, h6]; ring
  by_cases hbk : tx.isBroker = true
  · have hl : ¬ tx.isLoan = true := by cases tx <;> simp_all [LendingTx.isBroker, LendingTx.isLoan]
    have hon := l.onBroker_of_not_loan j hl
    have hf : l.feesToCoverOf j tx = 0 ∧ l.brokerDefaultCoveredOf j tx = 0 := by
      simp [LendingLedger.feesToCoverOf, LendingLedger.brokerDefaultCoveredOf, hon]
    rw [hf.1, hf.2]
    rw [hf.1, add_zero] at hin
    have hpre := LendingLedger.apply_preflight hok
    obtain ⟨u, hu, rfl⟩ := LendingLedger.apply_broker hbk hok
    rw [LendingLedger.broker?_commitBroker] at hb'
    have hjl := LendingLedger.broker?_lt hb
    have hcan : ∀ t : TER, ¬ (!t.isTesSuccess) = true → t = .tesSUCCESS := fun t ht =>
      (TER.isTesSuccess_iff t).mp (by simpa using ht)
    -- the slot a transaction on the stored broker `i` writes
    have hslot : ∀ (i : Nat) (x : LoanBroker), l.broker? i = some x → u.index = i →
        (if j = i then u.broker else l.broker? j) = some b' := by
      intro i x hx hi
      rw [hi, if_pos (LendingLedger.broker?_lt hx)] at hb'
      exact hb'
    cases tx with
    | loanBrokerCreate ctx =>
      simp only [LendingLedger.applyBroker] at hu
      unfold_ter at hu
      walk_ok
      rw [if_neg (lt_irrefl _), if_neg (by omega), hb] at hb'
      cases hb'
      simp [LendingLedger.coverDepositsOf, LendingLedger.coverWithdrawalsOf, LendingLedger.coverClawbacksOf]
    | loanBrokerUpdate i dm =>
      simp only [LendingLedger.applyBroker] at hu
      unfold_ter at hu
      walk_ok
      have hbi : l.broker? i = some _ := ‹_›
      have hcz := congrArg RawLoanBroker.coverAvailable
        (RawLoanBroker.to_lawful_ok ‹RawLoanBroker.to_lawful _ = Except.ok _›).1
      simp only at hcz
      have h' := hslot i _ hbi rfl
      by_cases hij : j = i
      · subst hij
        rw [if_pos rfl] at h'
        rw [hb] at hbi
        cases h'
        cases hbi
        show (_ : LoanBroker).coverAvailable.toRat = _
        rw [hcz]; simp [LendingLedger.coverDepositsOf, LendingLedger.coverWithdrawalsOf,
          LendingLedger.coverClawbacksOf]
      · rw [if_neg hij, hb] at h'
        cases h'
        simp [LendingLedger.coverDepositsOf, LendingLedger.coverWithdrawalsOf, LendingLedger.coverClawbacksOf]
    | loanBrokerCoverDeposit i a =>
      simp only [LendingLedger.applyBroker] at hu
      unfold_ter at hu
      walk_ok
      have hbi : l.broker? i = some _ := ‹_›
      have h' := hslot i _ hbi rfl
      by_cases hij : j = i
      · subst hij
        rw [if_pos rfl] at h'
        rw [hb] at hbi
        cases hbi
        obtain ⟨res, hdep, rfl⟩ : ∃ res, (b.coverDeposit l.vault a).run = .ok (.ok res) ∧ res.loanBroker' = b' :=
          ⟨_, ‹_›, Option.some.inj h'⟩
        have hflow : l.coverDepositsOf j (.loanBrokerCoverDeposit j a) = res.amount'.toRat := by
          simp only [LendingLedger.coverDepositsOf, if_true, hb, hdep]
        rw [hflow] at hin ⊢
        have hpa : (isCanonicalAmount a l.vault.numericType && isPositiveAmount a) = true := by
          by_contra hne
          simp only [Bool.not_eq_true] at hne
          simp [LendingTx.preflight, hne] at hpre
        obtain ⟨hac, hapos⟩ := LendingTx.preflight_coverAmount l hr.holdsAsset a hpa
        rw [LoanBroker.coverDeposit_cover b l.vault a _ hc
          (fun hi => l.vault.baseExponent_bounds.2.2 (by rw [← hbnt]; exact hi)) hac hapos hdep (by linarith)]
        simp [LendingLedger.coverWithdrawalsOf, LendingLedger.coverClawbacksOf]
      · rw [if_neg hij, hb] at h'
        cases h'
        simp [LendingLedger.coverDepositsOf, LendingLedger.coverWithdrawalsOf, LendingLedger.coverClawbacksOf,
          Ne.symm hij]
    | loanBrokerCoverWithdraw i a =>
      simp only [LendingLedger.applyBroker] at hu
      unfold_ter at hu
      walk_ok
      have hbi : l.broker? i = some _ := ‹_›
      have h' := hslot i _ hbi rfl
      by_cases hij : j = i
      · subst hij
        rw [if_pos rfl] at h'
        rw [hb] at hbi
        cases hbi
        obtain ⟨res, hwd, rfl⟩ : ∃ res, (b.coverWithdraw l.vault a).run = .ok (.ok res) ∧ res.loanBroker' = b' :=
          ⟨_, ‹_›, Option.some.inj h'⟩
        obtain ⟨t, hct, ht⟩ : ∃ t, b.canCoverWithdraw l.vault a = .ok t ∧ ¬ (!t.isTesSuccess) = true :=
          ⟨_, ‹_›, ‹_›⟩
        rw [hcan t ht] at hct
        have hflow : l.coverWithdrawalsOf j (.loanBrokerCoverWithdraw j a) = res.amount'.toRat := by
          simp only [LendingLedger.coverWithdrawalsOf, if_true, hb, hwd]
        rw [hflow]
        have hpa : (isCanonicalAmount a l.vault.numericType && isPositiveAmount a) = true := by
          by_contra hne
          simp only [Bool.not_eq_true] at hne
          simp [LendingTx.preflight, hne] at hpre
        obtain ⟨hac, hapos⟩ := LendingTx.preflight_coverAmount l hr.holdsAsset a hpa
        have h0 : l.coverDepositsOf j (.loanBrokerCoverWithdraw j a) = 0 := rfl
        rw [h0] at hin
        rw [LoanBroker.coverWithdraw_cover b l.vault a _ hc hac hapos hct hwd (by linarith)]
        simp [LendingLedger.coverDepositsOf, LendingLedger.coverClawbacksOf]
      · rw [if_neg hij, hb] at h'
        cases h'
        simp [LendingLedger.coverDepositsOf, LendingLedger.coverWithdrawalsOf, LendingLedger.coverClawbacksOf,
          Ne.symm hij]
    | loanBrokerCoverClawback i a =>
      simp only [LendingLedger.applyBroker] at hu
      unfold_ter at hu
      walk_ok
      have hbi : l.broker? i = some _ := ‹_›
      have h' := hslot i _ hbi rfl
      by_cases hij : j = i
      · subst hij
        rw [if_pos rfl] at h'
        rw [hb] at hbi
        cases hbi
        obtain ⟨res, hcl, rfl⟩ : ∃ res, (b.coverClawback l.vault a).run = .ok (.ok res) ∧ res.loanBroker' = b' :=
          ⟨_, ‹_›, Option.some.inj h'⟩
        have hflow : l.coverClawbacksOf j (.loanBrokerCoverClawback j a) = res.amount'.toRat := by
          simp only [LendingLedger.coverClawbacksOf, if_true, hb, hcl]
        rw [hflow]
        have h0 : l.coverDepositsOf j (.loanBrokerCoverClawback j a) = 0 := rfl
        rw [h0] at hin
        rw [LoanBroker.coverClawback_cover b l.vault a _ hc (by rw [hbnt]; exact hr.holdsAsset.maxValue_le) hcl
          (by linarith)]
        simp [LendingLedger.coverDepositsOf, LendingLedger.coverWithdrawalsOf]
      · rw [if_neg hij, hb] at h'
        cases h'
        simp [LendingLedger.coverDepositsOf, LendingLedger.coverWithdrawalsOf, LendingLedger.coverClawbacksOf,
          Ne.symm hij]
    | loanBrokerDelete i =>
      simp only [LendingLedger.applyBroker] at hu
      unfold_ter at hu
      walk_ok
      have hbi : l.broker? i = some _ := ‹_›
      have h' := hslot i _ hbi rfl
      by_cases hij : j = i
      · rw [if_pos hij] at h'
        cases h'
      · rw [if_neg hij, hb] at h'
        cases h'
        simp [LendingLedger.coverDepositsOf, LendingLedger.coverWithdrawalsOf, LendingLedger.coverClawbacksOf]
    | _ => simp only [LendingTx.isBroker, Bool.false_eq_true] at hbk
  by_cases hl : tx.isLoan = true
  swap
  · have hz := l.coverFlows_of_other j hbk hl
    have hbr := LendingLedger.apply_brokers hbk hl hok
    have hb'' : l.broker? j = some b' := by unfold LendingLedger.broker? at hb' ⊢; rw [hbr] at hb'; exact hb'
    rw [hb] at hb''
    cases hb''
    exact hsame rfl hz.1 hz.2.1 hz.2.2.1 hz.2.2.2.1 hz.2.2.2.2
  have hbf : l.coverDepositsOf j tx = 0 ∧ l.coverWithdrawalsOf j tx = 0 ∧ l.coverClawbacksOf j tx = 0 := by
    cases tx <;> simp_all [LendingTx.isLoan, LendingLedger.coverDepositsOf, LendingLedger.coverWithdrawalsOf,
      LendingLedger.coverClawbacksOf]
  rw [hbf.1, add_zero] at hin
  rw [hbf.1, hbf.2.1, hbf.2.2]
  -- a loan transaction writes the slot of its loan's broker: broker `j` moves only when it is that broker
  have hslot : ∀ (k : Nat) (x : LoanBroker), (∀ k', l'.broker? k' = if k' = k then some x else l.broker? k') →
      (j = k → b'.coverAvailable.toRat = b.coverAvailable.toRat + l.feesToCoverOf j tx -
        l.brokerDefaultCoveredOf j tx) → (j ≠ k → l.onBroker j tx = false) →
      b'.coverAvailable.toRat = b.coverAvailable.toRat + 0 - 0 - 0 + l.feesToCoverOf j tx -
        l.brokerDefaultCoveredOf j tx := by
    intro k x hbr hon hoff
    by_cases hjk : j = k
    · rw [hon hjk]; ring
    · rw [hbr j, if_neg hjk, hb] at hb'
      cases hb'
      simp [LendingLedger.feesToCoverOf, LendingLedger.brokerDefaultCoveredOf, hoff hjk]
  have hloanOn : ∀ {i : Nat} {e : LoanEntry}, l.loan? i = some e → j ≠ e.brokerIndex →
      (e.brokerIndex == j) = false := fun _ hjk => by simpa using Ne.symm hjk
  cases tx with
  | loanSet i principal rates fees pi pt gp sd twoStep ao =>
    obtain ⟨broker, r, hbi, -, -, -, hcr, -, -, -, -, hbr⟩ := LendingLedger.loanSet_ok hok
    refine hslot i _ hbr (fun hji => ?_) (fun hji => by simpa [LendingLedger.onBroker] using Ne.symm hji)
    subst hji
    rw [hbr j, if_pos rfl] at hb'
    have hbb : broker = b := Option.some.inj (hbi.symm.trans hb)
    subst hbb
    cases hb'
    obtain ⟨_, _, _, -, hbraw⟩ := Loan.create_ok_broker broker l.vault principal rates fees _ ao twoStep r hcr
    have hcv : r.loan'.broker.coverAvailable = broker.coverAvailable :=
      (congrArg RawLoanBroker.coverAvailable hbraw :)
    rw [hcv]
    simp [LendingLedger.feesToCoverOf, LendingLedger.brokerDefaultCoveredOf, LendingLedger.defaultCoveredOf]
  | loanAccept i =>
    obtain ⟨e, loan, r, he, hat, -, ha, -, -, -, -, hbr⟩ := LendingLedger.loanAccept_ok hok
    obtain ⟨e₀, he₀, hbk', -⟩ := hat.stored
    obtain rfl := Option.some.inj (he₀.symm.trans he)
    refine hslot _ _ hbr (fun hji => ?_) (fun hji => by rw [(l.onBroker_loan j he₀).1]; exact hloanOn he₀ hji)
    subst hji
    rw [hbr _, if_pos rfl] at hb'
    rw [hbk'] at hb
    cases hb
    cases hb'
    rw [Loan.accept_broker loan _ r ha]
    simp [LendingLedger.feesToCoverOf, LendingLedger.brokerDefaultCoveredOf, LendingLedger.defaultCoveredOf]
  | loanDelete i =>
    obtain ⟨e, loan, r, he, hat, -, hd, -, -, -, -, hbr⟩ := LendingLedger.loanDelete_ok hok
    obtain ⟨e₀, he₀, hbk', -⟩ := hat.stored
    obtain rfl := Option.some.inj (he₀.symm.trans he)
    refine hslot _ _ hbr (fun hji => ?_) (fun hji => by rw [(l.onBroker_loan j he₀).2.1]; exact hloanOn he₀ hji)
    subst hji
    rw [hbr _, if_pos rfl] at hb'
    rw [hbk'] at hb
    cases hb
    cases hb'
    rw [Loan.delete_cover loan _ r hd]
    simp [LendingLedger.feesToCoverOf, LendingLedger.brokerDefaultCoveredOf, LendingLedger.defaultCoveredOf]
  | loanManage i action =>
    obtain ⟨e, loan, r, he, hat, -, hm, -, -, -, -, hbr⟩ := LendingLedger.loanManage_ok hok
    obtain ⟨e₀, he₀, hbk', -⟩ := hat.stored
    obtain rfl := Option.some.inj (he₀.symm.trans he)
    have hon := (l.onBroker_loan j he₀).2.2.1 action
    cases action with
    | impair =>
      refine hslot _ _ hbr (fun hji => ?_) (fun hji => by rw [hon]; exact hloanOn he₀ hji)
      subst hji
      rw [hbr _, if_pos rfl] at hb'
      rw [hbk'] at hb
      cases hb
      cases hb'
      rw [(Loan.manageImpair_debt loan l.vault l.now r hm).1]
      simp [LendingLedger.feesToCoverOf, LendingLedger.brokerDefaultCoveredOf, LendingLedger.defaultCoveredOf]
    | unimpair =>
      refine hslot _ _ hbr (fun hji => ?_) (fun hji => by rw [hon]; exact hloanOn he₀ hji)
      subst hji
      rw [hbr _, if_pos rfl] at hb'
      rw [hbk'] at hb
      cases hb
      cases hb'
      rw [(Loan.manageUnimpair_debt loan l.vault r hm).1]
      simp [LendingLedger.feesToCoverOf, LendingLedger.brokerDefaultCoveredOf, LendingLedger.defaultCoveredOf]
    | default =>
      obtain ⟨e₂, loan₂, r₂, he₂, hat₂, -, hdef, -, -, -, -, hbrd⟩ := LendingLedger.loanDefault_ok hok
      obtain rfl := hat.eq hat₂
      obtain rfl := Option.some.inj (he₀.symm.trans he₂)
      refine hslot _ _ hbrd (fun hji => ?_) (fun hji => by rw [hon]; exact hloanOn he₀ hji)
      subst hji
      rw [hbrd _, if_pos rfl] at hb'
      rw [hbk'] at hb
      cases hb
      cases hb'
      have hflow : l.brokerDefaultCoveredOf e₀.brokerIndex (.loanManage i .default) = r₂.amountToPool.toRat := by
        simp [LendingLedger.brokerDefaultCoveredOf, LendingLedger.defaultCoveredOf, hon, hat.read, hdef]
      have hfee : l.feesToCoverOf e₀.brokerIndex (.loanManage i .default) = 0 := by
        simp [LendingLedger.feesToCoverOf]
      rw [hflow] at hout ⊢
      rw [hfee, add_zero]
      exact LendingLedger.default_cover hr hat hdef hout
  | loanPay i pt amount =>
    obtain ⟨e, loan, r, he, hat, -, -, hpay, -, -, hat', -, hbr⟩ := LendingLedger.loanPay_ok hok
    obtain ⟨e₀, he₀, hbk', -⟩ := hat.stored
    obtain rfl := Option.some.inj (he₀.symm.trans he)
    have hon := (l.onBroker_loan j he₀).2.2.2 pt amount
    refine hslot _ _ hbr (fun hji => ?_) (fun hji => by rw [hon]; exact hloanOn he₀ hji)
    subst hji
    rw [hbr _, if_pos rfl] at hb'
    rw [hbk'] at hb
    cases hb
    cases hb'
    have hdc : l.brokerDefaultCoveredOf e₀.brokerIndex (.loanPay i pt amount) = 0 := by
      simp [LendingLedger.brokerDefaultCoveredOf, LendingLedger.defaultCoveredOf]
    rw [hdc, sub_zero]
    obtain ⟨p, hp⟩ := LendingLedger.loanPay_instalments hok hat
    rcases Loan.pay_minimumCover loan l.vault pt amount l.now r hpay with hmc | hmc
    · have hfee : l.feesToCoverOf e₀.brokerIndex (.loanPay i pt amount) = 0 := by
        simp [LendingLedger.feesToCoverOf, hon, hat.read, hmc]
      rw [hfee, add_zero, LendingLedger.payment_fees_proof l l' i pt amount hok loan r.loan' hat hat' hmc]
    · have hfee : l.feesToCoverOf e₀.brokerIndex (.loanPay i pt amount) = p.amounts.feePaid.toRat := by
        simp [LendingLedger.feesToCoverOf, hon, hat.read, hmc, hp]
      rw [hfee] at hin ⊢
      exact LendingLedger.pay_fee_cover hr hat hpay hp hmc hin
  | _ => simp only [LendingTx.isLoan, Bool.false_eq_true] at hl

/-- The broker slots along a sequence never shrink. -/
private lemma LendingLedger.Reaches.brokers_length {start l : LendingLedger} {txs : List LendingTx}
    (h : LendingLedger.Reaches start txs l) : start.brokers.length ≤ l.brokers.length := by
  induction h with
  | refl => exact le_refl _
  | step tx _ hok ih => exact ih.trans (LendingLedger.apply_brokers_length hok)

/-- Proof of the CoverAvailable line: a broker present at both ends was there at every step, and each step moves its
cover by what it pays in less what it takes out. -/
private lemma LendingLedger.broker_cover_accounting {start l : LendingLedger} {txs : List LendingTx}
    (hr : start.Reachable) (hrun : LendingLedger.Reaches start txs l) (j : Nat) (b : LoanBroker)
    (hb : start.broker? j = some b) (hnc : start.CoverNotCoarsenedAlong j txs) (b' : LoanBroker)
    (hb' : l.broker? j = some b') :
    b'.coverAvailable.toRat = b.coverAvailable.toRat + start.coverDeposits j txs - start.coverWithdrawals j txs -
      start.coverClawbacks j txs + start.feesToCover j txs - start.brokerDefaultCovered j txs := by
  induction hrun generalizing b' with
  | refl =>
    rw [hb] at hb'
    cases hb'
    simp [LendingLedger.coverDeposits, LendingLedger.coverWithdrawals, LendingLedger.coverClawbacks,
      LendingLedger.feesToCover, LendingLedger.brokerDefaultCovered, LendingLedger.runSum]
  | @step txs₀ l₀ l₁ tx hprev hok ih =>
    have hjl := (LendingLedger.broker?_lt hb).trans_le hprev.brokers_length
    obtain ⟨b₀, hb₀⟩ : ∃ b₀, l₀.broker? j = some b₀ := by
      cases h0 : l₀.broker? j with
      | none => rw [LendingLedger.apply_broker_none hok hjl h0] at hb'; cases hb'
      | some b₀ => exact ⟨b₀, rfl⟩
    have ih' := ih (fun pre l₂ t b₂ hp hr' hb₂ => hnc pre l₂ t b₂ (hp.trans (List.prefix_append _ _)) hr' hb₂)
      b₀ hb₀
    obtain ⟨hin, hout⟩ := hnc txs₀ l₀ tx b₀ (List.prefix_refl _) hprev hb₀
    have hstep := LendingLedger.cover_accounting_step (hprev.reachable hr) hok hb₀ hb' hin hout
    unfold LendingLedger.coverDeposits LendingLedger.coverWithdrawals LendingLedger.coverClawbacks
      LendingLedger.feesToCover LendingLedger.brokerDefaultCovered at ih' ⊢
    simp only [LendingLedger.runSum_snoc hprev hok]
    linarith

/-- Over any sequence from a reachable ledger, for a broker present at both ends -> the DebtTotal, CoverAvailable (while
the cover is not coarsened) and LoanCount lines, each sum over the broker's transactions. -/
lemma LendingLedger.broker_accounting_proof {start l : LendingLedger} {txs : List LendingTx} (hr : start.Reachable)
    (hrun : LendingLedger.Reaches start txs l) :
    ∀ (j : Nat) (b b' : LoanBroker), start.broker? j = some b → l.broker? j = some b' →
      b'.debtTotal.toRat = b.debtTotal.toRat + start.brokerLent j txs - start.brokerPrincipalPaid j txs -
        start.brokerDefaulted j txs - start.brokerDeletedPending j txs ∧
      (start.CoverNotCoarsenedAlong j txs →
        b'.coverAvailable.toRat = b.coverAvailable.toRat + start.coverDeposits j txs - start.coverWithdrawals j txs -
          start.coverClawbacks j txs + start.feesToCover j txs - start.brokerDefaultCovered j txs) ∧
      (b'.loanCount.toNat : ℚ) = b.loanCount.toNat + start.newLoans j txs - start.deletedLoans j txs :=
  fun j b b' hb hb' => ⟨LendingLedger.broker_debt_accounting hr hrun j b b' hb hb',
    fun hnc => LendingLedger.broker_cover_accounting hr hrun j b hb hnc b' hb',
    LendingLedger.broker_count_accounting hr hrun j b b' hb hb'⟩

end XRPL.Model.Lending
