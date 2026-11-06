import XRPL.Properties.Lending.Ledger.Common.CoarsenedVault
import XRPL.Properties.Lending.Ledger.Common.IsolationDefs

/-! # Witnesses for the isolation of loan transactions

On the IOU vault of `CoarsenedVault.lean` two pending loans each fit the Open limit, and once one is accepted the
other's LoanAccept exceeds it. A late payment of a large loan lifts AssetsAvailable past `10^16` base units, and a
payment of `0.1` on another loan, which passed before, then rounds to no credit and is rejected. -/

set_option linter.style.nativeDecide false

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault (Vault)

/-- An InterestRate of 60% and no other rate. -/
private def isoRates : LoanRates := { cwRates 0 with interestRate := 60000 }

/-- A deposit of 800000000000000, two brokers without cover requirements, and two pending loans of 100000000000000
that each owe 60000000000000 of interest in one yearly payment. The second loan is on broker `k`. -/
private def isoOpenTxs (k : Nat) : List LendingTx :=
  [.vaultDeposit 0 (cwAmount 8000000000000000 (-1)) false,
   .close 1001,
   .loanBrokerCreate ⟨none, none, none, none⟩,
   .loanBrokerCreate ⟨none, none, none, none⟩,
   .loanSet 0 ⟨false, 1000000000000000000, -4⟩ isoRates cwFees (some 31536000) (some 1) (some 60) 5000 true false,
   .loanSet k ⟨false, 1000000000000000000, -4⟩ isoRates cwFees (some 31536000) (some 1) (some 60) 5000 true false]

/-- A deposit of 899999000000000, two brokers, loan A of 700000000000000 at a late interest rate of 100% on broker
`k`, loan C of 2 in twenty instalments of 0.1 on broker 0, and a close 800 days on, when both are late. -/
private def isoCoarseTxs (k : Nat) : List LendingTx :=
  [.vaultDeposit 0 (cwAmount 8999990000000000 (-1)) false,
   .close 1001,
   .loanBrokerCreate ⟨none, none, none, none⟩,
   .loanBrokerCreate ⟨none, none, none, none⟩,
   .loanSet k ⟨false, 7000000000000000000, -4⟩ (cwRates 100000) cwFees (some 86400) (some 5) (some 60) 0 false
     false,
   .loanSet 0 ⟨false, 2000000000000000000, -18⟩ (cwRates 0) cwFees (some 86400) (some 20) (some 60) 0 false false,
   .close 69207461]

/-- Loan A's late payment of 7000000000000000. -/
private def isoCoarsenTx : LendingTx := .loanPay 0 .late ⟨false, 7000000000000000000, -3⟩

/-- Loan C's late payment of 0.1. -/
private def isoDustTx : LendingTx := .loanPay 1 .late ⟨false, 1000000000000000000, -19⟩

/-- The fee a payment of loan `j` pays fits beside the broker's cover on an IOU vault. -/
private def feeFitsCheck (l : LendingLedger) (j : Nat) (pt : LoanPaymentType) (amount : Number) : Bool :=
  match l.loan? j with
  | none => true
  | some e =>
    match l.broker? e.brokerIndex with
    | none => true
    | some b =>
      match e.loan.withBroker b with
      | .error _ => true
      | .ok loan =>
        match (loan.payInstalments l.vault pt amount l.now).run with
        | .ok (.ok p) => l.vault.numericType == .fractional &&
            decide (loan.broker.coverAvailable.toRat + p.amounts.feePaid.toRat < 10 ^ 89)
        | _ => true

private lemma feeFits_of_check (l : LendingLedger) (j : Nat) (pt : LoanPaymentType) (amount : Number)
    (h : feeFitsCheck l j pt amount = true) : l.FeeFits j pt amount := by
  intro loan p hat hp
  obtain ⟨e, b, he, hb, hw⟩ := hat
  unfold feeFitsCheck at h
  simp only [he, hb, hw, hp, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  exact Or.inl h

/-- The fee check of the second transaction when it is a payment. -/
private def txFeeCheck (l : LendingLedger) (j : Nat) : LendingTx → Bool
  | .loanPay _ pt amount => feeFitsCheck l j pt amount
  | _ => true

/-- A run from the new vault, two transactions that pass on its last ledger, and the second one's result after the
first. `rel` checks how the transactions relate to the loan, `base` asks for the vault not to be coarsened. -/
private def isoCheck (txs : List LendingTx) (tx tx' : LendingTx) (j : Nat) (ter : TER) (base : Bool)
    (rel : LendingLedger → LoanEntry → Bool) : Bool :=
  match cwGenesis.run txs with
  | .error _ => false
  | .ok l =>
    match l.loan? j with
    | none => false
    | some e' =>
      match (l.apply tx).run, (l.apply tx').run with
      | .ok (.ok la), .ok (.ok _) =>
        rel l e' &&
          (match la.broker? e'.brokerIndex with
           | some b => decide (b.coverAvailable.toRat < 10 ^ 96)
           | none => true) &&
          !la.vault.numericType.isIntegral && txFeeCheck la j tx' &&
          (!base || decide (la.vault.assetsAvailable.toRat + la.vault.assetsDeployed.toRat <
            10 ^ 16 * (10 : ℚ) ^ la.vault.baseExponent)) &&
          (match (la.apply tx').run with
           | .ok (.error t) => decide (t = ter)
           | _ => false)
      | _, _ => false

/-- What a passing `isoCheck` gives: a reachable ledger, both transactions passing on it, the stand-in hypotheses
of the isolation theorems on the ledger after the first, and the second one rejected there. -/
private lemma isolation_of_check (txs : List LendingTx) (tx tx' : LendingTx) (j : Nat) (ter : TER) (base : Bool)
    (rel : LendingLedger → LoanEntry → Bool) (h : isoCheck txs tx tx' j ter base rel = true) :
    ∃ (l la lb : LendingLedger) (e' : LoanEntry), l.Reachable ∧ l.loan? j = some e' ∧ rel l e' = true ∧
      (l.apply tx).run = .ok (.ok la) ∧ (l.apply tx').run = .ok (.ok lb) ∧
      (∀ b, la.broker? e'.brokerIndex = some b → b.coverAvailable.toRat < 10 ^ 96) ∧
      (∀ pt amount, tx' = .loanPay j pt amount → la.CreditFits j pt amount) ∧
      (∀ pt amount, tx' = .loanPay j pt amount → la.FeeFits j pt amount) ∧
      (base = true → la.vault.assetsAvailable.toRat + la.vault.assetsDeployed.toRat <
        10 ^ 16 * (10 : ℚ) ^ la.vault.baseExponent) ∧
      (la.apply tx').run = .ok (.error ter) := by
  unfold isoCheck at h
  split at h
  · cases h
  rename_i l hl
  split at h
  · cases h
  rename_i e' he'
  split at h
  · rename_i la lb ha hb
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at h
    obtain ⟨⟨⟨⟨⟨hrel, hcov⟩, hint⟩, hfee⟩, htot⟩, hrej⟩ := h
    refine ⟨l, la, lb, e', LendingLedger.Reachable.of_run cwGenesis_genesis hl, he', hrel, ha, hb, ?_, ?_, ?_, ?_,
      ?_⟩
    · intro b hb'
      rw [hb'] at hcov
      exact of_decide_eq_true hcov
    · intro pt amount _ loan p _ _ hi
      rw [hi] at hint
      cases hint
    · rintro pt amount rfl
      exact feeFits_of_check la j pt amount hfee
    · intro hbase
      rw [hbase] at htot
      simpa using htot
    · split at hrej
      · rename_i t ht
        rw [ht, of_decide_eq_true hrej]
      · cases hrej
  · cases h

/-- Two pending loans on one broker each fit the Open limit, on a reachable ledger. Accepting the first books
its interest, and the second can no longer be accepted. -/
lemma LendingLedger.payment_isolation_open_witness :
    ∃ (l la lb : LendingLedger) (j : Nat) (e' : LoanEntry) (tx tx' : LendingTx),
      l.Reachable ∧ l.loan? j = some e' ∧ l.loanTxBroker? tx = some e'.brokerIndex ∧ tx.loanIndex? ≠ some j ∧
      tx'.loanIndex? = some j ∧ (l.apply tx).run = .ok (.ok la) ∧ (l.apply tx').run = .ok (.ok lb) ∧
      la.vault.assetsAvailable.toRat + la.vault.assetsDeployed.toRat <
        10 ^ 16 * (10 : ℚ) ^ la.vault.baseExponent ∧
      (∀ b, la.broker? e'.brokerIndex = some b → b.coverAvailable.toRat < 10 ^ 96) ∧
      (∀ pt amount, tx' = .loanPay j pt amount → la.CreditFits j pt amount) ∧
      (∀ pt amount, tx' = .loanPay j pt amount → la.FeeFits j pt amount) ∧
      (la.apply tx').run = .ok (.error .tecLIMIT_EXCEEDED) := by
  obtain ⟨l, la, lb, e', hr, he', hrel, ha, hb, hca, hcr, hfee, htot, hrej⟩ := isolation_of_check (isoOpenTxs 0)
    (.loanAccept 0) (.loanAccept 1) 1 .tecLIMIT_EXCEEDED true
    (fun l e' => l.loanTxBroker? (.loanAccept 0) == some e'.brokerIndex) (by native_decide)
  exact ⟨l, la, lb, 1, e', .loanAccept 0, .loanAccept 1, hr, he', by simpa using hrel,
    by simp [LendingTx.loanIndex?], rfl, ha, hb, htot rfl, hca, hcr, hfee, hrej⟩

/-- The run of `payment_isolation_open_witness` after the first accept: the second loan is still pending and before
its StartDate, and its LoanAccept is rejected. -/
private def acceptBlockedCheck : Bool :=
  match cwGenesis.run (isoOpenTxs 0 ++ [.loanAccept 0]) with
  | .error _ => false
  | .ok l =>
    match l.loan? 1 with
    | none => false
    | some e =>
      !l.vaultDeleted && e.loan.isPending && decide (l.now < e.loan.schedule.startDate) &&
        (match (l.apply (.loanAccept 1)).run with
         | .ok (.error t) => decide (t = .tecLIMIT_EXCEEDED)
         | _ => false)

/-- A pending loan before its StartDate whose LoanAccept is rejected, on a reachable ledger. Accepting the other
pending loan booked its interest and used up the Open limit. -/
lemma LendingLedger.accept_before_start_witness :
    ∃ l : LendingLedger, l.Reachable ∧ l.vaultDeleted = false ∧ ∃ (i : Nat) (e : LoanEntry), l.loan? i = some e ∧
      e.loan.isPending = true ∧ l.now < e.loan.schedule.startDate ∧
      (l.apply (.loanAccept i)).run = .ok (.error .tecLIMIT_EXCEEDED) := by
  have h : acceptBlockedCheck = true := by native_decide
  unfold acceptBlockedCheck at h
  split at h
  · cases h
  rename_i l hl
  split at h
  · cases h
  rename_i e he
  simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq] at h
  obtain ⟨⟨⟨hnd, hp⟩, ht⟩, hrej⟩ := h
  refine ⟨l, LendingLedger.Reachable.of_run cwGenesis_genesis hl, hnd, 1, e, he, hp, ht, ?_⟩
  split at hrej
  · rename_i t ht'
    rw [ht', of_decide_eq_true hrej]
  · cases hrej

/-- A late payment on one loan coarsens the vault, and a payment of 0.1 on another loan of the same broker, which
passed before, is then rejected, on a reachable ledger. -/
lemma LendingLedger.payment_isolation_coarsened_witness :
    ∃ (l la lb : LendingLedger) (j : Nat) (e' : LoanEntry) (tx tx' : LendingTx),
      l.Reachable ∧ l.loan? j = some e' ∧ l.loanTxBroker? tx = some e'.brokerIndex ∧ tx.loanIndex? ≠ some j ∧
      tx'.loanIndex? = some j ∧ (l.apply tx).run = .ok (.ok la) ∧ (l.apply tx').run = .ok (.ok lb) ∧
      (∀ x, tx' = .loanAccept j → e'.loan.interestDue = .ok x → la.vault.exceedsOpenLimit x = .ok false) ∧
      (∀ b, la.broker? e'.brokerIndex = some b → b.coverAvailable.toRat < 10 ^ 96) ∧
      (∀ pt amount, tx' = .loanPay j pt amount → la.CreditFits j pt amount) ∧
      (∀ pt amount, tx' = .loanPay j pt amount → la.FeeFits j pt amount) ∧
      (la.apply tx').run = .ok (.error .tecPRECISION_LOSS) := by
  obtain ⟨l, la, lb, e', hr, he', hrel, ha, hb, hca, hcr, hfee, -, hrej⟩ := isolation_of_check (isoCoarseTxs 0)
    isoCoarsenTx isoDustTx 1 .tecPRECISION_LOSS false
    (fun l e' => l.loanTxBroker? isoCoarsenTx == some e'.brokerIndex) (by native_decide)
  exact ⟨l, la, lb, 1, e', isoCoarsenTx, isoDustTx, hr, he', by simpa using hrel,
    by simp [isoCoarsenTx, LendingTx.loanIndex?], rfl, ha, hb, fun _ h _ => absurd h (by simp [isoDustTx]), hca, hcr,
    hfee, hrej⟩

/-- Two pending loans on two brokers each fit the Open limit, on a reachable ledger. Accepting the first books
its interest, and the second can no longer be accepted. -/
lemma LendingLedger.broker_isolation_open_witness :
    ∃ (l la lb : LendingLedger) (j k : Nat) (e' : LoanEntry) (tx tx' : LendingTx),
      l.Reachable ∧ l.loan? j = some e' ∧ l.txBroker? tx = some k ∧ k ≠ e'.brokerIndex ∧
      tx'.loanIndex? = some j ∧ (l.apply tx).run = .ok (.ok la) ∧ (l.apply tx').run = .ok (.ok lb) ∧
      la.vault.assetsAvailable.toRat + la.vault.assetsDeployed.toRat <
        10 ^ 16 * (10 : ℚ) ^ la.vault.baseExponent ∧
      (∀ b, la.broker? e'.brokerIndex = some b → b.coverAvailable.toRat < 10 ^ 96) ∧
      (∀ pt amount, tx' = .loanPay j pt amount → la.CreditFits j pt amount) ∧
      (la.apply tx').run = .ok (.error .tecLIMIT_EXCEEDED) := by
  obtain ⟨l, la, lb, e', hr, he', hrel, ha, hb, hca, hcr, -, htot, hrej⟩ := isolation_of_check (isoOpenTxs 1)
    (.loanAccept 0) (.loanAccept 1) 1 .tecLIMIT_EXCEEDED true
    (fun l e' => l.txBroker? (.loanAccept 0) == some 0 && 0 != e'.brokerIndex) (by native_decide)
  simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne] at hrel
  exact ⟨l, la, lb, 1, 0, e', .loanAccept 0, .loanAccept 1, hr, he', hrel.1, hrel.2, rfl, ha, hb, htot rfl, hca,
    hcr, hrej⟩

/-- A late payment on a loan of one broker coarsens the vault, and a payment of 0.1 on a loan of another broker,
which passed before, is then rejected, on a reachable ledger. -/
lemma LendingLedger.broker_isolation_coarsened_witness :
    ∃ (l la lb : LendingLedger) (j k : Nat) (e' : LoanEntry) (tx tx' : LendingTx),
      l.Reachable ∧ l.loan? j = some e' ∧ l.txBroker? tx = some k ∧ k ≠ e'.brokerIndex ∧
      tx'.loanIndex? = some j ∧ (l.apply tx).run = .ok (.ok la) ∧ (l.apply tx').run = .ok (.ok lb) ∧
      (∀ x, tx' = .loanAccept j → e'.loan.interestDue = .ok x → la.vault.exceedsOpenLimit x = .ok false) ∧
      (∀ b, la.broker? e'.brokerIndex = some b → b.coverAvailable.toRat < 10 ^ 96) ∧
      (∀ pt amount, tx' = .loanPay j pt amount → la.CreditFits j pt amount) ∧
      (la.apply tx').run = .ok (.error .tecPRECISION_LOSS) := by
  obtain ⟨l, la, lb, e', hr, he', hrel, ha, hb, hca, hcr, -, -, hrej⟩ := isolation_of_check (isoCoarseTxs 1)
    isoCoarsenTx isoDustTx 1 .tecPRECISION_LOSS false
    (fun l e' => l.txBroker? isoCoarsenTx == some 1 && 1 != e'.brokerIndex) (by native_decide)
  simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne] at hrel
  exact ⟨l, la, lb, 1, 1, e', isoCoarsenTx, isoDustTx, hr, he', hrel.1, hrel.2, rfl, ha, hb,
    fun _ h _ => absurd h (by simp [isoDustTx]), hca, hcr, hrej⟩

end XRPL.Model.Lending
