import XRPL.Properties.Lending.Ledger.Common.BrokerSubsequenceDefs
import XRPL.Properties.Lending.Ledger.Common.LoanSubsequenceWitness

/-! # Witnesses for the transactions of one broker

On the coarsened vault of `CoarsenedVault.lean`, a VaultWithdraw lets a late payment of 0.1 on a loan of broker 0
pass, and in the broker's own transactions the same payment is rejected. A default whose cover is not on the coarse
grid moves less cover once another loan's late payment coarsens the vault, and the broker keeps more. -/

set_option linter.style.nativeDecide false

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open private feeFitsCheck feeFits_of_check from XRPL.Properties.Lending.Ledger.Common.IsolationWitness
open private LendingLedger.strictRun LendingLedger.strictRun_of_reaches LendingLedger.reaches_of_strictRun swStartTxs
  swTxs from XRPL.Properties.Lending.Ledger.Common.LoanSubsequenceWitness

/-- `c` before each transaction of `txs` applied in order from `m`, up to the first that fails. -/
private def alongCheck (c : LendingLedger → LendingTx → Bool) (m : LendingLedger) : List LendingTx → Bool
  | [] => true
  | tx :: txs =>
    c m tx &&
      match (m.apply tx).run with
      | .ok (.ok m') => alongCheck c m' txs
      | _ => true

private lemma of_alongCheck {c : LendingLedger → LendingTx → Bool} {start : LendingLedger} {txs : List LendingTx}
    (h : alongCheck c start txs = true) :
    ∀ (pre : List LendingTx) (m : LendingLedger) (tx : LendingTx), pre ++ [tx] <+: txs →
      LendingLedger.Reaches start pre m → c m tx = true := by
  induction txs generalizing start with
  | nil =>
    intro pre m tx hp _
    simpa using hp.length_le
  | cons t ts ih =>
    unfold alongCheck at h
    simp only [Bool.and_eq_true] at h
    obtain ⟨ht, hts⟩ := h
    intro pre m tx hp hr
    cases pre with
    | nil =>
      obtain rfl := hr.nil_inv
      obtain ⟨rfl, -⟩ := List.cons_prefix_cons.mp hp
      exact ht
    | cons p ps =>
      obtain ⟨rfl, hp'⟩ := List.cons_prefix_cons.mp hp
      obtain ⟨l₁, h₁, hr₁⟩ := hr.cons_inv
      rw [h₁] at hts
      exact ih hts ps m tx hp' hr₁

/-- An opening passes, broker `k`'s cover is below `10^96`, and a LoanPay is on an IOU vault with its fee beside the
cover below `10^89`. -/
private def brokerStepCheck (k : Nat) (m : LendingLedger) (tx : LendingTx) : Bool :=
  (!tx.isOpening ||
    match (m.apply tx).run with
    | .ok (.ok _) => true
    | _ => false) &&
  (match m.broker? k with
   | none => true
   | some b => decide (b.coverAvailable.toRat < 10 ^ 96)) &&
    match tx with
    | .loanPay i pt amount => !m.vault.numericType.isIntegral && feeFitsCheck m i pt amount
    | _ => true

private lemma along_of_brokerCheck {start : LendingLedger} {k : Nat} {txs : List LendingTx}
    (h : alongCheck (brokerStepCheck k) start txs = true) :
    start.OpeningsSucceedAlong txs ∧ start.BrokerUntrackedFitsAlong k txs := by
  have hstep := of_alongCheck h
  refine ⟨fun pre m tx hp hr ho => ?_, fun pre m tx hp hr => ⟨fun b hb => ?_, ?_⟩⟩
  · have hc := hstep pre m tx hp hr
    unfold brokerStepCheck at hc
    simp only [ho, Bool.not_true, Bool.false_or, Bool.and_eq_true] at hc
    obtain ⟨⟨hc, -⟩, -⟩ := hc
    split at hc
    · rename_i m' hm'
      exact ⟨m', hm'⟩
    · cases hc
  · have hc := hstep pre m tx hp hr
    unfold brokerStepCheck at hc
    simp only [hb, Bool.and_eq_true] at hc
    exact of_decide_eq_true hc.1.2
  · rintro i pt amount rfl
    have hc := hstep pre m _ hp hr
    unfold brokerStepCheck at hc
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at hc
    obtain ⟨-, hint, hfee⟩ := hc
    refine ⟨fun loan p _ _ hi => ?_, feeFits_of_check m i pt amount hfee⟩
    rw [hi] at hint
    cases hint

/-- From the ledger `s` after `swStartTxs`: `swTxs` all pass, the openings pass and the untracked balances fit along
broker 0's own transactions, and those fail. -/
private def bsCheck : Bool :=
  match cwGenesis.run swStartTxs with
  | .error _ => false
  | .ok s =>
    (LendingLedger.strictRun s swTxs).isSome &&
      alongCheck (brokerStepCheck (s.aloneBrokerIndex 0)) s (s.brokerSubsequence 0 swTxs) &&
      (LendingLedger.strictRun s (s.brokerSubsequence 0 swTxs)).isNone

/-- A VaultWithdraw on a coarsened vault lets a late payment of 0.1 on a loan of broker 0 pass. In broker 0's own
transactions, without the VaultWithdraw, the same payment is rejected. -/
lemma LendingLedger.broker_subsequence_witness :
    ∃ (start l : LendingLedger) (txs : List LendingTx) (k : Nat),
      start.Reachable ∧ LendingLedger.Reaches start txs l ∧
      start.OpeningsSucceedAlong (start.brokerSubsequence k txs) ∧
      start.BrokerUntrackedFitsAlong (start.aloneBrokerIndex k) (start.brokerSubsequence k txs) ∧
      ¬ ∃ m, LendingLedger.Reaches start (start.brokerSubsequence k txs) m := by
  have h : bsCheck = true := by native_decide
  unfold bsCheck at h
  split at h
  · cases h
  rename_i s hs
  simp only [Bool.and_eq_true, Option.isSome_iff_exists, Option.isNone_iff_eq_none] at h
  obtain ⟨⟨⟨l, hl⟩, hfits⟩, hfail⟩ := h
  obtain ⟨hopen, hfits⟩ := along_of_brokerCheck hfits
  refine ⟨s, l, swTxs, 0, LendingLedger.Reachable.of_run cwGenesis_genesis hs,
    LendingLedger.reaches_of_strictRun hl, hopen, hfits, ?_⟩
  rintro ⟨m, hm⟩
  rw [LendingLedger.strictRun_of_reaches hm] at hfail
  cases hfail

/-- A deposit, broker 1 with cover 2 at a CoverRateMinimum of 10%, loan A of 700000000000000 on broker 0 at a late
rate of 100%, loan B of 15 on broker 1 in one payment, and a close 800 days on, when both are late. -/
private def cvSetupTxs : List LendingTx :=
  [.vaultDeposit 0 (cwAmount 8999990000000000 (-1)) false,
   .close 1001,
   .loanBrokerCreate ⟨none, none, none, none⟩,
   .loanBrokerCreate ⟨none, none, some 10000, some 100000⟩,
   .loanBrokerCoverDeposit 1 (cwAmount 2000000000000000 (-15)),
   .loanSet 0 ⟨false, 7000000000000000000, -4⟩ (cwRates 100000) cwFees (some 86400) (some 5) (some 60) 0 false
     false,
   .loanSet 1 ⟨false, 1500000000000000000, -17⟩ (cwRates 0) cwFees (some 86400) (some 1) (some 60) 0 false false,
   .close 69207461]

/-- Loan A's late payment of 7000000000000000, which coarsens the vault, and the default of loan B. -/
private def cvTxs : List LendingTx :=
  [.loanPay 0 .late ⟨false, 7000000000000000000, -3⟩,
   .loanManage 1 .default]

/-- From the ledger `s` after `cvSetupTxs`: `cvTxs` and broker 1's own transactions all pass, and broker 1 ends
with a different cover. -/
private def cvCheck : Bool :=
  match cwGenesis.run cvSetupTxs with
  | .error _ => false
  | .ok s =>
    match LendingLedger.strictRun s cvTxs, LendingLedger.strictRun s (s.brokerSubsequence 1 cvTxs) with
    | some l, some m =>
      match l.broker? 1, m.broker? (s.aloneBrokerIndex 1) with
      | some b, some b' => decide (b'.coverAvailable.toRat ≠ b.coverAvailable.toRat)
      | _, _ => false
    | _, _ => false

/-- A late payment on loan A coarsens the vault, and the default of loan B on another broker then moves 1 of its
cover of 1.5. In the broker's own transactions the default moves all 1.5. -/
lemma LendingLedger.broker_subsequence_cover_witness :
    ∃ (start l : LendingLedger) (txs : List LendingTx) (k : Nat) (m : LendingLedger) (b b' : LoanBroker),
      start.Reachable ∧ LendingLedger.Reaches start txs l ∧
      LendingLedger.Reaches start (start.brokerSubsequence k txs) m ∧ l.broker? k = some b ∧
      m.broker? (start.aloneBrokerIndex k) = some b' ∧ b'.coverAvailable.toRat ≠ b.coverAvailable.toRat := by
  have h : cvCheck = true := by native_decide
  unfold cvCheck at h
  split at h
  · cases h
  rename_i s hs
  split at h
  · rename_i l m hl hm
    split at h
    · rename_i b b' hb hb'
      exact ⟨s, l, cvTxs, 1, m, b, b', LendingLedger.Reachable.of_run cwGenesis_genesis hs,
        LendingLedger.reaches_of_strictRun hl, LendingLedger.reaches_of_strictRun hm, hb, hb',
        of_decide_eq_true h⟩
    · cases h
  · cases h

end XRPL.Model.Lending
