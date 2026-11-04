import XRPL.Properties.Lending.Ledger.Common.AssetFlowDefs
import XRPL.Properties.Lending.Ledger.Common.IsolationWitness
import XRPL.Properties.Lending.Ledger.Common.LoanSubsequenceDefs

/-! # Witness for the transactions of one loan

On the coarsened vault of `CoarsenedVault.lean`, a VaultWithdraw takes AssetsAvailable below `10^16` base units,
and a late payment of 0.1 on loan C then passes. In the loan's own transactions the VaultWithdraw is left out, the
payment rounds to no credit and is rejected. -/

set_option linter.style.nativeDecide false

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault (WithdrawAmount)
open private feeFitsCheck feeFits_of_check from XRPL.Properties.Lending.Ledger.Common.IsolationWitness

/-- The transactions applied in order, `none` once one is rejected or fails. -/
private def LendingLedger.strictRun (l : LendingLedger) : List LendingTx → Option LendingLedger
  | [] => some l
  | tx :: txs =>
    match (l.apply tx).run with
    | .ok (.ok l') => LendingLedger.strictRun l' txs
    | _ => none

private lemma LendingLedger.strictRun_of_reaches {start l : LendingLedger} {txs : List LendingTx}
    (h : LendingLedger.Reaches start txs l) : start.strictRun txs = some l := by
  induction txs generalizing start with
  | nil =>
    rw [h.nil_inv]
    rfl
  | cons tx txs ih =>
    obtain ⟨l₁, h₁, hr⟩ := h.cons_inv
    simp only [LendingLedger.strictRun, h₁]
    exact ih hr

private lemma LendingLedger.reaches_of_strictRun {start l : LendingLedger} {txs : List LendingTx}
    (h : start.strictRun txs = some l) : LendingLedger.Reaches start txs l := by
  induction txs generalizing start with
  | nil =>
    simp only [LendingLedger.strictRun, Option.some.injEq] at h
    exact h ▸ .refl
  | cons tx txs ih =>
    simp only [LendingLedger.strictRun] at h
    split at h
    · rename_i l₁ h₁
      simpa using (LendingLedger.Reaches.single h₁).trans (ih h)
    · cases h

/-- The cover of loan `i`'s broker is below `10^96`, and a LoanPay is on an IOU vault with its fee beside the
cover below `10^89`. -/
private def untrackedCheck (m : LendingLedger) (i : Nat) (tx : LendingTx) : Bool :=
  (match m.loan? i with
   | none => true
   | some e =>
     match m.broker? e.brokerIndex with
     | none => true
     | some b => decide (b.coverAvailable.toRat < 10 ^ 96)) &&
    match tx with
    | .loanPay _ pt amount => !m.vault.numericType.isIntegral && feeFitsCheck m i pt amount
    | _ => true

private lemma untracked_of_check {m : LendingLedger} {i : Nat} {tx : LendingTx} (h : untrackedCheck m i tx = true) :
    (∀ (e : LoanEntry) (b : LoanBroker), m.loan? i = some e → m.broker? e.brokerIndex = some b →
      b.coverAvailable.toRat < 10 ^ 96) ∧
    ∀ (paymentType : LoanPaymentType) (amount : Number), tx = .loanPay i paymentType amount →
      m.CreditFits i paymentType amount ∧ m.FeeFits i paymentType amount := by
  unfold untrackedCheck at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨hcov, hpay⟩ := h
  refine ⟨fun e b he hb => ?_, ?_⟩
  · simp only [he, hb] at hcov
    exact of_decide_eq_true hcov
  · rintro pt amount rfl
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at hpay
    refine ⟨fun loan p _ _ hi => ?_, feeFits_of_check m i pt amount hpay.2⟩
    rw [hi] at hpay
    cases hpay.1

/-- `untrackedCheck` before each transaction of `txs` applied in order from `m`, up to the first that fails. -/
private def untrackedAlongCheck (m : LendingLedger) (i : Nat) : List LendingTx → Bool
  | [] => true
  | tx :: txs =>
    untrackedCheck m i tx &&
      match (m.apply tx).run with
      | .ok (.ok m') => untrackedAlongCheck m' i txs
      | _ => true

private lemma untrackedFitsAlong_of_check {start : LendingLedger} {i : Nat} {txs : List LendingTx}
    (h : untrackedAlongCheck start i txs = true) : start.UntrackedFitsAlong i txs := by
  induction txs generalizing start with
  | nil =>
    intro pre m tx hp _
    simpa using hp.length_le
  | cons t ts ih =>
    unfold untrackedAlongCheck at h
    simp only [Bool.and_eq_true] at h
    obtain ⟨ht, hts⟩ := h
    intro pre m tx hp hr
    cases pre with
    | nil =>
      obtain rfl := hr.nil_inv
      obtain ⟨rfl, -⟩ := List.cons_prefix_cons.mp hp
      exact untracked_of_check ht
    | cons p ps =>
      obtain ⟨rfl, hp'⟩ := List.cons_prefix_cons.mp hp
      obtain ⟨l₁, h₁, hr₁⟩ := hr.cons_inv
      rw [h₁] at hts
      exact ih hts ps m tx hp' hr₁

/-- The ledger after the FV_M4_27 repro run up to loan A's late payment, which coarsened the vault. -/
private def swStartTxs : List LendingTx := cwTxs.take 10

/-- A close in the redemption phase, a VaultWithdraw of 874246907153727.1, and loan C's late payment of 0.1. -/
private def swTxs : List LendingTx :=
  [.close (1000 + 900 * 86400 + 1),
   .vaultWithdraw 0 (.vaultAssets (cwAmount 8742469071537271 (-1))),
   .loanPay 2 .late ⟨false, 1000000000000000000, -19⟩]

/-- From the ledger `s` after `swStartTxs`: `swTxs` all pass, loan C is active, the untracked balances fit along
its own transactions, and those fail. -/
private def swCheck : Bool :=
  match cwGenesis.run swStartTxs with
  | .error _ => false
  | .ok s =>
    (s.strictRun swTxs).isSome &&
      (match s.loan? (s.aloneIndex 2) with
       | none => false
       | some e =>
         match s.broker? e.brokerIndex with
         | none => false
         | some b =>
           match e.loan.withBroker b with
           | .ok loan => !loan.isPending
           | .error _ => false) &&
      untrackedAlongCheck s (s.aloneIndex 2) (s.loanSubsequence 2 swTxs) &&
      (s.strictRun (s.loanSubsequence 2 swTxs)).isNone

/-- A VaultWithdraw on a coarsened vault lets a late payment of 0.1 on loan C pass. In loan C's own transactions,
without the VaultWithdraw, the same payment is rejected. -/
lemma LendingLedger.loan_subsequence_witness :
    ∃ (start l : LendingLedger) (txs : List LendingTx) (i : Nat) (pre post : List LendingTx) (m : LendingLedger)
      (loan : Loan),
      start.Reachable ∧ LendingLedger.Reaches start txs l ∧ txs = pre ++ post ∧
      LendingLedger.Reaches start (start.loanSubsequence i pre) m ∧ m.LoanAt (start.aloneIndex i) loan ∧
      loan.isPending = false ∧ start.UntrackedFitsAlong (start.aloneIndex i) (start.loanSubsequence i txs) ∧
      ¬ ∃ m', LendingLedger.Reaches start (start.loanSubsequence i txs) m' := by
  have h : swCheck = true := by native_decide
  unfold swCheck at h
  split at h
  · cases h
  rename_i s hs
  simp only [Bool.and_eq_true, Option.isSome_iff_exists, Option.isNone_iff_eq_none] at h
  obtain ⟨⟨⟨⟨l, hl⟩, hloan⟩, hfits⟩, hfail⟩ := h
  split at hloan
  · cases hloan
  rename_i e he
  split at hloan
  · cases hloan
  rename_i b hb
  split at hloan
  · rename_i loan hw
    simp only [Bool.not_eq_true'] at hloan
    refine ⟨s, l, swTxs, 2, [], swTxs, s, loan, LendingLedger.Reachable.of_run cwGenesis_genesis hs,
      LendingLedger.reaches_of_strictRun hl, rfl, .refl, ⟨e, b, he, hb, hw⟩, hloan,
      untrackedFitsAlong_of_check hfits, ?_⟩
    rintro ⟨m', hm'⟩
    rw [LendingLedger.strictRun_of_reaches hm'] at hfail
    cases hfail
  · cases hloan

end XRPL.Model.Lending
