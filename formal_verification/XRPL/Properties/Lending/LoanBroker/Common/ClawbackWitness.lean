import XRPL.Properties.Lending.LoanBroker.Common.WitnessSupport
import XRPL.Properties.Lending.Ledger.Common.CoverWitness
import XRPL.Properties.Lending.Ledger.Common.ScaleInv
import XRPL.Properties.Lending.Ledger.Common.VaultSteps

/-! # Witnesses for the clawback theorems

Runs on a reachable broker of a vault with base exponent `-6`, and on the broker of the ledger run of
`CoverWitness.lean`, whose cover a LoanPay fee takes to `2000001` at the scale `10^-10`. -/

set_option linter.style.nativeDecide false

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault (Vault)

open private rcGenesis rcTxs rcGenesis_genesis from XRPL.Properties.Lending.Ledger.Common.CoverWitness

/-- `waHalves` clawed from `wbHeld`, then again, and `waThree` at once. -/
private def wrClaw1 : LoanBrokerCoverResult := wResultOf (wbHeld.coverClawback wvBase6 (some waHalves))
private def wrClaw2 : LoanBrokerCoverResult :=
  wResultOf (wrClaw1.loanBroker'.coverClawback wvBase6 (some waHalves))
private def wrClaw3 : LoanBrokerCoverResult := wResultOf (wbHeld.coverClawback wvBase6 (some waThree))

/-- Proof body of `cover_split_clawback_attained`. -/
lemma LoanBroker.coverClawback_split_witness :
    ∃ (lb : LoanBroker) (base : Int) (v : Vault) (a b c : STAmount) (r1 r2 s : LoanBrokerCoverResult),
      lb.Reachable base ∧
      v.baseExponent = base ∧ v.numericType = lb.numericType ∧
      a.Canonical ∧ b.Canonical ∧ c.Canonical ∧
      a.mNumericType = lb.numericType ∧ b.mNumericType = lb.numericType ∧ c.mNumericType = lb.numericType ∧
      0 < a.toRat ∧ 0 < b.toRat ∧ c.toRat = a.toRat + b.toRat ∧
      lb.canCoverClawback v (some a) = .ok .tesSUCCESS ∧ (lb.coverClawback v (some a)).run = .ok (.ok r1) ∧
      r1.loanBroker'.canCoverClawback v (some b) = .ok .tesSUCCESS ∧
      (r1.loanBroker'.coverClawback v (some b)).run = .ok (.ok r2) ∧
      lb.canCoverClawback v (some c) = .ok .tesSUCCESS ∧ (lb.coverClawback v (some c)).run = .ok (.ok s) ∧
      r2.loanBroker'.toExact.coverAvailable ≠ s.loanBroker'.toExact.coverAvailable :=
  ⟨wbHeld, -6, wvBase6, waHalves, waHalves, waThree, wrClaw1, wrClaw2, wrClaw3, wbHeld_reachable,
    by native_decide, by native_decide,
    STAmount.canonical_of_canonicalB _ (by native_decide), STAmount.canonical_of_canonicalB _ (by native_decide),
    STAmount.canonical_of_canonicalB _ (by native_decide), by native_decide, by native_decide, by native_decide,
    by native_decide, by native_decide, by native_decide, by native_decide, by native_decide, by native_decide,
    by native_decide, by native_decide, by native_decide, by native_decide⟩

/-- The ledger at the end of `txs` from `rcGenesis`, with its broker 0. -/
private def rcEnd (txs : List LendingTx) : Option (LendingLedger × LoanBroker) :=
  match rcGenesis.run txs with
  | .ok l => (l.broker? 0).map fun b => (l, b)
  | .error _ => none

/-- Broker 0 at the end of a run from `rcGenesis` is on a reachable ledger, in the vault's asset. -/
private lemma rcEnd_reachable (txs : List LendingTx) (l : LendingLedger) (b : LoanBroker)
    (h : rcEnd txs = some (l, b)) :
    l.Reachable ∧ l.broker? 0 = some b ∧ l.vault.numericType = b.numericType ∧
      (b.numericType.isIntegral = true → b.numericType.maxValue.toNat ≤ maxRep.toNat) := by
  unfold rcEnd at h
  split at h
  · rename_i l₀ hl
    cases hb : l₀.broker? 0 with
    | none => simp [hb] at h
    | some b₀ =>
      simp only [hb, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have hr : l₀.Reachable := LendingLedger.Reachable.of_run rcGenesis_genesis hl
      have hbnt := hr.scaleInv.brokers 0 _ hb
      exact ⟨hr, hb, hbnt.symm, by rw [hbnt]; exact hr.holdsAsset.maxValue_le⟩
  · cases h

/-- A full clawback at the end of `rcTxs` claws more than CoverAvailable − minCover and leaves less than minCover. -/
private def rcAllCheck : Bool :=
  match rcEnd rcTxs with
  | some (l, b) =>
    match (b.coverClawback l.vault none).run,
        minimumBrokerCover b.numericType b.debtTotal b.coverRateMinimum l.vault.baseExponent with
    | .ok (.ok r), .ok m => decide (b.toExact.coverAvailable - m.toRat < r.amount'.toRat) &&
        decide (r.loanBroker'.toExact.coverAvailable < m.toRat)
    | _, _ => false
  | none => false

private lemma rcAllCheck_true : rcAllCheck = true := by native_decide

/-- A full clawback on a reachable broker that claws more than CoverAvailable − minCover and leaves less than
minCover. -/
private lemma rcAll :
    ∃ (l : LendingLedger) (lb : LoanBroker) (res : LoanBrokerCoverResult) (m : Number),
      l.Reachable ∧ l.broker? 0 = some lb ∧ l.vault.numericType = lb.numericType ∧
      (lb.numericType.isIntegral = true → lb.numericType.maxValue.toNat ≤ maxRep.toNat) ∧
      minimumBrokerCover lb.numericType lb.debtTotal lb.coverRateMinimum l.vault.baseExponent = .ok m ∧
      (lb.coverClawback l.vault none).run = .ok (.ok res) ∧
      lb.toExact.coverAvailable - m.toRat < res.amount'.toRat ∧ res.loanBroker'.toExact.coverAvailable < m.toRat := by
  have h := rcAllCheck_true
  unfold rcAllCheck at h
  split at h
  · rename_i l lb hend
    split at h
    · rename_i r m hok hm
      obtain ⟨hr, hb, hnt, hmax⟩ := rcEnd_reachable rcTxs l lb hend
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h
      exact ⟨l, lb, r, m, hr, hb, hnt, hmax, hm, hok, h.1, h.2⟩
    · cases h
  · cases h

/-- Proof body of `LoanBroker.roundedCoverClawback_all_attained`. -/
lemma LoanBroker.roundedCoverClawback_all_witness :
    ∃ (l : LendingLedger) (j : Nat) (lb : LoanBroker) (amount : Option STAmount) (res : LoanBrokerCoverResult)
      (minimumCover : Number),
      l.Reachable ∧ l.broker? j = some lb ∧ l.vault.numericType = lb.numericType ∧
      (lb.numericType.isIntegral = true → lb.numericType.maxValue.toNat ≤ maxRep.toNat) ∧
      (∀ a ∈ amount, a.CanonicalOrZero ∧ a.mNumericType = lb.numericType ∧ 0 ≤ a.toRat) ∧
      (amount = none ∨ ∃ a, amount = some a ∧ a.isZero = true) ∧
      minimumBrokerCover lb.numericType lb.debtTotal lb.coverRateMinimum l.vault.baseExponent = .ok minimumCover ∧
      (lb.coverClawback l.vault amount).run = .ok (.ok res) ∧
      lb.toExact.coverAvailable - minimumCover.toRat < res.amount'.toRat ∧
      res.loanBroker'.toExact.coverAvailable < minimumCover.toRat := by
  obtain ⟨l, lb, res, m, hr, hb, hnt, hmax, hm, hok, hclaw, hcov⟩ := rcAll
  exact ⟨l, 0, lb, none, res, m, hr, hb, hnt, hmax, (fun a ha => by cases ha), Or.inl rfl, hm, hok, hclaw, hcov⟩

/-- Proof body of `LoanBroker.cover_keeps_minimum_clawback_attained`. -/
lemma LoanBroker.coverClawback_keeps_minimum_witness :
    ∃ (l : LendingLedger) (j : Nat) (lb : LoanBroker) (amount : Option STAmount) (res : LoanBrokerCoverResult)
      (minimumCover : Number),
      l.Reachable ∧ l.broker? j = some lb ∧ l.vault.numericType = lb.numericType ∧
      (lb.numericType.isIntegral = true → lb.numericType.maxValue.toNat ≤ maxRep.toNat) ∧
      (∀ a ∈ amount, a.CanonicalOrZero ∧ a.mNumericType = lb.numericType ∧ 0 ≤ a.toRat) ∧
      minimumBrokerCover lb.numericType lb.debtTotal lb.coverRateMinimum l.vault.baseExponent = .ok minimumCover ∧
      (lb.coverClawback l.vault amount).run = .ok (.ok res) ∧
      res.loanBroker'.toExact.coverAvailable < minimumCover.toRat := by
  obtain ⟨l, lb, res, m, hr, hb, hnt, hmax, hm, hok, -, hcov⟩ := rcAll
  exact ⟨l, 0, lb, none, res, m, hr, hb, hnt, hmax, (fun a ha => by cases ha), hm, hok, hcov⟩

/-- A clawback of `2000000`, more than CoverAvailable − minCover. -/
private def rcCappedAmount : STAmount := cwAmount 2000000000000000 (-9)

/-- A clawback of `rcCappedAmount` at the end of `rcTxs` claws more than CoverAvailable − minCover. -/
private def rcCappedCheck : Bool :=
  match rcEnd rcTxs with
  | some (l, b) =>
    match (b.coverClawback l.vault (some rcCappedAmount)).run,
        minimumBrokerCover b.numericType b.debtTotal b.coverRateMinimum l.vault.baseExponent with
    | .ok (.ok r), .ok m => decide (rcCappedAmount.mNumericType = b.numericType) &&
        decide ((⌊min rcCappedAmount.toRat (b.toExact.coverAvailable - m.toRat) /
          10 ^ l.vault.baseExponent⌋ : ℚ) * 10 ^ l.vault.baseExponent < r.amount'.toRat)
    | _, _ => false
  | none => false

private lemma rcCappedCheck_true : rcCappedCheck = true := by native_decide

/-- Proof body of `LoanBroker.roundedCoverClawback_capped_attained`. -/
lemma LoanBroker.roundedCoverClawback_capped_witness :
    ∃ (l : LendingLedger) (j : Nat) (lb : LoanBroker) (minimumCover : Number) (a : STAmount)
      (res : LoanBrokerCoverResult),
      l.Reachable ∧ l.broker? j = some lb ∧ l.vault.numericType = lb.numericType ∧
      minimumBrokerCover lb.numericType lb.debtTotal lb.coverRateMinimum l.vault.baseExponent = .ok minimumCover ∧
      (a.CanonicalOrZero ∧ a.mNumericType = lb.numericType ∧ 0 ≤ a.toRat) ∧ a.isZero = false ∧
      (lb.coverClawback l.vault (some a)).run = .ok (.ok res) ∧
      (⌊min a.toRat (lb.toExact.coverAvailable - minimumCover.toRat) / 10 ^ l.vault.baseExponent⌋ : ℚ) *
        10 ^ l.vault.baseExponent < res.amount'.toRat := by
  have h := rcCappedCheck_true
  unfold rcCappedCheck at h
  split at h
  · rename_i l lb hend
    split at h
    · rename_i r m hok hm
      obtain ⟨hr, hb, hnt, -⟩ := rcEnd_reachable rcTxs l lb hend
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h
      exact ⟨l, 0, lb, m, rcCappedAmount, r, hr, hb, hnt, hm,
        ⟨Or.inl (STAmount.canonical_of_canonicalB _ (by native_decide)), h.1, by native_decide⟩, by native_decide,
        hok, h.2⟩
    · cases h
  · cases h

/-- `rcTxs`, then a default of loan C, which leaves a cover of `1999999.9999999999`, and loan B paid off, which
leaves no debt. -/
private def rcPaidTxs : List LendingTx :=
  rcTxs ++ [.loanManage 2 .default, .loanPay 1 .regular ⟨false, 2005000000000000000, -12⟩]

/-- A full clawback at the end of `rcPaidTxs` passes its checks and is notLawful. -/
private def rcNegativeCheck : Bool :=
  match rcEnd rcPaidTxs with
  | some (l, b) =>
    match b.canCoverClawback l.vault none, (b.coverClawback l.vault none).run with
    | .ok .tesSUCCESS, .error .notLawful => true
    | _, _ => false
  | none => false

private lemma rcNegativeCheck_true : rcNegativeCheck = true := by native_decide

/-- Proof body of `LoanBroker.cover_total_clawback_attained`. -/
lemma LoanBroker.coverClawback_lawful_total_witness :
    ∃ (l : LendingLedger) (j : Nat) (lb : LoanBroker) (amount : Option STAmount),
      l.Reachable ∧ l.broker? j = some lb ∧ l.vault.numericType = lb.numericType ∧
      (lb.numericType.isIntegral = true → lb.numericType.maxValue.toNat ≤ maxRep.toNat) ∧
      (∀ a ∈ amount, a.CanonicalOrZero ∧ a.mNumericType = lb.numericType ∧ 0 ≤ a.toRat) ∧
      lb.canCoverClawback l.vault amount = .ok .tesSUCCESS ∧
      (lb.coverClawback l.vault amount).run = .error .notLawful := by
  have h := rcNegativeCheck_true
  unfold rcNegativeCheck at h
  split at h
  · rename_i l lb hend
    split at h
    · rename_i hcan hrun
      obtain ⟨hr, hb, hnt, hmax⟩ := rcEnd_reachable rcPaidTxs l lb hend
      exact ⟨l, 0, lb, none, hr, hb, hnt, hmax, (fun a ha => by cases ha), hcan, hrun⟩
    · cases h
  · cases h

end XRPL.Model.Lending
