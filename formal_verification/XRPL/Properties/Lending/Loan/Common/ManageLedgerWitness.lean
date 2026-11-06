import XRPL.Properties.Lending.Ledger.Common.CoarsenedVault
import XRPL.Properties.Lending.Ledger.Common.CoverPrecisionWitness
import XRPL.Properties.Lending.Loan.Common.ManageDefs

/-! # Witnesses for the LoanManage defaults on a reachable ledger

Each witness is a run from a new IOU vault, then a successful default, checked by `native_decide`. The runs are the
coarsened run of `CoarsenedVault.lean`, the cover precision run of `CoverPrecisionWitness.lean`, and a run where a
broker covers a loan of 100 in full. -/

set_option linter.style.nativeDecide false

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault (Vault)

open private cpGenesis cpGenesis_genesis cpTxs from XRPL.Properties.Lending.Ledger.Common.CoverPrecisionWitness

/-- The loan at `i` read with its broker's ledger copy, as every loan transaction reads it. -/
private def readLoan? (l : LendingLedger) (i : Nat) : Option Loan :=
  match l.loan? i with
  | some e =>
    match l.broker? e.brokerIndex with
    | some b =>
      match e.loan.withBroker b with
      | .ok loan => some loan
      | .error _ => none
    | none => none
  | none => none

private lemma readLoan?_some {l : LendingLedger} {i : Nat} {loan : Loan} (h : readLoan? l i = some loan) :
    l.LoanAt i loan := by
  unfold readLoan? at h
  split at h
  · rename_i e he
    split at h
    · rename_i b hb
      split at h
      · rename_i loan' hw
        obtain rfl := Option.some.inj h
        exact ⟨e, b, he, hb, hw⟩
      · cases h
    · cases h
  · cases h

/-- Defaulting loan C of the cover precision run takes `1.0000000001` off the cover of `1000000000001` and leaves
`10^12`. -/
private def coverInexactCheck : Bool :=
  match cpGenesis.run cpTxs with
  | .ok l =>
    match (l.apply (.loanManage 2 .default)).run with
    | .ok (.ok l') =>
      match readLoan? l 2, readLoan? l' 2 with
      | some loan, some loan' =>
        match (loan.manageDefault l.vault).run with
        | .ok (.ok r) =>
          decide (loan'.broker.coverAvailable.toRat ≠ loan.broker.coverAvailable.toRat - r.amountToPool.toRat)
        | _ => false
      | _, _ => false
    | _ => false
  | .error _ => false

private lemma coverInexactCheck_true : coverInexactCheck = true := by native_decide

/-- A broker at 100% minimum cover and 100% liquidation with 5000 of cover lends loans A of 100 and B of 900,
both due after one day, and the ledger closes past A's grace period. -/
private def coveredTxs : List LendingTx :=
  [.vaultDeposit 0 (cwAmount 1000000000000000 (-11)) false,
   .close 1001,
   .loanBrokerCreate ⟨none, none, some 100000, some 100000⟩,
   .loanBrokerCoverDeposit 0 (cwAmount 5000000000000000 (-12)),
   .loanSet 0 ⟨false, 1000000000000000000, -16⟩ (cwRates 0) cwFees (some 86400) (some 1) (some 60) 0 false false,
   .loanSet 0 ⟨false, 9000000000000000000, -16⟩ (cwRates 0) cwFees (some 86400) (some 1) (some 60) 0 false false,
   .close 90000]

/-- Defaulting loan A: DebtTotal is 1000, so the liquidation amount is 1000, and the cover pays all 100. -/
private def coveredCheck : Bool :=
  match cwGenesis.run coveredTxs with
  | .ok l =>
    match (l.apply (.loanManage 0 .default)).run, readLoan? l 0 with
    | .ok (.ok _), some loan =>
      match (loan.manageDefault l.vault).run,
          tenthBipsOfValue loan.broker.debtTotal loan.broker.coverRateMinimum .upward with
      | .ok (.ok r), .ok minimumCover =>
        match tenthBipsOfValue minimumCover loan.broker.coverRateLiquidation .upward with
        | .ok liquidationAmount =>
          decide (r.amountToPool.toRat - min (min liquidationAmount.toRat loan.principalOutstanding.toRat)
              loan.broker.coverAvailable.toRat = 0)
        | .error _ => false
      | _, _ => false
    | _, _ => false
  | .error _ => false

private lemma coveredCheck_true : coveredCheck = true := by native_decide

/-- Defaulting loan B of the coarsened run: the cover pays the vault `-0.9`, which is 9.9999 units of the scale of
AssetsAvailable' below the capped liquidation amount of `0.09999`. -/
private def negativeCoverCheck : Bool :=
  match cwGenesis.run cwTxs with
  | .ok l =>
    match (l.apply (.loanManage 1 .default)).run, readLoan? l 1 with
    | .ok (.ok l'), some loan =>
      match (loan.manageDefault l.vault).run,
          tenthBipsOfValue loan.broker.debtTotal loan.broker.coverRateMinimum .upward with
      | .ok (.ok r), .ok minimumCover =>
        match tenthBipsOfValue minimumCover loan.broker.coverRateLiquidation .upward,
            numberExponent l'.vault.assetsAvailable l.vault.baseExponent l.vault.numericType with
        | .ok liquidationAmount, .ok ex =>
          decide (r.amountToPool.toRat < 0) &&
            decide (min (min liquidationAmount.toRat loan.principalOutstanding.toRat)
              loan.broker.coverAvailable.toRat - r.amountToPool.toRat = (99999 / 10000 : ℚ) * 10 ^ ex)
        | _, _ => false
      | _, _ => false
    | _, _ => false
  | .error _ => false

private lemma negativeCoverCheck_true : negativeCoverCheck = true := by native_decide

/-- `0.09`. -/
private def smallCover : Number := ⟨false, 9000000000000000000, -20⟩

/-- Loan B's default on the coarsened run against the same ledger with only `0.09` of cover on its broker: the
cover of `0.1` pays the vault `-0.9` and loses `1.9`, the cover of `0.09` pays nothing and loses 1. -/
private def coverMonotoneCheck : Bool :=
  match cwGenesis.run cwTxs with
  | .ok l =>
    match l.loan? 1 with
    | some e =>
      match l.broker? e.brokerIndex with
      | some b =>
        match RawLoanBroker.to_lawful { b.toRawLoanBroker with coverAvailable := smallCover } with
        | .ok b₁ =>
          match (l.apply (.loanManage 1 .default)).run,
              (({ l with brokers := l.brokers.set e.brokerIndex (some b₁) } : LendingLedger).apply
                (.loanManage 1 .default)).run with
          | .ok (.ok l'), .ok (.ok l₁') =>
            decide (b₁.coverAvailable.toRat ≤ b.coverAvailable.toRat) &&
              decide (l.vault.toExact.assetsTotal - l₁'.vault.toExact.assetsTotal <
                l.vault.toExact.assetsTotal - l'.vault.toExact.assetsTotal)
          | _, _ => false
        | .error _ => false
      | none => false
    | none => false
  | .error _ => false

private lemma coverMonotoneCheck_true : coverMonotoneCheck = true := by native_decide

/-- A default on a reachable IOU ledger can leave CoverAvailable' ≠ CoverAvailable − defaultCovered. The cover
holds 23 digits of base units, the `Number` difference keeps 19. -/
lemma LendingLedger.manageDefault_coverAvailable_witness :
    ∃ (l l' : LendingLedger) (i : Nat) (loan loan' : Loan) (r : LoanWithAmounts Vault),
      l.Reachable ∧ (l.apply (.loanManage i .default)).run = .ok (.ok l') ∧ l.LoanAt i loan ∧
      l'.LoanAt i loan' ∧ (loan.manageDefault l.vault).run = .ok (.ok r) ∧
      loan'.broker.coverAvailable.toRat ≠ loan.broker.coverAvailable.toRat - r.amountToPool.toRat := by
  have h := coverInexactCheck_true
  unfold coverInexactCheck at h
  split at h
  case h_2 => cases h
  rename_i l hl
  split at h
  case h_2 => cases h
  rename_i l' hl'
  split at h
  case h_2 => cases h
  rename_i loan loan' hat hat'
  split at h
  case h_2 => cases h
  rename_i r hdef
  exact ⟨l, l', 2, loan, loan', r, LendingLedger.Reachable.of_run cpGenesis_genesis hl, hl', readLoan?_some hat,
    readLoan?_some hat', hdef, of_decide_eq_true h⟩

/-- A default on a reachable ledger where defaultCovered reaches min(liquidationAmount, PrincipalOutstanding,
CoverAvailable). -/
lemma LendingLedger.manageDefault_cover_upper_bound_witness :
    ∃ (l l' : LendingLedger) (i : Nat) (loan : Loan) (minimumCover liquidationAmount : Number)
      (r : LoanWithAmounts Vault),
      l.Reachable ∧ (l.apply (.loanManage i .default)).run = .ok (.ok l') ∧ l.LoanAt i loan ∧
      (loan.manageDefault l.vault).run = .ok (.ok r) ∧
      tenthBipsOfValue loan.broker.debtTotal loan.broker.coverRateMinimum .upward = .ok minimumCover ∧
      tenthBipsOfValue minimumCover loan.broker.coverRateLiquidation .upward = .ok liquidationAmount ∧
      r.amountToPool.toRat -
        min (min liquidationAmount.toRat loan.principalOutstanding.toRat) loan.broker.coverAvailable.toRat = 0 := by
  have h := coveredCheck_true
  unfold coveredCheck at h
  split at h
  case h_2 => cases h
  rename_i l hl
  split at h
  case h_2 => cases h
  rename_i l' loan hl' hat
  split at h
  case h_2 => cases h
  rename_i r minimumCover hdef hmin
  split at h
  case h_2 => cases h
  rename_i liquidationAmount hliq
  exact ⟨l, l', 0, loan, minimumCover, liquidationAmount, r, LendingLedger.Reachable.of_run cwGenesis_genesis hl,
    hl', readLoan?_some hat, hdef, hmin, hliq, of_decide_eq_true h⟩

/-- A default of loan B on the coarsened run. The cover pays the vault `-0.9`, which is 9.9999 units of the scale of
AssetsAvailable' below the capped liquidation amount. -/
private lemma negative_cover_reachable :
    ∃ (l l' : LendingLedger) (i : Nat) (loan : Loan) (minimumCover liquidationAmount : Number)
      (r : LoanWithAmounts Vault) (e : Int),
      l.Reachable ∧ (l.apply (.loanManage i .default)).run = .ok (.ok l') ∧ l.LoanAt i loan ∧
      (loan.manageDefault l.vault).run = .ok (.ok r) ∧
      tenthBipsOfValue loan.broker.debtTotal loan.broker.coverRateMinimum .upward = .ok minimumCover ∧
      tenthBipsOfValue minimumCover loan.broker.coverRateLiquidation .upward = .ok liquidationAmount ∧
      numberExponent l'.vault.assetsAvailable l.vault.baseExponent l.vault.numericType = .ok e ∧
      r.amountToPool.toRat < 0 ∧
      min (min liquidationAmount.toRat loan.principalOutstanding.toRat) loan.broker.coverAvailable.toRat -
        r.amountToPool.toRat = (99999 / 10000 : ℚ) * 10 ^ e := by
  have h := negativeCoverCheck_true
  unfold negativeCoverCheck at h
  split at h
  case h_2 => cases h
  rename_i l hl
  split at h
  case h_2 => cases h
  rename_i l' loan hl' hat
  split at h
  case h_2 => cases h
  rename_i r minimumCover hdef hmin
  split at h
  case h_2 => cases h
  rename_i liquidationAmount e hliq he
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨l, l', 1, loan, minimumCover, liquidationAmount, r, e, LendingLedger.Reachable.of_run cwGenesis_genesis hl,
    hl', readLoan?_some hat, hdef, hmin, hliq, he, h.1, h.2⟩

/-- A default on a reachable coarsened vault where the capped liquidation amount exceeds defaultCovered by
9.9999 units of the scale of AssetsAvailable'. -/
lemma LendingLedger.manageDefault_cover_lower_bound_witness :
    ∃ (l l' : LendingLedger) (i : Nat) (loan : Loan) (minimumCover liquidationAmount : Number)
      (r : LoanWithAmounts Vault) (e : Int),
      l.Reachable ∧ (l.apply (.loanManage i .default)).run = .ok (.ok l') ∧ l.LoanAt i loan ∧
      (loan.manageDefault l.vault).run = .ok (.ok r) ∧
      tenthBipsOfValue loan.broker.debtTotal loan.broker.coverRateMinimum .upward = .ok minimumCover ∧
      tenthBipsOfValue minimumCover loan.broker.coverRateLiquidation .upward = .ok liquidationAmount ∧
      numberExponent l'.vault.assetsAvailable l.vault.baseExponent l.vault.numericType = .ok e ∧
      min (min liquidationAmount.toRat loan.principalOutstanding.toRat) loan.broker.coverAvailable.toRat -
        r.amountToPool.toRat = (99999 / 10000 : ℚ) * 10 ^ e := by
  obtain ⟨l, l', i, loan, mc, liq, r, e, hr, h, hat, hdef, hmin, hliq, he, -, hgap⟩ := negative_cover_reachable
  exact ⟨l, l', i, loan, mc, liq, r, e, hr, h, hat, hdef, hmin, hliq, he, hgap⟩

/-- A default on a reachable coarsened vault where defaultCovered < 0. -/
lemma LendingLedger.manageDefault_cover_nonneg_witness :
    ∃ (l l' : LendingLedger) (i : Nat) (loan : Loan) (r : LoanWithAmounts Vault),
      l.Reachable ∧ (l.apply (.loanManage i .default)).run = .ok (.ok l') ∧ l.LoanAt i loan ∧
      (loan.manageDefault l.vault).run = .ok (.ok r) ∧ r.amountToPool.toRat < 0 := by
  obtain ⟨l, l', i, loan, -, -, r, -, hr, h, hat, hdef, -, -, -, hneg, -⟩ := negative_cover_reachable
  exact ⟨l, l', i, loan, r, hr, h, hat, hdef, hneg⟩

/-- A default on a reachable coarsened vault where a larger cover loses more of AssetsTotal. `l₁` is the same
ledger with less cover on the loan's broker. -/
lemma LendingLedger.manageDefault_cover_monotone_witness :
    ∃ (l l' : LendingLedger) (i : Nat) (e : LoanEntry) (b b₁ : LoanBroker) (l₁ l₁' : LendingLedger),
      l.Reachable ∧ (l.apply (.loanManage i .default)).run = .ok (.ok l') ∧ l.loan? i = some e ∧
      l.broker? e.brokerIndex = some b ∧
      b₁.toRawLoanBroker = { b.toRawLoanBroker with coverAvailable := b₁.coverAvailable } ∧
      b₁.coverAvailable.toRat ≤ b.coverAvailable.toRat ∧
      l₁ = { l with brokers := l.brokers.set e.brokerIndex (some b₁) } ∧
      (l₁.apply (.loanManage i .default)).run = .ok (.ok l₁') ∧
      l₁.vault.toExact.assetsTotal - l₁'.vault.toExact.assetsTotal <
        l.vault.toExact.assetsTotal - l'.vault.toExact.assetsTotal := by
  have h := coverMonotoneCheck_true
  unfold coverMonotoneCheck at h
  split at h
  case h_2 => cases h
  rename_i l hl
  split at h
  case h_2 => cases h
  rename_i e he
  split at h
  case h_2 => cases h
  rename_i b hb
  split at h
  case h_2 => cases h
  rename_i b₁ hb₁
  split at h
  case h_2 => cases h
  rename_i l' l₁' h₂ h₁
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  have hraw := (RawLoanBroker.to_lawful_ok hb₁).1
  have hc : b₁.coverAvailable = smallCover := (congrArg RawLoanBroker.coverAvailable hraw :)
  refine ⟨l, l', 1, e, b, b₁, _, l₁', LendingLedger.Reachable.of_run cwGenesis_genesis hl, h₂, he, hb, ?_, h.1, rfl,
    h₁, h.2⟩
  rw [hc]
  exact hraw

end XRPL.Model.Lending
