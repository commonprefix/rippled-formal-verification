import XRPL.Properties.Lending.Ledger.Common.CoarsenedVault
import XRPL.Properties.Lending.Loan.Common.ManageDefs

/-! # Defaults on a reachable coarsened vault

On the coarsened vault of `CoarsenedVault.lean` a default can credit the vault less than its capped cover amount.
Defaulting loan B there pays the vault `-0.9`, and with a full cover of 1 it pays only `0.1`. -/

set_option linter.style.nativeDecide false

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault (Vault RawVault)

/-- The coarsened run with broker 1 at a 100% minimum cover and 100% liquidation, holding a cover of 1. -/
private def fcTxs : List LendingTx :=
  cwTxs.take 3 ++ [.loanBrokerCreate ⟨none, none, some 100000, some 100000⟩,
    .loanBrokerCoverDeposit 1 (cwAmount 1000000000000000 (-15))] ++ cwTxs.drop 5

/-- Loan B's default on that run is covered in full, yet the cover pays only `0.1` and AssetsTotal drops by
`0.9`. -/
private def fullyCoveredCheck : Bool :=
  match cwGenesis.run fcTxs with
  | .ok l =>
    match l.loan? 1 with
    | some e =>
      match l.broker? e.brokerIndex with
      | some b =>
        match e.loan.withBroker b with
        | .ok loan =>
          match (loan.manageDefault l.vault).run,
              tenthBipsOfValue loan.broker.debtTotal loan.broker.coverRateMinimum .upward with
          | .ok (.ok r), .ok minimumCover =>
            match tenthBipsOfValue minimumCover loan.broker.coverRateLiquidation .upward with
            | .ok liquidationAmount =>
              decide (loan.principalOutstanding.toRat ≤
                  min liquidationAmount.toRat loan.broker.coverAvailable.toRat) &&
                decide (r.amountToPool.toRat < loan.principalOutstanding.toRat) &&
                decide (r.pool'.toExact.assetsTotal < l.vault.toExact.assetsTotal)
            | .error _ => false
          | _, _ => false
        | .error _ => false
      | none => false
    | none => false
  | .error _ => false

private lemma fullyCoveredCheck_true : fullyCoveredCheck = true := by native_decide

/-- A fully covered default on a reachable coarsened vault can lower AssetsTotal. -/
lemma LendingLedger.default_fully_covered_loss_reachable :
    ∃ (l : LendingLedger) (i : Nat) (loan : Loan) (minimumCover liquidationAmount : Number)
      (r : LoanWithAmounts Vault),
      l.Reachable ∧ l.LoanAt i loan ∧ (loan.manageDefault l.vault).run = .ok (.ok r) ∧
      tenthBipsOfValue loan.broker.debtTotal loan.broker.coverRateMinimum .upward = .ok minimumCover ∧
      tenthBipsOfValue minimumCover loan.broker.coverRateLiquidation .upward = .ok liquidationAmount ∧
      loan.principalOutstanding.toRat ≤ min liquidationAmount.toRat loan.broker.coverAvailable.toRat ∧
      r.amountToPool.toRat < loan.principalOutstanding.toRat ∧
      r.pool'.toExact.assetsTotal < l.vault.toExact.assetsTotal := by
  have h := fullyCoveredCheck_true
  unfold fullyCoveredCheck at h
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
  rename_i loan hw
  split at h
  case h_2 => cases h
  rename_i r minimumCover hok hmin
  split at h
  case h_2 => cases h
  rename_i liquidationAmount hliq
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨l, 1, loan, minimumCover, liquidationAmount, r, LendingLedger.Reachable.of_run cwGenesis_genesis hl,
    ⟨e, b, he, hb, hw⟩, hok, hmin, hliq, h.1.1, h.1.2, h.2⟩

end XRPL.Model.Lending
