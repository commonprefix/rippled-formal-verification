import XRPL.Properties.Lending.Ledger.Common.VaultAccounting
import XRPL.Properties.Lending.Ledger.Common.ShareValueWitness
import XRPL.Properties.Lending.Ledger.Common.AssetsTotalBoundWitness

/-! # A payment where AssetsTotal strays from the flows, and a delete where AssetsAvailable does

On the coarsened vault of `ShareValueWitness.lean`, a late instalment of 1.5 without interest is credited to
AssetsAvailable on the coarser grid as 1. AssetsDeployed drops by the exact 1.5, so AssetsTotal ends 0.5 below the
flows. On the coarsened vault of `AssetsTotalBoundWitness.lean`, a LoanDelete of a pending loan of 0.6 credits
AssetsAvailable 1. -/

set_option linter.style.nativeDecide false

namespace XRPL.Model.Lending

open XRPL.Model.Protocol

open private ubSetup from XRPL.Properties.Lending.Ledger.Common.AssetsTotalBoundWitness

/-- The late payment of 1.5 on loan D. -/
private def pwTx : LendingTx := .loanPay 3 .late ⟨false, 1500000000000000000, -18⟩

/-- The payment succeeds, and AssetsTotal misses the flows of the one-step run. -/
private def pwCheck : Bool :=
  match cwGenesis.run svTxs with
  | .ok l =>
    match (l.apply pwTx).run with
    | .ok (.ok l') =>
      decide (l'.vault.toRawVault.toExact.assetsTotal ≠ l.vault.toRawVault.toExact.assetsTotal +
        l.deposits [pwTx] - l.withdrawals [pwTx] - l.clawbacks [pwTx] + l.interestPaid [pwTx] - l.defaulted [pwTx] +
        l.defaultCovered [pwTx])
    | _ => false
  | .error _ => false

private lemma pwCheck_true : pwCheck = true := by native_decide

/-- A late payment of 1.5 without interest on a coarsened vault lowers AssetsTotal from 2434246907153729 to
2434246907153728.5, while the flows (no interest paid) keep it at 2434246907153729. -/
lemma LendingLedger.accounting_assetsTotal_witness :
    ∃ (start : LendingLedger) (txs : List LendingTx) (l : LendingLedger), start.Reachable ∧
      LendingLedger.Reaches start txs l ∧
      l.vault.toRawVault.toExact.assetsTotal ≠ start.vault.toRawVault.toExact.assetsTotal + start.deposits txs -
        start.withdrawals txs - start.clawbacks txs + start.interestPaid txs - start.defaulted txs +
        start.defaultCovered txs := by
  have h := pwCheck_true
  unfold pwCheck at h
  split at h
  case h_2 => cases h
  rename_i l hl
  split at h
  case h_2 => cases h
  rename_i l' hl'
  exact ⟨l, [pwTx], l', LendingLedger.Reachable.of_run cwGenesis_genesis hl, LendingLedger.Reaches.single hl',
    of_decide_eq_true h⟩

/-- The LoanDelete of the pending loan E of 0.6. -/
private def dwTx : LendingTx := .loanDelete 3

/-- The delete succeeds, and AssetsAvailable misses the flows of the one-step run. -/
private def dwCheck : Bool :=
  match cwGenesis.run ubSetup with
  | .ok l =>
    match (l.apply dwTx).run with
    | .ok (.ok l') =>
      decide (l'.vault.assetsAvailable.toRat ≠ l.vault.assetsAvailable.toRat + l.deposits [dwTx] -
        l.withdrawals [dwTx] - l.clawbacks [dwTx] - l.lent [dwTx] + l.amountToPool [dwTx] +
        l.defaultCovered [dwTx] + l.deletedPending [dwTx])
    | _ => false
  | .error _ => false

private lemma dwCheck_true : dwCheck = true := by native_decide

/-- A LoanDelete of a pending loan of 0.6 on a coarsened vault credits AssetsAvailable 1: it goes from
1874246907153724 to 1874246907153725, while the flows give 1874246907153724.6. -/
lemma LendingLedger.accounting_assetsAvailable_witness :
    ∃ (start : LendingLedger) (txs : List LendingTx) (l : LendingLedger), start.Reachable ∧
      LendingLedger.Reaches start txs l ∧
      l.vault.assetsAvailable.toRat ≠ start.vault.assetsAvailable.toRat + start.deposits txs - start.withdrawals txs -
        start.clawbacks txs - start.lent txs + start.amountToPool txs + start.defaultCovered txs +
        start.deletedPending txs := by
  have h := dwCheck_true
  unfold dwCheck at h
  split at h
  case h_2 => cases h
  rename_i l hl
  split at h
  case h_2 => cases h
  rename_i l' hl'
  exact ⟨l, [dwTx], l', LendingLedger.Reachable.of_run cwGenesis_genesis hl, LendingLedger.Reaches.single hl',
    of_decide_eq_true h⟩

end XRPL.Model.Lending
