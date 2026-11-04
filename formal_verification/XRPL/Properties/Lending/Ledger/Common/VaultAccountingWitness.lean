import XRPL.Properties.Lending.Ledger.Common.VaultAccounting
import XRPL.Properties.Lending.Ledger.Common.ShareValueWitness

/-! # A payment where AssetsTotal and AssetsAvailable stray from the flows

On the coarsened vault of `ShareValueWitness.lean`, a late instalment of 1.5 without interest is credited to
AssetsAvailable on the coarser grid as 1. AssetsDeployed drops by the exact 1.5, so AssetsTotal and AssetsAvailable
both end 0.5 below the flows. -/

set_option linter.style.nativeDecide false

namespace XRPL.Model.Lending

open XRPL.Model.Protocol

/-- The late payment of 1.5 on loan D. -/
private def pwTx : LendingTx := .loanPay 3 .late ⟨false, 1500000000000000000, -18⟩

/-- The payment succeeds, and AssetsTotal and AssetsAvailable both miss the flows of the one-step run. -/
private def pwCheck : Bool :=
  match cwGenesis.run svTxs with
  | .ok l =>
    match (l.apply pwTx).run with
    | .ok (.ok l') =>
      decide (l'.vault.toRawVault.toExact.assetsTotal ≠ l.vault.toRawVault.toExact.assetsTotal +
        l.deposits [pwTx] - l.withdrawals [pwTx] - l.clawbacks [pwTx] + l.interestPaid [pwTx] - l.defaulted [pwTx] +
        l.defaultCovered [pwTx]) &&
      decide (l'.vault.assetsAvailable.toRat ≠ l.vault.assetsAvailable.toRat + l.deposits [pwTx] -
        l.withdrawals [pwTx] - l.clawbacks [pwTx] - l.lent [pwTx] + l.principalPaid [pwTx] + l.interestPaid [pwTx] +
        l.defaultCovered [pwTx] + l.deletedPending [pwTx])
    | _ => false
  | .error _ => false

private lemma pwCheck_true : pwCheck = true := by native_decide

/-- The one-payment run from a reachable ledger where both lines fail. -/
private lemma LendingLedger.payment_witness_run :
    ∃ (start : LendingLedger) (txs : List LendingTx) (l : LendingLedger), start.Reachable ∧
      LendingLedger.Reaches start txs l ∧
      l.vault.toRawVault.toExact.assetsTotal ≠ start.vault.toRawVault.toExact.assetsTotal + start.deposits txs -
        start.withdrawals txs - start.clawbacks txs + start.interestPaid txs - start.defaulted txs +
        start.defaultCovered txs ∧
      l.vault.assetsAvailable.toRat ≠ start.vault.assetsAvailable.toRat + start.deposits txs - start.withdrawals txs -
        start.clawbacks txs - start.lent txs + start.principalPaid txs + start.interestPaid txs +
        start.defaultCovered txs + start.deletedPending txs := by
  have h := pwCheck_true
  unfold pwCheck at h
  split at h
  case h_2 => cases h
  rename_i l hl
  split at h
  case h_2 => cases h
  rename_i l' hl'
  obtain ⟨hT, hA⟩ := Bool.and_eq_true_iff.mp h
  exact ⟨l, [pwTx], l', LendingLedger.Reachable.of_run cwGenesis_genesis hl, LendingLedger.Reaches.single hl',
    of_decide_eq_true hT, of_decide_eq_true hA⟩

/-- A late payment of 1.5 without interest on a coarsened vault lowers AssetsTotal from 2434246907153729 to
2434246907153728.5, while the flows (no interest paid) keep it at 2434246907153729. -/
lemma LendingLedger.accounting_assetsTotal_witness :
    ∃ (start : LendingLedger) (txs : List LendingTx) (l : LendingLedger), start.Reachable ∧
      LendingLedger.Reaches start txs l ∧
      l.vault.toRawVault.toExact.assetsTotal ≠ start.vault.toRawVault.toExact.assetsTotal + start.deposits txs -
        start.withdrawals txs - start.clawbacks txs + start.interestPaid txs - start.defaulted txs +
        start.defaultCovered txs :=
  let ⟨start, txs, l, hr, hrun, hT, _⟩ := LendingLedger.payment_witness_run
  ⟨start, txs, l, hr, hrun, hT⟩

/-- The same payment credits AssetsAvailable 1 instead of its principal 1.5: AssetsAvailable goes from
1874246907153723 to 1874246907153724, while the flows give 1874246907153724.5. -/
lemma LendingLedger.accounting_assetsAvailable_witness :
    ∃ (start : LendingLedger) (txs : List LendingTx) (l : LendingLedger), start.Reachable ∧
      LendingLedger.Reaches start txs l ∧
      l.vault.assetsAvailable.toRat ≠ start.vault.assetsAvailable.toRat + start.deposits txs - start.withdrawals txs -
        start.clawbacks txs - start.lent txs + start.principalPaid txs + start.interestPaid txs +
        start.defaultCovered txs + start.deletedPending txs :=
  let ⟨start, txs, l, hr, hrun, _, hA⟩ := LendingLedger.payment_witness_run
  ⟨start, txs, l, hr, hrun, hA⟩

end XRPL.Model.Lending
