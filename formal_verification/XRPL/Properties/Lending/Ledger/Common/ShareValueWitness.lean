import XRPL.Properties.Lending.Ledger.Common.CoarsenedVault
import XRPL.Properties.Lending.Loan.Common.ShareValue

/-! # A payment that lowers AssetsTotal on a coarsened vault

On the coarsened vault of `CoarsenedVault.lean`, an instalment of 1.5 without interest is credited on the
coarser grid as 1, so AssetsTotal falls. -/

set_option linter.style.nativeDecide false

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault (Vault RawVault)

/-- The coarsened run with a fourth loan D of 3 in two instalments of 1.5, created before the vault coarsens. -/
def svTxs : List LendingTx :=
  cwTxs.take 8 ++
  [.loanSet 0 ⟨false, 3000000000000000000, -18⟩ (cwRates 0) cwFees (some 35424000) (some 2) (some 60) 0 false false,
   .close 69207461,
   .loanPay 0 .late ⟨false, 7000000000000000000, -3⟩]

/-- Loan D's late instalment lowers AssetsTotal. -/
private def svTotalCheck : Bool :=
  match cwGenesis.run svTxs with
  | .ok l =>
    match (l.apply (.loanPay 3 .late ⟨false, 1500000000000000000, -18⟩)).run with
    | .ok (.ok l') => decide (l'.vault.toRawVault.toExact.assetsTotal < l.vault.toRawVault.toExact.assetsTotal)
    | _ => false
  | .error _ => false

private lemma svTotalCheck_true : svTotalCheck = true := by native_decide

/-- A payment on a reachable ledger can lower AssetsTotal. -/
lemma LendingLedger.payment_lowers_assetsTotal_reachable :
    ∃ l l' : LendingLedger, l.Reachable ∧
      (l.apply (.loanPay 3 .late ⟨false, 1500000000000000000, -18⟩)).run = .ok (.ok l') ∧
      l'.vault.toRawVault.toExact.assetsTotal < l.vault.toRawVault.toExact.assetsTotal := by
  have h := svTotalCheck_true
  unfold svTotalCheck at h
  split at h
  case h_2 => cases h
  rename_i l hl
  split at h
  case h_2 => cases h
  rename_i l' hl'
  exact ⟨l, l', LendingLedger.Reachable.of_run cwGenesis_genesis hl, hl', of_decide_eq_true h⟩

end XRPL.Model.Lending
