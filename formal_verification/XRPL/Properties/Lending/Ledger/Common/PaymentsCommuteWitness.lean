import XRPL.Properties.Lending.Ledger.Common.CoarsenedVault

/-! # Witness for the order of two payments on a vault that coarsens

Loan A's late payment takes AssetsAvailable past `10^16` base units, after which the vault credits whole units only.
Loan D's instalment of 1.9 paid after it credits 1, and paid before it the vault ends one unit higher. -/

set_option linter.style.nativeDecide false

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault (Vault RawVault)

/-- The run of `cwTxs` up to loan C, then at close time 69207461 loan D of 3.8 in two monthly instalments without
interest. -/
private def pcTxs : List LendingTx :=
  cwTxs.take 8 ++
  [.close 69207461,
   .loanSet 0 ⟨false, 3800000000000000000, -18⟩ (cwRates 0) cwFees (some 2592000) (some 2) (some 60) 0 false false]

/-- Loan A's late payment of 7000000000000000. -/
private def pcAmountA : Number := ⟨false, 7000000000000000000, -3⟩

/-- `1.9`, one instalment of loan D. -/
private def pcAmountD : Number := ⟨false, 1900000000000000000, -18⟩

/-- Both orders of the two payments pass and leave different AssetsAvailable. -/
private def commCheck : Bool :=
  match cwGenesis.run pcTxs with
  | .error _ => false
  | .ok l =>
    match (l.apply (.loanPay 0 .late pcAmountA)).run, (l.apply (.loanPay 3 .regular pcAmountD)).run with
    | .ok (.ok la), .ok (.ok lb) =>
      match (la.apply (.loanPay 3 .regular pcAmountD)).run, (lb.apply (.loanPay 0 .late pcAmountA)).run with
      | .ok (.ok lab), .ok (.ok lba) => decide (lab.vault.assetsAvailable.toRat ≠ lba.vault.assetsAvailable.toRat)
      | _, _ => false
    | _, _ => false

private lemma commCheck_true : commCheck = true := by native_decide

/-- Two payments on a reachable ledger can leave different vaults in the two orders. Loan A's late payment coarsens
the vault, and loan D's instalment of 1.9 credits 1 after it, while paid before it the vault ends one unit higher. -/
lemma LendingLedger.payments_comm_coarsened_witness :
    ∃ (l la lb lab lba : LendingLedger) (i j : Nat) (pt pt' : LoanPaymentType) (a a' : Number),
      l.Reachable ∧ i ≠ j ∧
      (l.apply (.loanPay i pt a)).run = .ok (.ok la) ∧ (la.apply (.loanPay j pt' a')).run = .ok (.ok lab) ∧
      (l.apply (.loanPay j pt' a')).run = .ok (.ok lb) ∧ (lb.apply (.loanPay i pt a)).run = .ok (.ok lba) ∧
      lab.vault ≠ lba.vault := by
  have h := commCheck_true
  unfold commCheck at h
  split at h
  · cases h
  rename_i l hl
  split at h
  · rename_i la lb ha hb
    split at h
    · rename_i lab lba hab hba
      exact ⟨l, la, lb, lab, lba, 0, 3, .late, .regular, _, _, LendingLedger.Reachable.of_run cwGenesis_genesis hl,
        by decide, ha, hab, hb, hba, fun hv => of_decide_eq_true h (by rw [hv])⟩
    · exact absurd h (by decide)
  · exact absurd h (by decide)

end XRPL.Model.Lending
