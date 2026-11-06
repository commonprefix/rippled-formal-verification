import XRPL.Properties.Lending.Ledger.Common.CoarsenedVault

/-! # A reachable payment that credits the vault a negative amount

An IOU vault at Scale 10 lends almost all it holds, the loan is paid 130 years late so the late interest takes
AssetsAvailable past `10^10`, and a withdrawal leaves it just below `10^10`. The last instalment of a second loan
then rounds its sum up to `10^10`, and the floor at that coarser exponent lowers AssetsAvailable. -/

set_option linter.style.nativeDecide false

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault (Vault RawVault VaultSchedule)

/-- A closed-ended vault, subscription until 1000, redemption 900 days later. -/
private def ncSchedule : VaultSchedule := ⟨1000, 1000 + 900 * 86400⟩

/-- The new vault VaultCreate makes for `ncSchedule` at Scale 10. -/
private def ncRawVault : RawVault := { cwRawVault with scale := 10, schedule := some ncSchedule }

private def ncVault : Vault := ⟨ncRawVault, by native_decide, by native_decide⟩

/-- The ledger right after VaultCreate. -/
private def ncGenesis : LendingLedger := { vault := ncVault, shares := [], brokers := [], loans := [], now := 0 }

private lemma ncGenesis_genesis : ncGenesis.Genesis where
  created := ⟨some 10, none, ncSchedule, none, false, .fractional, by native_decide, by
    unfold Vault.create RawVault.to_lawful
    exact dif_pos ⟨ncVault.wf, ncVault.valid⟩⟩
  holds_asset := Or.inl rfl
  no_holders := rfl
  no_brokers := rfl
  no_loans := rfl
  not_deleted := rfl

/-- The last instalment of loan B, 0.0000019996. -/
private def ncDue : Number := ⟨false, 1999600000000000000, -24⟩

/-- A deposit of 500000, loan A of 450000 in 400 instalments with a 100% late rate, loan B of 0.0000019996, a close
130 years later, 400 late payments of loan A and a withdrawal that leaves AssetsAvailable at 9999999999.999998. -/
private def ncTxs : List LendingTx :=
  [.vaultDeposit 0 (cwAmount 5000000000000000 (-10)) false,
   .close 1001,
   .loanBrokerCreate ⟨none, none, none, none⟩,
   .loanSet 0 ⟨false, 4500000000000000000, -13⟩ (cwRates 100000) cwFees (some 60) (some 400) (some 60) 0 false false,
   .loanSet 0 ncDue (cwRates 0) cwFees (some 86400) (some 1) (some 60) 0 false false,
   .close 4100000000] ++
  List.replicate 400 (.loanPay 0 .late ⟨false, 1000000000000000000, -9⟩) ++
  [.vaultWithdraw 0 (.vaultAssets (cwAmount 1730639658667762 (-6)))]

/-- After `txs` the payment of loan `i` of `amount` succeeds and lowers AssetsAvailable and AssetsTotal. -/
private def negCheck (g : LendingLedger) (txs : List LendingTx) (i : Nat) (amount : Number) : Bool :=
  match g.run txs with
  | .ok l =>
    match (l.apply (.loanPay i .late amount)).run with
    | .ok (.ok l') =>
      decide (l'.vault.assetsAvailable.toRat < l.vault.assetsAvailable.toRat) &&
        decide (l'.vault.assetsAvailable.toRat + l'.vault.assetsDeployed.toRat <
          l.vault.assetsAvailable.toRat + l.vault.assetsDeployed.toRat)
    | _ => false
  | .error _ => false

/-- A run whose check passes gives a reachable ledger with that payment. -/
private lemma LendingLedger.negCheck_sound {g : LendingLedger} (hg : g.Genesis) {txs : List LendingTx} {i : Nat}
    {amount : Number} (h : negCheck g txs i amount = true) :
    ∃ l l' : LendingLedger, l.Reachable ∧ (l.apply (.loanPay i .late amount)).run = .ok (.ok l') ∧
      l'.vault.assetsAvailable.toRat < l.vault.assetsAvailable.toRat ∧
      l'.vault.assetsAvailable.toRat + l'.vault.assetsDeployed.toRat <
        l.vault.assetsAvailable.toRat + l.vault.assetsDeployed.toRat := by
  unfold negCheck at h
  split at h
  case h_2 => cases h
  rename_i l hl
  split at h
  case h_2 => cases h
  rename_i l' hl'
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨l, l', LendingLedger.Reachable.of_run hg hl, hl', h.1, h.2⟩

private lemma ncCheck_true : negCheck ncGenesis ncTxs 1 ncDue = true := by native_decide

/-- A payment on a reachable ledger can succeed and credit the vault a negative amount. Loan B's last instalment
of 0.0000019996 lowers AssetsAvailable, and AssetsTotal with it. -/
lemma LendingLedger.payment_negative_credit_witness :
    ∃ l l' : LendingLedger, l.Reachable ∧
      (l.apply (.loanPay 1 .late ⟨false, 1999600000000000000, -24⟩)).run = .ok (.ok l') ∧
      l'.vault.assetsAvailable.toRat < l.vault.assetsAvailable.toRat ∧
      l'.vault.assetsAvailable.toRat + l'.vault.assetsDeployed.toRat <
        l.vault.assetsAvailable.toRat + l.vault.assetsDeployed.toRat :=
  LendingLedger.negCheck_sound ncGenesis_genesis ncCheck_true

end XRPL.Model.Lending
