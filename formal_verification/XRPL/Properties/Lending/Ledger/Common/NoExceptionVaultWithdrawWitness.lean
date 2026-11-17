import XRPL.Properties.Lending.Ledger.Common.ReachableProofs
import XRPL.Properties.Vault.Common.WithdrawDefs

/-! # Witness for a VaultWithdraw that ends in an exception

A run from a new closed-ended XRP vault, checked by `native_decide`. The vault holds 100 drops and 100 shares after
one deposit. An account that owns no shares asks to redeem `10^17 + 1` shares, which are worth `10^17 + 1` drops, one
drop above the largest XRP amount. Pricing them ends in the out-of-range error before the holder's shares are
checked (FV_M2_25). -/

set_option linter.style.nativeDecide false

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault (Vault RawVault VaultSchedule WithdrawAmount)

/-- A closed-ended XRP vault, subscription until 1000, redemption about 30 years later. -/
private def vwSchedule : VaultSchedule := ⟨1000, 1000 + 946000000⟩

/-- The new vault VaultCreate makes for `vwSchedule`. -/
private def vwRawVault : RawVault :=
  { assetsAvailable := Number.zero, assetsDeployed := Number.zero, assetsReserved := Number.zero,
    assetsMaximum := none, numericType := .native, scale := 0, sharesTotal := Number.zero,
    lossUnrealized := Number.zero, yieldUnrealized := Number.zero, schedule := some vwSchedule,
    earlyExitFeeRate := none, ownerCanBlockDeposit := false, depositBlocked := false }

/-- The new vault as a lawful vault. -/
private def vwVault : Vault := ⟨vwRawVault, by native_decide, by native_decide⟩

/-- The ledger right after VaultCreate. -/
private def vwGenesis : LendingLedger := { vault := vwVault, shares := [], brokers := [], loans := [], now := 0 }

/-- That ledger is a genesis ledger: a VaultCreate that passed its checks made the vault. -/
private lemma vwGenesis_genesis : vwGenesis.Genesis where
  created := ⟨none, none, vwSchedule, none, false, .native, by native_decide, by
    unfold Vault.create RawVault.to_lawful
    exact dif_pos ⟨vwVault.wf, vwVault.valid⟩⟩
  holds_asset := Or.inr (Or.inl rfl)
  no_holders := rfl
  no_brokers := rfl
  no_loans := rfl
  not_deleted := rfl

/-- Holder `0` deposits 100 drops. -/
private def vwSetup : List LendingTx := [.vaultDeposit 0 (STAmount.unchecked .native 100 0 false) false]

/-- `10^17 + 1` shares, worth one drop more than the largest XRP amount. -/
private def vwShares : STAmount := ⟨.int64, 100000000000000001, 0, false⟩

/-- The withdrawal by account `1`, which owns no shares. -/
private def vwWithdraw : LendingTx := .vaultWithdraw 1 (.vaultShares vwShares)

/-- True when a run ended in the model's out-of-range error. -/
private def vwOutOfRange (r : Except Error (Except TER LendingLedger)) : Bool :=
  match r with
  | .error .outOfRange => true
  | _ => false

/-- A run the check accepts ended in the out-of-range error. -/
private lemma vwOutOfRange_spec {r : Except Error (Except TER LendingLedger)} (h : vwOutOfRange r = true) :
    r = .error .outOfRange := by
  unfold vwOutOfRange at h
  split at h
  · rfl
  · cases h

/-- The vault holds XRP, the account's shares are within SharesTotal, the withdrawal passes preflight, the shares
are worth more than `10^17` drops and the run ends in the out-of-range error. -/
private def vwCheck : Bool :=
  match vwGenesis.run vwSetup with
  | .ok l =>
    decide (l.vault.numericType = NumericType.native) &&
      decide ((l.sharesOf 1).toRat ≤ l.vault.sharesTotal.toRat) &&
      decide (vwWithdraw.preflight l = .tesSUCCESS) &&
      decide ((10 : ℚ) ^ 17 < l.vault.idealAssetsWithdraw (l.isSoleShareholder 1) vwShares.toRat) &&
      vwOutOfRange (l.apply vwWithdraw).run
  | .error _ => false

/-- The model run passes the check. -/
private lemma vwCheck_true : vwCheck = true := by native_decide

/-- VaultWithdraw by shares on a reachable XRP ledger, the shares worth more than the largest XRP amount -> an
error, not a result code. The account owns no shares. -/
lemma LendingLedger.vaultWithdraw_out_of_range_witness :
    ∃ (l : LendingLedger) (h : Nat) (shares : STAmount),
      l.Reachable ∧ l.vault.numericType = NumericType.native ∧
      (l.sharesOf h).toRat ≤ l.vault.sharesTotal.toRat ∧
      (LendingTx.vaultWithdraw h (.vaultShares shares)).preflight l = .tesSUCCESS ∧
      (10 : ℚ) ^ 17 < l.vault.idealAssetsWithdraw (l.isSoleShareholder h) shares.toRat ∧
      (l.apply (.vaultWithdraw h (.vaultShares shares))).run = .error .outOfRange := by
  have h := vwCheck_true
  unfold vwCheck at h
  split at h
  case h_2 => cases h
  rename_i l hl
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨hnt, hbal⟩, hpre⟩, hworth⟩, herr⟩ := h
  exact ⟨l, 1, vwShares, LendingLedger.Reachable.of_run vwGenesis_genesis hl, hnt, hbal, hpre, hworth,
    vwOutOfRange_spec herr⟩

end XRPL.Model.Lending
