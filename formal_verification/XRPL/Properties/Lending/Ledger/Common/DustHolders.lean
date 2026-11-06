import XRPL.Properties.Lending.Ledger.Common.CoarsenedVault

/-! # Two holders that can't leave

The run of the C++ test VaultDustHoldersLocked on the lending ledger. Two holders own 10^9 shares each, an
uncovered default leaves one base unit, and after RedemptionDate neither full redemption pays anything. -/

set_option linter.style.nativeDecide false

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault (Vault RawVault VaultSchedule WithdrawAmount)

/-- A closed-ended IOU vault at Scale 6, subscription until 1000, redemption 30 days later. -/
def dhSchedule : VaultSchedule := ⟨1000, 1000 + 30 * 86400⟩

/-- The new vault VaultCreate makes for `dhSchedule`. -/
private def dhRawVault : RawVault := { cwRawVault with scale := 6, schedule := some dhSchedule }

private def dhVault : Vault := ⟨dhRawVault, by native_decide, by native_decide⟩

/-- The ledger right after VaultCreate. -/
private def dhGenesis : LendingLedger := { vault := dhVault, shares := [], brokers := [], loans := [], now := 0 }

private lemma dhGenesis_genesis : dhGenesis.Genesis where
  created := ⟨some 6, none, dhSchedule, none, false, .fractional, by native_decide, by
    unfold Vault.create RawVault.to_lawful
    exact dif_pos ⟨dhVault.wf, dhVault.valid⟩⟩
  holds_asset := Or.inl rfl
  no_holders := rfl
  no_brokers := rfl
  no_loans := rfl
  not_deleted := rfl

/-- Two deposits of 1000, loan A of all but one base unit, its default after the grace period, a close time past
RedemptionDate and the grace period, then the delete of loan A and of its broker. -/
private def dhTxs : List LendingTx :=
  [.vaultDeposit 0 (cwAmount 1000000000000000 (-12)) false,
   .vaultDeposit 1 (cwAmount 1000000000000000 (-12)) false,
   .close 1001,
   .loanBrokerCreate ⟨none, none, none, none⟩,
   .loanSet 0 ⟨false, 1999999999000000000, -15⟩ (cwRates 0) cwFees (some 86400) (some 1) (some 60) 0 false false,
   .close (1001 + 86400 + 61),
   .loanManage 0 .default,
   .close (1000 + 30 * 86400 + 61),
   .loanDelete 0,
   .loanBrokerDelete 0]

end XRPL.Model.Lending
