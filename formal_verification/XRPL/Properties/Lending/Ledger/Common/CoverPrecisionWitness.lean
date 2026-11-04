import XRPL.Properties.Lending.Ledger.Common.CoarsenedVault

/-! # A default that takes the cover off inexactly

A LoanServiceFee of `10^12` paid into a cover below its minimum leaves `1000000000001` at the scale `10^-10`.
Defaulting a loan of `1.0000000001` leaves `999999999999.9999999999`, which a `Number` rounds to `10^12`. -/

set_option linter.style.nativeDecide false

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault (Vault RawVault VaultSchedule)

/-- A closed-ended IOU vault at Scale 10, subscription until 1000, redemption 900 days later. -/
private def cpSchedule : VaultSchedule := ⟨1000, 1000 + 900 * 86400⟩

/-- The new vault VaultCreate makes for `cpSchedule`. -/
private def cpRawVault : RawVault := { cwRawVault with scale := 10, schedule := some cpSchedule }

private def cpVault : Vault := ⟨cpRawVault, by native_decide, by native_decide⟩

/-- The ledger right after VaultCreate. -/
private def cpGenesis : LendingLedger := { vault := cpVault, shares := [], brokers := [], loans := [], now := 0 }

private lemma cpGenesis_genesis : cpGenesis.Genesis where
  created := ⟨some 10, none, cpSchedule, none, false, .fractional, by native_decide, by
    unfold Vault.create RawVault.to_lawful
    exact dif_pos ⟨cpVault.wf, cpVault.valid⟩⟩
  holds_asset := Or.inl rfl
  no_holders := rfl
  no_brokers := rfl
  no_loans := rfl
  not_deleted := rfl

/-- No fees but the given LoanServiceFee. -/
private def cpFees (service : Number) : LoanFees := { cwFees with serviceFee := service }

/-- A broker at 10% minimum cover and 100% liquidation lends loans A and B. Defaulting A leaves a cover of 1, so
B's first instalment adds its fee of `10^12` to the cover. Then loan C of `1.0000000001`. -/
private def cpTxs : List LendingTx :=
  [.vaultDeposit 0 (cwAmount 8000000000000000 (-10)) false,
   .close 1001,
   .loanBrokerCreate ⟨none, none, some 10000, some 100000⟩,
   .loanBrokerCoverDeposit 0 (cwAmount 1000100000000000 (-11)),
   .loanSet 0 ⟨false, 9000000000000000000, -14⟩ (cwRates 0) cwFees (some 60) (some 1) (some 60) 0 false false,
   .loanSet 0 ⟨false, 1000000000000000000, -14⟩ (cwRates 0) (cpFees ⟨false, 1000000000000000000, -6⟩)
     (some 86400) (some 2) (some 60) 0 false false,
   .close 1300,
   .loanManage 0 .default,
   .loanPay 1 .regular ⟨false, 1000000005000000000, -6⟩,
   .loanSet 0 ⟨false, 1000000000100000000, -18⟩ (cwRates 0) cwFees (some 60) (some 1) (some 60) 0 false false,
   .close 1500]

end XRPL.Model.Lending
