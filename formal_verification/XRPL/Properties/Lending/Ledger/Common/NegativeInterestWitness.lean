import XRPL.Properties.Lending.Ledger.Common.CoarsenedVault

/-! # A reachable regular payment rejected for a negative interest part

A loan at a tiny rate, paid one instalment at a time. The third instalment takes more principal than its amount,
so its interest part is negative and LoanPay rejects its amount due with tecLIMIT_EXCEEDED (C++ LoanPay.cpp:479). -/

set_option linter.style.nativeDecide false

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault (Vault RawVault VaultSchedule)

/-- A closed-ended IOU vault at Scale 2, subscription until 1000, redemption 900 days later. -/
private def niSchedule : VaultSchedule := ⟨1000, 1000 + 900 * 86400⟩

/-- The new vault VaultCreate makes for `niSchedule`. -/
private def niRawVault : RawVault := { cwRawVault with scale := 2, schedule := some niSchedule }

private def niVault : Vault := ⟨niRawVault, by native_decide, by native_decide⟩

/-- The ledger right after VaultCreate. -/
private def niGenesis : LendingLedger := { vault := niVault, shares := [], brokers := [], loans := [], now := 0 }

private lemma niGenesis_genesis : niGenesis.Genesis where
  created := ⟨some 2, none, niSchedule, none, false, .fractional, by native_decide, by
    unfold Vault.create RawVault.to_lawful
    exact dif_pos ⟨niVault.wf, niVault.valid⟩⟩
  holds_asset := Or.inl rfl
  no_holders := rfl
  no_brokers := rfl
  no_loans := rfl
  not_deleted := rfl

/-- An InterestRate of 6 tenth basis points and no other rate. -/
private def niRates : LoanRates :=
  { interestRate := 6, lateInterestRate := 0, closeInterestRate := 0, overpaymentInterestRate := 0,
    overpaymentFee := 0 }

/-- A deposit of `10^12`, a broker without fees or cover, a loan of 5198461379.86 in thirty payments 60 seconds
apart, and its first two instalments of 173282046.55. -/
private def niTxs : List LendingTx :=
  [.vaultDeposit 0 (cwAmount 1000000000000000 (-3)) false,
   .close 1001,
   .loanBrokerCreate ⟨none, none, none, none⟩,
   .loanSet 0 ⟨false, 5198461379860000000, -9⟩ niRates cwFees (some 60) (some 30) (some 60) 0 false false,
   .close 1012,
   .loanPay 0 .regular ⟨false, 1732820465500000000, -10⟩,
   .close 1013,
   .loanPay 0 .regular ⟨false, 1732820465500000000, -10⟩,
   .close 1014]

end XRPL.Model.Lending
