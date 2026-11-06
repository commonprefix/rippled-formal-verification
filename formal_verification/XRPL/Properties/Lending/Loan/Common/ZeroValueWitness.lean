import XRPL.Properties.Lending.Ledger.Common.CoarsenedVault
import XRPL.Properties.Lending.Loan.Common.PayDefs

/-! # A late instalment that takes no value off the loan

A loan of 6 at 14.5% in 16 yearly instalments with a 10% management fee, on a Scale 0 vault. After four instalments
the targets of the fifth equal the loan's amounts, so its late payment pays only late interest. -/

set_option linter.style.nativeDecide false

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault (Vault RawVault VaultSchedule)

/-- A closed-ended IOU vault at Scale 0, subscription until 1000, redemption about 19 years later. -/
private def zvSchedule : VaultSchedule := ⟨1000, 1000 + 600000000⟩

/-- The new vault VaultCreate makes for `zvSchedule`. -/
private def zvRawVault : RawVault := { cwRawVault with scale := 0, schedule := some zvSchedule }

private def zvVault : Vault := ⟨zvRawVault, by native_decide, by native_decide⟩

/-- The ledger right after VaultCreate. -/
private def zvGenesis : LendingLedger := { vault := zvVault, shares := [], brokers := [], loans := [], now := 0 }

private lemma zvGenesis_genesis : zvGenesis.Genesis where
  created := ⟨some 0, none, zvSchedule, none, false, .fractional, by native_decide, by
    unfold Vault.create RawVault.to_lawful
    exact dif_pos ⟨zvVault.wf, zvVault.valid⟩⟩
  holds_asset := Or.inl rfl
  no_holders := rfl
  no_brokers := rfl
  no_loans := rfl
  not_deleted := rfl

/-- InterestRate 14.5% and LateInterestRate 100%. -/
private def zvRates : LoanRates :=
  { interestRate := 14500, lateInterestRate := 100000, closeInterestRate := 0, overpaymentInterestRate := 0,
    overpaymentFee := 0 }

/-- One year in seconds, the PaymentInterval. -/
private def zvYear : UInt32 := 31536000

/-- `1`. -/
private def zvOne : Number := ⟨false, 1000000000000000000, -18⟩

/-- A broker with a 10% management fee lends 6 in 16 yearly instalments. Three instalments of 1 are paid early,
the fourth 0.2 years late with 1 of late interest, then the fifth falls due. -/
private def zvTxs : List LendingTx :=
  [.vaultDeposit 0 (cwAmount 1000000000000000 (-9)) false,
   .close 1001,
   .loanBrokerCreate ⟨none, some 10000, none, none⟩,
   .loanSet 0 ⟨false, 6000000000000000000, -18⟩ zvRates cwFees (some zvYear) (some 16) (some 60) 0 false false,
   .loanPay 0 .regular zvOne,
   .loanPay 0 .regular zvOne,
   .loanPay 0 .regular zvOne,
   .close (1001 + 4 * zvYear + 6307200),
   .loanPay 0 .late ⟨false, 2000000000000000000, -18⟩,
   .close (1001 + 5 * zvYear + 6307200)]

end XRPL.Model.Lending
