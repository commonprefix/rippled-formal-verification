import XRPL.Properties.Lending.Ledger.Common.ReachableProofs

/-! # A reachable coarsened vault

The run of the FV_M4_27 repro on the lending ledger, where late interest takes the vault past
10^16 base units. Other witnesses build on this run. -/

set_option linter.style.nativeDecide false

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault (Vault RawVault VaultSchedule WithdrawAmount)

/-- A closed-ended IOU vault at Scale 1, subscription until 1000, redemption 900 days later. -/
private def cwSchedule : VaultSchedule := ⟨1000, 1000 + 900 * 86400⟩

/-- The new vault VaultCreate makes for `cwSchedule`. -/
def cwRawVault : RawVault :=
  { assetsAvailable := Number.zero, assetsDeployed := Number.zero, assetsReserved := Number.zero,
    assetsMaximum := none, numericType := .fractional, scale := 1, sharesTotal := Number.zero,
    lossUnrealized := Number.zero, yieldUnrealized := Number.zero, schedule := some cwSchedule,
    earlyExitFeeRate := none, ownerCanBlockDeposit := false, depositBlocked := false }

private def cwVault : Vault := ⟨cwRawVault, by native_decide, by native_decide⟩

/-- The ledger right after VaultCreate. -/
def cwGenesis : LendingLedger := { vault := cwVault, shares := [], brokers := [], loans := [], now := 0 }

lemma cwGenesis_genesis : cwGenesis.Genesis where
  created := ⟨some 1, none, cwSchedule, none, false, .fractional, by native_decide, by
    unfold Vault.create RawVault.to_lawful
    exact dif_pos ⟨cwVault.wf, cwVault.valid⟩⟩
  holds_asset := Or.inl rfl
  no_holders := rfl
  no_brokers := rfl
  no_loans := rfl
  not_deleted := rfl

/-- An IOU amount `m × 10^e`. -/
def cwAmount (m : UInt64) (e : Int) : STAmount := STAmount.unchecked .fractional m e false

/-- Zero fees. -/
def cwFees : LoanFees :=
  { originationFee := Number.zero, serviceFee := Number.zero, latePaymentFee := Number.zero,
    closePaymentFee := Number.zero }

/-- Zero interest, with the given late interest rate. -/
def cwRates (late : TenthBips32) : LoanRates :=
  { interestRate := 0, lateInterestRate := late, closeInterestRate := 0, overpaymentInterestRate := 0,
    overpaymentFee := 0 }

/-- The run of the FV_M4_27 repro: a deposit, two brokers, loans A, B and C, loan A paid
800 days late to coarsen the vault, a withdrawal and eight 0.1 instalments of loan C. -/
def cwTxs : List LendingTx :=
  [.vaultDeposit 0 (cwAmount 8999990000000000 (-1)) false,
   .close 1001,
   .loanBrokerCreate ⟨none, none, none, none⟩,
   .loanBrokerCreate ⟨none, none, some 9999, some 100000⟩,
   .loanBrokerCoverDeposit 1 (cwAmount 1000000000000000 (-16)),
   .loanSet 0 ⟨false, 7000000000000000000, -4⟩ (cwRates 100000) cwFees (some 86400) (some 5) (some 60) 0 false false,
   .loanSet 1 ⟨false, 1000000000000000000, -18⟩ (cwRates 0) cwFees (some 86400) (some 1) (some 60) 0 false false,
   .loanSet 0 ⟨false, 2000000000000000000, -18⟩ (cwRates 0) cwFees (some 86400) (some 20) (some 60) 0 false false,
   .close 69207461,
   .loanPay 0 .late ⟨false, 7000000000000000000, -3⟩,
   .close (1000 + 900 * 86400 + 1),
   .vaultWithdraw 0 (.vaultAssets (cwAmount 8742469071537271 (-1)))] ++
  List.replicate 8 (.loanPay 2 .late ⟨false, 1000000000000000000, -19⟩)

end XRPL.Model.Lending
