import XRPL.Properties.Lending.Loan.Common.RegularPayoffSplit
import XRPL.Properties.Lending.Ledger.Common.CoarsenedVault

/-! # Regular payoffs that pay less than the schedule

A loan of 1.5 paid off on the coarsened vault of `CoarsenedVault.lean` credits the vault 1. A LoanServiceFee of
`10^30` makes the 19-digit sums drop the loan's value and fee, so the payoff charges and pays the broker less. -/

set_option linter.style.nativeDecide false

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault (Vault RawVault)

/-- `1.5`. -/
private def rwInstalment : Number := ⟨false, 1500000000000000000, -18⟩

/-- The coarsened run with a loan D of 1.5 in one payment due 850 days after it, created before loan A's late
payment coarsens the vault. -/
private def rwVaultTxs : List LendingTx :=
  cwTxs.take 8 ++
  [.loanSet 0 rwInstalment (cwRates 0) cwFees (some 73440000) (some 1) (some 60) 0 false false,
   .close 69207461,
   .loanPay 0 .late ⟨false, 7000000000000000000, -3⟩]

/-- `10^30`. -/
private def rwHugeFee : Number := ⟨false, 1000000000000000000, 12⟩

/-- A broker with a 10% management fee, then a loan of 1000 at 10% over one year in one payment with
LoanServiceFee `10^30`. -/
private def rwFeeTxs : List LendingTx :=
  [.vaultDeposit 0 (cwAmount 1000000000000000 (-1)) false,
   .close 1001,
   .loanBrokerCreate ⟨none, some 10000, none, none⟩,
   .loanSet 0 ⟨false, 1000000000000000000, -15⟩ { cwRates 0 with interestRate := 10000 }
     { cwFees with serviceFee := rwHugeFee } (some 31536000) (some 1) (some 60) 0 false false]

end XRPL.Model.Lending
