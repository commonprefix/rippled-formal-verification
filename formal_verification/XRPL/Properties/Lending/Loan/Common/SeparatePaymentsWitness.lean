import XRPL.Properties.Lending.Loan.Common.SeparatePayments
import XRPL.Properties.Lending.Ledger.Common.CoarsenedVault

/-! # Witness for a regular payment of two scheduled payments on a coarsened vault

Loan D of 3, two instalments of 1.5, is created just before loan A's payment 800 days late takes AssetsAvailable past
`10^16` base units. The vault then credits only whole units: 3 for both instalments together, 1 for each apart. -/

set_option linter.style.nativeDecide false

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault (Vault RawVault)

/-- The run of `cwTxs` up to loan C, then at close time 69207461 loan D of 3 in two monthly instalments without
interest, and loan A's late payment that coarsens the vault. -/
private def spTxs : List LendingTx :=
  cwTxs.take 8 ++
  [.close 69207461,
   .loanSet 0 ⟨false, 3000000000000000000, -18⟩ (cwRates 0) cwFees (some 2592000) (some 2) (some 60) 0 false false,
   .loanPay 0 .late ⟨false, 7000000000000000000, -3⟩]

/-- `1.5`, one instalment of loan D. -/
private def spHalf : Number := ⟨false, 1500000000000000000, -18⟩

/-- `3`, both instalments of loan D. -/
private def spWhole : Number := ⟨false, 3000000000000000000, -18⟩

end XRPL.Model.Lending
