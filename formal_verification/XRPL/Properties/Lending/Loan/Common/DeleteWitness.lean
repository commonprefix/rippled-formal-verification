import XRPL.Properties.Lending.Ledger.Common.CoarsenedVault

/-! # A pending delete on a coarsened vault

On the coarsened vault of `CoarsenedVault.lean` a pending delete can credit AssetsAvailable other than the
principal: deleting a pending loan of 0.6 credits 1. -/

set_option linter.style.nativeDecide false

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault (Vault)

/-- A run on the coarsened vault of `CoarsenedVault.lean`: loans A, B and C, a pending loan E of 0.6, then
loan A paid 800 days late, which takes AssetsAvailable to 1874246907153724 on the grid of 1. -/
private def dwTxs : List LendingTx :=
  cwTxs.take 8 ++
  [.loanSet 0 ⟨false, 6000000000000000000, -19⟩ (cwRates 0) cwFees (some 86400) (some 1) (some 60) 70000000 true
     false,
   .close 69207461,
   .loanPay 0 .late ⟨false, 7000000000000000000, -3⟩]

end XRPL.Model.Lending
