import XRPL.Properties.Vault.Defs
import XRPL.Model.Vault.VaultClawback
import XRPL.Properties.Vault.Common.DepositDefs
import XRPL.Properties.Vault.Common.WithdrawDefs

/-! # Exact-arithmetic reference values for `Vault.clawback`

The ideal (unrounded) exchange quantities the `Vault.clawback` accuracy
headlines are stated against. -/

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol

/-- The pricing of a clawback, read off the code: the shares the request names and their price, repriced from the
cash when that price exceeds the cash. -/
inductive Vault.ClawbackPriced (v : Vault) (assets holderShares : STAmount) (waive : Bool) :
    STAmount → STAmount → Prop
  | direct (shares recovered : STAmount) (recoveredNumber : Number) :
      assetsToSharesClawback v assets holderShares waive = .ok shares →
      v.sharesToAssetsWithdraw shares waive = .ok recovered →
      recovered.toNumber .to_nearest = .ok recoveredNumber →
      recoveredNumber.operator_gt v.assetsAvailable = false →
      Vault.ClawbackPriced v assets holderShares waive shares recovered
  | capped (shares0 recovered0 cash shares recovered : STAmount) (recoveredNumber0 recoveredNumber : Number) :
      assetsToSharesClawback v assets holderShares waive = .ok shares0 →
      v.sharesToAssetsWithdraw shares0 waive = .ok recovered0 →
      recovered0.toNumber .to_nearest = .ok recoveredNumber0 →
      recoveredNumber0.operator_gt v.assetsAvailable = true →
      STAmount.ofNumber v.numericType v.assetsAvailable .to_nearest = .ok cash →
      assetsToSharesWithdraw v cash true waive = .ok shares →
      v.sharesToAssetsWithdraw shares waive = .ok recovered →
      recovered.toNumber .to_nearest = .ok recoveredNumber →
      recoveredNumber.operator_gt v.assetsAvailable = false →
      Vault.ClawbackPriced v assets holderShares waive shares recovered

/-- Same formula as `idealSharesWithdraw`, the clawback prices through the withdrawal pipeline. -/
abbrev RawVault.idealSharesClawback (rv : RawVault) (waiveUnrealizedLoss : Bool) (assets : ℚ) : ℚ :=
  rv.idealSharesWithdraw waiveUnrealizedLoss assets

/-- Same formula as `idealAssetsWithdraw`, the clawback prices through the withdrawal pipeline. -/
abbrev RawVault.idealAssetsClawback (rv : RawVault) (waiveUnrealizedLoss : Bool) (shares : ℚ) : ℚ :=
  rv.idealAssetsWithdraw waiveUnrealizedLoss shares

end XRPL.Model.SingleAssetVault
