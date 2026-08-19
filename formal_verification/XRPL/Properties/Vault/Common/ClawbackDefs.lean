import XRPL.Properties.Vault.Defs
import XRPL.Model.Vault.VaultClawback
import XRPL.Properties.Vault.Common.DepositDefs
import XRPL.Properties.Vault.Common.WithdrawDefs

/-! # Exact-arithmetic reference values for `Vault.clawback`

The ideal (unrounded) exchange quantities the `Vault.clawback` accuracy
headlines are stated against. Kept in `Common` so both the headline file and
its proof files can see them. -/

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol

/-- The exact share amount a clawback of `assets` destroys, before any
rounding. The XLS-0065 exchange formula for the withdrawal direction:
`sharesTotal * assets / withdrawNav`. A clawback never waives the unrealized
loss, so the price always uses `withdrawNav`. -/
def Vault.idealSharesClawback (v : Vault) (assets : ℚ) : ℚ :=
  v.toExact.sharesTotal * assets / v.withdrawNav

/-- The exact asset amount recovered for destroying `shares`, before any
rounding: `withdrawNav * shares / sharesTotal`. -/
def Vault.idealAssetsClawback (v : Vault) (shares : ℚ) : ℚ :=
  v.withdrawNav * shares / v.toExact.sharesTotal

end XRPL.Model.SingleAssetVault
