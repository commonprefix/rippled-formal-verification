import XRPL.NewModel.SingleAssetVault.VaultDeposit
import XRPL.Model.Protocol.Number
import XRPL.Model.Protocol.STAmount
import XRPL.Model.Protocol.Asset
import XRPL.FFI.CommonFFI

open XRPL.FFI (FFITERResult encodeTERResult)
open XRPL.Model.Protocol (Number STAmount Asset)

@[export lean_can_deposit]
def lean_can_deposit (state : VaultState) (amount : STAmount) (accountBalance : Option STAmount) : FFITERResult :=
  encodeTERResult (canDeposit state amount accountBalance)

@[export lean_vault_state_build]
def lean_vault_state_build (assetsTotal : Number) (asset : Asset) : VaultState := { assetsTotal, asset }

@[export lean_vault_state_assets_total]
def lean_vault_state_assets_total (vs : VaultState) : Number := vs.assetsTotal

@[export lean_vault_state_asset]
def lean_vault_state_asset (vs : VaultState) : Asset := vs.asset
