import XRPL.NewModel.SingleAssetVault.VaultDeposit
import XRPL.Model.Protocol.Number
import XRPL.Model.Protocol.STAmount
import XRPL.Model.Protocol.Asset
import XRPL.FFI.CommonFFI

open XRPL.FFI (FFITERResult encodeTERResult)
open XRPL.Model.Protocol (Number STAmount Asset)

@[export lean_can_deposit]
def lean_can_deposit (state : VaultState) (amount : STAmount) (accountIsIssuer : Bool) : FFITERResult :=
  encodeTERResult (canDeposit state amount accountIsIssuer)

@[export lean_vault_state_build]
def lean_vault_state_build (assetsTotal : Number) (accountBalance : STAmount) (asset : Asset) : VaultState := { assetsTotal, accountBalance, asset }

@[export lean_vault_state_assets_total]
def lean_vault_state_assets_total (vs : VaultState) : Number := vs.assetsTotal

@[export lean_vault_state_account_balance]
def lean_vault_state_account_balance (vs : VaultState) : STAmount := vs.accountBalance

@[export lean_vault_state_asset]
def lean_vault_state_asset (vs : VaultState) : Asset := vs.asset
