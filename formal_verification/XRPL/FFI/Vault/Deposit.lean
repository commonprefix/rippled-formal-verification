import XRPL.NewModel.SingleAssetVault.VaultDeposit
import XRPL.Model.Protocol.Number
import XRPL.Model.Protocol.STAmount
import XRPL.Model.Protocol.Asset
import XRPL.FFI.CommonFFI

open XRPL.FFI (FFIRoundedDepositResult encodeAsset)
open XRPL.Model.Protocol (Number STAmount Asset)

def encodeRoundedDeposit (r : Except String RoundedDeposit) : FFIRoundedDepositResult :=
  match r with
  | .error _ => ⟨0, 0, 0, 0, 0, 2⟩
  | .ok (.rejected t) => ⟨t.code.toInt64, 0, 0, 0, 0, 1⟩
  | .ok (.rounded s) =>
      ⟨0, s.mantissa, s.exponent.toInt64, encodeAsset s.asset, (if s.negative then 1 else 0), 0⟩

@[export lean_rounded_deposit_amount]
def lean_rounded_deposit_amount (vault : Vault) (amount : STAmount) : FFIRoundedDepositResult :=
  encodeRoundedDeposit (vault.roundedDepositAmount amount)

@[export lean_vault_state_build]
def lean_vault_state_build (assetsTotal : Number) (asset : Asset) : Vault := { assetsTotal, asset }

@[export lean_vault_state_assets_total]
def lean_vault_state_assets_total (vs : Vault) : Number := vs.assetsTotal

@[export lean_vault_state_asset]
def lean_vault_state_asset (vs : Vault) : Asset := vs.asset
