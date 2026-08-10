import XRPL.Model.Protocol.Number
import XRPL.Model.Protocol.NumericType
import XRPL.Model.Vault.Vault

open XRPL.Model.Protocol (Number NumericType)
open XRPL.Model.SingleAssetVault

@[export lean_vault_state_build]
def lean_vault_state_build (assetsTotal : Number) (assetsAvailable : Number)
    (hasMaximum : UInt8) (assetsMaximum : Number)
    (numericType : NumericType) (scale : UInt8) (sharesTotal : Number) (lossUnrealized : Number)
    : Vault :=
  { assetsTotal, assetsAvailable,
    assetsReserved := Number.zero, -- new field, set zero for now
    assetsMaximum := if hasMaximum != 0 then some assetsMaximum else none,
    numericType, scale, sharesTotal, lossUnrealized }

@[export lean_vault_state_assets_total]
def lean_vault_state_assets_total (vault : Vault) : Number := vault.assetsTotal
@[export lean_vault_state_assets_available]
def lean_vault_state_assets_available (vault : Vault) : Number := vault.assetsAvailable
@[export lean_vault_state_has_maximum]
def lean_vault_state_has_maximum (vault : Vault) : UInt8 := if vault.assetsMaximum.isSome then 1 else 0
-- Accessor semantics mirror the C++ read of the default-valued field: absent reads as 0.
@[export lean_vault_state_assets_maximum]
def lean_vault_state_assets_maximum (vault : Vault) : Number := vault.assetsMaximum.getD Number.zero
@[export lean_vault_state_numeric_type]
def lean_vault_state_numeric_type (vault : Vault) : NumericType := vault.numericType
-- 3-way tag matching the C++ VaultState.numericType contract:
-- 0 = native (XRP), 1 = int64 (MPT), 2 = fractional (IOU).
@[export lean_vault_state_numeric_tag]
def lean_vault_state_numeric_tag (vault : Vault) : UInt8 :=
  match vault.numericType with
  | .fractional => 2
  | .integral maxValue _ _ _ => if maxValue == 100000000000000000 then 0 else 1
@[export lean_vault_state_scale]
def lean_vault_state_scale (vault : Vault) : UInt8 := vault.scale
@[export lean_vault_state_shares_total]
def lean_vault_state_shares_total (vault : Vault) : Number := vault.sharesTotal
@[export lean_vault_state_loss_unrealized]
def lean_vault_state_loss_unrealized (vault : Vault) : Number := vault.lossUnrealized
