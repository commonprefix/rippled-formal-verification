import XRPL.Model.Protocol.Number
import XRPL.Model.Protocol.NumericType
import XRPL.Model.Vault.Vault

open XRPL.Model.Protocol (Number NumericType)
open XRPL.Model.SingleAssetVault

@[export lean_vault_state_build]
def lean_vault_state_build (assetsTotal : Number) (assetsAvailable : Number) (assetsMaximum : Number)
    (numericType : NumericType) (scale : UInt8) (sharesTotal : Number) (interestUnrealized lossUnrealized : Number)
    : Vault :=
  { assetsTotal, assetsAvailable, assetsMaximum, numericType, scale, sharesTotal, interestUnrealized, lossUnrealized }

@[export lean_vault_state_assets_total]
def lean_vault_state_assets_total (vault : Vault) : Number := vault.assetsTotal
@[export lean_vault_state_assets_available]
def lean_vault_state_assets_available (vault : Vault) : Number := vault.assetsAvailable
@[export lean_vault_state_assets_maximum]
def lean_vault_state_assets_maximum (vault : Vault) : Number := vault.assetsMaximum
@[export lean_vault_state_numeric_type]
def lean_vault_state_numeric_type (vault : Vault) : NumericType := vault.numericType
@[export lean_vault_state_scale]
def lean_vault_state_scale (vault : Vault) : UInt8 := vault.scale
@[export lean_vault_state_shares_total]
def lean_vault_state_shares_total (vault : Vault) : Number := vault.sharesTotal
@[export lean_vault_state_interest_unrealized]
def lean_vault_state_interest_unrealized (vault : Vault) : Number := vault.interestUnrealized
@[export lean_vault_state_loss_unrealized]
def lean_vault_state_loss_unrealized (vault : Vault) : Number := vault.lossUnrealized
