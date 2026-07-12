import XRPL.Model.Vault.Vault
import XRPL.Model.Protocol.Number
import XRPL.Model.Protocol.Asset

open XRPL.Model.Protocol (Number Asset)

@[export lean_vault_state_build]
def lean_vault_state_build (assetsTotal : Number) (assetsAvailable : Number) (asset : Asset) (scale : UInt8)
    (sharesTotal : Number) (sharesAsset : Asset) (interestUnrealized lossUnrealized : Number) : Vault :=
  { assetsTotal, assetsAvailable, asset, scale, sharesTotal, sharesAsset, interestUnrealized, lossUnrealized }

@[export lean_vault_state_assets_total]
def lean_vault_state_assets_total (vault : Vault) : Number := vault.assetsTotal
@[export lean_vault_state_assets_available]
def lean_vault_state_assets_available (vault : Vault) : Number := vault.assetsAvailable
@[export lean_vault_state_asset]
def lean_vault_state_asset (vault : Vault) : Asset := vault.asset
@[export lean_vault_state_scale]
def lean_vault_state_scale (vault : Vault) : UInt8 := vault.scale
@[export lean_vault_state_shares_total]
def lean_vault_state_shares_total (vault : Vault) : Number := vault.sharesTotal
@[export lean_vault_state_shares_asset]
def lean_vault_state_shares_asset (vault : Vault) : Asset := vault.sharesAsset
@[export lean_vault_state_interest_unrealized]
def lean_vault_state_interest_unrealized (vault : Vault) : Number := vault.interestUnrealized
