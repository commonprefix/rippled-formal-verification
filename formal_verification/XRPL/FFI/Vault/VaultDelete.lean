import XRPL.Model.Protocol.TER
import XRPL.Model.Vault.VaultDelete

open XRPL.Model.Protocol (Error)
open XRPL.Model.SingleAssetVault

@[export lean_can_vault_delete]
def lean_can_vault_delete (v : Vault) : Except Error Int32 := do
  let ter ← v.canVaultDelete
  return ter.code
