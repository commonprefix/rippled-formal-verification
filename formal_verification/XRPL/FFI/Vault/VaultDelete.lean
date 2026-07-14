import XRPL.Model.Vault.VaultDelete

open XRPL.Model.SingleAssetVault

@[export lean_can_vault_delete]
def lean_can_vault_delete (vault : Vault) : Int32 :=
  vault.canVaultDelete.code
