import XRPL.Model.Vault.VaultSet
import XRPL.Model.Protocol.Number

open XRPL.Model.Protocol (Number)
open XRPL.Model.SingleAssetVault

@[export lean_can_vault_set]
def lean_can_vault_set (vault : Vault) (assetsMaximum : Number) : Int32 :=
  (vault.canVaultSet assetsMaximum).code
