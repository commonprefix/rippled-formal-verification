import XRPL.Model.Protocol.Number
import XRPL.Model.Protocol.NumericType
import XRPL.Model.Vault.VaultDelete

open XRPL.Model.Protocol (Number NumericType Error)
open XRPL.Model.SingleAssetVault

@[export lean_can_vault_delete]
def lean_can_vault_delete (lv : LawfulVault) : Int32 :=
  lv.canVaultDelete.code
