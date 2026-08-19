import XRPL.Model.Protocol.Number
import XRPL.Model.Protocol.NumericType
import XRPL.Model.Vault.VaultCreate

open XRPL.Model.Protocol (Number NumericType)
open XRPL.Model.SingleAssetVault

@[export lean_vault_create]
def lean_vault_create (hasMaximum : UInt8) (assetsMaximum : Number)
    (numericType : NumericType) (scale : UInt8) : Vault :=
  Vault.create numericType scale (if hasMaximum != 0 then some assetsMaximum else none)
