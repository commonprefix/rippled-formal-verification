import XRPL.Model.Protocol.Number
import XRPL.Model.Protocol.TER
import XRPL.Model.Vault.VaultSet

open XRPL.Model.Protocol (Number Error)
open XRPL.Model.SingleAssetVault

@[export lean_can_vault_update]
def lean_can_vault_update (v : Vault) (assetsMaximum : Option Number) (blockDeposit unblockDeposit : UInt8)
    : Except Error Int32 :=
  (·.code) <$> v.canVaultUpdate assetsMaximum (blockDeposit != 0) (unblockDeposit != 0)

@[export lean_vault_update]
def lean_vault_update (v : Vault) (assetsMaximum : Option Number) (blockDeposit unblockDeposit : UInt8)
    : Except Error Vault :=
  v.update assetsMaximum (blockDeposit != 0) (unblockDeposit != 0)
