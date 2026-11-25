import XRPL.Model.Protocol.Number
import XRPL.Model.Protocol.TER
import XRPL.Model.Vault.VaultSet

open XRPL.Model.Protocol (Number Error)
open XRPL.Model.SingleAssetVault

-- the two transaction flags as the model's `Option Bool`; both set would have failed preflight
def blockDepositOf (blockDeposit unblockDeposit : UInt8) : Except Error (Option Bool) :=
  match blockDeposit != 0, unblockDeposit != 0 with
  | true, true => .error .badInput
  | true, false => .ok (some true)
  | false, true => .ok (some false)
  | false, false => .ok none

@[export lean_can_vault_update]
-- `.error .badInput`: both flags would have failed preflight (`temINVALID_FLAG`).
def lean_can_vault_update (v : Vault) (assetsMaximum : Option Number) (blockDeposit unblockDeposit : UInt8)
    : Except Error Int32 := do
  let ter ← v.canVaultUpdate assetsMaximum (← blockDepositOf blockDeposit unblockDeposit)
  return ter.code

@[export lean_vault_update]
def lean_vault_update (v : Vault) (assetsMaximum : Option Number) (blockDeposit unblockDeposit : UInt8)
    : Except Error Vault := do
  v.update assetsMaximum (← blockDepositOf blockDeposit unblockDeposit)
