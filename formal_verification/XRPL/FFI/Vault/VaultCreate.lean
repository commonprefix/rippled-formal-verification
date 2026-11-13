import XRPL.Model.Protocol.Number
import XRPL.Model.Protocol.NumericType
import XRPL.Model.Protocol.TER
import XRPL.Model.Vault.VaultCreate
import XRPL.FFI.Vault.Vault

open XRPL.Model.Protocol (Number NumericType Error)
open XRPL.Model.SingleAssetVault

@[export lean_can_vault_create]
def lean_can_vault_create (scale : Option UInt8) (assetsMaximum : Option Number)
    (subscriptionDate redemptionDate : Option UInt32) (parentCloseTime : UInt32) (nt : NumericType)
    : Except Error Int32 := do
  let schedule ← scheduleOf subscriptionDate redemptionDate
  let ter ← Vault.canCreate scale assetsMaximum schedule parentCloseTime nt
  return ter.code

@[export lean_vault_create]
def lean_vault_create (scale : Option UInt8) (assetsMaximum : Option Number)
    (subscriptionDate redemptionDate : Option UInt32) (earlyExitFeeRate : Option UInt32)
    (ownerCanBlockDeposit : UInt8) (nt : NumericType) : Except Error Vault := do
  let schedule ← scheduleOf subscriptionDate redemptionDate
  Vault.create scale assetsMaximum schedule earlyExitFeeRate (ownerCanBlockDeposit != 0) nt
