import XRPL.Model.Protocol.Number
import XRPL.Model.Protocol.Rounding
import XRPL.Model.Protocol.TER
import XRPL.Model.Vault.Vault

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol

def Vault.canVaultUpdate (v : Vault) (assetsMaximum : Option Number) (blockDeposit unblockDeposit : Bool)
    : Except Error TER := do
  if let some m := assetsMaximum then
    if !(← m.isOnExponentGrid v.baseExponent v.numericType) then
      return .tecPRECISION_LOSS

  if !v.ownerCanBlockDeposit && (blockDeposit || unblockDeposit) then
    return .tecNO_PERMISSION

  if let some m := assetsMaximum then
    let assetsTotal ← v.assetsTotal
    if m.operator_ne Number.zero && m.operator_lt assetsTotal then
      return .tecLIMIT_EXCEEDED

  return .tesSUCCESS

def Vault.update (v : Vault) (assetsMaximum : Option Number) (blockDeposit unblockDeposit : Bool)
    : Except Error Vault :=
  let assetsMaximum' := match assetsMaximum with
    | none => v.assetsMaximum
    | some m => if m.operator_eq Number.zero then none else some m

  let depositBlocked' := if blockDeposit then true else if unblockDeposit then false else v.depositBlocked
  let rawVault' : RawVault := { v.toRawVault with
    assetsMaximum := assetsMaximum'
    depositBlocked := depositBlocked' }

  rawVault'.to_lawful

end XRPL.Model.SingleAssetVault
