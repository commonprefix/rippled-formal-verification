import XRPL.Model.Protocol.Number
import XRPL.Model.Protocol.Rounding
import XRPL.Model.Protocol.TER
import XRPL.Model.Vault.Vault

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol

-- `blockDeposit`: none = no flag, some true = tfVaultDepositBlock, some false = tfVaultDepositUnblock
def Vault.canVaultUpdate (v : Vault) (assetsMaximum : Option Number) (blockDeposit : Option Bool)
    : Except Error TER := do
  if let some m := assetsMaximum then
    if !(← m.isOnExponentGrid v.baseExponent v.numericType) then
      return .tecPRECISION_LOSS

  if !v.ownerCanBlockDeposit && blockDeposit.isSome then
    return .tecNO_PERMISSION

  if let some m := assetsMaximum then
    let assetsTotal ← v.assetsTotal
    if m.operator_ne Number.zero && m.operator_lt assetsTotal then
      return .tecLIMIT_EXCEEDED

  return .tesSUCCESS

def Vault.update (v : Vault) (assetsMaximum : Option Number) (blockDeposit : Option Bool)
    : Except Error Vault :=
  let assetsMaximum' := match assetsMaximum with
    | none => v.assetsMaximum
    | some m => if m.operator_eq Number.zero then none else some m

  let depositBlocked' := blockDeposit.getD v.depositBlocked
  let rawVault' : RawVault := { v.toRawVault with
    assetsMaximum := assetsMaximum'
    depositBlocked := depositBlocked' }

  rawVault'.to_lawful

end XRPL.Model.SingleAssetVault
