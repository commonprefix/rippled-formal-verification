import XRPL.Model.Protocol.Number
import XRPL.Model.Protocol.STAmount
import XRPL.Model.Protocol.TER
import XRPL.Model.Vault.Vault

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol

def Vault.canBurnShares (v : Vault) (amount holderShares : STAmount) : TerExcept STAmount := do
  if !v.isInsolvent then
    throw .tecNO_PERMISSION
  if !amount.isZero && !(amount.operator_eq holderShares) then
    throw .tecLIMIT_EXCEEDED
  let sharesTotal ← STAmount.ofNumber .int64 v.sharesTotal .to_nearest
  return sharesTotal

-- The owner burns the holder's shares.
def Vault.burnShares (v : Vault) (sharesDestroyed : STAmount) : TerExcept Vault := do
  if sharesDestroyed.isZero then
    throw .tecPRECISION_LOSS

  let vault := v.toRawVault
  let sharesDestroyedNumber ← sharesDestroyed.toNumber .to_nearest
  let vault' := {
    vault with
      sharesTotal := ← vault.sharesTotal.operator_sub sharesDestroyedNumber .to_nearest
  }
  vault'.to_lawful

end XRPL.Model.SingleAssetVault
