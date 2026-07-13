import XRPL.Model.Protocol.STAmount
import XRPL.Model.Protocol.Number
import XRPL.Model.Protocol.TER
import XRPL.Model.Vault.Vault
import XRPL.Model.Vault.VaultWithdraw
import XRPL.Model.Vault.Helpers

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault

inductive CanClawbackVaultSharesResult where
  | error (error : TER)
  | assets (amount : STAmount) 

inductive AmountClawback where
  | vaultShares
  | vaultAssets (amount : STAmount)

structure ComputeClawbackResult where
  error : Option TER
  assetsRecovered : STAmount
  sharesDestroyed : STAmount

structure ClawbackResult where
  error : Option TER
  vault' : Vault
  assetsRecovered : STAmount
  sharesDestroyed : STAmount

def canClawbackVaultShares (vault : Vault) : Except String CanClawbackVaultSharesResult := do
  if vault.sharesTotal.mantissa_ == 0 || (vault.assetsTotal.mantissa_ != 0 || vault.assetsAvailable.mantissa_ != 0) then do
    return .error .tecNO_PERMISSION
  return .assets (← STAmount.ofNumber vault.sharesAsset vault.sharesTotal .to_nearest)


def computeClawback (vault : Vault) (amount : AmountClawback) : Except String ComputeClawbackResult := do
  let result : ComputeClawbackResult := ⟨none, STAmount.ofAsset vault.asset, STAmount.ofAsset vault.sharesAsset⟩
  let amount ← match amount with 
  | .vaultShares => pure (← STAmount.ofNumber vault.sharesAsset vault.sharesTotal .to_nearest)
  | .vaultAssets amount => pure amount
  if amount.negative then
    return {result with error := some .tecINTERNAL}
  try
    let sharesDestroyed ← assetsToSharesWithdraw vault amount false false
    let assetsRecovered ← Vault.sharesToAssetsWithdraw vault sharesDestroyed false

    let assetsRecoveredNumber ← assetsRecovered.toNumber .to_nearest
    if assetsRecoveredNumber.operator_gt vault.assetsAvailable then
      let assetsRecovered ← STAmount.ofNumber vault.asset vault.assetsAvailable .to_nearest
      let sharesDestroyed ← assetsToSharesWithdraw vault assetsRecovered true false
      let assetsRecovered ← Vault.sharesToAssetsWithdraw vault sharesDestroyed false

      let assetsRecoveredNumber ← assetsRecovered.toNumber .to_nearest
      if assetsRecoveredNumber.operator_gt vault.assetsAvailable then
        return {result with error := some .tecINTERNAL}
      return {result with assetsRecovered := assetsRecovered, sharesDestroyed := sharesDestroyed}
    return {result with assetsRecovered := assetsRecovered, sharesDestroyed := sharesDestroyed}
  catch e =>
    if isOverflow e then
      return ⟨.some .tecPATH_DRY, STAmount.ofAsset vault.asset, STAmount.ofAsset vault.sharesAsset⟩
    else
      throw e


def clawback (vault : Vault) (amount : AmountClawback) : Except String ClawbackResult := do
  let result ← computeClawback vault amount
  if result.error.isSome then
    return {result with vault' := vault}

  if result.sharesDestroyed.isZero then
    return {result with error := .some .tecPRECISION_LOSS, vault' := vault}

  let sharesDestroyedNumber ← result.sharesDestroyed.toNumber .to_nearest
  let assetsRecoveredNumber ← result.assetsRecovered.toNumber .to_nearest
  let vault' := {
    vault with
      sharesTotal := ← vault.sharesTotal.operator_sub sharesDestroyedNumber .to_nearest
      assetsAvailable := ← vault.assetsAvailable.operator_sub assetsRecoveredNumber .to_nearest
      assetsTotal := ← vault.assetsTotal.operator_sub assetsRecoveredNumber .to_nearest
  }
  return {result with vault' := vault'}

end XRPL.Model.SingleAssetVault
