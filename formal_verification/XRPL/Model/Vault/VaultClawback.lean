import XRPL.Model.Protocol.Number
import XRPL.Model.Protocol.STAmount
import XRPL.Model.Protocol.TER
import XRPL.Model.Vault.Vault
import XRPL.Model.Vault.VaultWithdraw

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol

structure ComputeClawbackResult where
  error : Option TER
  assetsRecovered : STAmount
  sharesDestroyed : STAmount

structure ClawbackResult where
  error : Option TER
  vault' : Vault
  assetsRecovered : STAmount
  sharesDestroyed : STAmount

-- A rejection changes nothing and reports nothing: the vault is returned
-- unchanged and both amount fields are zero.
def ClawbackResult.rejected (vault : Vault) (ter : TER) : ClawbackResult :=
  ⟨some ter, vault, STAmount.zero vault.numericType, STAmount.zero .int64⟩

def assetsToSharesClawback (vault : Vault) (assets holderShares : STAmount) : Except Error STAmount := do
  if assets.isZero then
    -- zero means destroy "all" holder shares
    return holderShares
  assetsToSharesWithdraw vault assets false false

def computeClawback (vault : Vault) (assets holderShares : STAmount) : Except Error ComputeClawbackResult := do
  let result : ComputeClawbackResult := ⟨none, STAmount.zero vault.numericType, STAmount.zero .int64⟩
  if assets.negative then
    return {result with error := some .tecINTERNAL}
  try
    let sharesDestroyed ← assetsToSharesClawback vault assets holderShares
    let assetsRecovered ← Vault.sharesToAssetsWithdraw vault sharesDestroyed false

    let assetsRecoveredNumber ← assetsRecovered.toNumber .to_nearest
    if assetsRecoveredNumber.operator_gt vault.assetsAvailable then
      let assetsRecovered ← STAmount.ofNumber vault.numericType vault.assetsAvailable .to_nearest
      let sharesDestroyed ← assetsToSharesWithdraw vault assetsRecovered true false
      let assetsRecovered ← Vault.sharesToAssetsWithdraw vault sharesDestroyed false

      let assetsRecoveredNumber ← assetsRecovered.toNumber .to_nearest
      if assetsRecoveredNumber.operator_gt vault.assetsAvailable then
        return {result with error := some .tecINTERNAL}
      return {result with assetsRecovered := assetsRecovered, sharesDestroyed := sharesDestroyed}
    return {result with assetsRecovered := assetsRecovered, sharesDestroyed := sharesDestroyed}
  catch e =>
    if isOverflow e then
      return ⟨.some .tecPATH_DRY, STAmount.zero vault.numericType, STAmount.zero .int64⟩
    else
      throw e


def Vault.clawback (vault : Vault) (assets holderShares : STAmount) : Except Error ClawbackResult := do
  let result ← computeClawback vault assets holderShares
  if result.error.isSome then
    return ⟨result.error, vault, STAmount.zero vault.numericType, STAmount.zero .int64⟩

  if result.sharesDestroyed.isZero then
    return .rejected vault .tecPRECISION_LOSS

  let sharesDestroyedNumber ← result.sharesDestroyed.toNumber .to_nearest
  let assetsRecoveredNumber ← result.assetsRecovered.toNumber .to_nearest
  let assetsTotal' ← vault.assetsTotal.operator_sub assetsRecoveredNumber .to_nearest

  -- (waiting the C++ fix) reject a recovery too small to reduce the stored assetsTotal
  let assetsTotalRounded ← STAmount.ofNumber vault.numericType vault.assetsTotal .to_nearest
  let assetsTotalRounded' ← STAmount.ofNumber vault.numericType assetsTotal' .to_nearest
  if assetsRecoveredNumber.mantissa_ != 0 && assetsTotalRounded.operator_eq assetsTotalRounded' then
    return .rejected vault .tecPRECISION_LOSS

  let vault' := {
    vault with
      sharesTotal := ← vault.sharesTotal.operator_sub sharesDestroyedNumber .to_nearest
      assetsAvailable := ← vault.assetsAvailable.operator_sub assetsRecoveredNumber .to_nearest
      assetsTotal := assetsTotal'
  }
  return ⟨none, vault', result.assetsRecovered, result.sharesDestroyed⟩

end XRPL.Model.SingleAssetVault
