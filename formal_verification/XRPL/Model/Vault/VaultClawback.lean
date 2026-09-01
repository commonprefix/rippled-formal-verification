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
  vault' : LawfulVault
  assetsRecovered : STAmount
  sharesDestroyed : STAmount

-- A rejection changes nothing and reports nothing: the vault is returned
-- unchanged and both amount fields are zero.
def ClawbackResult.rejected (lv : LawfulVault) (ter : TER) : ClawbackResult :=
  ⟨some ter, lv, STAmount.zero lv.numericType, STAmount.zero .int64⟩

def assetsToSharesClawback (lv : LawfulVault) (assets holderShares : STAmount) : Except Error STAmount := do
  if assets.isZero then
    -- zero means destroy "all" holder shares
    return holderShares
  assetsToSharesWithdraw lv assets false false

def computeClawback (lv : LawfulVault) (assets holderShares : STAmount) : Except Error ComputeClawbackResult := do
  let result : ComputeClawbackResult := ⟨none, STAmount.zero lv.numericType, STAmount.zero .int64⟩
  if assets.negative then
    return {result with error := some .tecINTERNAL}
  try
    let sharesDestroyed ← assetsToSharesClawback lv assets holderShares
    let assetsRecovered ← lv.sharesToAssetsWithdraw sharesDestroyed false

    let assetsRecoveredNumber ← assetsRecovered.toNumber .to_nearest
    if assetsRecoveredNumber.operator_gt lv.assetsAvailable then
      let assetsRecovered ← STAmount.ofNumber lv.numericType lv.assetsAvailable .to_nearest
      let sharesDestroyed ← assetsToSharesWithdraw lv assetsRecovered true false
      let assetsRecovered ← lv.sharesToAssetsWithdraw sharesDestroyed false

      let assetsRecoveredNumber ← assetsRecovered.toNumber .to_nearest
      if assetsRecoveredNumber.operator_gt lv.assetsAvailable then
        return {result with error := some .tecINTERNAL}
      return {result with assetsRecovered := assetsRecovered, sharesDestroyed := sharesDestroyed}
    return {result with assetsRecovered := assetsRecovered, sharesDestroyed := sharesDestroyed}
  catch e =>
    if isOverflow e then
      return ⟨.some .tecPATH_DRY, STAmount.zero lv.numericType, STAmount.zero .int64⟩
    else
      throw e


def LawfulVault.clawback (lv : LawfulVault) (assets holderShares : STAmount) : Except Error ClawbackResult := do
  let vault := lv.toRawVault
  let result ← computeClawback lv assets holderShares
  if result.error.isSome then
    return ⟨result.error, lv, STAmount.zero lv.numericType, STAmount.zero .int64⟩

  if result.sharesDestroyed.isZero then
    return .rejected lv .tecPRECISION_LOSS

  let sharesDestroyedNumber ← result.sharesDestroyed.toNumber .to_nearest
  let assetsRecoveredNumber ← result.assetsRecovered.toNumber .to_nearest
  let assetsTotal' ← vault.assetsTotal.operator_sub assetsRecoveredNumber .to_nearest

  -- (waiting the C++ fix) reject a recovery too small to reduce the stored assetsTotal
  let assetsTotalRounded ← STAmount.ofNumber vault.numericType vault.assetsTotal .to_nearest
  let assetsTotalRounded' ← STAmount.ofNumber vault.numericType assetsTotal' .to_nearest
  if assetsRecoveredNumber.mantissa_ != 0 && assetsTotalRounded.operator_eq assetsTotalRounded' then
    return .rejected lv .tecPRECISION_LOSS

  let vault' := {
    vault with
      sharesTotal := ← vault.sharesTotal.operator_sub sharesDestroyedNumber .to_nearest
      assetsAvailable := ← vault.assetsAvailable.operator_sub assetsRecoveredNumber .to_nearest
      assetsTotal := assetsTotal'
  }
  -- re-validate the new state into a LawfulVault. Clawback-all on a fractional vault can leave dust
  -- (sharesTotal=0, assetsTotal>0), which fails empty_shares, so this can error.
  let lv' ← vault'.to_lawful
  return ⟨none, lv', result.assetsRecovered, result.sharesDestroyed⟩

end XRPL.Model.SingleAssetVault
