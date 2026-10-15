import XRPL.Model.Protocol.Number
import XRPL.Model.Protocol.NumericType
import XRPL.Model.Protocol.Rounding
import XRPL.Model.Protocol.TER
import XRPL.Model.Vault.Vault

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol

-- C++ VaultCreate::preclaim
def Vault.canCreate (scale : Option UInt8) (assetsMaximum : Option Number) (schedule : Option VaultSchedule)
    (parentCloseTime : UInt32) (nt : NumericType) : Except Error TER := do
  if let some s := schedule then
    let hasSubscriptionExpired : Bool := parentCloseTime ≥ s.subscriptionDate
    let hasRedemptionExpired : Bool := parentCloseTime ≥ s.redemptionDate
    if hasSubscriptionExpired || hasRedemptionExpired then
      return .tecEXPIRED

  if let some m := assetsMaximum then
    let baseExponent := nt.baseExponent (scale.getD vaultDefaultIOUScale)
    if !(← m.isOnExponentGrid baseExponent nt) then
      return .tecPRECISION_LOSS
  return .tesSUCCESS

-- C++ VaultCreate::doApply: an empty FixedPrecision vault.
def Vault.create (scale : Option UInt8) (assetsMaximum : Option Number) (schedule : Option VaultSchedule)
    (earlyExitFeeRate : Option TenthBips32) (ownerCanBlockDeposit : Bool) (nt : NumericType) : Except Error Vault :=
  let scale' : UInt8 := if nt.isIntegral then 0 else scale.getD vaultDefaultIOUScale
  let assetsMaximum' := assetsMaximum.filter (·.operator_ne Number.zero)
  -- only a closed-ended vault stores the rate
  let earlyExitFeeRate' := if schedule.isSome then earlyExitFeeRate else none

  let rawVault : RawVault := {
    assetsAvailable := Number.zero
    assetsDeployed := Number.zero
    assetsReserved := Number.zero
    assetsMaximum := assetsMaximum'
    numericType := nt
    scale := scale'
    sharesTotal := Number.zero
    lossUnrealized := Number.zero
    yieldUnrealized := Number.zero
    schedule
    earlyExitFeeRate := earlyExitFeeRate'
    ownerCanBlockDeposit
    depositBlocked := false }

  rawVault.to_lawful

end XRPL.Model.SingleAssetVault
