import XRPL.Properties.Vault.Proofs.CreateUpdate

/-! # `Vault.canCreate` and `Vault.create`

A vault created with in-range fields is lawful and starts with no assets and no shares. -/

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol

/-- Vault creation with fields that pass the lawfulness check -> it succeeds, with no assets and no shares, and an
AssetsMaximum that passes the checks is stored exactly. -/
theorem Vault.create_success (nt : NumericType) :
    -- an IOU scale at most 10, a nonzero maximum positive, a valid investment period, and with a schedule a fee rate
    -- at most 100%
    (∀ (scale : Option UInt8) (assetsMaximum : Option Number) (schedule : Option VaultSchedule)
      (earlyExitFeeRate : Option TenthBips32) (ownerCanBlockDeposit : Bool),
      (nt.isIntegral = false → scale.getD vaultDefaultIOUScale ≤ vaultMaximumIOUScale) →
      (∀ m ∈ assetsMaximum, m.operator_ne Number.zero = true →
        m.isNormalized ∧ Number.zero.operator_lt m = true) →
      (∀ s ∈ schedule, s.hasValidGap = true) → (∀ s ∈ schedule, ∀ r ∈ earlyExitFeeRate, r ≤ maxEarlyExitFeeRate) →
      ∃ v, Vault.create scale assetsMaximum schedule earlyExitFeeRate ownerCanBlockDeposit nt = .ok v) ∧
    (∀ (scale : Option UInt8) (assetsMaximum : Option Number) (schedule : Option VaultSchedule)
      (earlyExitFeeRate : Option TenthBips32) (ownerCanBlockDeposit : Bool) (v : Vault),
      Vault.create scale assetsMaximum schedule earlyExitFeeRate ownerCanBlockDeposit nt = .ok v →
      v.assetsAvailable = Number.zero ∧ v.assetsDeployed = Number.zero ∧ v.assetsReserved = Number.zero ∧
        v.sharesTotal = Number.zero ∧ v.lossUnrealized = Number.zero ∧ v.yieldUnrealized = Number.zero) ∧
    ∀ (scale : Option UInt8) (m : Number) (schedule : Option VaultSchedule) (t : UInt32),
      Vault.canCreate scale (some m) schedule t nt = .ok .tesSUCCESS → STAmount.isRounded nt m = false :=
  ⟨fun scale assetsMaximum schedule earlyExitFeeRate ownerCanBlockDeposit =>
      Vault.create_success_proof scale assetsMaximum schedule earlyExitFeeRate ownerCanBlockDeposit nt,
    fun scale assetsMaximum schedule earlyExitFeeRate ownerCanBlockDeposit =>
      Vault.create_empty_proof scale assetsMaximum schedule earlyExitFeeRate ownerCanBlockDeposit nt,
    fun scale m schedule t => Vault.canCreate_assetsMaximum_not_rounded_proof scale m schedule t nt⟩

/-- The exits of `canCreate`, in the order it runs its checks. Each line assumes the checks before it passed. -/
theorem Vault.canCreate_exits (scale : Option UInt8) (t : UInt32) (nt : NumericType) :
    (∀ (assetsMaximum : Option Number) (s : VaultSchedule),
      (t ≥ s.subscriptionDate || t ≥ s.redemptionDate) = true →
      Vault.canCreate scale assetsMaximum (some s) t nt = .ok .tecEXPIRED) ∧
    (∀ (m : Number) (schedule : Option VaultSchedule),
      (∀ s ∈ schedule, (t ≥ s.subscriptionDate || t ≥ s.redemptionDate) = false) →
      m.isOnExponentGrid (nt.baseExponent (scale.getD vaultDefaultIOUScale)) nt = .ok false →
      Vault.canCreate scale (some m) schedule t nt = .ok .tecPRECISION_LOSS) ∧
    ∀ (assetsMaximum : Option Number) (schedule : Option VaultSchedule),
      (∀ s ∈ schedule, (t ≥ s.subscriptionDate || t ≥ s.redemptionDate) = false) →
      (∀ m ∈ assetsMaximum, m.isOnExponentGrid (nt.baseExponent (scale.getD vaultDefaultIOUScale)) nt = .ok true) →
      Vault.canCreate scale assetsMaximum schedule t nt = .ok .tesSUCCESS :=
  ⟨fun assetsMaximum s => Vault.canCreate_expired_proof scale assetsMaximum s t nt,
    fun m schedule => Vault.canCreate_precision_loss_proof scale m schedule t nt,
    fun assetsMaximum schedule => Vault.canCreate_success_proof scale assetsMaximum schedule t nt⟩

/-- Error codes: success, tecEXPIRED or tecPRECISION_LOSS. -/
theorem Vault.canCreate_error_codes (scale : Option UInt8) (assetsMaximum : Option Number)
    (schedule : Option VaultSchedule) (t : UInt32) (nt : NumericType) (ter : TER)
    (hok : Vault.canCreate scale assetsMaximum schedule t nt = .ok ter) :
    ter = .tesSUCCESS ∨ ter = .tecEXPIRED ∨ ter = .tecPRECISION_LOSS :=
  Vault.canCreate_error_codes_proof scale assetsMaximum schedule t nt ter hok

/-- A field out of range -> `create` returns notLawful, one line per field rule. -/
theorem Vault.create_not_lawful (scale : Option UInt8) (assetsMaximum : Option Number)
    (schedule : Option VaultSchedule) (earlyExitFeeRate : Option TenthBips32) (ownerCanBlockDeposit : Bool)
    (nt : NumericType) :
    (nt.isIntegral = false → vaultMaximumIOUScale < scale.getD vaultDefaultIOUScale →
      Vault.create scale assetsMaximum schedule earlyExitFeeRate ownerCanBlockDeposit nt = .error .notLawful) ∧
    (∀ m : Number, assetsMaximum = some m → m.operator_ne Number.zero = true →
      ¬ m.isNormalized ∨ Number.zero.operator_lt m = false →
      Vault.create scale assetsMaximum schedule earlyExitFeeRate ownerCanBlockDeposit nt = .error .notLawful) ∧
    (∀ s : VaultSchedule, schedule = some s → s.hasValidGap = false →
      Vault.create scale assetsMaximum schedule earlyExitFeeRate ownerCanBlockDeposit nt = .error .notLawful) ∧
    ∀ (s : VaultSchedule) (r : TenthBips32), schedule = some s → earlyExitFeeRate = some r →
      maxEarlyExitFeeRate < r →
      Vault.create scale assetsMaximum schedule earlyExitFeeRate ownerCanBlockDeposit nt = .error .notLawful :=
  ⟨Vault.create_scale_out_of_range_proof scale assetsMaximum schedule earlyExitFeeRate ownerCanBlockDeposit nt,
    fun m hm => hm ▸ Vault.create_assetsMaximum_out_of_range_proof scale m schedule earlyExitFeeRate
      ownerCanBlockDeposit nt,
    fun s hs => hs ▸ Vault.create_schedule_gap_proof scale assetsMaximum s earlyExitFeeRate ownerCanBlockDeposit nt,
    fun s r hs hr => hs ▸ hr ▸ Vault.create_fee_above_maximum_proof scale assetsMaximum s r ownerCanBlockDeposit nt⟩

end XRPL.Model.SingleAssetVault
