import XRPL.Properties.Vault.Proofs.ClawbackExits
import XRPL.Properties.Vault.Proofs.ClawbackUpdates
import XRPL.Properties.Vault.Proofs.MaxValueFits

/-! # `Vault.clawback` exits

One line per exit of `Vault.clawback_exits`, in the order the clawback runs its checks. A rejection
carries only its code: the vault is not touched. The later exits assume a vault whose asset is not XRP, and the pricing
exits assume the pricing reached them, read off the code (`Vault.ClawbackPriced`). -/

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol

variable (v : Vault)

/-- The exits of `clawback`, in the order it runs its checks, then its success lines. Each line assumes the checks
before it passed. -/
theorem Vault.clawback_exits (assets holderShares : STAmount) (waive : Bool) (hnn : 0 ≤ assets.toRat) :
    (v.numericType = NumericType.native →
      (v.clawback assets holderShares waive hnn).run = .ok (.error .tecNO_PERMISSION)) ∧
    (v.numericType ≠ NumericType.native →
      (computeClawback v assets holderShares waive).run = .ok (.error .tecPATH_DRY) →
      (v.clawback assets holderShares waive hnn).run = .ok (.error .tecPATH_DRY)) ∧
    (∀ (shares recovered capped shares' recovered' : STAmount) (recoveredNumber recoveredNumber' : Number),
      v.numericType ≠ NumericType.native →
      assetsToSharesClawback v assets holderShares waive = .ok shares →
      v.sharesToAssetsWithdraw shares waive = .ok recovered →
      recovered.toNumber .to_nearest = .ok recoveredNumber → recoveredNumber.operator_gt v.assetsAvailable = true →
      STAmount.ofNumber v.numericType v.assetsAvailable .to_nearest = .ok capped →
      assetsToSharesWithdraw v capped true waive = .ok shares' →
      v.sharesToAssetsWithdraw shares' waive = .ok recovered' →
      recovered'.toNumber .to_nearest = .ok recoveredNumber' → recoveredNumber'.operator_gt v.assetsAvailable = true →
      (v.clawback assets holderShares waive hnn).run = .ok (.error .tecINTERNAL)) ∧
    (∀ shares recovered sharesTotalAmount : STAmount, v.numericType ≠ NumericType.native →
      v.ClawbackPriced assets holderShares waive shares recovered →
      STAmount.ofNumber .int64 v.sharesTotal .to_nearest = .ok sharesTotalAmount →
      shares.operator_eq sharesTotalAmount = true → v.assetsDeployed.operator_ne Number.zero = true →
      (v.clawback assets holderShares waive hnn).run = .ok (.error .tecHAS_OBLIGATIONS)) ∧
    (∀ shares recovered sharesTotalAmount clamped : STAmount, v.numericType ≠ NumericType.native →
      v.ClawbackPriced assets holderShares waive shares recovered →
      STAmount.ofNumber .int64 v.sharesTotal .to_nearest = .ok sharesTotalAmount →
      (shares.operator_eq sharesTotalAmount && v.assetsDeployed.operator_ne Number.zero) = false →
      recovered.isZero = false →
      clampToSumExponent v.assetsAvailable recovered.operator_neg v.baseExponent = .ok clamped →
      clamped.isFractionalNonPositive = .ok true →
      (v.clawback assets holderShares waive hnn).run = .ok (.error .tecPRECISION_LOSS)) ∧
    (∀ amounts : VaultAmounts, v.numericType ≠ NumericType.native →
      (computeClawback v assets holderShares waive).run = .ok (.ok amounts) → amounts.shares.isZero = true →
      (v.clawback assets holderShares waive hnn).run = .ok (.error .tecPRECISION_LOSS)) ∧
    (∀ (amounts : VaultAmounts) (assetsNumber : Number) (ter : TER), v.numericType ≠ NumericType.native →
      (computeClawback v assets holderShares waive).run = .ok (.ok amounts) → amounts.shares.isZero = false →
      amounts.assets.toNumber .to_nearest = .ok assetsNumber → v.checkDebitNotDust assetsNumber = .ok ter →
      (ter != .tesSUCCESS) = true → (v.clawback assets holderShares waive hnn).run = .ok (.error ter)) ∧
    -- a clawback amount is canonical, or zero to claw back the holding, and the asset's maximum fits an int64
    -- amount, as C++ caps every MPT maximum
    (assets.CanonicalOrZero → holderShares.ShareBalance →
      (v.numericType.isIntegral = true → v.numericType.maxValue.toNat ≤ maxRep.toNat) →
      (∀ amounts : VaultAmounts, (computeClawback v assets holderShares waive).run = .ok (.ok amounts) →
        amounts.shares.toRat < v.toExact.sharesTotal) →
      (v.clawback assets holderShares waive hnn).run ≠ .error .notLawful) ∧
    -- a clawback amount is canonical, or zero to claw back the holding
    (∀ (t0 : UInt32) (r : VaultWithAmounts), Vault.Reachable v t0 → assets.CanonicalOrZero →
      holderShares.ShareBalance → (v.clawback assets holderShares waive hnn).run = .ok (.ok r) →
      r.shares.toRat = v.toExact.sharesTotal →
      r.assets.toRat = v.assetsAvailable.toRat ∧ r.vault'.assetsAvailable = Number.zero ∧
        r.vault'.sharesTotal = Number.zero) ∧
    -- a clawback amount is canonical, or zero to claw back the holding. The clawback destroys every outstanding
    -- share
    ∀ t0 : UInt32, Vault.Reachable v t0 → assets.CanonicalOrZero → holderShares.ShareBalance →
      (∀ amounts : VaultAmounts, (computeClawback v assets holderShares waive).run = .ok (.ok amounts) →
        amounts.shares.toRat = v.toExact.sharesTotal) →
      (v.clawback assets holderShares waive hnn).run ≠ .error .notLawful :=
  ⟨Vault.clawback_no_permission_proof v assets holderShares waive hnn,
    fun hxrp => Vault.clawback_compute_rejected_proof v assets holderShares waive hnn hxrp _,
    fun shares recovered capped shares' recovered' recoveredNumber recoveredNumber' hxrp =>
      Vault.clawback_capped_internal_proof v assets holderShares waive hnn hxrp shares recovered capped shares'
        recovered' recoveredNumber recoveredNumber',
    fun shares recovered sharesTotalAmount hxrp =>
      Vault.clawback_has_obligations_proof v assets holderShares waive hnn hxrp shares recovered sharesTotalAmount,
    fun shares recovered sharesTotalAmount clamped hxrp =>
      Vault.clawback_clamp_precision_loss_proof v assets holderShares waive hnn hxrp shares recovered
        sharesTotalAmount clamped,
    fun amounts hxrp => Vault.clawback_zero_shares_proof v assets holderShares waive hnn hxrp amounts,
    fun amounts assetsNumber ter hxrp =>
      Vault.clawback_recovery_too_small_proof v assets holderShares waive hnn hxrp amounts assetsNumber ter,
    Vault.clawback_success_proof v assets holderShares waive hnn,
    fun t0 r hr hc hhs hok hfinal => Vault.clawback_final_proof v assets holderShares waive t0 hnn hr hc hhs
      (Vault.Reachable.maxValue_fits v t0 hr
        (Vault.Reachable.clawback_sharesTotal_pos v t0 hr assets holderShares waive hhs hnn r hok)) r hok hfinal,
    fun t0 => Vault.clawback_final_success_proof v assets holderShares waive t0 hnn⟩

/-- Every rejection of a clawback. -/
theorem Vault.clawback_error_codes (assets holderShares : STAmount) (waive : Bool) (hnn : 0 ≤ assets.toRat)
    (hc : assets.CanonicalOrZero) -- a clawback amount is canonical, or zero to claw back the holding
    (hhs : holderShares.ShareBalance)
    -- the asset's maximum fits an int64 amount, as C++ caps every MPT maximum
    (hmax : v.numericType.isIntegral = true → v.numericType.maxValue.toNat ≤ maxRep.toNat)
    (ter : TER) (hok : (v.clawback assets holderShares waive hnn).run = .ok (.error ter)) :
    ter = .tecNO_PERMISSION ∨ ter = .tecINTERNAL ∨ ter = .tecHAS_OBLIGATIONS ∨ ter = .tecPRECISION_LOSS ∨
      ter = .tecPATH_DRY ∨ ter = .tecINSUFFICIENT_FUNDS :=
  Vault.clawback_error_codes_proof v assets holderShares waive hnn hc hhs hmax ter hok

end XRPL.Model.SingleAssetVault
