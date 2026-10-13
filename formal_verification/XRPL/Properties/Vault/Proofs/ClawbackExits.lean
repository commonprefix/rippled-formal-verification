import XRPL.Model.Vault.VaultClawback
import XRPL.Properties.Vault.Proofs.Walk

/-! # `Vault.clawback` exits

Proof bodies behind `VaultClawbackReturn.lean`. -/

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol

/-- Every outcome of a `computeClawback` that runs without a throw. -/
lemma computeClawback_error_codes (v : Vault) (assets holderShares : STAmount)
    (cc : ComputeClawbackResult) (hok : computeClawback v assets holderShares = .ok cc) :
    cc.error = none ∨ cc.error = some .tecINTERNAL ∨ cc.error = some .tecPATH_DRY ∨
      cc.error = some .tecPRECISION_LOSS := by
  simp only [computeClawback, bind, Except.bind, pure, Except.pure, tryCatch, tryCatchThe,
    MonadExceptOf.tryCatch, Except.tryCatch] at hok
  walk_ok
  all_goals simp

lemma Vault.clawback_error_codes_proof (v : Vault) (assets holderShares : STAmount)
    (r : ClawbackResult) (hnn : 0 ≤ assets.toRat) (hok : v.clawback assets holderShares hnn = .ok r) :
    r.error = none ∨ r.error = some .tecINTERNAL ∨ r.error = some .tecPATH_DRY ∨
      r.error = some .tecPRECISION_LOSS := by
  simp only [Vault.clawback, bind, Except.bind, pure, Except.pure] at hok
  walk_ok
  all_goals first
    | simp only [ClawbackResult.rejected]; simp
    | exact computeClawback_error_codes v assets holderShares _ ‹_›

lemma Vault.clawback_zero_shares_proof (v : Vault) (assets holderShares : STAmount)
    (result : ComputeClawbackResult)
    (hcomp : computeClawback v assets holderShares = .ok result)
    (herr : result.error = none)
    (hz : result.sharesDestroyed.isZero = true) (hnn : 0 ≤ assets.toRat) :
    v.clawback assets holderShares hnn = .ok (.rejected v .tecPRECISION_LOSS) := by
  simp [Vault.clawback, hcomp, herr, hz, bind, Except.bind, pure, Except.pure]

lemma Vault.clawback_recovery_too_small_proof (v : Vault) (assets holderShares : STAmount)
    (result : ComputeClawbackResult)
    (sharesDestroyedNumber assetsRecoveredNumber at' : Number)
    (assetsTotalRounded assetsTotalRounded' : STAmount)
    (hcomp : computeClawback v assets holderShares = .ok result)
    (herr : result.error = none)
    (hz : result.sharesDestroyed.isZero = false)
    (hsN : result.sharesDestroyed.toNumber .to_nearest = .ok sharesDestroyedNumber)
    (haN : result.assetsRecovered.toNumber .to_nearest = .ok assetsRecoveredNumber)
    (hat : v.assetsTotal.operator_sub assetsRecoveredNumber .to_nearest = .ok at')
    (hrt : STAmount.ofNumber v.numericType v.assetsTotal .to_nearest = .ok assetsTotalRounded)
    (hrt' : STAmount.ofNumber v.numericType at' .to_nearest = .ok assetsTotalRounded')
    (hguard : (assetsRecoveredNumber.mantissa_ != 0 &&
      assetsTotalRounded.operator_eq assetsTotalRounded') = true)
    (hnn : 0 ≤ assets.toRat) :
    v.clawback assets holderShares hnn = .ok (.rejected v .tecPRECISION_LOSS) := by
  simp [Vault.clawback, hcomp, herr, hz, hsN, haN, hat, hrt, hrt', hguard, bind, Except.bind,
    pure, Except.pure]

end XRPL.Model.SingleAssetVault
