import XRPL.Properties.Vault.Common.ClawbackExits

/-! # `LawfulVault.clawback` exits -/

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol

variable (lv : LawfulVault)

/-! ## `LawfulVault.clawback` -/

/-- A negative `assets` amount: `some .tecINTERNAL`, the vault is unchanged
and nothing is recovered. -/
theorem LawfulVault.clawback_negative_amount (assets holderShares : STAmount)
    (hneg : assets.negative = true) :
    lv.clawback assets holderShares = .ok (.rejected lv .tecINTERNAL) :=
  LawfulVault.clawback_negative_amount_proof lv assets holderShares hneg

/-- The exchange computation destroys zero shares: `some .tecPRECISION_LOSS`
and the vault is unchanged. -/
theorem LawfulVault.clawback_zero_shares (assets holderShares : STAmount)
    (result : ComputeClawbackResult)
    (hcomp : computeClawback lv assets holderShares = .ok result)
    (herr : result.error = none)
    (hz : result.sharesDestroyed.isZero = true) :
    lv.clawback assets holderShares = .ok (.rejected lv .tecPRECISION_LOSS) :=
  LawfulVault.clawback_zero_shares_proof lv assets holderShares result hcomp herr hz

/-- A nonzero recovery whose subtraction does not change `assetsTotal` rounded
into the vault's `numericType`: `some .tecPRECISION_LOSS`. The guard is marked
"(waiting the C++ fix)" in the model. -/
theorem LawfulVault.clawback_recovery_too_small (assets holderShares : STAmount)
    (result : ComputeClawbackResult)
    (sharesDestroyedNumber assetsRecoveredNumber at' : Number)
    (assetsTotalRounded assetsTotalRounded' : STAmount)
    (hcomp : computeClawback lv assets holderShares = .ok result)
    (herr : result.error = none)
    (hz : result.sharesDestroyed.isZero = false)
    (hsN : result.sharesDestroyed.toNumber .to_nearest = .ok sharesDestroyedNumber)
    (haN : result.assetsRecovered.toNumber .to_nearest = .ok assetsRecoveredNumber)
    (hat : lv.assetsTotal.operator_sub assetsRecoveredNumber .to_nearest = .ok at')
    (hrt : STAmount.ofNumber lv.numericType lv.assetsTotal .to_nearest = .ok assetsTotalRounded)
    (hrt' : STAmount.ofNumber lv.numericType at' .to_nearest = .ok assetsTotalRounded')
    (hguard : (assetsRecoveredNumber.mantissa_ != 0 &&
      assetsTotalRounded.operator_eq assetsTotalRounded') = true) :
    lv.clawback assets holderShares = .ok (.rejected lv .tecPRECISION_LOSS) :=
  LawfulVault.clawback_recovery_too_small_proof lv assets holderShares result sharesDestroyedNumber
    assetsRecoveredNumber at' assetsTotalRounded assetsTotalRounded'
    hcomp herr hz hsN haN hat hrt hrt' hguard

/-- Every outcome of a clawback that runs without a throw.

`tecINTERNAL` has two origins: a negative `assets` amount, and the check after
the recomputation against `assetsAvailable` (when the first computed recovery
exceeded `assetsAvailable`, the amount is recomputed from truncated shares,
and a recovery that still exceeds `assetsAvailable` returns `tecINTERNAL`).
xrpld excludes that second check from coverage as believed unreachable, but no
proof exists either way. -/
theorem LawfulVault.clawback_error_codes (assets holderShares : STAmount) (r : ClawbackResult)
    (hok : lv.clawback assets holderShares = .ok r) :
    r.error = none ∨
    r.error = some .tecINTERNAL ∨
    r.error = some .tecPATH_DRY ∨
    r.error = some .tecPRECISION_LOSS :=
  LawfulVault.clawback_error_codes_proof lv assets holderShares r hok

end XRPL.Model.SingleAssetVault
