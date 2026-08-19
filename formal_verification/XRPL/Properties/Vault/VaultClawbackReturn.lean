import XRPL.Properties.Vault.Common.ClawbackExits

/-! # `Vault.clawback` exits -/

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol

variable (v : Vault)

/-! ## `Vault.clawback` -/

/-- A negative `assets` amount: `some .tecINTERNAL`, the vault is unchanged
and nothing is recovered. -/
theorem Vault.clawback_negative_amount (assets holderShares : STAmount)
    (hneg : assets.negative = true) :
    v.clawback assets holderShares = .ok (.rejected v .tecINTERNAL) :=
  Vault.clawback_negative_amount_proof v assets holderShares hneg

/-- The exchange computation destroys zero shares: `some .tecPRECISION_LOSS`
and the vault is unchanged. -/
theorem Vault.clawback_zero_shares (assets holderShares : STAmount)
    (result : ComputeClawbackResult)
    (hcomp : computeClawback v assets holderShares = .ok result)
    (herr : result.error = none)
    (hz : result.sharesDestroyed.isZero = true) :
    v.clawback assets holderShares = .ok (.rejected v .tecPRECISION_LOSS) :=
  Vault.clawback_zero_shares_proof v assets holderShares result hcomp herr hz

/-- A nonzero recovery whose subtraction does not change `assetsTotal` rounded
into the vault's `numericType`: `some .tecPRECISION_LOSS`. The guard is marked
"(waiting the C++ fix)" in the model. -/
theorem Vault.clawback_recovery_too_small (assets holderShares : STAmount)
    (result : ComputeClawbackResult)
    (sharesDestroyedNumber assetsRecoveredNumber at' : Number)
    (assetsTotalRounded assetsTotalRounded' : STAmount)
    (hcomp : computeClawback v assets holderShares = .ok result)
    (herr : result.error = none)
    (hz : result.sharesDestroyed.isZero = false)
    (hsN : result.sharesDestroyed.toNumber .to_nearest = .ok sharesDestroyedNumber)
    (haN : result.assetsRecovered.toNumber .to_nearest = .ok assetsRecoveredNumber)
    -- at' = assetsTotal - assetsRecovered
    (hat : v.assetsTotal.operator_sub assetsRecoveredNumber .to_nearest = .ok at')
    -- old and new assetsTotal, each rounded into the vault's numericType,
    -- the values the smallness guard compares
    (hrt : STAmount.ofNumber v.numericType v.assetsTotal .to_nearest = .ok assetsTotalRounded)
    (hrt' : STAmount.ofNumber v.numericType at' .to_nearest = .ok assetsTotalRounded')
    -- the guard fires: the recovery is nonzero yet the rounded totals are equal
    (hguard : (assetsRecoveredNumber.mantissa_ != 0 &&
      assetsTotalRounded.operator_eq assetsTotalRounded') = true) :
    v.clawback assets holderShares = .ok (.rejected v .tecPRECISION_LOSS) :=
  Vault.clawback_recovery_too_small_proof v assets holderShares result sharesDestroyedNumber
    assetsRecoveredNumber at' assetsTotalRounded assetsTotalRounded'
    hcomp herr hz hsN haN hat hrt hrt' hguard

/-- Every guard passes: the clawback returns the exact updated vault, the
recovered assets, and the destroyed shares. The updated vault stores the
rounded differences `sharesTotal - sharesDestroyed`,
`assetsAvailable - assetsRecovered`, and `assetsTotal - assetsRecovered`. -/
theorem Vault.clawback_success (assets holderShares : STAmount) (result : ComputeClawbackResult)
    (sharesDestroyedNumber assetsRecoveredNumber st' av' at' : Number)
    (assetsTotalRounded assetsTotalRounded' : STAmount)
    (hcomp : computeClawback v assets holderShares = .ok result)
    (herr : result.error = none)
    (hz : result.sharesDestroyed.isZero = false)
    (hsN : result.sharesDestroyed.toNumber .to_nearest = .ok sharesDestroyedNumber)
    (haN : result.assetsRecovered.toNumber .to_nearest = .ok assetsRecoveredNumber)
    (hat : v.assetsTotal.operator_sub assetsRecoveredNumber .to_nearest = .ok at')
    -- old and new assetsTotal, each rounded into the vault's numericType,
    -- the values the smallness guard compares
    (hrt : STAmount.ofNumber v.numericType v.assetsTotal .to_nearest = .ok assetsTotalRounded)
    (hrt' : STAmount.ofNumber v.numericType at' .to_nearest = .ok assetsTotalRounded')
    -- the guard passes: the recovery actually reduces the rounded assetsTotal
    (hguard : (assetsRecoveredNumber.mantissa_ != 0 &&
      assetsTotalRounded.operator_eq assetsTotalRounded') = false)
    (hst : v.sharesTotal.operator_sub sharesDestroyedNumber .to_nearest = .ok st')
    (hav : v.assetsAvailable.operator_sub assetsRecoveredNumber .to_nearest = .ok av') :
    v.clawback assets holderShares =
      .ok ⟨none, { v with sharesTotal := st', assetsAvailable := av', assetsTotal := at' },
        result.assetsRecovered, result.sharesDestroyed⟩ :=
  Vault.clawback_success_proof v assets holderShares result sharesDestroyedNumber assetsRecoveredNumber
    st' av' at' assetsTotalRounded assetsTotalRounded'
    hcomp herr hz hsN haN hat hrt hrt' hguard hst hav

/-- Every outcome of a clawback that runs without a throw.

`tecINTERNAL` has two origins: a negative `assets` amount, and the check after
the recomputation against `assetsAvailable` (when the first computed recovery
exceeded `assetsAvailable`, the amount is recomputed from truncated shares,
and a recovery that still exceeds `assetsAvailable` returns `tecINTERNAL`).
xrpld excludes that second check from coverage as believed unreachable, but no
proof exists either way. TODO: prove the recomputation check dead on lawful
vaults if possible. Then for nonnegative `assets` this inventory loses
`tecINTERNAL`, and the matching xrpld check is certified removable. If instead
a lawful vault reaches it, that is a reportable xrpld bug. -/
theorem Vault.clawback_error_codes (assets holderShares : STAmount) (r : ClawbackResult)
    (hok : v.clawback assets holderShares = .ok r) :
    r.error = none ∨
    r.error = some .tecINTERNAL ∨
    r.error = some .tecPATH_DRY ∨
    r.error = some .tecPRECISION_LOSS :=
  Vault.clawback_error_codes_proof v assets holderShares r hok

end XRPL.Model.SingleAssetVault
