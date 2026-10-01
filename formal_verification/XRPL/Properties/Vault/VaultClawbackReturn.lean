import XRPL.Properties.Vault.Proofs.ClawbackExits
import XRPL.Properties.Vault.Proofs.Lawful

/-! # `Vault.clawback` exits -/

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol

variable (v : Vault)

/-! ## `Vault.clawback` -/

/-- The exchange computation destroys zero shares: `some .tecPRECISION_LOSS`
and the vault is unchanged. -/
theorem Vault.clawback_zero_shares (assets holderShares : STAmount)
    (result : ComputeClawbackResult)
    (hcomp : computeClawback v assets holderShares = .ok result)
    (herr : result.error = none)
    (hz : result.sharesDestroyed.isZero = true)
    (hnn : 0 ≤ assets.toRat) :
    v.clawback assets holderShares hnn = .ok (.rejected v .tecPRECISION_LOSS) :=
  Vault.clawback_zero_shares_proof v assets holderShares result hcomp herr hz hnn

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
    (hat : v.assetsTotal.operator_sub assetsRecoveredNumber .to_nearest = .ok at')
    (hrt : STAmount.ofNumber v.numericType v.assetsTotal .to_nearest = .ok assetsTotalRounded)
    (hrt' : STAmount.ofNumber v.numericType at' .to_nearest = .ok assetsTotalRounded')
    (hguard : (assetsRecoveredNumber.mantissa_ != 0 &&
      assetsTotalRounded.operator_eq assetsTotalRounded') = true)
    (hnn : 0 ≤ assets.toRat) :
    v.clawback assets holderShares hnn = .ok (.rejected v .tecPRECISION_LOSS) :=
  Vault.clawback_recovery_too_small_proof v assets holderShares result sharesDestroyedNumber
    assetsRecoveredNumber at' assetsTotalRounded assetsTotalRounded'
    hcomp herr hz hsN haN hat hrt hrt' hguard hnn

/-- Every guard passes on a clawback: the stored total and available assets each
drop by the recovery and the share total by the destroyed shares, the post-state
is still a `Vault`. -/
theorem Vault.clawback_success (assets holderShares : STAmount) (result : ComputeClawbackResult)
    (sharesDestroyedNumber assetsRecoveredNumber st' av' at' : Number)
    (assetsTotalRounded assetsTotalRounded' : STAmount)
    (hL : v.toExact.lossUnrealized = 0)
    (hAV : v.assetsAvailable = v.assetsTotal)
    (hr_norm : assetsRecoveredNumber.isNormalized) (hr_nn : 0 ≤ assetsRecoveredNumber.toRat)
    (hr_le : assetsRecoveredNumber.toRat ≤ v.assetsTotal.toRat)
    (hd_norm : sharesDestroyedNumber.isNormalized) (hd_nn : 0 ≤ sharesDestroyedNumber.toRat)
    (hd_den : sharesDestroyedNumber.toRat.den = 1)
    (hd_le : sharesDestroyedNumber.toRat ≤ v.sharesTotal.toRat)
    (hfit : v.sharesTotal.toRat ≤ 2 ^ 63 - 1)
    (hcomp : computeClawback v assets holderShares = .ok result)
    (herr : result.error = none)
    (hz : result.sharesDestroyed.isZero = false)
    (hsN : result.sharesDestroyed.toNumber .to_nearest = .ok sharesDestroyedNumber)
    (haN : result.assetsRecovered.toNumber .to_nearest = .ok assetsRecoveredNumber)
    (hat : v.assetsTotal.operator_sub assetsRecoveredNumber .to_nearest = .ok at')
    (hrt : STAmount.ofNumber v.numericType v.assetsTotal .to_nearest = .ok assetsTotalRounded)
    (hrt' : STAmount.ofNumber v.numericType at' .to_nearest = .ok assetsTotalRounded')
    (hguard : (assetsRecoveredNumber.mantissa_ != 0 &&
      assetsTotalRounded.operator_eq assetsTotalRounded') = false)
    (hst : v.sharesTotal.operator_sub sharesDestroyedNumber .to_nearest = .ok st')
    (hav : v.assetsAvailable.operator_sub assetsRecoveredNumber .to_nearest = .ok av')
    (hempty : st'.toRat = 0 → at'.toRat = 0)
    (hnn : 0 ≤ assets.toRat) :
    ∃ v' : Vault,
      v.clawback assets holderShares hnn =
        .ok ⟨none, v', result.assetsRecovered, result.sharesDestroyed⟩ ∧
      v'.toRawVault = { v.toRawVault with sharesTotal := st', assetsAvailable := av', assetsTotal := at' } := by
  obtain ⟨v', htl, hlv'eq⟩ := Vault.subtract_lawful v assetsRecoveredNumber
    sharesDestroyedNumber at' av' st' hL hAV hr_norm hr_nn hr_le hd_norm hd_nn hd_den hd_le hfit
    hat hav hst hempty
  refine ⟨v', ?_, hlv'eq⟩
  simp [Vault.clawback, hcomp, herr, hz, hsN, haN, hat, hrt, hrt', hguard, hst, hav, htl, bind,
    Except.bind, pure, Except.pure]

/-- Every outcome of a clawback that runs without a throw.

`tecINTERNAL` comes from the check after the recomputation against
`assetsAvailable` (when the first computed recovery exceeded `assetsAvailable`,
the amount is recomputed from truncated shares, and a recovery that still
exceeds `assetsAvailable` returns `tecINTERNAL`). xrpld excludes that check from
coverage as believed unreachable, but no proof exists either way. -/
theorem Vault.clawback_error_codes (assets holderShares : STAmount) (r : ClawbackResult)
    (hnn : 0 ≤ assets.toRat) (hok : v.clawback assets holderShares hnn = .ok r) :
    r.error = none ∨
    r.error = some .tecINTERNAL ∨
    r.error = some .tecPATH_DRY ∨
    r.error = some .tecPRECISION_LOSS :=
  Vault.clawback_error_codes_proof v assets holderShares r hnn hok

end XRPL.Model.SingleAssetVault
