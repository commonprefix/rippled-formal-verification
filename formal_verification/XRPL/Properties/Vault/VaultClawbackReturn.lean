import XRPL.Properties.Vault.Common.ClawbackExits
import XRPL.Properties.Vault.Common.Preservation

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

/-- Every guard passes on a clawback: the stored total and available assets each
drop by the recovery and the share total by the destroyed shares, the post-state
is still a `LawfulVault`. -/
theorem LawfulVault.clawback_success (assets holderShares : STAmount) (result : ComputeClawbackResult)
    (sharesDestroyedNumber assetsRecoveredNumber st' av' at' : Number)
    (assetsTotalRounded assetsTotalRounded' : STAmount)
    (hL : lv.toExact.lossUnrealized = 0)
    (hAV : lv.assetsAvailable = lv.assetsTotal)
    (hr_norm : assetsRecoveredNumber.isNormalized) (hr_nn : 0 ≤ assetsRecoveredNumber.toRat)
    (hr_le : assetsRecoveredNumber.toRat ≤ lv.assetsTotal.toRat)
    (hd_norm : sharesDestroyedNumber.isNormalized) (hd_nn : 0 ≤ sharesDestroyedNumber.toRat)
    (hd_den : sharesDestroyedNumber.toRat.den = 1)
    (hd_le : sharesDestroyedNumber.toRat ≤ lv.sharesTotal.toRat)
    (hfit : lv.sharesTotal.toRat ≤ 2 ^ 63 - 1)
    (hcomp : computeClawback lv assets holderShares = .ok result)
    (herr : result.error = none)
    (hz : result.sharesDestroyed.isZero = false)
    (hsN : result.sharesDestroyed.toNumber .to_nearest = .ok sharesDestroyedNumber)
    (haN : result.assetsRecovered.toNumber .to_nearest = .ok assetsRecoveredNumber)
    (hat : lv.assetsTotal.operator_sub assetsRecoveredNumber .to_nearest = .ok at')
    (hrt : STAmount.ofNumber lv.numericType lv.assetsTotal .to_nearest = .ok assetsTotalRounded)
    (hrt' : STAmount.ofNumber lv.numericType at' .to_nearest = .ok assetsTotalRounded')
    (hguard : (assetsRecoveredNumber.mantissa_ != 0 &&
      assetsTotalRounded.operator_eq assetsTotalRounded') = false)
    (hst : lv.sharesTotal.operator_sub sharesDestroyedNumber .to_nearest = .ok st')
    (hav : lv.assetsAvailable.operator_sub assetsRecoveredNumber .to_nearest = .ok av')
    (hempty : st'.toRat = 0 → at'.toRat = 0) :
    ∃ lv' : LawfulVault,
      lv.clawback assets holderShares =
        .ok ⟨none, lv', result.assetsRecovered, result.sharesDestroyed⟩ ∧
      lv'.toRawVault = { lv.toRawVault with sharesTotal := st', assetsAvailable := av', assetsTotal := at' } := by
  obtain ⟨lv', htl, hlv'eq⟩ := LawfulVault.clawback_poststate_lawful lv assetsRecoveredNumber
    sharesDestroyedNumber at' av' st' hL hAV hr_norm hr_nn hr_le hd_norm hd_nn hd_den hd_le hfit
    hat hav hst hempty
  refine ⟨lv', ?_, hlv'eq⟩
  unfold LawfulVault.clawback
  simp only []
  rw [hcomp, ok_bind]
  rw [if_neg (by rw [herr, Option.isSome_none]; exact Bool.false_ne_true)]
  try simp only [pure_bind]
  rw [if_neg (by rw [hz]; exact Bool.false_ne_true)]
  try simp only [pure_bind]
  rw [hsN, ok_bind, haN, ok_bind, hat, ok_bind, hrt, ok_bind, hrt', ok_bind]
  rw [if_neg (by rw [hguard]; exact Bool.false_ne_true)]
  try simp only [pure_bind]
  rw [hst, ok_bind, hav, ok_bind, htl, ok_bind]
  rfl

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
