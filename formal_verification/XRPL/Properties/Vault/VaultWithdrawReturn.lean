import XRPL.Properties.Vault.Proofs.WithdrawExits
import XRPL.Properties.Vault.Proofs.WithdrawExitsB
import XRPL.Properties.Vault.Proofs.WithdrawExitsC

/-! # `Vault.withdraw` exits -/

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol

/-! ## `Vault.sharesToAssetsWithdraw` -/

/-- When assetsTotal minus lossUnrealized rounds to a zero mantissa, any `shares`
are paid exactly zero. This is the only early exit of `sharesToAssetsWithdraw`. -/
theorem Vault.sharesToAssetsWithdraw_zero_nav (v : Vault) (shares : STAmount)
    (waiveUnrealizedLoss : Bool) (netAssetValue : Number)
    (hnav : v.assetsTotal.operator_sub
      (match waiveUnrealizedLoss with
        | true => Number.zero
        | false => v.lossUnrealized) .to_nearest = .ok netAssetValue)
    (hz : netAssetValue.mantissa_ = 0) :
    v.sharesToAssetsWithdraw shares waiveUnrealizedLoss =
      .ok (STAmount.zero v.numericType) :=
  Vault.sharesToAssetsWithdraw_zero_nav_proof v shares waiveUnrealizedLoss
    netAssetValue hnav hz

variable (v : Vault)

/-! ## `Vault.withdraw` -/

/-- The withdrawn amount `assets'` exceeds `assetsAvailable`: `some .tecINSUFFICIENT_FUNDS`. -/
theorem Vault.withdraw_insufficient_funds (amount : WithdrawAmount)
    (waiveUnrealizedLoss : Bool) (cw : ComputeWithdrawResult) (assetsNumber' : Number)
    (hpos : 0 < amount.amount.toRat) -- the requested amount is positive, the preflight guard
    (hcomp : (match amount with
        | .vaultAssets assets => computeWithdrawByAssets v assets waiveUnrealizedLoss
        | .vaultShares shares => computeWithdrawByShares v shares waiveUnrealizedLoss)
      = .ok cw)
    (herr : cw.error = none)
    (haN : cw.assets'.toNumber .to_nearest = .ok assetsNumber')
    (hins : v.assetsAvailable.operator_lt assetsNumber' = true) :
    v.withdraw amount waiveUnrealizedLoss hpos =
      .ok (.rejected v .tecINSUFFICIENT_FUNDS) :=
  Vault.withdraw_insufficient_funds_proof v amount waiveUnrealizedLoss cw assetsNumber'
    hpos hcomp herr haN hins

/-- The withdrawal redeems the whole share total while `lossUnrealized` is
nonzero: `some .tefINTERNAL`. -/
theorem Vault.withdraw_final_nonzero_loss (amount : WithdrawAmount)
    (waiveUnrealizedLoss : Bool) (cw : ComputeWithdrawResult) (assetsNumber' : Number)
    (sharesTotalAmount : STAmount)
    (hpos : 0 < amount.amount.toRat) -- the requested amount is positive, the preflight guard
    (hcomp : (match amount with
        | .vaultAssets assets => computeWithdrawByAssets v assets waiveUnrealizedLoss
        | .vaultShares shares => computeWithdrawByShares v shares waiveUnrealizedLoss)
      = .ok cw)
    (herr : cw.error = none)
    (haN : cw.assets'.toNumber .to_nearest = .ok assetsNumber')
    (hins : v.assetsAvailable.operator_lt assetsNumber' = false)
    (hst : STAmount.ofNumber .int64 v.sharesTotal .to_nearest = .ok sharesTotalAmount)
    (hfin : cw.sharesRedeemed.operator_eq sharesTotalAmount = true)
    (hloss : v.lossUnrealized.operator_ne Number.zero = true) :
    v.withdraw amount waiveUnrealizedLoss hpos =
      .ok (.rejected v .tefINTERNAL) :=
  Vault.withdraw_final_nonzero_loss_proof v amount waiveUnrealizedLoss cw assetsNumber'
    sharesTotalAmount hpos hcomp herr haN hins hst hfin hloss

/-- The withdrawal redeems the whole share total on a vault with no unrealized
loss: the vault is zeroed and the withdrawer is paid all of `assetsAvailable`.
The `to_lawful` re-check is proven to succeed via `zero_record_never_notLawful`,
so the `.notLawful` throw is unreachable. -/
theorem Vault.withdraw_final (amount : WithdrawAmount) (waiveUnrealizedLoss : Bool)
    (cw : ComputeWithdrawResult) (assetsNumber' : Number)
    (sharesTotalAmount allAvailable : STAmount)
    (hcomp : (match amount with
        | .vaultAssets assets => computeWithdrawByAssets v assets waiveUnrealizedLoss
        | .vaultShares shares => computeWithdrawByShares v shares waiveUnrealizedLoss)
      = .ok cw)
    (herr : cw.error = none)
    (haN : cw.assets'.toNumber .to_nearest = .ok assetsNumber')
    (hins : v.assetsAvailable.operator_lt assetsNumber' = false)
    (hst : STAmount.ofNumber .int64 v.sharesTotal .to_nearest = .ok sharesTotalAmount)
    (hfin : cw.sharesRedeemed.operator_eq sharesTotalAmount = true)
    (hloss : v.lossUnrealized.operator_ne Number.zero = false)
    (hallAvail : STAmount.ofNumber v.numericType v.assetsAvailable .to_nearest = .ok allAvailable)
    (hpos : 0 < amount.amount.toRat) :
    ∃ v' : Vault,
      v.withdraw amount waiveUnrealizedLoss hpos = .ok ⟨none, v', allAvailable, cw.sharesRedeemed⟩ ∧
      v'.toRawVault = { v.toRawVault with assetsTotal := Number.zero, assetsAvailable := Number.zero, sharesTotal := Number.zero } :=
  Vault.withdraw_final_proof v amount waiveUnrealizedLoss cw assetsNumber' sharesTotalAmount
    allAvailable hcomp herr haN hins hst hfin hloss hallAvail hpos

/-- A nonzero `assets'` whose subtraction does not change `assetsTotal` rounded
into the vault's `numericType`: `some .tecPRECISION_LOSS`. The guard is marked
"(waiting the C++ fix)" in the model. -/
theorem Vault.withdraw_payout_too_small (amount : WithdrawAmount)
    (waiveUnrealizedLoss : Bool) (cw : ComputeWithdrawResult)
    (assetsNumber' sharesBurnedNumber assetsTotal' : Number)
    (sharesTotalAmount assetsTotalRounded assetsTotalRounded' : STAmount)
    (hcomp : (match amount with
        | .vaultAssets assets => computeWithdrawByAssets v assets waiveUnrealizedLoss
        | .vaultShares shares => computeWithdrawByShares v shares waiveUnrealizedLoss)
      = .ok cw)
    (herr : cw.error = none)
    (haN : cw.assets'.toNumber .to_nearest = .ok assetsNumber')
    (hins : v.assetsAvailable.operator_lt assetsNumber' = false)
    (hst : STAmount.ofNumber .int64 v.sharesTotal .to_nearest = .ok sharesTotalAmount)
    (hfin : cw.sharesRedeemed.operator_eq sharesTotalAmount = false)
    (hsN : cw.sharesRedeemed.toNumber .to_nearest = .ok sharesBurnedNumber)
    (hat : v.assetsTotal.operator_sub assetsNumber' .to_nearest = .ok assetsTotal')
    (hrt : STAmount.ofNumber v.numericType v.assetsTotal .to_nearest = .ok assetsTotalRounded)
    (hrt' : STAmount.ofNumber v.numericType assetsTotal' .to_nearest = .ok assetsTotalRounded')
    (hguard : (assetsNumber'.mantissa_ != 0 &&
      assetsTotalRounded.operator_eq assetsTotalRounded') = true)
    (hpos : 0 < amount.amount.toRat)
    (hcanon : amount.amount.Canonical) :
    v.withdraw amount waiveUnrealizedLoss hpos =
      .ok (.rejected v .tecPRECISION_LOSS) :=
  Vault.withdraw_payout_too_small_proof v amount waiveUnrealizedLoss cw
    assetsNumber' sharesBurnedNumber assetsTotal' sharesTotalAmount assetsTotalRounded
    assetsTotalRounded' hcomp herr haN hins hst hfin hsN hat hrt hrt' hguard hpos hcanon

/-- Every guard passes on a non-final withdrawal: the stored total and available
assets each drop by the payout and the share total by the redeemed shares, the
post-state is still a `Vault`. -/
theorem Vault.withdraw_success (amount : WithdrawAmount) (waiveUnrealizedLoss : Bool)
    (cw : ComputeWithdrawResult) (reported : STAmount)
    (aN assetsNumber' sharesBurnedNumber assetsTotal' assetsAvailable' sharesTotal' : Number)
    (sharesTotalAmount assetsTotalRounded assetsTotalRounded' : STAmount)
    (hL : v.toExact.lossUnrealized = 0)
    (hAV : v.assetsAvailable = v.assetsTotal)
    (hp_norm : assetsNumber'.isNormalized) (hp_nn : 0 ≤ assetsNumber'.toRat)
    (hp_le : assetsNumber'.toRat ≤ v.assetsTotal.toRat)
    (hb_norm : sharesBurnedNumber.isNormalized) (hb_nn : 0 ≤ sharesBurnedNumber.toRat)
    (hb_den : sharesBurnedNumber.toRat.den = 1)
    (hb_le : sharesBurnedNumber.toRat ≤ v.sharesTotal.toRat)
    (hfit : v.sharesTotal.toRat ≤ 2 ^ 63 - 1)
    (hcomp : (match amount with
        | .vaultAssets assets => computeWithdrawByAssets v assets waiveUnrealizedLoss
        | .vaultShares shares => computeWithdrawByShares v shares waiveUnrealizedLoss)
      = .ok cw)
    (herr : cw.error = none)
    (haN0 : cw.assets'.toNumber .to_nearest = .ok aN)
    (hins : v.assetsAvailable.operator_lt aN = false)
    (hstn : STAmount.ofNumber .int64 v.sharesTotal .to_nearest = .ok sharesTotalAmount)
    (hfin : cw.sharesRedeemed.operator_eq sharesTotalAmount = false)
    (hclamp : clampToSumExponent v.assetsTotal cw.assets'.operator_neg = .ok reported)
    (hcpos : reported.integral = true ∨ 0 < reported.toRat)
    (haN : reported.toNumber .to_nearest = .ok assetsNumber')
    (hsN : cw.sharesRedeemed.toNumber .to_nearest = .ok sharesBurnedNumber)
    (hat : v.assetsTotal.operator_sub assetsNumber' .to_nearest = .ok assetsTotal')
    (hrt : STAmount.ofNumber v.numericType v.assetsTotal .to_nearest = .ok assetsTotalRounded)
    (hrt' : STAmount.ofNumber v.numericType assetsTotal' .to_nearest = .ok assetsTotalRounded')
    (hguard : (assetsNumber'.mantissa_ != 0 &&
      assetsTotalRounded.operator_eq assetsTotalRounded') = false)
    (hav : v.assetsAvailable.operator_sub assetsNumber' .to_nearest = .ok assetsAvailable')
    (hshares : v.sharesTotal.operator_sub sharesBurnedNumber .to_nearest = .ok sharesTotal')
    (hempty : sharesTotal'.toRat = 0 → assetsTotal'.toRat = 0)
    (hpos : 0 < amount.amount.toRat) :
    ∃ v' : Vault,
      v.withdraw amount waiveUnrealizedLoss hpos = .ok ⟨none, v', reported, cw.sharesRedeemed⟩ ∧
      v'.toRawVault = { v.toRawVault with assetsTotal := assetsTotal', assetsAvailable := assetsAvailable', sharesTotal := sharesTotal' } :=
  Vault.withdraw_success_proof v amount waiveUnrealizedLoss cw reported aN assetsNumber'
    sharesBurnedNumber assetsTotal' assetsAvailable' sharesTotal' sharesTotalAmount
    assetsTotalRounded assetsTotalRounded' hL hAV hp_norm hp_nn hp_le hb_norm hb_nn hb_den hb_le
    hfit hcomp herr haN0 hins hstn hfin hclamp hcpos haN hsN hat hrt hrt' hguard hav hshares
    hempty hpos

/-- The grid clamp snaps a non-final payout to zero (or below): the withdrawal
fails with `tecPRECISION_LOSS`. With `withdraw_success` this covers both
outcomes of the clamp. -/
theorem Vault.withdraw_clamp_precision_loss (amount : WithdrawAmount)
    (waiveUnrealizedLoss : Bool) (cw : ComputeWithdrawResult) (reported : STAmount) (aN : Number)
    (sharesTotalAmount : STAmount)
    (hcomp : (match amount with
        | .vaultAssets assets => computeWithdrawByAssets v assets waiveUnrealizedLoss
        | .vaultShares shares => computeWithdrawByShares v shares waiveUnrealizedLoss)
      = .ok cw)
    (herr : cw.error = none)
    (haN0 : cw.assets'.toNumber .to_nearest = .ok aN)
    (hins : v.assetsAvailable.operator_lt aN = false)
    (hstn : STAmount.ofNumber .int64 v.sharesTotal .to_nearest = .ok sharesTotalAmount)
    (hfin : cw.sharesRedeemed.operator_eq sharesTotalAmount = false)
    (hclamp : clampToSumExponent v.assetsTotal cw.assets'.operator_neg = .ok reported)
    (hvanish : reported.integral = false ∧ reported.toRat ≤ 0)
    (hpos : 0 < amount.amount.toRat) :
    v.withdraw amount waiveUnrealizedLoss hpos = .ok (.rejected v .tecPRECISION_LOSS) :=
  Vault.withdraw_clamp_precision_loss_proof v amount waiveUnrealizedLoss cw reported aN
    sharesTotalAmount hcomp herr haN0 hins hstn hfin hclamp hvanish hpos

/-- Every outcome of a withdrawal that runs without a throw. -/
theorem Vault.withdraw_error_codes (amount : WithdrawAmount) (waiveUnrealizedLoss : Bool)
    (r : WithdrawResult)
    (hpos : 0 < amount.amount.toRat) (hok : v.withdraw amount waiveUnrealizedLoss hpos = .ok r) :
    r.error = none ∨
    r.error = some .tecPRECISION_LOSS ∨
    r.error = some .tecPATH_DRY ∨
    r.error = some .tecINSUFFICIENT_FUNDS ∨
    r.error = some .tefINTERNAL :=
  Vault.withdraw_error_codes_proof v amount waiveUnrealizedLoss r hpos hok

end XRPL.Model.SingleAssetVault
