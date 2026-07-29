import XRPL.Properties.Vault.Common.WithdrawExits

/-! # `Vault.withdraw` exits -/

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol

variable (v : Vault)

/-! ## `Vault.sharesToAssetsWithdraw` -/

/-- When assetsTotal minus lossUnrealized rounds to a zero mantissa, any `shares`
are paid exactly zero. This is the only early exit of `sharesToAssetsWithdraw`. -/
theorem Vault.sharesToAssetsWithdraw_zero_nav (shares : STAmount) (waiveUnrealizedLoss : Bool)
    (netAssetValue : Number)
    -- the pricing value: assetsTotal minus lossUnrealized (or minus zero when the loss is waived)
    (hnav : v.assetsTotal.operator_sub
      (match waiveUnrealizedLoss with
        | true => Number.zero
        | false => v.lossUnrealized) .to_nearest = .ok netAssetValue)
    -- and it rounded to a zero mantissa
    (hz : netAssetValue.mantissa_ = 0) :
    v.sharesToAssetsWithdraw shares waiveUnrealizedLoss =
      .ok (STAmount.zero v.numericType) :=
  Vault.sharesToAssetsWithdraw_zero_nav_proof v shares waiveUnrealizedLoss
    netAssetValue hnav hz

/-! ## `Vault.withdraw` -/

/-- The withdrawn amount `assets'` exceeds `assetsAvailable`: `some .tecINSUFFICIENT_FUNDS`. -/
theorem Vault.withdraw_insufficient_funds (amount : WithdrawAmount)
    (waiveUnrealizedLoss : Bool) (cw : ComputeWithdrawResult) (assetsNumber' : Number)
    -- the exchange computation (by assets or by shares) succeeded,
    -- cw carries the withdrawn amount assets' and the redeemed shares
    (hcomp : (match amount with
        | .vaultAssets assets => computeWithdrawByAssets v assets waiveUnrealizedLoss
        | .vaultShares shares => computeWithdrawByShares v shares waiveUnrealizedLoss)
      = .ok cw)
    (herr : cw.error = none)
    -- assets' converted to Number, the value all guards compare against
    (haN : cw.assets'.toNumber .to_nearest = .ok assetsNumber')
    -- assets' exceeds assetsAvailable
    (hins : v.assetsAvailable.operator_lt assetsNumber' = true) :
    v.withdraw amount waiveUnrealizedLoss =
      .ok (.rejected v .tecINSUFFICIENT_FUNDS) :=
  Vault.withdraw_insufficient_funds_proof v amount waiveUnrealizedLoss cw assetsNumber'
    hcomp herr haN hins

/-- The withdrawal redeems the whole share total while `lossUnrealized` is
nonzero: `some .tefINTERNAL`. -/
theorem Vault.withdraw_final_nonzero_loss (amount : WithdrawAmount)
    (waiveUnrealizedLoss : Bool) (cw : ComputeWithdrawResult) (assetsNumber' : Number)
    (sharesTotalAmount : STAmount)
    -- the exchange computation (by assets or by shares) succeeded,
    -- cw carries the withdrawn amount assets' and the redeemed shares
    (hcomp : (match amount with
        | .vaultAssets assets => computeWithdrawByAssets v assets waiveUnrealizedLoss
        | .vaultShares shares => computeWithdrawByShares v shares waiveUnrealizedLoss)
      = .ok cw)
    (herr : cw.error = none)
    -- assets' converted to Number, the value all guards compare against
    (haN : cw.assets'.toNumber .to_nearest = .ok assetsNumber')
    -- assets' fits in assetsAvailable
    (hins : v.assetsAvailable.operator_lt assetsNumber' = false)
    -- the redeemed shares equal the whole share total: a final withdrawal
    (hst : STAmount.ofNumber .int64 v.sharesTotal .to_nearest = .ok sharesTotalAmount)
    (hfin : cw.sharesRedeemed.operator_eq sharesTotalAmount = true)
    -- and lossUnrealized is nonzero
    (hloss : v.lossUnrealized.operator_ne Number.zero = true) :
    v.withdraw amount waiveUnrealizedLoss =
      .ok (.rejected v .tefINTERNAL) :=
  Vault.withdraw_final_nonzero_loss_proof v amount waiveUnrealizedLoss cw assetsNumber'
    sharesTotalAmount hcomp herr haN hins hst hfin hloss

/-- The withdrawal redeems the whole share total with `lossUnrealized` zero:
the withdrawal pays all of `assetsAvailable`, rounded once into the vault's
`numericType`, and the stored `assetsTotal`, `assetsAvailable` and
`sharesTotal` are all zeroed. -/
theorem Vault.withdraw_final (amount : WithdrawAmount) (waiveUnrealizedLoss : Bool)
    (cw : ComputeWithdrawResult) (assetsNumber' : Number)
    (sharesTotalAmount allAvailable : STAmount)
    -- the exchange computation (by assets or by shares) succeeded,
    -- cw carries the withdrawn amount assets' and the redeemed shares
    (hcomp : (match amount with
        | .vaultAssets assets => computeWithdrawByAssets v assets waiveUnrealizedLoss
        | .vaultShares shares => computeWithdrawByShares v shares waiveUnrealizedLoss)
      = .ok cw)
    (herr : cw.error = none)
    -- assets' converted to Number, the value all guards compare against
    (haN : cw.assets'.toNumber .to_nearest = .ok assetsNumber')
    -- assets' fits in assetsAvailable
    (hins : v.assetsAvailable.operator_lt assetsNumber' = false)
    -- the redeemed shares equal the whole share total: a final withdrawal
    (hst : STAmount.ofNumber .int64 v.sharesTotal .to_nearest = .ok sharesTotalAmount)
    (hfin : cw.sharesRedeemed.operator_eq sharesTotalAmount = true)
    -- and lossUnrealized is zero
    (hloss : v.lossUnrealized.operator_ne Number.zero = false)
    -- the whole assetsAvailable as an amount of the vault's numericType
    (hall : STAmount.ofNumber v.numericType v.assetsAvailable .to_nearest = .ok allAvailable) :
    v.withdraw amount waiveUnrealizedLoss =
      .ok ⟨none,
        { v with assetsAvailable := Number.zero, assetsTotal := Number.zero,
                 sharesTotal := Number.zero },
        allAvailable, cw.sharesRedeemed⟩ :=
  Vault.withdraw_final_proof v amount waiveUnrealizedLoss cw assetsNumber'
    sharesTotalAmount allAvailable hcomp herr haN hins hst hfin hloss hall

/-- A nonzero `assets'` whose subtraction does not change `assetsTotal` rounded
into the vault's `numericType`: `some .tecPRECISION_LOSS`. The guard is marked
"(waiting the C++ fix)" in the model. -/
theorem Vault.withdraw_payout_too_small (amount : WithdrawAmount)
    (waiveUnrealizedLoss : Bool) (cw : ComputeWithdrawResult)
    (assetsNumber' sharesBurnedNumber assetsTotal' : Number)
    (sharesTotalAmount assetsTotalRounded assetsTotalRounded' : STAmount)
    -- the exchange computation (by assets or by shares) succeeded,
    -- cw carries the withdrawn amount assets' and the redeemed shares
    (hcomp : (match amount with
        | .vaultAssets assets => computeWithdrawByAssets v assets waiveUnrealizedLoss
        | .vaultShares shares => computeWithdrawByShares v shares waiveUnrealizedLoss)
      = .ok cw)
    (herr : cw.error = none)
    -- assets' converted to Number, the value all guards compare against
    (haN : cw.assets'.toNumber .to_nearest = .ok assetsNumber')
    -- assets' fits in assetsAvailable
    (hins : v.assetsAvailable.operator_lt assetsNumber' = false)
    -- the redeemed shares are less than the whole share total: not final
    (hst : STAmount.ofNumber .int64 v.sharesTotal .to_nearest = .ok sharesTotalAmount)
    (hfin : cw.sharesRedeemed.operator_eq sharesTotalAmount = false)
    (hsN : cw.sharesRedeemed.toNumber .to_nearest = .ok sharesBurnedNumber)
    -- assetsTotal' = assetsTotal - assets'
    (hat : v.assetsTotal.operator_sub assetsNumber' .to_nearest = .ok assetsTotal')
    -- old and new assetsTotal, each rounded into the vault's numericType,
    -- the values the smallness guard compares
    (hrt : STAmount.ofNumber v.numericType v.assetsTotal .to_nearest = .ok assetsTotalRounded)
    (hrt' : STAmount.ofNumber v.numericType assetsTotal' .to_nearest = .ok assetsTotalRounded')
    -- the guard fires: assets' is nonzero yet the rounded totals are equal
    (hguard : (assetsNumber'.mantissa_ != 0 &&
      assetsTotalRounded.operator_eq assetsTotalRounded') = true) :
    v.withdraw amount waiveUnrealizedLoss =
      .ok (.rejected v .tecPRECISION_LOSS) :=
  Vault.withdraw_payout_too_small_proof v amount waiveUnrealizedLoss cw
    assetsNumber' sharesBurnedNumber assetsTotal' sharesTotalAmount assetsTotalRounded
    assetsTotalRounded' hcomp herr haN hins hst hfin hsN hat hrt hrt' hguard

/-- Every guard passes: the withdrawal returns the exact updated vault, the
withdrawn `assets'`, and the redeemed shares. -/
theorem Vault.withdraw_success (amount : WithdrawAmount) (waiveUnrealizedLoss : Bool)
    (cw : ComputeWithdrawResult)
    (assetsNumber' sharesBurnedNumber assetsTotal' assetsAvailable' sharesTotal' : Number)
    (sharesTotalAmount assetsTotalRounded assetsTotalRounded' : STAmount)
    -- the exchange computation (by assets or by shares) succeeded,
    -- cw carries the withdrawn amount assets' and the redeemed shares
    (hcomp : (match amount with
        | .vaultAssets assets => computeWithdrawByAssets v assets waiveUnrealizedLoss
        | .vaultShares shares => computeWithdrawByShares v shares waiveUnrealizedLoss)
      = .ok cw)
    (herr : cw.error = none)
    -- assets' converted to Number, the value all guards compare against
    (haN : cw.assets'.toNumber .to_nearest = .ok assetsNumber')
    -- assets' fits in assetsAvailable
    (hins : v.assetsAvailable.operator_lt assetsNumber' = false)
    -- the redeemed shares are less than the whole share total: not final
    (hst : STAmount.ofNumber .int64 v.sharesTotal .to_nearest = .ok sharesTotalAmount)
    (hfin : cw.sharesRedeemed.operator_eq sharesTotalAmount = false)
    (hsN : cw.sharesRedeemed.toNumber .to_nearest = .ok sharesBurnedNumber)
    -- assetsTotal' = assetsTotal - assets'
    (hat : v.assetsTotal.operator_sub assetsNumber' .to_nearest = .ok assetsTotal')
    -- old and new assetsTotal, each rounded into the vault's numericType,
    -- the values the smallness guard compares
    (hrt : STAmount.ofNumber v.numericType v.assetsTotal .to_nearest = .ok assetsTotalRounded)
    (hrt' : STAmount.ofNumber v.numericType assetsTotal' .to_nearest = .ok assetsTotalRounded')
    -- the guard passes: assets' actually reduces the rounded assetsTotal
    (hguard : (assetsNumber'.mantissa_ != 0 &&
      assetsTotalRounded.operator_eq assetsTotalRounded') = false)
    -- assetsAvailable' = assetsAvailable - assets',
    -- sharesTotal' = sharesTotal - redeemed shares
    (hav : v.assetsAvailable.operator_sub assetsNumber' .to_nearest = .ok assetsAvailable')
    (hshares : v.sharesTotal.operator_sub sharesBurnedNumber .to_nearest = .ok sharesTotal') :
    v.withdraw amount waiveUnrealizedLoss =
      .ok ⟨none,
        { v with assetsAvailable := assetsAvailable', assetsTotal := assetsTotal',
                 sharesTotal := sharesTotal' },
        cw.assets', cw.sharesRedeemed⟩ :=
  Vault.withdraw_success_proof v amount waiveUnrealizedLoss cw
    assetsNumber' sharesBurnedNumber assetsTotal' assetsAvailable' sharesTotal'
    sharesTotalAmount assetsTotalRounded assetsTotalRounded'
    hcomp herr haN hins hst hfin hsN hat hrt hrt' hguard hav hshares

/-- Every outcome of a withdrawal that runs without a throw. -/
theorem Vault.withdraw_error_codes (amount : WithdrawAmount) (waiveUnrealizedLoss : Bool)
    (r : WithdrawResult)
    (hok : v.withdraw amount waiveUnrealizedLoss = .ok r) :
    r.error = none ∨
    r.error = some .tecPRECISION_LOSS ∨
    r.error = some .tecPATH_DRY ∨
    r.error = some .tecINSUFFICIENT_FUNDS ∨
    r.error = some .tefINTERNAL :=
  Vault.withdraw_error_codes_proof v amount waiveUnrealizedLoss r hok

end XRPL.Model.SingleAssetVault
