import XRPL.Model.Vault.VaultWithdraw
import XRPL.Properties.Vault.Proofs.Lawful
import XRPL.Properties.Vault.Proofs.ExitsC.Basic
import XRPL.Properties.Vault.Proofs.ExitsC.Payout

/-! # `Vault.withdraw` exits through the grid clamp

Proof bodies behind `VaultWithdrawReturn.lean`. -/

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol

lemma Vault.withdraw_success_proof (v : Vault) (amount : WithdrawAmount) (waiveUnrealizedLoss : Bool)
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
      v'.toRawVault = { v.toRawVault with assetsTotal := assetsTotal', assetsAvailable := assetsAvailable', sharesTotal := sharesTotal' } := by
  obtain ⟨v', htl, hlv'eq⟩ := Vault.subtract_lawful v assetsNumber'
    sharesBurnedNumber assetsTotal' assetsAvailable' sharesTotal' hL hAV hp_norm hp_nn hp_le
    hb_norm hb_nn hb_den hb_le hfit hat hav hshares hempty
  refine ⟨v', ?_, hlv'eq⟩
  have hfnp := ExitsC.fnp_false reported hcpos
  cases amount <;>
    simp_all [Vault.withdraw, bind, Except.bind, pure, Except.pure]

lemma Vault.withdraw_clamp_precision_loss_proof (v : Vault) (amount : WithdrawAmount)
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
    v.withdraw amount waiveUnrealizedLoss hpos = .ok (.rejected v .tecPRECISION_LOSS) := by
  have hfnp := ExitsC.fnp_true reported hvanish
  cases amount <;>
    simp_all [Vault.withdraw, bind, Except.bind, pure, Except.pure]

lemma Vault.withdraw_payout_too_small_proof (v : Vault) (amount : WithdrawAmount)
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
  ExitsC.payout_too_small v amount waiveUnrealizedLoss cw assetsNumber' sharesBurnedNumber
    assetsTotal' sharesTotalAmount assetsTotalRounded assetsTotalRounded' hcomp herr haN hins hst
    hfin hsN hat hrt hrt' hguard hpos hcanon

end XRPL.Model.SingleAssetVault
