import XRPL.Properties.Vault.Common.WithdrawExits
import XRPL.Properties.Vault.Common.GuardProofs
import XRPL.Properties.Vault.Common.Preservation

/-! # `LawfulVault.withdraw` exits -/

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol

/-! ## `LawfulVault.sharesToAssetsWithdraw` -/

/-- When assetsTotal minus lossUnrealized rounds to a zero mantissa, any `shares`
are paid exactly zero. This is the only early exit of `sharesToAssetsWithdraw`. -/
theorem LawfulVault.sharesToAssetsWithdraw_zero_nav (lv : LawfulVault) (shares : STAmount)
    (waiveUnrealizedLoss : Bool) (netAssetValue : Number)
    (hnav : lv.assetsTotal.operator_sub
      (match waiveUnrealizedLoss with
        | true => Number.zero
        | false => lv.lossUnrealized) .to_nearest = .ok netAssetValue)
    (hz : netAssetValue.mantissa_ = 0) :
    lv.sharesToAssetsWithdraw shares waiveUnrealizedLoss =
      .ok (STAmount.zero lv.numericType) :=
  LawfulVault.sharesToAssetsWithdraw_zero_nav_proof lv shares waiveUnrealizedLoss
    netAssetValue hnav hz

variable (lv : LawfulVault)

/-! ## `LawfulVault.withdraw` -/

/-- The withdrawn amount `assets'` exceeds `assetsAvailable`: `some .tecINSUFFICIENT_FUNDS`. -/
theorem LawfulVault.withdraw_insufficient_funds (amount : WithdrawAmount)
    (waiveUnrealizedLoss : Bool) (cw : ComputeWithdrawResult) (assetsNumber' : Number)
    (hcomp : (match amount with
        | .vaultAssets assets => computeWithdrawByAssets lv assets waiveUnrealizedLoss
        | .vaultShares shares => computeWithdrawByShares lv shares waiveUnrealizedLoss)
      = .ok cw)
    (herr : cw.error = none)
    (haN : cw.assets'.toNumber .to_nearest = .ok assetsNumber')
    (hins : lv.assetsAvailable.operator_lt assetsNumber' = true) :
    lv.withdraw amount waiveUnrealizedLoss =
      .ok (.rejected lv .tecINSUFFICIENT_FUNDS) :=
  LawfulVault.withdraw_insufficient_funds_proof lv amount waiveUnrealizedLoss cw assetsNumber'
    hcomp herr haN hins

/-- The withdrawal redeems the whole share total while `lossUnrealized` is
nonzero: `some .tefINTERNAL`. -/
theorem LawfulVault.withdraw_final_nonzero_loss (amount : WithdrawAmount)
    (waiveUnrealizedLoss : Bool) (cw : ComputeWithdrawResult) (assetsNumber' : Number)
    (sharesTotalAmount : STAmount)
    (hcomp : (match amount with
        | .vaultAssets assets => computeWithdrawByAssets lv assets waiveUnrealizedLoss
        | .vaultShares shares => computeWithdrawByShares lv shares waiveUnrealizedLoss)
      = .ok cw)
    (herr : cw.error = none)
    (haN : cw.assets'.toNumber .to_nearest = .ok assetsNumber')
    (hins : lv.assetsAvailable.operator_lt assetsNumber' = false)
    (hst : STAmount.ofNumber .int64 lv.sharesTotal .to_nearest = .ok sharesTotalAmount)
    (hfin : cw.sharesRedeemed.operator_eq sharesTotalAmount = true)
    (hloss : lv.lossUnrealized.operator_ne Number.zero = true) :
    lv.withdraw amount waiveUnrealizedLoss =
      .ok (.rejected lv .tefINTERNAL) :=
  LawfulVault.withdraw_final_nonzero_loss_proof lv amount waiveUnrealizedLoss cw assetsNumber'
    sharesTotalAmount hcomp herr haN hins hst hfin hloss

/-- The withdrawal redeems the whole share total on a vault with no unrealized
loss: the vault is zeroed and the withdrawer is paid all of `assetsAvailable`.
The `to_lawful` re-check is proven to succeed via `withdraw_final_poststate_lawful`,
so the `.notLawful` throw is unreachable. -/
theorem LawfulVault.withdraw_final (amount : WithdrawAmount) (waiveUnrealizedLoss : Bool)
    (cw : ComputeWithdrawResult) (assetsNumber' : Number)
    (sharesTotalAmount allAvailable : STAmount)
    (hcomp : (match amount with
        | .vaultAssets assets => computeWithdrawByAssets lv assets waiveUnrealizedLoss
        | .vaultShares shares => computeWithdrawByShares lv shares waiveUnrealizedLoss)
      = .ok cw)
    (herr : cw.error = none)
    (haN : cw.assets'.toNumber .to_nearest = .ok assetsNumber')
    (hins : lv.assetsAvailable.operator_lt assetsNumber' = false)
    (hst : STAmount.ofNumber .int64 lv.sharesTotal .to_nearest = .ok sharesTotalAmount)
    (hfin : cw.sharesRedeemed.operator_eq sharesTotalAmount = true)
    (hloss : lv.lossUnrealized.operator_ne Number.zero = false)
    (hallAvail : STAmount.ofNumber lv.numericType lv.assetsAvailable .to_nearest = .ok allAvailable) :
    ∃ lv' : LawfulVault,
      lv.withdraw amount waiveUnrealizedLoss = .ok ⟨none, lv', allAvailable, cw.sharesRedeemed⟩ ∧
      lv'.toRawVault = { lv.toRawVault with assetsTotal := Number.zero, assetsAvailable := Number.zero, sharesTotal := Number.zero } := by
  have hL : lv.toExact.lossUnrealized = 0 :=
    (Number.operator_ne_zero_eq_false_iff lv.lossUnrealized lv.wf.lossUnrealized_norm).mp hloss
  obtain ⟨lv', htl, hlv'eq⟩ := LawfulVault.withdraw_final_poststate_lawful lv hL
  refine ⟨lv', ?_, hlv'eq⟩
  unfold LawfulVault.withdraw
  simp only []
  cases amount
  all_goals {
    simp only [] at hcomp ⊢
    rw [hcomp, ok_bind]
    rw [if_neg (by rw [herr, Option.isSome_none]; exact Bool.false_ne_true)]
    try simp only [pure_bind]
    rw [haN, ok_bind, if_neg (by rw [hins]; exact Bool.false_ne_true)]
    try simp only [pure_bind]
    rw [hst, ok_bind, if_pos hfin,
      if_neg (by rw [hloss]; exact Bool.false_ne_true)]
    try simp only [pure_bind]
    rw [hallAvail, ok_bind, htl, ok_bind]
    rfl
  }

/-- A nonzero `assets'` whose subtraction does not change `assetsTotal` rounded
into the vault's `numericType`: `some .tecPRECISION_LOSS`. The guard is marked
"(waiting the C++ fix)" in the model. -/
theorem LawfulVault.withdraw_payout_too_small (amount : WithdrawAmount)
    (waiveUnrealizedLoss : Bool) (cw : ComputeWithdrawResult)
    (assetsNumber' sharesBurnedNumber assetsTotal' : Number)
    (sharesTotalAmount assetsTotalRounded assetsTotalRounded' : STAmount)
    (hcomp : (match amount with
        | .vaultAssets assets => computeWithdrawByAssets lv assets waiveUnrealizedLoss
        | .vaultShares shares => computeWithdrawByShares lv shares waiveUnrealizedLoss)
      = .ok cw)
    (herr : cw.error = none)
    (haN : cw.assets'.toNumber .to_nearest = .ok assetsNumber')
    (hins : lv.assetsAvailable.operator_lt assetsNumber' = false)
    (hst : STAmount.ofNumber .int64 lv.sharesTotal .to_nearest = .ok sharesTotalAmount)
    (hfin : cw.sharesRedeemed.operator_eq sharesTotalAmount = false)
    (hsN : cw.sharesRedeemed.toNumber .to_nearest = .ok sharesBurnedNumber)
    (hat : lv.assetsTotal.operator_sub assetsNumber' .to_nearest = .ok assetsTotal')
    (hrt : STAmount.ofNumber lv.numericType lv.assetsTotal .to_nearest = .ok assetsTotalRounded)
    (hrt' : STAmount.ofNumber lv.numericType assetsTotal' .to_nearest = .ok assetsTotalRounded')
    (hguard : (assetsNumber'.mantissa_ != 0 &&
      assetsTotalRounded.operator_eq assetsTotalRounded') = true) :
    lv.withdraw amount waiveUnrealizedLoss =
      .ok (.rejected lv .tecPRECISION_LOSS) :=
  LawfulVault.withdraw_payout_too_small_proof lv amount waiveUnrealizedLoss cw
    assetsNumber' sharesBurnedNumber assetsTotal' sharesTotalAmount assetsTotalRounded
    assetsTotalRounded' hcomp herr haN hins hst hfin hsN hat hrt hrt' hguard

/-- Every outcome of a withdrawal that runs without a throw. -/
theorem LawfulVault.withdraw_error_codes (amount : WithdrawAmount) (waiveUnrealizedLoss : Bool)
    (r : WithdrawResult)
    (hok : lv.withdraw amount waiveUnrealizedLoss = .ok r) :
    r.error = none ∨
    r.error = some .tecPRECISION_LOSS ∨
    r.error = some .tecPATH_DRY ∨
    r.error = some .tecINSUFFICIENT_FUNDS ∨
    r.error = some .tefINTERNAL :=
  LawfulVault.withdraw_error_codes_proof lv amount waiveUnrealizedLoss r hok

end XRPL.Model.SingleAssetVault
