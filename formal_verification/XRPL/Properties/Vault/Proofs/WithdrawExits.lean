import XRPL.Model.Vault.VaultWithdraw

/-! # `Vault.withdraw` exits

Proof bodies behind `VaultWithdrawReturn.lean`. -/

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol

lemma Vault.sharesToAssetsWithdraw_zero_nav_proof (v : Vault) (shares : STAmount)
    (waiveUnrealizedLoss : Bool) (netAssetValue : Number)
    (hnav : v.assetsTotal.operator_sub
      (match waiveUnrealizedLoss with
        | true => Number.zero
        | false => v.lossUnrealized) .to_nearest = .ok netAssetValue)
    (hz : netAssetValue.mantissa_ = 0) :
    v.sharesToAssetsWithdraw shares waiveUnrealizedLoss =
      .ok (STAmount.zero v.numericType) := by
  cases waiveUnrealizedLoss <;>
    simp_all [Vault.sharesToAssetsWithdraw, bind, Except.bind, pure, Except.pure]

lemma Vault.withdraw_insufficient_funds_proof (v : Vault) (amount : WithdrawAmount)
    (waiveUnrealizedLoss : Bool) (cw : ComputeWithdrawResult) (assetsNumber' : Number)
    (hpos : 0 < amount.amount.toRat)
    (hcomp : (match amount with
        | .vaultAssets assets => computeWithdrawByAssets v assets waiveUnrealizedLoss
        | .vaultShares shares => computeWithdrawByShares v shares waiveUnrealizedLoss)
      = .ok cw)
    (herr : cw.error = none)
    (haN : cw.assets'.toNumber .to_nearest = .ok assetsNumber')
    (hins : v.assetsAvailable.operator_lt assetsNumber' = true) :
    v.withdraw amount waiveUnrealizedLoss hpos =
      .ok (.rejected v .tecINSUFFICIENT_FUNDS) := by
  cases amount <;>
    simp_all [Vault.withdraw, bind, Except.bind, pure, Except.pure]

lemma Vault.withdraw_final_nonzero_loss_proof (v : Vault) (amount : WithdrawAmount)
    (waiveUnrealizedLoss : Bool) (cw : ComputeWithdrawResult) (assetsNumber' : Number)
    (sharesTotalAmount : STAmount)
    (hpos : 0 < amount.amount.toRat)
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
      .ok (.rejected v .tefINTERNAL) := by
  cases amount <;>
    simp_all [Vault.withdraw, bind, Except.bind, pure, Except.pure]

end XRPL.Model.SingleAssetVault
