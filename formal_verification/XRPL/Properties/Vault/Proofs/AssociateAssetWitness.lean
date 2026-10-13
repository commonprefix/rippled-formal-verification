import XRPL.Properties.Vault.Common.VaultDecidable
import XRPL.Properties.Vault.Defs

/-! # Underflow witnesses for the `associateAsset` rows

An on-grid IOU vault holding `2·10⁻⁸¹` (the bottom decade of the IOU grid) with
`2·10¹⁵` shares, so one share is worth `10⁻⁹⁶`. Redeeming, or clawing back, all but
one share leaves `10⁻⁹⁶`, nonzero and below the smallest IOU magnitude `10⁻⁸¹`, so
`STAmount.ofNumber` flushes it to zero: the stored total is off the grid. -/

set_option linter.style.nativeDecide false

namespace XRPL.Model.SingleAssetVault.CatHI

open XRPL.Model.Protocol

def ufv : RawVault :=
  { assetsTotal := ⟨false, 2000000000000000000, -99⟩
  , assetsAvailable := ⟨false, 2000000000000000000, -99⟩
  , assetsReserved := Number.zero, assetsMaximum := none
  , numericType := .fractional, scale := 15
  , sharesTotal := ⟨false, 2000000000000000000, -3⟩
  , lossUnrealized := Number.zero }

def ufvL : Vault := ⟨ufv, by native_decide, by native_decide⟩

/-- All but one of the `2·10¹⁵` shares. -/
def ufShares : STAmount := STAmount.unchecked .int64 1999999999999999 0 false

lemma ufShares_pos : 0 < (WithdrawAmount.vaultShares ufShares).amount.toRat := by native_decide

/-- The withdrawal's result, computed by the model. -/
def ufWR : WithdrawResult :=
  (ufvL.withdraw (.vaultShares ufShares) false ufShares_pos).toOption.getD
    (WithdrawResult.rejected ufvL .tecINTERNAL)

/-- The clawed-back amount, `1999999999999999·10⁻⁹⁶`. -/
def ufClawAssets : STAmount := STAmount.unchecked .fractional 1999999999999999 (-96) false

def ufHolderShares : STAmount := STAmount.unchecked .int64 2000000000000000 0 false

lemma ufClawAssets_nn : 0 ≤ ufClawAssets.toRat := by native_decide

/-- The clawback's result, computed by the model. -/
def ufCR : ClawbackResult :=
  (ufvL.clawback ufClawAssets ufHolderShares ufClawAssets_nn).toOption.getD
    (ClawbackResult.rejected ufvL .tecINTERNAL)

lemma ufvL_ongrid : ¬ ufvL.assetsRounded := by
  unfold Vault.assetsRounded; native_decide

end XRPL.Model.SingleAssetVault.CatHI

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol CatHI

set_option maxRecDepth 10000

lemma Vault.withdraw_underflow_witness :
    ∃ (v : Vault) (amount : WithdrawAmount) (waiveUnrealizedLoss : Bool)
      (hpos : 0 < amount.amount.toRat) (r : WithdrawResult),
      ¬ v.assetsRounded ∧ v.withdraw amount waiveUnrealizedLoss hpos = .ok r ∧
      r.error = none ∧ r.vault'.assetsRounded :=
  ⟨ufvL, .vaultShares ufShares, false, ufShares_pos, ufWR, ufvL_ongrid,
    by native_decide, by native_decide, by unfold Vault.assetsRounded; native_decide⟩

lemma Vault.clawback_underflow_witness :
    ∃ (v : Vault) (assets holderShares : STAmount) (hnn : 0 ≤ assets.toRat)
      (r : ClawbackResult),
      ¬ v.assetsRounded ∧ v.clawback assets holderShares hnn = .ok r ∧
      r.error = none ∧ r.vault'.assetsRounded :=
  ⟨ufvL, ufClawAssets, ufHolderShares, ufClawAssets_nn, ufCR, ufvL_ongrid,
    by native_decide, by native_decide, by unfold Vault.assetsRounded; native_decide⟩

end XRPL.Model.SingleAssetVault
