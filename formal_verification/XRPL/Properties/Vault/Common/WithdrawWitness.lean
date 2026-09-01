import XRPL.Model.Vault.VaultDeposit
import XRPL.Model.Vault.VaultWithdraw
import XRPL.Properties.Approx
import XRPL.Properties.Vault.Common.WithdrawDefs
import XRPL.Properties.Vault.Common.DilutionWitness

/-! # Witness data for the `LawfulVault.withdraw` sharpness theorems

Concrete vaults, amounts, and results for the withdraw `*_attained`
witnesses `VaultWithdraw.lean` delegates to, each closed by `native_decide`
over the withdraw pipeline. One fractional vault holding `3` assets against
`7·10¹⁵` shares backs every witness.

* Witnesses for `sharesToAssetsWithdraw`, `withdraw_sharesBurned` and
  `withdraw_payout`: withdrawing the amount `1` prices
  `7·10¹⁵ / 3 = 2333333333333333.33…` shares, rounded to `2333333333333333`
  whole shares. The share error `1/3` exceeds the relative budget
  `ideal · depositε`. Those shares are worth
  `3 · 2333333333333333 / 7·10¹⁵ = 0.99999999999999985714…`, converted downward
  at 16 digits to `0.9999999999999998`. The shortfall `4/(7·10¹⁶)` exceeds
  `ideal · depositε < 10^(-17)`.
* Witness for `withdraw_vault_updates`: redeeming `2333333333333` shares pays
  `0.0009999999999998571`, whose lowest digit sits below the 19-digit window of
  the stored total `3`. The stored difference `2.999000000000000143` is the
  exact difference `2.9990000000000001429` rounded to nearest, so the stored
  total is not the exact difference. -/

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol

set_option linter.style.nativeDecide false

/-- The shared withdraw witness vault: 3 assets, 7·10¹⁵ shares. -/
def wvW : RawVault :=
  { assetsTotal := ⟨false, 3000000000000000000, -18⟩
  , assetsAvailable := ⟨false, 3000000000000000000, -18⟩
  , assetsReserved := Number.zero
  , assetsMaximum := none, numericType := .fractional, scale := 0
  , sharesTotal := ⟨false, 7000000000000000000, -3⟩
  , lossUnrealized := Number.zero }

/-- The withdraw witness vault as a `LawfulVault`. -/
def wvWL : LawfulVault := ⟨wvW, by native_decide, by native_decide⟩

/-- The asset-denominated witness amount, `1` of the IOU. -/
def waW : STAmount := STAmount.unchecked .fractional 1000000000000000 (-15) false

/-- The redeemed shares, `7·10¹⁵/3` rounded to nearest: `2333333333333333`. -/
def wshW : STAmount := STAmount.unchecked .int64 2333333333333333 0 false

/-- The payout: `3 · 2333333333333333 / 7·10¹⁵` rounded downward at 16 digits,
`0.9999999999999998`. -/
def wpW : STAmount := STAmount.unchecked .fractional 9999999999999998 (-16) false

/-- The stored share total as an int64 amount, `7000000000000000`. -/
def wstW : STAmount := STAmount.unchecked .int64 7000000000000000 0 false

/-- The post-withdrawal vault of the asset-denominated run. -/
def wvW' : RawVault :=
  { assetsTotal := ⟨false, 2000000000000000200, -18⟩
  , assetsAvailable := ⟨false, 2000000000000000200, -18⟩
  , assetsReserved := Number.zero
  , assetsMaximum := none, numericType := .fractional, scale := 0
  , sharesTotal := ⟨false, 4666666666666667000, -3⟩
  , lossUnrealized := Number.zero }

/-- The post-withdrawal vault as a `LawfulVault` (the op re-validates). -/
def wvW'L : LawfulVault := ⟨wvW', by native_decide, by native_decide⟩

/-- The witness result of the asset-denominated run. -/
def wrW : WithdrawResult := ⟨none, wvW'L, wpW, wshW⟩

/-- The share-denominated witness shares of the vault-updates run,
`2333333333333`. -/
def wsh4W : STAmount := STAmount.unchecked .int64 2333333333333 0 false

/-- The payout of the vault-updates run: `3 · 2333333333333 / 7·10¹⁵` rounded
downward at 16 digits, `0.0009999999999998571`. -/
def wp4W : STAmount := STAmount.unchecked .fractional 9999999999998571 (-19) false

/-- The post-withdrawal vault of the vault-updates run. Its stored
`assetsTotal` is the 19-digit rounding of the exact difference. -/
def wv4W' : RawVault :=
  { assetsTotal := ⟨false, 2999000000000000143, -18⟩
  , assetsAvailable := ⟨false, 2999000000000000143, -18⟩
  , assetsReserved := Number.zero
  , assetsMaximum := none, numericType := .fractional, scale := 0
  , sharesTotal := ⟨false, 6997666666666667000, -3⟩
  , lossUnrealized := Number.zero }

/-- The vault-updates post-withdrawal vault as a `LawfulVault` (the op re-validates). -/
def wv4W'L : LawfulVault := ⟨wv4W', by native_decide, by native_decide⟩

/-- The witness result of the vault-updates run. -/
def wr4W : WithdrawResult := ⟨none, wv4W'L, wp4W, wsh4W⟩

/-! ## The `*_attained` witnesses -/

set_option maxRecDepth 10000

/-- Witness data for `LawfulVault.sharesToAssetsWithdraw_attained`. -/
theorem LawfulVault.sharesToAssetsWithdraw_witness :
    ∃ (lv : LawfulVault) (shares assets : STAmount) (waiveUnrealizedLoss : Bool),
      0 < shares.toRat ∧
      lv.WithdrawNavExact waiveUnrealizedLoss ∧
      lv.sharesToAssetsWithdraw shares waiveUnrealizedLoss = .ok assets ∧
      RoundsWithinWitness assets
        (lv.idealAssetsWithdraw waiveUnrealizedLoss shares.toRat) depositε := by
  refine ⟨wvWL, wshW, wpW, false, by native_decide, ?_,
    by native_decide, by unfold RoundsWithinWitness; native_decide⟩
  exact ⟨⟨false, 3000000000000000000, -18⟩,
    by native_decide, by native_decide⟩

/-- Witness data for `LawfulVault.withdraw_sharesBurned_attained`. -/
theorem LawfulVault.withdraw_sharesBurned_witness :
    ∃ (lv : LawfulVault) (assets : STAmount) (waiveUnrealizedLoss : Bool) (r : WithdrawResult),
      0 < assets.toRat ∧
      lv.WithdrawNavExact waiveUnrealizedLoss ∧
      lv.withdraw (.vaultAssets assets) waiveUnrealizedLoss = .ok r ∧ r.error = none ∧
      RoundsWithinWitness r.sharesBurned
        (lv.idealSharesWithdraw waiveUnrealizedLoss assets.toRat) depositε := by
  refine ⟨wvWL, waW, false, wrW, by native_decide, ?_,
    by unfold RoundsWithinWitness; native_decide⟩
  exact ⟨⟨false, 3000000000000000000, -18⟩,
    by native_decide, by native_decide⟩

/-- Witness data for `LawfulVault.withdraw_payout_attained`. -/
theorem LawfulVault.withdraw_payout_witness :
    ∃ (lv : LawfulVault) (amount : WithdrawAmount) (waiveUnrealizedLoss : Bool)
      (sharesTotalAmount : STAmount) (r : WithdrawResult),
      lv.WithdrawNavExact waiveUnrealizedLoss ∧
      lv.withdraw amount waiveUnrealizedLoss = .ok r ∧ r.error = none ∧
      STAmount.ofNumber .int64 lv.sharesTotal .to_nearest = .ok sharesTotalAmount ∧
      r.sharesBurned.operator_eq sharesTotalAmount = false ∧
      RoundsWithinWitness r.assets'
        (lv.idealAssetsWithdraw waiveUnrealizedLoss r.sharesBurned.toRat) depositε := by
  refine ⟨wvWL, .vaultAssets waW, false, wstW, wrW, ?_,
    by unfold RoundsWithinWitness; native_decide⟩
  exact ⟨⟨false, 3000000000000000000, -18⟩,
    by native_decide, by native_decide⟩

/-- Witness data for `LawfulVault.withdraw_vault_updates_attained`. -/
theorem LawfulVault.withdraw_vault_updates_witness :
    ∃ (lv : LawfulVault) (amount : WithdrawAmount) (waiveUnrealizedLoss : Bool)
      (sharesTotalAmount : STAmount) (r : WithdrawResult),
      lv.withdraw amount waiveUnrealizedLoss = .ok r ∧ r.error = none ∧
      STAmount.ofNumber .int64 lv.sharesTotal .to_nearest = .ok sharesTotalAmount ∧
      r.sharesBurned.operator_eq sharesTotalAmount = false ∧
      r.vault'.assetsTotal.toRat ≠ lv.toExact.assetsTotal - r.assets'.toRat :=
  ⟨wvWL, .vaultShares wsh4W, false, wstW, wr4W, by native_decide⟩

/-- The vault-updates payout re-rounded to the vault scale,
`0.000999999999999`. -/
def wpr4W : STAmount := STAmount.unchecked .fractional 9999999999990000 (-19) false

/-- The applied total delta of the vault-updates run, `0.000999999999999857`,
as a `Number`. -/
def wdn4W : Number := ⟨false, 9999999999998570000, -22⟩

/-- The applied delta as an on-ledger amount, one step below the payout. -/
def wda4W : STAmount := STAmount.unchecked .fractional 9999999999998570 (-19) false

/-- Witness data for `LawfulVault.withdraw_applied_delta_attained`. -/
theorem LawfulVault.withdraw_applied_delta_witness :
    ∃ (lv : LawfulVault) (amount : WithdrawAmount) (waiveUnrealizedLoss : Bool)
      (assets'' : STAmount) (r : WithdrawResult)
      (deltaTotal : Number) (deltaAmount : STAmount),
      lv.withdraw amount waiveUnrealizedLoss = .ok r ∧ r.error = none ∧
      roundToVaultExponent r.assets' lv.assetsTotal = .ok assets'' ∧
      assets''.operator_eq r.assets' = false ∧
      lv.assetsTotal.operator_sub r.vault'.assetsTotal .to_nearest = .ok deltaTotal ∧
      STAmount.ofNumber lv.numericType deltaTotal .to_nearest = .ok deltaAmount ∧
      deltaAmount.operator_eq r.assets' = false :=
  ⟨wvWL, .vaultShares wsh4W, false, wpr4W, wr4W, wdn4W, wda4W, by native_decide⟩

end XRPL.Model.SingleAssetVault
