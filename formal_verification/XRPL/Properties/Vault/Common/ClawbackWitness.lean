import XRPL.Properties.Vault.Common.ClawbackDefs
import XRPL.Properties.Vault.Common.WithdrawDefs
import XRPL.Properties.Vault.Common.DilutionWitness
import XRPL.Model.Vault.VaultClawback
import XRPL.Model.Vault.VaultDeposit

/-! # Witness data for the clawback `*_attained` theorems

Concrete vaults, amounts, and results for the clawback `*_attained`
witnesses `VaultClawback.lean` delegates to, each closed by `native_decide`
over the clawback pipeline. -/

set_option linter.style.nativeDecide false

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol

/-! ## The witness vaults, amounts, and results -/

/-- The shared witness vault: 3 assets, 3 available, 7·10¹⁵ shares. -/
def cwv : RawVault :=
  { assetsTotal := ⟨false, 3000000000000000000, -18⟩
  , assetsAvailable := ⟨false, 3000000000000000000, -18⟩
  , assetsReserved := Number.zero
  , assetsMaximum := none, numericType := .fractional, scale := 0
  , sharesTotal := ⟨false, 7000000000000000000, -3⟩
  , lossUnrealized := Number.zero }

/-- The clamped-run vault: the same vault with only `0.0001` available. -/
def cwvB : RawVault :=
  { cwv with assetsAvailable := ⟨false, 1000000000000000000, -22⟩ }

/-- Lawful-vault witnesses. -/
def cwvL : Vault := ⟨cwv, by native_decide, by native_decide⟩
def cwvBL : Vault := ⟨cwvB, by native_decide, by native_decide⟩

/-- The clawed amount, `1` of the IOU. -/
def cwa1 : STAmount := STAmount.unchecked .fractional 1000000000000000 (-15) false

/-- Witness holder-shares balance passed to `Vault.clawback`. Unused on these
runs since `cwa1` is nonzero (the zero-amount "claw all" branch never fires). -/
def cwHolderShares : STAmount := STAmount.zero .int64

/-- The destroyed shares of the `cwv` run, `2333333333333333`. -/
def cwsh1 : STAmount := STAmount.unchecked .int64 2333333333333333 0 false

/-- The recovered assets of the `cwv` run, `0.9999999999999998`. -/
def cwar1 : STAmount := STAmount.unchecked .fractional 9999999999999998 (-16) false

/-- The clamped recovery amount of the `cwvB` run, `0.0001`. -/
def cwclamp : STAmount := STAmount.unchecked .fractional 1000000000000000 (-19) false

/-- The destroyed shares of the `cwvB` run, `233333333333`. -/
def cwsh2 : STAmount := STAmount.unchecked .int64 233333333333 0 false

/-- The recovered assets of the `cwvB` run, `0.000099999999999857140`. -/
def cwar2 : STAmount := STAmount.unchecked .fractional 9999999999985714 (-20) false

/-- The `cwv` post-clawback vault. -/
def cwv1' : RawVault :=
  { assetsTotal := ⟨false, 2000000000000000200, -18⟩
  , assetsAvailable := ⟨false, 2000000000000000200, -18⟩
  , assetsReserved := Number.zero
  , assetsMaximum := none, numericType := .fractional, scale := 0
  , sharesTotal := ⟨false, 4666666666666667000, -3⟩
  , lossUnrealized := Number.zero }

/-- The `cwv` post-clawback vault as a `Vault` (the op re-validates). -/
def cwv1'L : Vault := ⟨cwv1', by native_decide, by native_decide⟩

/-- The `cwv` clawback result. -/
def cwr1 : ClawbackResult := ⟨none, cwv1'L, cwar1, cwsh1⟩

/-- The `cwvB` post-clawback vault. -/
def cwvB' : RawVault :=
  { assetsTotal := ⟨false, 2999900000000000143, -18⟩
  , assetsAvailable := ⟨false, 1428600000000000000, -34⟩
  , assetsReserved := Number.zero, assetsMaximum := none, numericType := .fractional, scale := 0
  , sharesTotal := ⟨false, 6999766666666667000, -3⟩
  , lossUnrealized := Number.zero }

/-- The `cwvB` post-clawback vault as a `Vault` (the op re-validates). -/
def cwvB'L : Vault := ⟨cwvB', by native_decide, by native_decide⟩

/-- The `cwvB` clawback result. -/
def cwr2 : ClawbackResult := ⟨none, cwvB'L, cwar2, cwsh2⟩

/-! ## The `*_attained` witnesses -/

set_option maxRecDepth 10000

/-- Witness for `Vault.clawback_sharesDestroyed_attained`: the `cwv` run's
half-share rounding error `1/3` exceeds the relative budget alone. -/
theorem Vault.clawback_sharesDestroyed_witness :
    ∃ (v : Vault) (assets holderShares sharesDestroyed assetsRecovered : STAmount)
      (assetsRecoveredNumber : Number) (r : ClawbackResult),
      v.WithdrawNavExact false ∧
      assetsToSharesWithdraw v assets false false = .ok sharesDestroyed ∧
      v.sharesToAssetsWithdraw sharesDestroyed false = .ok assetsRecovered ∧
      assetsRecovered.toNumber .to_nearest = .ok assetsRecoveredNumber ∧
      assetsRecoveredNumber.operator_gt v.assetsAvailable = false ∧
      v.clawback assets holderShares = .ok r ∧ r.error = none ∧
      RoundsWithinWitness r.sharesDestroyed
        (v.idealSharesClawback assets.toRat) depositε := by
  refine ⟨cwvL, cwa1, cwHolderShares, cwsh1, cwar1, ⟨false, 9999999999999998000, -19⟩, cwr1,
    ?_, by unfold RoundsWithinWitness; native_decide⟩
  exact ⟨⟨false, 3000000000000000000, -18⟩,
    by native_decide, by native_decide⟩

/-- Witness for `Vault.clawback_sharesDestroyed_clamped_attained`: the `cwvB`
run reprices from `assetsAvailable` and its truncation error `1/3` exceeds the
relative budget alone. -/
theorem Vault.clawback_sharesDestroyed_clamped_witness :
    ∃ (v : Vault) (assets holderShares sharesDestroyed assetsRecovered assetsRecovered' : STAmount)
      (assetsRecoveredNumber : Number) (r : ClawbackResult),
      v.WithdrawNavExact false ∧
      assetsToSharesWithdraw v assets false false = .ok sharesDestroyed ∧
      v.sharesToAssetsWithdraw sharesDestroyed false = .ok assetsRecovered ∧
      assetsRecovered.toNumber .to_nearest = .ok assetsRecoveredNumber ∧
      assetsRecoveredNumber.operator_gt v.assetsAvailable = true ∧
      STAmount.ofNumber v.numericType v.assetsAvailable .to_nearest = .ok assetsRecovered' ∧
      v.clawback assets holderShares = .ok r ∧ r.error = none ∧
      RoundsWithinWitness r.sharesDestroyed
        (v.idealSharesClawback assetsRecovered'.toRat) depositε := by
  refine ⟨cwvBL, cwa1, cwHolderShares, cwsh1, cwar1, cwclamp, ⟨false, 9999999999999998000, -19⟩, cwr2,
    ?_, by unfold RoundsWithinWitness; native_decide⟩
  exact ⟨⟨false, 3000000000000000000, -18⟩,
    by native_decide, by native_decide⟩

/-- Witness for `Vault.clawback_assetsRecovered_attained`: the `cwv` run's
recovery misses the destroyed shares' exact worth by more than the relative
budget. -/
theorem Vault.clawback_assetsRecovered_witness :
    ∃ (v : Vault) (assets holderShares : STAmount) (r : ClawbackResult),
      v.WithdrawNavExact false ∧ v.clawback assets holderShares = .ok r ∧
      r.error = none ∧
      RoundsWithinWitness r.assetsRecovered
        (v.idealAssetsClawback r.sharesDestroyed.toRat) depositε := by
  refine ⟨cwvL, cwa1, cwHolderShares, cwr1,
    ?_, by unfold RoundsWithinWitness; native_decide⟩
  exact ⟨⟨false, 3000000000000000000, -18⟩,
    by native_decide, by native_decide⟩

/-- Witness for `Vault.clawback_vault_updates_attained`: the `cwvB` run's
stored total is not the exact difference. -/
theorem Vault.clawback_vault_updates_witness :
    ∃ (v : Vault) (assets holderShares : STAmount) (r : ClawbackResult),
      v.clawback assets holderShares = .ok r ∧ r.error = none ∧
      r.vault'.assetsTotal.toRat ≠ v.toExact.assetsTotal - r.assetsRecovered.toRat :=
  ⟨cwvBL, cwa1, cwHolderShares, cwr2, by native_decide⟩

/-- The `cwvB` recovery re-rounded to the vault scale, `0.000099999999999`. -/
def cwrr2 : STAmount := STAmount.unchecked .fractional 9999999999900000 (-20) false

/-- The applied total delta of the `cwvB` run, `0.000099999999999857` -/
def cwdn2 : Number := ⟨false, 9999999999985700000, -23⟩

/-- The applied delta as an on-ledger amount, below the recovery. -/
def cwda2 : STAmount := STAmount.unchecked .fractional 9999999999985700 (-20) false

/-- Witness for `Vault.clawback_applied_delta_attained`: the `cwvB` run's
recovery is off the vault grid and the stored total moves by a different
amount. -/
theorem Vault.clawback_applied_delta_witness :
    ∃ (v : Vault) (assets holderShares assetsRecovered' : STAmount) (r : ClawbackResult)
      (deltaTotal : Number) (deltaAmount : STAmount),
      v.clawback assets holderShares = .ok r ∧ r.error = none ∧
      roundToVaultExponent r.assetsRecovered v.assetsTotal = .ok assetsRecovered' ∧
      assetsRecovered'.operator_eq r.assetsRecovered = false ∧
      v.assetsTotal.operator_sub r.vault'.assetsTotal .to_nearest = .ok deltaTotal ∧
      STAmount.ofNumber v.numericType deltaTotal .to_nearest = .ok deltaAmount ∧
      deltaAmount.operator_eq r.assetsRecovered = false :=
  ⟨cwvBL, cwa1, cwHolderShares, cwrr2, cwr2, cwdn2, cwda2, by native_decide⟩

/-! ## Clawback-all empty-shares dust witness -/

/-- Dust witness vault: π assets/available (16-digit IOU), 7000025 shares. -/
def clawbackDustVault : RawVault :=
  { assetsTotal := ⟨false, 3141592653589793000, -18⟩
  , assetsAvailable := ⟨false, 3141592653589793000, -18⟩
  , assetsReserved := Number.zero
  , assetsMaximum := none, numericType := .fractional, scale := 0
  , sharesTotal := ⟨false, 7000025000000000000, -12⟩
  , lossUnrealized := Number.zero }

/-- The dust witness vault as a `Vault`. -/
def clawbackDustVaultL : Vault := ⟨clawbackDustVault, by decide, by decide⟩

/-- Witness that `clawback_success`'s `hempty` is meaningful: clawing back all
shares of a lawful vault can leave sub-ULP `assetsTotal` dust (`sharesTotal' = 0`,
`assetsTotal' ≠ 0`), so `to_lawful` rejects with `notLawful`. -/
theorem Vault.clawback_dust_witness :
    clawbackDustVaultL.clawback (STAmount.zero .fractional)
        (STAmount.unchecked .int64 7000025 0 false) = .error .notLawful := by
  native_decide

end XRPL.Model.SingleAssetVault
