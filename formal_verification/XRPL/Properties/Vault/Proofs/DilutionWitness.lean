import XRPL.Properties.Vault.Common.VaultDecidable
import XRPL.Properties.Vault.Common.WithdrawDefs
import XRPL.Properties.Vault.Common.ClawbackDefs

/-! # Witnesses for the dilution bounds

Each is closed by `native_decide` over the model; every result record is computed by the
operation, not written out.

* Deposit, grid term: assets `0.9999999999999995`, 1 share, deposit `10^15 + 1`: the charge
  `10^15 - 1` falls short of the issued shares' worth by `3/2 - 10⁻¹⁵` steps of the
  post-deposit grid `10^0`.
* Withdrawal / clawback, half-unit term: `int64` assets `3`, 4 shares, redeem (claw back) 2:
  the worth `1.5` is paid `2`, per-share value `3/4 → 1/2`, the whole half unit less `3·ε`.
* Claw-all: the same on 8 shares with a 4-share holder.
* Deposit, relative term: assets `4677880426214914.973`, `8916544631` shares, deposit
  `4727117026339798`: the dilution is `1.5029` grid steps, past the grid term alone.
* Relative term: `int64` vaults near `2^62`, where the `Number` stages err by more than half
  a unit. -/

set_option linter.style.nativeDecide false
set_option maxRecDepth 10000

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol

lemma Vault.deposit_no_dilution_grid_witness :
    ∃ (v : Vault) (amountDeposit : STAmount) (hpos : 0 < amountDeposit.toRat)
      (r : DepositResult) (e : ℤ),
      amountDeposit.Canonical ∧ v.toExact.lossUnrealized = 0 ∧
      (v.toExact.sharesTotal : ℚ) + r.sharesIssued.toRat ≤ 2 ^ 63 - 1 ∧
      v.deposit amountDeposit false hpos = .ok r ∧ r.error = none ∧
      postSumExponent v.assetsTotal amountDeposit = .ok e ∧
      r.vault'.withdrawNav * (v.toExact.sharesTotal : ℚ) <
        v.withdrawNav * (r.vault'.toExact.sharesTotal : ℚ) -
          (3 / 2 - 2 / 10 ^ 15) * (10 : ℚ) ^ e * (v.toExact.sharesTotal : ℚ) :=
  ⟨(⟨{ assetsTotal := ⟨false, 9999999999999995000, -19⟩, assetsAvailable := ⟨false, 9999999999999995000, -19⟩, assetsReserved := Number.zero, assetsMaximum := none, numericType := .fractional, scale := 0, sharesTotal := ⟨false, 1000000000000000000, -18⟩, lossUnrealized := Number.zero }, by native_decide, by native_decide⟩ : Vault), (STAmount.unchecked .fractional 1000000000000001 (0) false), by native_decide,
    (((⟨{ assetsTotal := ⟨false, 9999999999999995000, -19⟩, assetsAvailable := ⟨false, 9999999999999995000, -19⟩, assetsReserved := Number.zero, assetsMaximum := none, numericType := .fractional, scale := 0, sharesTotal := ⟨false, 1000000000000000000, -18⟩, lossUnrealized := Number.zero }, by native_decide, by native_decide⟩ : Vault)).deposit (STAmount.unchecked .fractional 1000000000000001 (0) false) false (by native_decide)).toOption.getD
      (DepositResult.rejected (⟨{ assetsTotal := ⟨false, 9999999999999995000, -19⟩, assetsAvailable := ⟨false, 9999999999999995000, -19⟩, assetsReserved := Number.zero, assetsMaximum := none, numericType := .fractional, scale := 0, sharesTotal := ⟨false, 1000000000000000000, -18⟩, lossUnrealized := Number.zero }, by native_decide, by native_decide⟩ : Vault) .tecINTERNAL), 0,
    ⟨fun h => absurd h (by simp [STAmount.integral, STAmount.unchecked, NumericType.isIntegral]),
      fun _ => ⟨rfl, by decide, by decide, by decide, by decide⟩⟩, by native_decide, by native_decide, by native_decide, by native_decide, by native_decide, by native_decide⟩

lemma Vault.deposit_no_dilution_relative_witness :
    ∃ (v : Vault) (amountDeposit : STAmount) (hpos : 0 < amountDeposit.toRat)
      (r : DepositResult) (e : ℤ),
      amountDeposit.Canonical ∧ v.toExact.lossUnrealized = 0 ∧
      (v.toExact.sharesTotal : ℚ) + r.sharesIssued.toRat ≤ 2 ^ 63 - 1 ∧
      v.deposit amountDeposit false hpos = .ok r ∧ r.error = none ∧
      postSumExponent v.assetsTotal amountDeposit = .ok e ∧
      r.vault'.withdrawNav * (v.toExact.sharesTotal : ℚ) <
        v.withdrawNav * (r.vault'.toExact.sharesTotal : ℚ) -
          3 / 2 * (10 : ℚ) ^ e * (v.toExact.sharesTotal : ℚ) :=
  ⟨(⟨{ assetsTotal := ⟨false, 4677880426214914973, -3⟩, assetsAvailable := ⟨false, 4677880426214914973, -3⟩, assetsReserved := Number.zero, assetsMaximum := none, numericType := .fractional, scale := 0, sharesTotal := ⟨false, 8916544631000000000, -9⟩, lossUnrealized := Number.zero }, by native_decide, by native_decide⟩ : Vault), (STAmount.unchecked .fractional 4727117026339798 (0) false), by native_decide,
    (((⟨{ assetsTotal := ⟨false, 4677880426214914973, -3⟩, assetsAvailable := ⟨false, 4677880426214914973, -3⟩, assetsReserved := Number.zero, assetsMaximum := none, numericType := .fractional, scale := 0, sharesTotal := ⟨false, 8916544631000000000, -9⟩, lossUnrealized := Number.zero }, by native_decide, by native_decide⟩ : Vault)).deposit (STAmount.unchecked .fractional 4727117026339798 (0) false) false (by native_decide)).toOption.getD
      (DepositResult.rejected (⟨{ assetsTotal := ⟨false, 4677880426214914973, -3⟩, assetsAvailable := ⟨false, 4677880426214914973, -3⟩, assetsReserved := Number.zero, assetsMaximum := none, numericType := .fractional, scale := 0, sharesTotal := ⟨false, 8916544631000000000, -9⟩, lossUnrealized := Number.zero }, by native_decide, by native_decide⟩ : Vault) .tecINTERNAL), 0,
    ⟨fun h => absurd h (by simp [STAmount.integral, STAmount.unchecked, NumericType.isIntegral]),
      fun _ => ⟨rfl, by decide, by decide, by decide, by decide⟩⟩, by native_decide, by native_decide, by native_decide, by native_decide, by native_decide, by native_decide⟩

lemma Vault.withdraw_no_dilution_half_ulp_witness :
    ∃ (v : Vault) (amount : WithdrawAmount) (hpos : 0 < amount.amount.toRat) (r : WithdrawResult),
      v.toExact.lossUnrealized = 0 ∧ 0 ≤ r.sharesBurned.toRat ∧
      r.sharesBurned.Canonical ∧ r.sharesBurned.mNumericType = .int64 ∧
      r.sharesBurned.toRat ≤ (v.toExact.sharesTotal : ℚ) / 2 ∧
      (v.toExact.sharesTotal : ℚ) ≤ 2 ^ 63 - 1 ∧
      v.withdraw amount false hpos = .ok r ∧ r.error = none ∧
      r.vault'.withdrawNav * (v.toExact.sharesTotal : ℚ) <
        v.withdrawNav * (r.vault'.toExact.sharesTotal : ℚ) * (1 - depositε) -
          (1 - 1 / 10 ^ 15) * (1 / 2 * (10 : ℚ) ^ r.assets'.exponent) *
            (v.toExact.sharesTotal : ℚ) := by
  refine ⟨(⟨{ assetsTotal := ⟨false, 3000000000000000000, -18⟩, assetsAvailable := ⟨false, 3000000000000000000, -18⟩, assetsReserved := Number.zero, assetsMaximum := none, numericType := .int64, scale := 0, sharesTotal := ⟨false, 4000000000000000000, -18⟩, lossUnrealized := Number.zero }, by native_decide, by native_decide⟩ : Vault), (.vaultShares (STAmount.unchecked .int64 2 (0) false)), by native_decide,
    (((⟨{ assetsTotal := ⟨false, 3000000000000000000, -18⟩, assetsAvailable := ⟨false, 3000000000000000000, -18⟩, assetsReserved := Number.zero, assetsMaximum := none, numericType := .int64, scale := 0, sharesTotal := ⟨false, 4000000000000000000, -18⟩, lossUnrealized := Number.zero }, by native_decide, by native_decide⟩ : Vault)).withdraw (.vaultShares (STAmount.unchecked .int64 2 (0) false)) false (by native_decide)).toOption.getD
      (WithdrawResult.rejected (⟨{ assetsTotal := ⟨false, 3000000000000000000, -18⟩, assetsAvailable := ⟨false, 3000000000000000000, -18⟩, assetsReserved := Number.zero, assetsMaximum := none, numericType := .int64, scale := 0, sharesTotal := ⟨false, 4000000000000000000, -18⟩, lossUnrealized := Number.zero }, by native_decide, by native_decide⟩ : Vault) .tecINTERNAL), by native_decide, by native_decide, ?_, by native_decide, by native_decide, by native_decide, by native_decide, by native_decide, by unfold depositε; native_decide⟩
  rw [show ((((⟨{ assetsTotal := ⟨false, 3000000000000000000, -18⟩, assetsAvailable := ⟨false, 3000000000000000000, -18⟩, assetsReserved := Number.zero, assetsMaximum := none, numericType := .int64, scale := 0, sharesTotal := ⟨false, 4000000000000000000, -18⟩, lossUnrealized := Number.zero }, by native_decide, by native_decide⟩ : Vault)).withdraw (.vaultShares (STAmount.unchecked .int64 2 (0) false)) false (by native_decide)).toOption.getD
      (WithdrawResult.rejected (⟨{ assetsTotal := ⟨false, 3000000000000000000, -18⟩, assetsAvailable := ⟨false, 3000000000000000000, -18⟩, assetsReserved := Number.zero, assetsMaximum := none, numericType := .int64, scale := 0, sharesTotal := ⟨false, 4000000000000000000, -18⟩, lossUnrealized := Number.zero }, by native_decide, by native_decide⟩ : Vault) .tecINTERNAL)).sharesBurned = (STAmount.unchecked .int64 2 (0) false) from by native_decide]
  exact ⟨fun _ => ⟨⟨rfl, rfl, by decide⟩, by decide⟩, fun h => absurd h (by decide)⟩

lemma Vault.withdraw_no_dilution_relative_witness :
    ∃ (v : Vault) (amount : WithdrawAmount) (hpos : 0 < amount.amount.toRat) (r : WithdrawResult),
      v.toExact.lossUnrealized = 0 ∧ 0 ≤ r.sharesBurned.toRat ∧
      r.sharesBurned.Canonical ∧ r.sharesBurned.mNumericType = .int64 ∧
      r.sharesBurned.toRat ≤ (v.toExact.sharesTotal : ℚ) / 2 ∧
      (v.toExact.sharesTotal : ℚ) ≤ 2 ^ 63 - 1 ∧
      v.withdraw amount false hpos = .ok r ∧ r.error = none ∧
      r.vault'.withdrawNav * (v.toExact.sharesTotal : ℚ) <
        v.withdrawNav * (r.vault'.toExact.sharesTotal : ℚ) -
          1 / 2 * (10 : ℚ) ^ r.assets'.exponent * (v.toExact.sharesTotal : ℚ) := by
  refine ⟨(⟨{ assetsTotal := ⟨false, 2434563349544987818, 0⟩, assetsAvailable := ⟨false, 2434563349544987818, 0⟩, assetsReserved := Number.zero, assetsMaximum := none, numericType := .int64, scale := 0, sharesTotal := ⟨false, 1248538884401275250, -1⟩, lossUnrealized := Number.zero }, by native_decide, by native_decide⟩ : Vault), (.vaultShares (STAmount.unchecked .int64 46175462685143005 (0) false)), by native_decide,
    (((⟨{ assetsTotal := ⟨false, 2434563349544987818, 0⟩, assetsAvailable := ⟨false, 2434563349544987818, 0⟩, assetsReserved := Number.zero, assetsMaximum := none, numericType := .int64, scale := 0, sharesTotal := ⟨false, 1248538884401275250, -1⟩, lossUnrealized := Number.zero }, by native_decide, by native_decide⟩ : Vault)).withdraw (.vaultShares (STAmount.unchecked .int64 46175462685143005 (0) false)) false (by native_decide)).toOption.getD
      (WithdrawResult.rejected (⟨{ assetsTotal := ⟨false, 2434563349544987818, 0⟩, assetsAvailable := ⟨false, 2434563349544987818, 0⟩, assetsReserved := Number.zero, assetsMaximum := none, numericType := .int64, scale := 0, sharesTotal := ⟨false, 1248538884401275250, -1⟩, lossUnrealized := Number.zero }, by native_decide, by native_decide⟩ : Vault) .tecINTERNAL), by native_decide, by native_decide, ?_, by native_decide, by native_decide, by native_decide, by native_decide, by native_decide, by native_decide⟩
  rw [show ((((⟨{ assetsTotal := ⟨false, 2434563349544987818, 0⟩, assetsAvailable := ⟨false, 2434563349544987818, 0⟩, assetsReserved := Number.zero, assetsMaximum := none, numericType := .int64, scale := 0, sharesTotal := ⟨false, 1248538884401275250, -1⟩, lossUnrealized := Number.zero }, by native_decide, by native_decide⟩ : Vault)).withdraw (.vaultShares (STAmount.unchecked .int64 46175462685143005 (0) false)) false (by native_decide)).toOption.getD
      (WithdrawResult.rejected (⟨{ assetsTotal := ⟨false, 2434563349544987818, 0⟩, assetsAvailable := ⟨false, 2434563349544987818, 0⟩, assetsReserved := Number.zero, assetsMaximum := none, numericType := .int64, scale := 0, sharesTotal := ⟨false, 1248538884401275250, -1⟩, lossUnrealized := Number.zero }, by native_decide, by native_decide⟩ : Vault) .tecINTERNAL)).sharesBurned = (STAmount.unchecked .int64 46175462685143005 (0) false) from by native_decide]
  exact ⟨fun _ => ⟨⟨rfl, rfl, by decide⟩, by decide⟩, fun h => absurd h (by decide)⟩

lemma Vault.clawback_no_dilution_half_ulp_witness :
    ∃ (v : Vault) (assets holderShares : STAmount) (hnn : 0 ≤ assets.toRat) (r : ClawbackResult),
      v.toExact.lossUnrealized = 0 ∧ assets.Canonical ∧
      holderShares.IntegralCanonical ∧ holderShares.Canonical ∧ holderShares.negative = false ∧
      r.sharesDestroyed.toRat ≤ (v.toExact.sharesTotal : ℚ) / 2 ∧
      (v.toExact.sharesTotal : ℚ) ≤ 2 ^ 63 - 1 ∧
      v.clawback assets holderShares hnn = .ok r ∧ r.error = none ∧
      r.vault'.withdrawNav * (v.toExact.sharesTotal : ℚ) <
        v.withdrawNav * (r.vault'.toExact.sharesTotal : ℚ) * (1 - depositε) -
          (1 - 1 / 10 ^ 15) * (1 / 2 * (10 : ℚ) ^ r.assetsRecovered.exponent) *
            (v.toExact.sharesTotal : ℚ) := by
  refine ⟨(⟨{ assetsTotal := ⟨false, 3000000000000000000, -18⟩, assetsAvailable := ⟨false, 3000000000000000000, -18⟩, assetsReserved := Number.zero, assetsMaximum := none, numericType := .int64, scale := 0, sharesTotal := ⟨false, 4000000000000000000, -18⟩, lossUnrealized := Number.zero }, by native_decide, by native_decide⟩ : Vault), (STAmount.unchecked .int64 2 (0) false), (STAmount.unchecked .int64 2 (0) false), by native_decide,
    (((⟨{ assetsTotal := ⟨false, 3000000000000000000, -18⟩, assetsAvailable := ⟨false, 3000000000000000000, -18⟩, assetsReserved := Number.zero, assetsMaximum := none, numericType := .int64, scale := 0, sharesTotal := ⟨false, 4000000000000000000, -18⟩, lossUnrealized := Number.zero }, by native_decide, by native_decide⟩ : Vault)).clawback (STAmount.unchecked .int64 2 (0) false) (STAmount.unchecked .int64 2 (0) false) (by native_decide)).toOption.getD
      (ClawbackResult.rejected (⟨{ assetsTotal := ⟨false, 3000000000000000000, -18⟩, assetsAvailable := ⟨false, 3000000000000000000, -18⟩, assetsReserved := Number.zero, assetsMaximum := none, numericType := .int64, scale := 0, sharesTotal := ⟨false, 4000000000000000000, -18⟩, lossUnrealized := Number.zero }, by native_decide, by native_decide⟩ : Vault) .tecINTERNAL), by native_decide, ?_, ⟨rfl, rfl, by decide⟩, ⟨fun _ => ⟨⟨rfl, rfl, by decide⟩, by decide⟩, fun h => absurd h (by decide)⟩, rfl, by native_decide, by native_decide, by native_decide, by native_decide, by unfold depositε; native_decide⟩
  exact ⟨fun _ => ⟨⟨rfl, rfl, by decide⟩, by decide⟩, fun h => absurd h (by decide)⟩

lemma Vault.clawback_no_dilution_relative_witness :
    ∃ (v : Vault) (assets holderShares : STAmount) (hnn : 0 ≤ assets.toRat) (r : ClawbackResult),
      v.toExact.lossUnrealized = 0 ∧ assets.Canonical ∧
      holderShares.IntegralCanonical ∧ holderShares.Canonical ∧ holderShares.negative = false ∧
      r.sharesDestroyed.toRat ≤ (v.toExact.sharesTotal : ℚ) / 2 ∧
      (v.toExact.sharesTotal : ℚ) ≤ 2 ^ 63 - 1 ∧
      v.clawback assets holderShares hnn = .ok r ∧ r.error = none ∧
      r.vault'.withdrawNav * (v.toExact.sharesTotal : ℚ) <
        v.withdrawNav * (r.vault'.toExact.sharesTotal : ℚ) -
          1 / 2 * (10 : ℚ) ^ r.assetsRecovered.exponent * (v.toExact.sharesTotal : ℚ) := by
  refine ⟨(⟨{ assetsTotal := ⟨false, 3435919952742337818, 0⟩, assetsAvailable := ⟨false, 3435919952742337818, 0⟩, assetsReserved := Number.zero, assetsMaximum := none, numericType := .int64, scale := 0, sharesTotal := ⟨false, 1284661237072100040, 0⟩, lossUnrealized := Number.zero }, by native_decide, by native_decide⟩ : Vault), (STAmount.unchecked .int64 1454101939520273818 (0) false), (STAmount.unchecked .int64 543676343496335169 (0) false), by native_decide,
    (((⟨{ assetsTotal := ⟨false, 3435919952742337818, 0⟩, assetsAvailable := ⟨false, 3435919952742337818, 0⟩, assetsReserved := Number.zero, assetsMaximum := none, numericType := .int64, scale := 0, sharesTotal := ⟨false, 1284661237072100040, 0⟩, lossUnrealized := Number.zero }, by native_decide, by native_decide⟩ : Vault)).clawback (STAmount.unchecked .int64 1454101939520273818 (0) false) (STAmount.unchecked .int64 543676343496335169 (0) false) (by native_decide)).toOption.getD
      (ClawbackResult.rejected (⟨{ assetsTotal := ⟨false, 3435919952742337818, 0⟩, assetsAvailable := ⟨false, 3435919952742337818, 0⟩, assetsReserved := Number.zero, assetsMaximum := none, numericType := .int64, scale := 0, sharesTotal := ⟨false, 1284661237072100040, 0⟩, lossUnrealized := Number.zero }, by native_decide, by native_decide⟩ : Vault) .tecINTERNAL), by native_decide, ?_, ⟨rfl, rfl, by decide⟩, ⟨fun _ => ⟨⟨rfl, rfl, by decide⟩, by decide⟩, fun h => absurd h (by decide)⟩, rfl, by native_decide, by native_decide, by native_decide, by native_decide, by native_decide⟩
  exact ⟨fun _ => ⟨⟨rfl, rfl, by decide⟩, by decide⟩, fun h => absurd h (by decide)⟩

lemma Vault.clawback_no_dilution_zero_half_ulp_witness :
    ∃ (v : Vault) (assets holderShares : STAmount) (hnn : 0 ≤ assets.toRat) (r : ClawbackResult),
      v.toExact.lossUnrealized = 0 ∧ assets.Canonical ∧
      holderShares.IntegralCanonical ∧ holderShares.Canonical ∧ holderShares.negative = false ∧
      assets.isZero = true ∧ r.sharesDestroyed = holderShares ∧
      r.sharesDestroyed.toRat ≤ (v.toExact.sharesTotal : ℚ) / 2 ∧
      (v.toExact.sharesTotal : ℚ) ≤ 2 ^ 63 - 1 ∧
      v.clawback assets holderShares hnn = .ok r ∧ r.error = none ∧
      r.vault'.withdrawNav * (v.toExact.sharesTotal : ℚ) <
        v.withdrawNav * (r.vault'.toExact.sharesTotal : ℚ) * (1 - depositε) -
          (1 - 1 / 10 ^ 15) * (1 / 2 * (10 : ℚ) ^ r.assetsRecovered.exponent) *
            (v.toExact.sharesTotal : ℚ) := by
  refine ⟨(⟨{ assetsTotal := ⟨false, 3000000000000000000, -18⟩, assetsAvailable := ⟨false, 3000000000000000000, -18⟩, assetsReserved := Number.zero, assetsMaximum := none, numericType := .int64, scale := 0, sharesTotal := ⟨false, 8000000000000000000, -18⟩, lossUnrealized := Number.zero }, by native_decide, by native_decide⟩ : Vault), (STAmount.zero .int64), (STAmount.unchecked .int64 4 (0) false), by native_decide,
    (((⟨{ assetsTotal := ⟨false, 3000000000000000000, -18⟩, assetsAvailable := ⟨false, 3000000000000000000, -18⟩, assetsReserved := Number.zero, assetsMaximum := none, numericType := .int64, scale := 0, sharesTotal := ⟨false, 8000000000000000000, -18⟩, lossUnrealized := Number.zero }, by native_decide, by native_decide⟩ : Vault)).clawback (STAmount.zero .int64) (STAmount.unchecked .int64 4 (0) false) (by native_decide)).toOption.getD
      (ClawbackResult.rejected (⟨{ assetsTotal := ⟨false, 3000000000000000000, -18⟩, assetsAvailable := ⟨false, 3000000000000000000, -18⟩, assetsReserved := Number.zero, assetsMaximum := none, numericType := .int64, scale := 0, sharesTotal := ⟨false, 8000000000000000000, -18⟩, lossUnrealized := Number.zero }, by native_decide, by native_decide⟩ : Vault) .tecINTERNAL), by native_decide, ?_, ⟨rfl, rfl, by decide⟩, ⟨fun _ => ⟨⟨rfl, rfl, by decide⟩, by decide⟩, fun h => absurd h (by decide)⟩, rfl, by native_decide, by native_decide, by native_decide, by native_decide, by native_decide, by native_decide, by unfold depositε; native_decide⟩
  rw [show STAmount.zero .int64 = (STAmount.unchecked .int64 0 (0) false) from by native_decide]
  exact ⟨fun _ => ⟨⟨rfl, rfl, by decide⟩, by decide⟩, fun h => absurd h (by decide)⟩

end XRPL.Model.SingleAssetVault
