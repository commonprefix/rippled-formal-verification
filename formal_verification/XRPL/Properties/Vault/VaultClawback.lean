import XRPL.Properties.Vault.Defs
import XRPL.Properties.Vault.VaultValid
import XRPL.Model.Vault.VaultClawback
import XRPL.Properties.Approx
import XRPL.Properties.Vault.Common.ClawbackDefs
import XRPL.Properties.Vault.Proofs.Ideal
import XRPL.Properties.Vault.Proofs.ClawbackAccuracy
import XRPL.Properties.Vault.Proofs.ExactUpdates
import XRPL.Properties.Vault.Proofs.ClawbackTight
import XRPL.Properties.Vault.Proofs.ClawbackTightWitness

/-! # `Vault.clawback` accuracy

The relative error budget reuses `depositε`: every clawback conversion chains
at most five correctly-rounded `Number` stages, each within
`10 / (2 ^ 63 + 2)`, so `10 ^ (-17)` covers every composition below, as it
does for the deposit computations. -/

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol

variable (rv : RawVault) (v : Vault)

/-- The two ideal conversions invert each other: the ideal share amount of
`assets` is worth exactly `assets`. The returned amounts differ from this
identity only by rounding. -/
theorem RawVault.idealAssetsClawback_idealSharesClawback (assets : ℚ)
    (hnav : rv.withdrawNav ≠ 0) (hsh : rv.toExact.sharesTotal ≠ 0) :
    rv.idealAssetsClawback (rv.idealSharesClawback assets) = assets :=
  RawVault.idealAssetsClawback_idealSharesClawback_proof rv assets hnav hsh


/-! ## `Vault.clawback` -/

/-- Destroyed shares are a nonnegative integer matching `idealSharesClawback` of
`assets`: at most `sharesε` relatively above, and less than one share plus `sharesε`
below (shares are truncated). The hypotheses state that the computed recovery does
not exceed `assetsAvailable`, so the shares are priced from `assets` directly. -/
theorem Vault.clawback_sharesDestroyed (v : Vault)
    (assets holderShares sharesDestroyed assetsRecovered : STAmount)
    (assetsRecoveredNumber : Number) (r : ClawbackResult)
    (hnav : v.WithdrawNavExact false)
    (hc : assets.Canonical)
    (hshares : assetsToSharesWithdraw v assets true false = .ok sharesDestroyed)
    (hassets : v.sharesToAssetsWithdraw sharesDestroyed false = .ok assetsRecovered)
    (hnum : assetsRecovered.toNumber .to_nearest = .ok assetsRecoveredNumber)
    (hle : assetsRecoveredNumber.operator_gt v.assetsAvailable = false)
    (hznz : assets.isZero = false)
    (hnn : 0 ≤ assets.toRat)
    (hok : v.clawback assets holderShares hnn = .ok r) (herr : r.error = none) :
    r.sharesDestroyed.toRat.den = 1 ∧ 0 ≤ r.sharesDestroyed.toRat ∧
    v.idealSharesClawback assets.toRat * (1 - sharesε) - 1 < r.sharesDestroyed.toRat ∧
    r.sharesDestroyed.toRat ≤ v.idealSharesClawback assets.toRat * (1 + sharesε) :=
  Vault.clawback_sharesDestroyed_proof v assets holderShares sharesDestroyed assetsRecovered
    assetsRecoveredNumber r hnav hc hshares hassets hnum hle hznz hnn hok herr

/-- Witness for the one-share truncation term of `clawback_sharesDestroyed`: a run
destroys fewer shares than the ideal less the relative term less `1 - 3·10⁻¹⁷`, so the
truncation term is attained to within `3·10⁻¹⁷` of a share. -/
theorem Vault.clawback_sharesDestroyed_truncation_attained :
    ∃ (v : Vault) (assets holderShares sharesDestroyed assetsRecovered : STAmount)
      (hnn : 0 ≤ assets.toRat) (assetsRecoveredNumber : Number) (r : ClawbackResult),
      v.WithdrawNavExact false ∧ assets.Canonical ∧
      assetsToSharesWithdraw v assets true false = .ok sharesDestroyed ∧
      v.sharesToAssetsWithdraw sharesDestroyed false = .ok assetsRecovered ∧
      assetsRecovered.toNumber .to_nearest = .ok assetsRecoveredNumber ∧
      assetsRecoveredNumber.operator_gt v.assetsAvailable = false ∧
      assets.isZero = false ∧
      v.clawback assets holderShares hnn = .ok r ∧ r.error = none ∧
      r.sharesDestroyed.toRat <
        v.idealSharesClawback assets.toRat * (1 - sharesε) - 1 + 3 * (10 : ℚ) ^ (-17 : ℤ) :=
  Vault.clawback_sharesDestroyed_witness

/-- Witness for the relative `sharesε` term of `clawback_sharesDestroyed`: a run destroys
`1.0841995·10⁻¹⁸` relatively more than the ideal, `98.56%` of `sharesε = 1.1·10⁻¹⁸`. -/
theorem Vault.clawback_sharesDestroyed_relative_attained :
    ∃ (v : Vault) (assets holderShares sharesDestroyed assetsRecovered : STAmount)
      (hnn : 0 ≤ assets.toRat) (assetsRecoveredNumber : Number) (r : ClawbackResult),
      v.WithdrawNavExact false ∧ assets.Canonical ∧
      assetsToSharesWithdraw v assets true false = .ok sharesDestroyed ∧
      v.sharesToAssetsWithdraw sharesDestroyed false = .ok assetsRecovered ∧
      assetsRecovered.toNumber .to_nearest = .ok assetsRecoveredNumber ∧
      assetsRecoveredNumber.operator_gt v.assetsAvailable = false ∧
      assets.isZero = false ∧
      v.clawback assets holderShares hnn = .ok r ∧ r.error = none ∧
      v.idealSharesClawback assets.toRat * (1 + 10841995 / 10 ^ 25) < r.sharesDestroyed.toRat :=
  Vault.clawback_sharesDestroyed_upper_witness

/-- When the first recovery exceeds `assetsAvailable`, the run reprices from
`assetsAvailable`: destroyed shares match `idealSharesClawback` of the clamped
recovery `assetsRecovered'` within `depositε` relatively above, and less than one
share plus `depositε` below. -/
theorem Vault.clawback_sharesDestroyed_clamped (v : Vault)
    (assets holderShares sharesDestroyed assetsRecovered assetsRecovered' : STAmount)
    (assetsRecoveredNumber : Number) (r : ClawbackResult)
    (hnav : v.WithdrawNavExact false)
    (hshares : assetsToSharesWithdraw v assets true false = .ok sharesDestroyed)
    (hassets : v.sharesToAssetsWithdraw sharesDestroyed false = .ok assetsRecovered)
    (hnum : assetsRecovered.toNumber .to_nearest = .ok assetsRecoveredNumber)
    (hgt : assetsRecoveredNumber.operator_gt v.assetsAvailable = true)
    (hclamped : STAmount.ofNumber v.numericType v.assetsAvailable .to_nearest =
      .ok assetsRecovered')
    (hznz : assets.isZero = false)
    (hnn : 0 ≤ assets.toRat)
    (hok : v.clawback assets holderShares hnn = .ok r) (herr : r.error = none) :
    r.sharesDestroyed.toRat.den = 1 ∧ 0 ≤ r.sharesDestroyed.toRat ∧
    v.idealSharesClawback assetsRecovered'.toRat * (1 - depositε) - 1 <
      r.sharesDestroyed.toRat ∧
    r.sharesDestroyed.toRat ≤
      v.idealSharesClawback assetsRecovered'.toRat * (1 + depositε) :=
  Vault.clawback_sharesDestroyed_clamped_proof v assets holderShares sharesDestroyed assetsRecovered
    assetsRecovered' assetsRecoveredNumber r hnav hshares hassets hnum hgt hclamped hznz hnn hok
    herr

/-- Witness: the truncation term in `clawback_sharesDestroyed_clamped` cannot
be dropped, a run that recomputes from `assetsAvailable` exists whose share
error exceeds the relative `depositε` bound alone. -/
theorem Vault.clawback_sharesDestroyed_clamped_attained :
    ∃ (v : Vault) (assets holderShares sharesDestroyed assetsRecovered assetsRecovered' : STAmount)
      (hnn : 0 ≤ assets.toRat) (assetsRecoveredNumber : Number) (r : ClawbackResult),
      v.WithdrawNavExact false ∧
      assetsToSharesWithdraw v assets true false = .ok sharesDestroyed ∧
      v.sharesToAssetsWithdraw sharesDestroyed false = .ok assetsRecovered ∧
      assetsRecovered.toNumber .to_nearest = .ok assetsRecoveredNumber ∧
      assetsRecoveredNumber.operator_gt v.assetsAvailable = true ∧
      STAmount.ofNumber v.numericType v.assetsAvailable .to_nearest = .ok assetsRecovered' ∧
      v.clawback assets holderShares hnn = .ok r ∧ r.error = none ∧
      RoundsWithinWitness r.sharesDestroyed
        (v.idealSharesClawback assetsRecovered'.toRat) depositε :=
  Vault.clawback_sharesDestroyed_clamped_witness

/-- A zero clawback amount claws back the holder's entire share balance: exactly
`holderShares` are destroyed, and the recorded recovery is the priced recovery
snapped to the grid of the post-clawback total (`reported`). -/
theorem Vault.clawback_zero_all_shares (v : Vault)
    (assets holderShares assetsRecovered reported : STAmount)
    (assetsRecoveredNumber : Number) (r : ClawbackResult)
    (hz : assets.isZero = true)
    (hassets : v.sharesToAssetsWithdraw holderShares false = .ok assetsRecovered)
    (hnum : assetsRecovered.toNumber .to_nearest = .ok assetsRecoveredNumber)
    (hle : assetsRecoveredNumber.operator_gt v.assetsAvailable = false)
    (hclamp : clampToSumExponent v.assetsTotal assetsRecovered.operator_neg = .ok reported)
    (hnn : 0 ≤ assets.toRat)
    (hok : v.clawback assets holderShares hnn = .ok r) (herr : r.error = none) :
    r.sharesDestroyed = holderShares ∧ r.assetsRecovered = reported ∧
    holderShares.isZero = false :=
  Vault.clawback_zero_all_shares_proof v assets holderShares assetsRecovered reported
    assetsRecoveredNumber r hz hassets hnum hle hclamp hnn hok herr

/-- The recovery never exceeds `assetsAvailable`, is nonnegative, exceeds the
destroyed shares' worth by at most the stage error plus half a ULP, and falls short
of it by at most the stage error plus the larger of half a ULP of the recovery and one
step of the post-clawback total's grid less half a ULP. A recovery that underflows to
zero only happens on an integral vault, whose ideal is then at most one half. -/
theorem Vault.clawback_assetsRecovered (v : Vault) (assets holderShares : STAmount)
    (r : ClawbackResult)
    (hnav : v.WithdrawNavExact false)
    (hc : assets.Canonical)
    (hznz : assets.isZero = false)
    (hnn : 0 ≤ assets.toRat)
    (hok : v.clawback assets holderShares hnn = .ok r) (herr : r.error = none) :
    r.assetsRecovered.toRat ≤ v.toExact.assetsAvailable ∧
    0 ≤ r.assetsRecovered.toRat ∧
    r.assetsRecovered.toRat ≤
      v.idealAssetsClawback r.sharesDestroyed.toRat * (1 + depositε) +
        1 / 2 * (10 : ℚ) ^ r.assetsRecovered.exponent ∧
    (∃ atr' : STAmount,
      STAmount.ofNumber v.numericType r.vault'.assetsTotal .to_nearest = .ok atr' ∧
      v.idealAssetsClawback r.sharesDestroyed.toRat - r.assetsRecovered.toRat ≤
        v.idealAssetsClawback r.sharesDestroyed.toRat * depositε +
          max (1 / 2 * (10 : ℚ) ^ r.assetsRecovered.exponent)
            ((10 : ℚ) ^ atr'.exponent - 1 / 2 * (10 : ℚ) ^ r.assetsRecovered.exponent)) ∧
    (r.assetsRecovered.isZero = true →
      v.numericType.isIntegral = true ∧
        v.idealAssetsClawback r.sharesDestroyed.toRat * (1 - depositε) ≤ 1 / 2) :=
  Vault.clawback_assetsRecovered_proof v assets holderShares r hnav hc hznz hnn hok herr

/-- Witness for the upper half-ULP term of `clawback_assetsRecovered`: a run's recovery
exceeds the destroyed shares' worth plus the relative term by the half-ULP term less
`10⁻¹⁶` (`2` for an ideal `1.5` on an int64 vault). -/
theorem Vault.clawback_assetsRecovered_overshoot_attained :
    ∃ (v : Vault) (assets holderShares : STAmount) (hnn : 0 ≤ assets.toRat) (r : ClawbackResult),
      v.WithdrawNavExact false ∧ assets.Canonical ∧ assets.isZero = false ∧
      v.clawback assets holderShares hnn = .ok r ∧ r.error = none ∧
      v.idealAssetsClawback r.sharesDestroyed.toRat * (1 + depositε) +
          1 / 2 * (10 : ℚ) ^ r.assetsRecovered.exponent - (10 : ℚ) ^ (-16 : ℤ) <
        r.assetsRecovered.toRat :=
  Vault.clawback_assetsRecovered_upper_witness

/-- Witness for the half-ULP arm of the lower `clawback_assetsRecovered` bound: a run's
recovery falls short of the destroyed shares' worth by the relative term plus the `max`
term less `10⁻¹⁶` (`2` for an ideal `2.5` on an int64 vault). -/
theorem Vault.clawback_assetsRecovered_round_attained :
    ∃ (v : Vault) (assets holderShares : STAmount) (hnn : 0 ≤ assets.toRat) (r : ClawbackResult),
      v.WithdrawNavExact false ∧ assets.Canonical ∧ assets.isZero = false ∧
      v.clawback assets holderShares hnn = .ok r ∧ r.error = none ∧
      r.assetsRecovered.isZero = false ∧
      ∃ atr' : STAmount,
        STAmount.ofNumber v.numericType r.vault'.assetsTotal .to_nearest = .ok atr' ∧
        v.idealAssetsClawback r.sharesDestroyed.toRat * depositε +
            max (1 / 2 * (10 : ℚ) ^ r.assetsRecovered.exponent)
              ((10 : ℚ) ^ atr'.exponent - 1 / 2 * (10 : ℚ) ^ r.assetsRecovered.exponent) -
            (10 : ℚ) ^ (-16 : ℤ) <
          v.idealAssetsClawback r.sharesDestroyed.toRat - r.assetsRecovered.toRat :=
  Vault.clawback_assetsRecovered_ulp_witness

/-- Witness for the grid-clamp arm of the lower `clawback_assetsRecovered` bound: a run
snapped from `1.999999999999996` to `1` on the post-clawback grid overshoots the half-ULP
arm alone and reaches the `max` term to within `10⁻¹⁴`. -/
theorem Vault.clawback_assetsRecovered_clamp_attained :
    ∃ (v : Vault) (assets holderShares : STAmount) (hnn : 0 ≤ assets.toRat) (r : ClawbackResult),
      v.WithdrawNavExact false ∧ assets.Canonical ∧ assets.isZero = false ∧
      v.clawback assets holderShares hnn = .ok r ∧ r.error = none ∧
      r.assetsRecovered.isZero = false ∧
      v.idealAssetsClawback r.sharesDestroyed.toRat * depositε +
          1 / 2 * (10 : ℚ) ^ r.assetsRecovered.exponent <
        v.idealAssetsClawback r.sharesDestroyed.toRat - r.assetsRecovered.toRat ∧
      ∃ atr' : STAmount,
        STAmount.ofNumber v.numericType r.vault'.assetsTotal .to_nearest = .ok atr' ∧
        v.idealAssetsClawback r.sharesDestroyed.toRat * depositε +
            max (1 / 2 * (10 : ℚ) ^ r.assetsRecovered.exponent)
              ((10 : ℚ) ^ atr'.exponent - 1 / 2 * (10 : ℚ) ^ r.assetsRecovered.exponent) -
            (10 : ℚ) ^ (-14 : ℤ) <
          v.idealAssetsClawback r.sharesDestroyed.toRat - r.assetsRecovered.toRat :=
  Vault.clawback_assetsRecovered_clamp_witness

/-- Integral strengthening of `clawback_assetsRecovered`: the shortfall
stays below one whole unit plus the stage error. -/
theorem Vault.clawback_assetsRecovered_integral (v : Vault) (assets holderShares : STAmount)
    (r : ClawbackResult)
    -- the starting vault is lawful
    -- the subtraction computing assetsTotal minus lossUnrealized
    -- does not round (automatic when loss is zero)
    (hnav : v.WithdrawNavExact false)
    (hint : v.numericType.isIntegral = true) -- the vault holds an integral asset
    -- the clawed-back amount is stored canonically, so `assets.toNumber` is exact
    (hc : assets.Canonical)
    -- zero amount claws all holder shares
    (hznz : assets.isZero = false)
    (hnn : 0 ≤ assets.toRat)
    (hok : v.clawback assets holderShares hnn = .ok r) (herr : r.error = none) :
    v.idealAssetsClawback r.sharesDestroyed.toRat - r.assetsRecovered.toRat ≤
      1 + v.idealAssetsClawback r.sharesDestroyed.toRat * depositε :=
  Vault.clawback_assetsRecovered_integral_proof v assets holderShares r hnav hint hc hznz
    hnn hok herr

/-- The stored total and available assets each drop by exactly the recorded recovery
(the grid clamp puts it on the grid of the new total, so the subtraction is exact), and
the share total drops by exactly the destroyed shares whenever the difference stays in
the share domain. -/
theorem Vault.clawback_vault_updates (v : Vault) (assets holderShares : STAmount) (r : ClawbackResult)
    -- the starting vault is lawful
    -- the clawed-back amount is stored canonically, so `assets.toNumber` is exact
    (hc : assets.Canonical)
    -- zero amount claws all holder shares
    (hznz : assets.isZero = false)
    (hnn : 0 ≤ assets.toRat)
    (hok : v.clawback assets holderShares hnn = .ok r) (herr : r.error = none) :
    r.vault'.assetsTotal.toRat = v.toExact.assetsTotal - r.assetsRecovered.toRat ∧
    r.vault'.assetsAvailable.toRat = v.toExact.assetsAvailable - r.assetsRecovered.toRat ∧
    (r.sharesDestroyed.toRat ≤ (v.toExact.sharesTotal : ℚ) ∧
        (v.toExact.sharesTotal : ℚ) ≤ 2 ^ 63 - 1 →
      (r.vault'.toExact.sharesTotal : ℚ) =
        (v.toExact.sharesTotal : ℚ) - r.sharesDestroyed.toRat) :=
  Vault.clawback_vault_updates_proof v assets holderShares r hc hznz hnn hok herr

/-- Integral strengthening of `clawback_vault_updates`: in-domain integer
differences are stored exactly. -/
theorem Vault.clawback_vault_updates_integral (v : Vault) (assets holderShares : STAmount) (r : ClawbackResult)
    -- the starting vault is lawful
    (hint : v.numericType.isIntegral = true) -- the vault holds an integral asset
    -- zero amount claws all holder shares
    (hznz : assets.isZero = false)
    (hnnA : 0 ≤ assets.toRat)
    (hok : v.clawback assets holderShares hnnA = .ok r) (herr : r.error = none)
    (hnn : 0 ≤ r.assetsRecovered.toRat) -- a nonnegative recovery, negative ones can leave the domain
    -- the stored total fits the asset domain (int64)
    (hsz : v.toExact.assetsTotal ≤ 2 ^ 63 - 1) :
    r.vault'.assetsTotal.toRat = v.toExact.assetsTotal - r.assetsRecovered.toRat ∧
    r.vault'.assetsAvailable.toRat = v.toExact.assetsAvailable - r.assetsRecovered.toRat :=
  Vault.clawback_vault_updates_integral_proof v assets holderShares r hint hznz hnnA hok herr hnn hsz

end XRPL.Model.SingleAssetVault
