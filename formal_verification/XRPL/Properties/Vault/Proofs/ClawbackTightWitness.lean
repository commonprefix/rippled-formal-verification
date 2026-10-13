import XRPL.Model.Vault.VaultClawback
import XRPL.Properties.Approx
import XRPL.Properties.Vault.VaultValid
import XRPL.Properties.Vault.Common.ClawbackDefs
import XRPL.Properties.Vault.Common.VaultDecidable

/-! # Witnesses for the tight `Vault.clawback` accuracy bounds

Each is closed by `native_decide` over the model.

* Shares, truncation: 10¹⁵ + 0.001 assets, 2·10¹⁵ shares, claw back `1`: ideal
  `1.999999999999999998`, one share destroyed.
* Shares, relative excess: `99999999999889682.7` assets, 1844674407370955163 shares, claw back
  `5·10¹⁵`: both `.to_nearest` stages round up by almost half a step of the maxRep band,
  destroying `92233720368649508` shares, `1.0841995·10⁻¹⁸` relatively above the ideal.
* Clamped shares: 3 assets, `0.0001` available, 7·10¹⁵ shares, claw back `1`.
* Claw all: 3 assets, 7·10¹⁵ shares, holder `2333333333333333` shares: priced
  `0.9999999999999999`, reported `0.999999999999999`.
* Recovery overshoot: int64, 3 assets, 2 shares, claw back `2`: ideal `1.5` of one share, paid `2`.
* Recovery shortfall (ULP): int64, 5 assets, 2 shares, claw back `3`: ideal `2.5`, paid `2`.
* Recovery shortfall (clamp): 1000000000000002 assets, 500000000000002 shares, claw back `2`:
  ideal `1.999999999999996`, snapped to `1` on the unit grid of the remaining total. -/

set_option linter.style.nativeDecide false

namespace XRPL.Model.SingleAssetVault.ClwTight

open XRPL.Model.Protocol

def mkV (nt : NumericType) (tot av sh : Number) : RawVault :=
  { assetsTotal := tot, assetsAvailable := av, assetsReserved := Number.zero
  , assetsMaximum := none, numericType := nt, scale := 0, sharesTotal := sh
  , lossUnrealized := Number.zero }

def cbR (v : Vault) (a h : STAmount) (hnn : 0 ≤ a.toRat) : ClawbackResult :=
  (v.clawback a h hnn).toOption.getD (ClawbackResult.rejected v .tecINTERNAL)

def shT (v : Vault) (a : STAmount) : STAmount :=
  (assetsToSharesWithdraw v a true false).toOption.getD (STAmount.zero .int64)

def prT (v : Vault) (s : STAmount) : STAmount :=
  (v.sharesToAssetsWithdraw s false).toOption.getD (STAmount.zero v.numericType)

def numT (s : STAmount) : Number := (s.toNumber .to_nearest).toOption.getD Number.zero

def holder5 : STAmount := STAmount.unchecked .int64 5 0 false

def vTr : Vault := ⟨mkV .fractional ⟨false, 1000000000000000001, -3⟩ ⟨false, 1000000000000000001, -3⟩
  ⟨false, 2000000000000000000, -3⟩, by native_decide, by native_decide⟩
def aOne : STAmount := STAmount.unchecked .fractional 1000000000000000 (-15) false
lemma hOne : 0 ≤ aOne.toRat := by native_decide
lemma cOne : aOne.Canonical :=
  ⟨fun h => absurd h (by native_decide), fun _ => ⟨rfl, by native_decide, by native_decide,
    by native_decide, by native_decide⟩⟩

def vUp : Vault := ⟨mkV .fractional ⟨false, 9999999999988968270, -2⟩ ⟨false, 9999999999988968270, -2⟩
  ⟨false, 1844674407370955163, 0⟩, by native_decide, by native_decide⟩
def aUp : STAmount := STAmount.unchecked .fractional 5000000000000000 0 false
lemma hUp : 0 ≤ aUp.toRat := by native_decide
lemma cUp : aUp.Canonical :=
  ⟨fun h => absurd h (by native_decide), fun _ => ⟨rfl, by native_decide, by native_decide,
    by native_decide, by native_decide⟩⟩

def vCl : Vault := ⟨mkV .fractional ⟨false, 3000000000000000000, -18⟩ ⟨false, 1000000000000000000, -22⟩
  ⟨false, 7000000000000000000, -3⟩, by native_decide, by native_decide⟩
def aCl' : STAmount := (STAmount.ofNumber vCl.numericType vCl.assetsAvailable .to_nearest).toOption.getD
  (STAmount.zero .fractional)

def vZ : Vault := ⟨mkV .fractional ⟨false, 3000000000000000000, -18⟩ ⟨false, 3000000000000000000, -18⟩
  ⟨false, 7000000000000000000, -3⟩, by native_decide, by native_decide⟩
def hZ : STAmount := STAmount.unchecked .int64 2333333333333333 0 false
def aZ : STAmount := STAmount.zero .fractional
def repZ : STAmount := (clampToSumExponent vZ.assetsTotal (prT vZ hZ).operator_neg).toOption.getD aZ

def vOv : Vault := ⟨mkV .int64 ⟨false, 3000000000000000000, -18⟩ ⟨false, 3000000000000000000, -18⟩
  ⟨false, 2000000000000000000, -18⟩, by native_decide, by native_decide⟩
def aTwoI : STAmount := STAmount.unchecked .int64 2 0 false

def vSh : Vault := ⟨mkV .int64 ⟨false, 5000000000000000000, -18⟩ ⟨false, 5000000000000000000, -18⟩
  ⟨false, 2000000000000000000, -18⟩, by native_decide, by native_decide⟩
def aThreeI : STAmount := STAmount.unchecked .int64 3 0 false

def vGr : Vault := ⟨mkV .fractional ⟨false, 1000000000000002000, -3⟩ ⟨false, 1000000000000002000, -3⟩
  ⟨false, 5000000000000020000, -4⟩, by native_decide, by native_decide⟩
def aTwo : STAmount := STAmount.unchecked .fractional 2000000000000000 (-15) false

lemma hZ0 : 0 ≤ aZ.toRat := by native_decide
lemma hTwoI : 0 ≤ aTwoI.toRat := by native_decide
lemma hThreeI : 0 ≤ aThreeI.toRat := by native_decide
lemma hTwo : 0 ≤ aTwo.toRat := by native_decide
lemma cTwo : aTwo.Canonical :=
  ⟨fun h => absurd h (by native_decide), fun _ => ⟨rfl, by native_decide, by native_decide,
    by native_decide, by native_decide⟩⟩
lemma cInt (s : STAmount) (h1 : s.mNumericType = .int64) (h2 : s.mOffset = 0)
    (h3 : s.mValue.toNat ≤ maxRep.toNat) : s.Canonical := by
  have hi : s.integral = true := by show s.mNumericType.isIntegral = true; rw [h1]; rfl
  refine ⟨fun _ => ⟨⟨by rw [h1]; rfl, h2, by rw [h1]; exact h3⟩, by rw [h1]; decide⟩, fun h => ?_⟩
  rw [hi] at h; exact absurd h (by decide)

end XRPL.Model.SingleAssetVault.ClwTight

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol ClwTight

/-- The truncation term of `clawback_sharesDestroyed` is attained to within `3·10⁻¹⁷` of a share. -/
lemma Vault.clawback_sharesDestroyed_witness :
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
        v.idealSharesClawback assets.toRat * (1 - sharesε) - 1 + 3 * (10 : ℚ) ^ (-17 : ℤ) := by
  refine ⟨vTr, aOne, holder5, shT vTr aOne, prT vTr (shT vTr aOne), hOne,
    numT (prT vTr (shT vTr aOne)), cbR vTr aOne holder5 hOne,
    ⟨⟨false, 1000000000000000001, -3⟩, by native_decide, by native_decide⟩, cOne,
    by native_decide, by native_decide, by native_decide, by native_decide, by native_decide,
    by native_decide, by native_decide, by unfold sharesε; native_decide⟩

/-- The relative term of `clawback_sharesDestroyed` is needed above the ideal: a run destroys
`1.0841995·10⁻¹⁸` relatively more than the ideal, 98.56% of `sharesε`. -/
lemma Vault.clawback_sharesDestroyed_upper_witness :
    ∃ (v : Vault) (assets holderShares sharesDestroyed assetsRecovered : STAmount)
      (hnn : 0 ≤ assets.toRat) (assetsRecoveredNumber : Number) (r : ClawbackResult),
      v.WithdrawNavExact false ∧ assets.Canonical ∧
      assetsToSharesWithdraw v assets true false = .ok sharesDestroyed ∧
      v.sharesToAssetsWithdraw sharesDestroyed false = .ok assetsRecovered ∧
      assetsRecovered.toNumber .to_nearest = .ok assetsRecoveredNumber ∧
      assetsRecoveredNumber.operator_gt v.assetsAvailable = false ∧
      assets.isZero = false ∧
      v.clawback assets holderShares hnn = .ok r ∧ r.error = none ∧
      v.idealSharesClawback assets.toRat * (1 + 10841995 / 10 ^ 25) < r.sharesDestroyed.toRat := by
  refine ⟨vUp, aUp, holder5, shT vUp aUp, prT vUp (shT vUp aUp), hUp,
    numT (prT vUp (shT vUp aUp)), cbR vUp aUp holder5 hUp,
    ⟨⟨false, 9999999999988968270, -2⟩, by native_decide, by native_decide⟩, cUp,
    by native_decide, by native_decide, by native_decide, by native_decide, by native_decide,
    by native_decide, by native_decide, by native_decide⟩

/-- Refreshed witness of `clawback_sharesDestroyed_clamped_attained` (truncating first
exchange): a run that reprices from `assetsAvailable` misses the ideal by more than the
relative budget. -/
lemma Vault.clawback_sharesDestroyed_clamped_witness :
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
        (v.idealSharesClawback assetsRecovered'.toRat) depositε := by
  refine ⟨vCl, aOne, holder5, shT vCl aOne, prT vCl (shT vCl aOne), aCl', hOne,
    numT (prT vCl (shT vCl aOne)), cbR vCl aOne holder5 hOne,
    ⟨⟨false, 3000000000000000000, -18⟩, by native_decide, by native_decide⟩,
    by native_decide, by native_decide, by native_decide, by native_decide, by native_decide,
    by native_decide, by native_decide, by unfold RoundsWithinWitness depositε; native_decide⟩

/-- `clawback_zero_all_shares` must name the clamped amount: a claw-all run records a
recovery different from the priced one. -/
lemma Vault.clawback_zero_all_shares_witness :
    ∃ (v : Vault) (assets holderShares assetsRecovered reported : STAmount)
      (hnn : 0 ≤ assets.toRat) (assetsRecoveredNumber : Number) (r : ClawbackResult),
      assets.isZero = true ∧
      v.sharesToAssetsWithdraw holderShares false = .ok assetsRecovered ∧
      assetsRecovered.toNumber .to_nearest = .ok assetsRecoveredNumber ∧
      assetsRecoveredNumber.operator_gt v.assetsAvailable = false ∧
      clampToSumExponent v.assetsTotal assetsRecovered.operator_neg = .ok reported ∧
      v.clawback assets holderShares hnn = .ok r ∧ r.error = none ∧
      r.assetsRecovered.toRat < assetsRecovered.toRat := by
  refine ⟨vZ, aZ, hZ, prT vZ hZ, repZ, hZ0, numT (prT vZ hZ), cbR vZ aZ hZ hZ0,
    by native_decide, by native_decide, by native_decide, by native_decide, by native_decide,
    by native_decide, by native_decide, by native_decide⟩

/-- The half-ULP term of the upper `clawback_assetsRecovered` bound is attained to within
`10⁻¹⁶`: an int64 run pays `2` for an ideal worth `1.5`. -/
lemma Vault.clawback_assetsRecovered_upper_witness :
    ∃ (v : Vault) (assets holderShares : STAmount) (hnn : 0 ≤ assets.toRat) (r : ClawbackResult),
      v.WithdrawNavExact false ∧ assets.Canonical ∧ assets.isZero = false ∧
      v.clawback assets holderShares hnn = .ok r ∧ r.error = none ∧
      v.idealAssetsClawback r.sharesDestroyed.toRat * (1 + depositε) +
          1 / 2 * (10 : ℚ) ^ r.assetsRecovered.exponent - (10 : ℚ) ^ (-16 : ℤ) <
        r.assetsRecovered.toRat := by
  refine ⟨vOv, aTwoI, holder5, hTwoI, cbR vOv aTwoI holder5 hTwoI,
    ⟨⟨false, 3000000000000000000, -18⟩, by native_decide, by native_decide⟩,
    cInt _ rfl rfl (by native_decide), by native_decide, by native_decide, by native_decide,
    by unfold depositε; native_decide⟩

/-- The half-ULP arm of the lower `clawback_assetsRecovered` bound is attained to within
`10⁻¹⁶`: an int64 run pays `2` for an ideal worth `2.5`. -/
lemma Vault.clawback_assetsRecovered_ulp_witness :
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
          v.idealAssetsClawback r.sharesDestroyed.toRat - r.assetsRecovered.toRat := by
  refine ⟨vSh, aThreeI, holder5, hThreeI, cbR vSh aThreeI holder5 hThreeI,
    ⟨⟨false, 5000000000000000000, -18⟩, by native_decide, by native_decide⟩,
    cInt _ rfl rfl (by native_decide), by native_decide, by native_decide, by native_decide,
    by native_decide, STAmount.unchecked .int64 3 0 false, by native_decide,
    by unfold depositε; native_decide⟩

/-- The grid arm of the lower `clawback_assetsRecovered` bound is attained to within
`10⁻¹⁴`, and the half-ULP arm alone does not cover the run: a fractional run is snapped
from `1.999999999999996` down to `1` on the unit grid of the remaining total. -/
lemma Vault.clawback_assetsRecovered_clamp_witness :
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
          v.idealAssetsClawback r.sharesDestroyed.toRat - r.assetsRecovered.toRat := by
  refine ⟨vGr, aTwo, holder5, hTwo, cbR vGr aTwo holder5 hTwo,
    ⟨⟨false, 1000000000000002000, -3⟩, by native_decide, by native_decide⟩,
    cTwo, by native_decide, by native_decide, by native_decide,
    by native_decide, by unfold depositε; native_decide,
    STAmount.unchecked .fractional 1000000000000001 0 false, by native_decide,
    by unfold depositε; native_decide⟩

end XRPL.Model.SingleAssetVault
