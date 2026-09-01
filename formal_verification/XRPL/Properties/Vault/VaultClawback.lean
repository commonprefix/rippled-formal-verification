import XRPL.Properties.Vault.Defs
import XRPL.Properties.Vault.LawfulVaultValid
import XRPL.Model.Vault.VaultClawback
import XRPL.Properties.Vault.VaultWithdraw
import XRPL.Properties.Approx
import XRPL.Properties.Vault.Common.ClawbackDefs
import XRPL.Properties.Vault.Common.ClawbackReduction
import XRPL.Properties.Vault.Common.ClawbackAccuracy
import XRPL.Properties.Vault.Common.ClawbackWitness

/-! # `LawfulVault.clawback` accuracy

The relative error budget reuses `depositε`: every clawback conversion chains
at most five correctly-rounded `Number` stages, each within
`10 / (2 ^ 63 + 2)`, so `10 ^ (-17)` covers every composition below, as it
does for the deposit computations. -/

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol

variable (v : RawVault) (lv : LawfulVault)

/-- The two ideal conversions invert each other: the ideal share amount of
`assets` is worth exactly `assets`. The returned amounts differ from this
identity only by rounding. -/
theorem RawVault.idealAssetsClawback_idealSharesClawback (assets : ℚ)
    (hnav : v.withdrawNav ≠ 0) (hsh : v.toExact.sharesTotal ≠ 0) :
    v.idealAssetsClawback (v.idealSharesClawback assets) = assets :=
  RawVault.idealAssetsClawback_idealSharesClawback_proof v assets hnav hsh


/-! ## `LawfulVault.clawback` -/

/-- Destroyed shares are a nonnegative integer matching `idealSharesClawback`
of `assets` up to the `Number` stage error plus the final rounding to a whole
share. The hypotheses state that the computed recovery does not exceed
`assetsAvailable`, so the shares are priced from `assets` directly. -/
theorem LawfulVault.clawback_sharesDestroyed (lv : LawfulVault)
    (assets holderShares sharesDestroyed assetsRecovered : STAmount)
    (assetsRecoveredNumber : Number) (r : ClawbackResult)
    -- the starting vault is lawful
    -- the subtraction computing assetsTotal minus lossUnrealized
    -- does not round (automatic when loss is zero)
    (hnav : lv.WithdrawNavExact false)
    -- the clawed-back amount is stored canonically, so `assets.toNumber` is exact
    -- (a non-canonical input rounds ~5e-16 and the bound below would be false)
    (hc : assets.Canonical)
    -- the exchange computation
    (hshares : assetsToSharesWithdraw lv assets false false = .ok sharesDestroyed)
    (hassets : lv.sharesToAssetsWithdraw sharesDestroyed false = .ok assetsRecovered)
    (hnum : assetsRecovered.toNumber .to_nearest = .ok assetsRecoveredNumber)
    -- the computed recovery does not exceed assetsAvailable
    (hle : assetsRecoveredNumber.operator_gt lv.assetsAvailable = false)
    -- zero amount claws all holder shares
    (hznz : assets.isZero = false)
    -- the clawback succeeds
    (hok : lv.clawback assets holderShares = .ok r) (herr : r.error = none) :
    r.sharesDestroyed.toRat.den = 1 ∧ 0 ≤ r.sharesDestroyed.toRat ∧
    |r.sharesDestroyed.toRat - lv.idealSharesClawback assets.toRat| ≤
      lv.idealSharesClawback assets.toRat * depositε + 1 / 2 :=
  LawfulVault.clawback_sharesDestroyed_proof lv assets holderShares sharesDestroyed assetsRecovered
    assetsRecoveredNumber r hnav hc hshares hassets hnum hle hznz hok herr

/-- Witness: the half-share term in `clawback_sharesDestroyed` cannot be
dropped, a run exists whose share error exceeds the relative `depositε`
bound alone. -/
theorem LawfulVault.clawback_sharesDestroyed_attained :
    ∃ (lv : LawfulVault) (assets holderShares sharesDestroyed assetsRecovered : STAmount)
      (assetsRecoveredNumber : Number) (r : ClawbackResult),
      lv.WithdrawNavExact false ∧
      assetsToSharesWithdraw lv assets false false = .ok sharesDestroyed ∧
      lv.sharesToAssetsWithdraw sharesDestroyed false = .ok assetsRecovered ∧
      assetsRecovered.toNumber .to_nearest = .ok assetsRecoveredNumber ∧
      assetsRecoveredNumber.operator_gt lv.assetsAvailable = false ∧
      lv.clawback assets holderShares = .ok r ∧ r.error = none ∧
      RoundsWithinWitness r.sharesDestroyed
        (lv.idealSharesClawback assets.toRat) depositε :=
  LawfulVault.clawback_sharesDestroyed_witness

/-- The computed recovery exceeds `assetsAvailable`, so the run prices the
shares from `assetsAvailable` instead: the destroyed shares are the truncated
share value of `assetsRecovered'`, at most `depositε` relatively above
`idealSharesClawback assetsRecovered'.toRat` and less than one whole share
plus `depositε` below it. -/
theorem LawfulVault.clawback_sharesDestroyed_clamped (lv : LawfulVault)
    (assets holderShares sharesDestroyed assetsRecovered assetsRecovered' : STAmount)
    (assetsRecoveredNumber : Number) (r : ClawbackResult)
    -- the starting vault is lawful
    -- the subtraction computing assetsTotal minus lossUnrealized
    -- does not round (automatic when loss is zero)
    (hnav : lv.WithdrawNavExact false)
    -- the first exchange computation
    (hshares : assetsToSharesWithdraw lv assets false false = .ok sharesDestroyed)
    (hassets : lv.sharesToAssetsWithdraw sharesDestroyed false = .ok assetsRecovered)
    (hnum : assetsRecovered.toNumber .to_nearest = .ok assetsRecoveredNumber)
    -- the computed recovery exceeds assetsAvailable, the run recomputes
    (hgt : assetsRecoveredNumber.operator_gt lv.assetsAvailable = true)
    -- the amount the recomputation prices from
    (hclamped : STAmount.ofNumber lv.numericType lv.assetsAvailable .to_nearest =
      .ok assetsRecovered')
    -- zero amount claws all holder shares
    (hznz : assets.isZero = false)
    -- the clawback succeeds
    (hok : lv.clawback assets holderShares = .ok r) (herr : r.error = none) :
    r.sharesDestroyed.toRat.den = 1 ∧ 0 ≤ r.sharesDestroyed.toRat ∧
    lv.idealSharesClawback assetsRecovered'.toRat * (1 - depositε) - 1 <
      r.sharesDestroyed.toRat ∧
    r.sharesDestroyed.toRat ≤
      lv.idealSharesClawback assetsRecovered'.toRat * (1 + depositε) :=
  LawfulVault.clawback_sharesDestroyed_clamped_proof lv assets holderShares sharesDestroyed
    assetsRecovered assetsRecovered' assetsRecoveredNumber r hnav hshares hassets hnum hgt
    hclamped hznz hok herr

/-- Witness: the truncation term in `clawback_sharesDestroyed_clamped` cannot
be dropped, a run that recomputes from `assetsAvailable` exists whose share
error exceeds the relative `depositε` bound alone. -/
theorem LawfulVault.clawback_sharesDestroyed_clamped_attained :
    ∃ (lv : LawfulVault) (assets holderShares sharesDestroyed assetsRecovered assetsRecovered' : STAmount)
      (assetsRecoveredNumber : Number) (r : ClawbackResult),
      lv.WithdrawNavExact false ∧
      assetsToSharesWithdraw lv assets false false = .ok sharesDestroyed ∧
      lv.sharesToAssetsWithdraw sharesDestroyed false = .ok assetsRecovered ∧
      assetsRecovered.toNumber .to_nearest = .ok assetsRecoveredNumber ∧
      assetsRecoveredNumber.operator_gt lv.assetsAvailable = true ∧
      STAmount.ofNumber lv.numericType lv.assetsAvailable .to_nearest = .ok assetsRecovered' ∧
      lv.clawback assets holderShares = .ok r ∧ r.error = none ∧
      RoundsWithinWitness r.sharesDestroyed
        (lv.idealSharesClawback assetsRecovered'.toRat) depositε :=
  LawfulVault.clawback_sharesDestroyed_clamped_witness

/-- A zero amount claws back the holder's entire share balance: the destroyed
shares are exactly `holderShares`, with no rounding, and the clawback prices
them through the withdraw pipeline. -/
theorem LawfulVault.clawback_zero_all_shares
    (assets holderShares assetsRecovered : STAmount)
    (assetsRecoveredNumber : Number) (r : ClawbackResult)
    -- the zero amount selects the claw all branch
    (hz : assets.isZero = true)
    -- the clawback computation prices the holder's shares
    (hassets : lv.sharesToAssetsWithdraw holderShares false = .ok assetsRecovered)
    (hnum : assetsRecovered.toNumber .to_nearest = .ok assetsRecoveredNumber)
    -- the computed number does not exceed assetsAvailable
    (hle : assetsRecoveredNumber.operator_gt lv.assetsAvailable = false)
    -- the clawback succeeds
    (hok : lv.clawback assets holderShares = .ok r) (herr : r.error = none) :
    r.sharesDestroyed = holderShares ∧ r.assetsRecovered = assetsRecovered ∧
    holderShares.isZero = false :=
  LawfulVault.clawback_zero_all_shares_proof lv assets holderShares assetsRecovered
    assetsRecoveredNumber r hz hassets hnum hle hok herr

/-- Recovered assets never exceed the stored `assetsAvailable`: every
successful run passes this exact comparison, and a run whose first computed
recovery is above `assetsAvailable` recomputes from `assetsAvailable` with
truncated shares, returning `tecINTERNAL` when even the recomputed recovery
lands above. The recovered assets are nonnegative and price the destroyed
shares at `withdrawNav`: at most `depositε` relatively above
`idealAssetsClawback` of the destroyed shares. The shortfall below the ideal
splits on the payout: a nonzero payout is at most the interior stage error plus
2 ULP below the ideal; a payout that underflows to the canonical zero forces the
ideal itself below the smallest positive representable of the vault's numeric
type (one whole unit for an integral asset, `10⁻⁸¹` for a fractional one). -/
theorem LawfulVault.clawback_assetsRecovered (lv : LawfulVault) (assets holderShares : STAmount) (r : ClawbackResult)
    -- the starting vault is lawful
    -- the subtraction computing assetsTotal minus lossUnrealized
    -- does not round (automatic when loss is zero)
    (hnav : lv.WithdrawNavExact false)
    -- the clawed-back amount is stored canonically, so `assets.toNumber` is exact
    (hc : assets.Canonical)
    -- zero amount claws all holder shares
    (hznz : assets.isZero = false)
    (hok : lv.clawback assets holderShares = .ok r) (herr : r.error = none) :
    -- recovered assets never exceed the stored assetsAvailable, exactly
    r.assetsRecovered.toRat ≤ lv.toExact.assetsAvailable ∧
    0 ≤ r.assetsRecovered.toRat ∧
    -- assetsRecovered prices the destroyed shares, at most depositε relatively above
    r.assetsRecovered.toRat ≤
      lv.idealAssetsClawback r.sharesDestroyed.toRat * (1 + depositε) ∧
    -- a nonzero payout falls short of the destroyed shares' worth by at most the
    -- interior stage error plus 2 ULP (the other direction is capped by the relative
    -- conjunct above)
    (r.assetsRecovered.isZero = false →
      lv.idealAssetsClawback r.sharesDestroyed.toRat - r.assetsRecovered.toRat ≤
        lv.idealAssetsClawback r.sharesDestroyed.toRat * depositε +
          2 * (10 : ℚ) ^ r.assetsRecovered.exponent) ∧
    -- a payout that underflows to the canonical zero forces the ideal (deflated by
    -- depositε) below the smallest positive representable of the vault's numeric type:
    -- one whole unit when integral, 10⁻⁸¹ when fractional (the IOU grid minimum)
    (r.assetsRecovered.isZero = true →
      lv.idealAssetsClawback r.sharesDestroyed.toRat * (1 - depositε) <
        if lv.numericType.isIntegral then 1 else (10 : ℚ) ^ (-81 : ℤ)) :=
  LawfulVault.clawback_assetsRecovered_proof lv assets holderShares r hnav hc hznz hok herr

/-- Witness: the ULP term in `clawback_assetsRecovered` cannot be dropped, a
run exists whose recovered assets miss the exact share value by more than
`depositε` relative. -/
theorem LawfulVault.clawback_assetsRecovered_attained :
    ∃ (lv : LawfulVault) (assets holderShares : STAmount) (r : ClawbackResult),
      lv.WithdrawNavExact false ∧ lv.clawback assets holderShares = .ok r ∧
      r.error = none ∧
      RoundsWithinWitness r.assetsRecovered
        (lv.idealAssetsClawback r.sharesDestroyed.toRat) depositε :=
  LawfulVault.clawback_assetsRecovered_witness

/-- Integral strengthening of `clawback_assetsRecovered`: the shortfall
stays below one whole unit plus the stage error. -/
theorem LawfulVault.clawback_assetsRecovered_integral (lv : LawfulVault) (assets holderShares : STAmount)
    (r : ClawbackResult)
    -- the starting vault is lawful
    -- the subtraction computing assetsTotal minus lossUnrealized
    -- does not round (automatic when loss is zero)
    (hnav : lv.WithdrawNavExact false)
    (hint : lv.numericType.isIntegral = true) -- the vault holds an integral asset
    -- the clawed-back amount is stored canonically, so `assets.toNumber` is exact
    (hc : assets.Canonical)
    -- zero amount claws all holder shares
    (hznz : assets.isZero = false)
    (hok : lv.clawback assets holderShares = .ok r) (herr : r.error = none) :
    lv.idealAssetsClawback r.sharesDestroyed.toRat - r.assetsRecovered.toRat ≤
      1 + lv.idealAssetsClawback r.sharesDestroyed.toRat * depositε :=
  LawfulVault.clawback_assetsRecovered_integral_proof lv assets holderShares r hnav hint hc hznz
    hok herr

/-- All three stored fields are the old value minus the returned amount:
`assetsTotal` and `assetsAvailable` are the old value minus `assetsRecovered`
up to the `depositε` relative error of the `Number` subtraction, and the
`sharesTotal` update is exact whenever the difference stays in the share
domain. -/
theorem LawfulVault.clawback_vault_updates (lv : LawfulVault) (assets holderShares : STAmount) (r : ClawbackResult)
    -- the starting vault is lawful
    -- the subtraction computing assetsTotal minus lossUnrealized
    -- does not round (automatic when loss is zero)
    (hnav : lv.WithdrawNavExact false)
    -- the clawed-back amount is stored canonically, so `assets.toNumber` is exact
    (hc : assets.Canonical)
    -- zero amount claws all holder shares
    (hznz : assets.isZero = false)
    (hok : lv.clawback assets holderShares = .ok r) (herr : r.error = none) :
    -- assetsTotal' = assetsTotal - recovered assets, within depositε
    RoundsWithin r.vault'.assetsTotal
      (lv.toExact.assetsTotal - r.assetsRecovered.toRat) .to_nearest depositε ∧
    -- assetsAvailable' = assetsAvailable - recovered assets, within depositε
    RoundsWithin r.vault'.assetsAvailable
      (lv.toExact.assetsAvailable - r.assetsRecovered.toRat) .to_nearest depositε ∧
    -- sharesTotal' = sharesTotal - destroyed shares, exactly, whenever the
    -- difference stays in the share domain (int64)
    (r.sharesDestroyed.toRat ≤ (lv.toExact.sharesTotal : ℚ) ∧
        (lv.toExact.sharesTotal : ℚ) ≤ 2 ^ 63 - 1 →
      (r.vault'.toExact.sharesTotal : ℚ) =
        (lv.toExact.sharesTotal : ℚ) - r.sharesDestroyed.toRat) :=
  LawfulVault.clawback_vault_updates_proof lv assets holderShares r hnav hc hznz hok herr

/-- Witness: the error term in `clawback_vault_updates` cannot be dropped, a
run exists where the stored total is not the exact difference. -/
theorem LawfulVault.clawback_vault_updates_attained :
    ∃ (lv : LawfulVault) (assets holderShares : STAmount) (r : ClawbackResult),
      lv.clawback assets holderShares = .ok r ∧ r.error = none ∧
      r.vault'.assetsTotal.toRat ≠ lv.toExact.assetsTotal - r.assetsRecovered.toRat :=
  LawfulVault.clawback_vault_updates_witness

/-- Witness: the recovery from the shares round-trip is never rounded to the
vault scale, unlike a deposit request on entry. A run exists where re-rounding
the recovery `0.00009999999999985714` would change it, and the stored total
moves by the different on-ledger amount `0.000099999999999857`.
`assetsRecovered'` - the recovery re-rounded to the vault scale -/
theorem LawfulVault.clawback_applied_delta_attained :
    ∃ (lv : LawfulVault) (assets holderShares assetsRecovered' : STAmount) (r : ClawbackResult)
      (deltaTotal : Number) (deltaAmount : STAmount),
      lv.clawback assets holderShares = .ok r ∧ r.error = none ∧
      roundToVaultExponent r.assetsRecovered lv.assetsTotal = .ok assetsRecovered' ∧
      assetsRecovered'.operator_eq r.assetsRecovered = false ∧
      lv.assetsTotal.operator_sub r.vault'.assetsTotal .to_nearest = .ok deltaTotal ∧
      STAmount.ofNumber lv.numericType deltaTotal .to_nearest = .ok deltaAmount ∧
      deltaAmount.operator_eq r.assetsRecovered = false :=
  LawfulVault.clawback_applied_delta_witness

/-- Integral strengthening of `clawback_vault_updates`: in-domain integer
differences are stored exactly. -/
theorem LawfulVault.clawback_vault_updates_integral (lv : LawfulVault) (assets holderShares : STAmount) (r : ClawbackResult)
    -- the starting vault is lawful
    (hint : lv.numericType.isIntegral = true) -- the vault holds an integral asset
    -- zero amount claws all holder shares
    (hznz : assets.isZero = false)
    (hok : lv.clawback assets holderShares = .ok r) (herr : r.error = none)
    (hnn : 0 ≤ r.assetsRecovered.toRat) -- a nonnegative recovery, negative ones can leave the domain
    -- the stored total fits the asset domain (int64)
    (hsz : lv.toExact.assetsTotal ≤ 2 ^ 63 - 1) :
    r.vault'.assetsTotal.toRat = lv.toExact.assetsTotal - r.assetsRecovered.toRat ∧
    r.vault'.assetsAvailable.toRat = lv.toExact.assetsAvailable - r.assetsRecovered.toRat :=
  LawfulVault.clawback_vault_updates_integral_proof lv assets holderShares r hint hznz hok herr hnn hsz

end XRPL.Model.SingleAssetVault
