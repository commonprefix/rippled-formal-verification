import XRPL.Properties.Vault.Defs
import XRPL.Properties.Vault.VaultValid
import XRPL.Model.Vault.VaultClawback
import XRPL.Properties.Approx
import XRPL.Properties.Vault.Common.ClawbackDefs
import XRPL.Properties.Vault.Common.ReachableDefs
import XRPL.Properties.Vault.Proofs.Ideal
import XRPL.Properties.Vault.Proofs.ClawbackUpdates
import XRPL.Properties.Vault.Proofs.ClawbackTightWitness
import XRPL.Properties.Vault.Proofs.MaxValueFits
import XRPL.Properties.Vault.Proofs.ShareFloor
import XRPL.Properties.Vault.Proofs.ClawbackShareFloor

/-! # `Vault.clawback` accuracy

The relative error is `sharesε`: a clawback prices shares and assets with two
correctly-rounded `Number` stages, a `mul` and a `div`, which together stay within
`sharesε = 1.1·10⁻¹⁸` of the exact quotient. -/

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol

variable (rv : RawVault) (v : Vault)

/-- The two ideal conversions invert each other: the ideal share amount of `assets` is worth exactly
`assets`. The computed amounts differ from this only by rounding. -/
theorem RawVault.idealAssetsClawback_idealSharesClawback (waiveUnrealizedLoss : Bool) (assets : ℚ)
    (hnav : (if waiveUnrealizedLoss then rv.depositNav else rv.withdrawNav) ≠ 0)
    (hsh : rv.toExact.sharesTotal ≠ 0) :
    rv.idealAssetsClawback waiveUnrealizedLoss (rv.idealSharesClawback waiveUnrealizedLoss assets) = assets :=
  RawVault.idealAssetsClawback_idealSharesClawback_proof rv waiveUnrealizedLoss assets hnav hsh

/-- Nonzero clawed amount whose recovery fits the cash -> the shares destroyed are the ideal rounded down, never above
it and less than one share below, on a reachable vault and, at the computed net asset value, on any valid vault. -/
theorem Vault.clawback_sharesDestroyed (v : Vault)
    (assets holderShares sharesDestroyed assetsRecovered : STAmount) (waiveUnrealizedLoss : Bool)
    (assetsRecoveredNumber : Number)
    (hc : assets.Canonical) -- a clawback amount is canonical
    (hshares : assetsToSharesWithdraw v assets true waiveUnrealizedLoss = .ok sharesDestroyed)
    (hassets : v.sharesToAssetsWithdraw sharesDestroyed waiveUnrealizedLoss = .ok assetsRecovered)
    (hnum : assetsRecovered.toNumber .to_nearest = .ok assetsRecoveredNumber)
    (hle : assetsRecoveredNumber.operator_gt v.assetsAvailable = false)
    (hznz : assets.isZero = false)
    (hnn : 0 ≤ assets.toRat) (r : VaultWithAmounts)
    (hok : (v.clawback assets holderShares waiveUnrealizedLoss hnn).run = .ok (.ok r)) :
    -- on a reachable vault. The 19-digit price can cross a whole number within `sharesε` of the ideal
    (∀ t0 : UInt32, Vault.Reachable v t0 →
      (∀ n : ℤ, v.idealSharesClawback waiveUnrealizedLoss assets.toRat * sharesε <
        |v.idealSharesClawback waiveUnrealizedLoss assets.toRat - n|) →
      r.shares.toRat.den = 1 ∧ 0 ≤ r.shares.toRat ∧
      v.idealSharesClawback waiveUnrealizedLoss assets.toRat - 1 < r.shares.toRat ∧
      r.shares.toRat ≤ v.idealSharesClawback waiveUnrealizedLoss assets.toRat) ∧
    -- on any valid vault, with the gap as in the line above at the computed net asset value
    ∀ netAssetValue : Number, v.assetsTotalForWithdrawal waiveUnrealizedLoss = .ok netAssetValue →
      (∀ n : ℤ, v.idealSharesWithdrawAt netAssetValue.toRat assets.toRat * sharesε <
        |v.idealSharesWithdrawAt netAssetValue.toRat assets.toRat - n|) →
      r.shares.toRat.den = 1 ∧ 0 ≤ r.shares.toRat ∧
      v.idealSharesWithdrawAt netAssetValue.toRat assets.toRat - 1 < r.shares.toRat ∧
      r.shares.toRat ≤ v.idealSharesWithdrawAt netAssetValue.toRat assets.toRat :=
  ⟨fun t0 hr hgap => shares_floor_of_gap _ _ _ _ le_rfl sharesε_nonneg le_rfl
      (Vault.clawback_sharesDestroyed_proof v assets holderShares sharesDestroyed assetsRecovered waiveUnrealizedLoss
        assetsRecoveredNumber t0 hr hc hshares hassets hnum hle hznz hnn r hok) hgap,
    fun netAssetValue hnav hgap => shares_floor_of_gap _ _ _ _ le_rfl sharesε_nonneg le_rfl
      (Vault.clawback_sharesDestroyed_total_proof v assets holderShares sharesDestroyed assetsRecovered
        waiveUnrealizedLoss assetsRecoveredNumber netAssetValue hnav hc hshares hassets hnum hle hznz hnn r hok) hgap⟩

/-- When the recovery priced for a nonzero clawed amount exceeds the cash -> the shares destroyed are the ideal for the
cash rounded down, on a reachable vault and, at the computed net asset value, on any valid vault. -/
theorem Vault.clawback_sharesDestroyed_clamped (v : Vault)
    (assets holderShares sharesDestroyed assetsRecovered assetsRecovered' : STAmount)
    (waiveUnrealizedLoss : Bool) (assetsRecoveredNumber : Number)
    (hshares : assetsToSharesWithdraw v assets true waiveUnrealizedLoss = .ok sharesDestroyed)
    (hassets : v.sharesToAssetsWithdraw sharesDestroyed waiveUnrealizedLoss = .ok assetsRecovered)
    (hnum : assetsRecovered.toNumber .to_nearest = .ok assetsRecoveredNumber)
    (hgt : assetsRecoveredNumber.operator_gt v.assetsAvailable = true)
    (hclamped : STAmount.ofNumber v.numericType v.assetsAvailable .to_nearest =
      .ok assetsRecovered')
    (hznz : assets.isZero = false)
    (hnn : 0 ≤ assets.toRat) (r : VaultWithAmounts)
    (hok : (v.clawback assets holderShares waiveUnrealizedLoss hnn).run = .ok (.ok r)) :
    -- on a reachable vault. The lower side needs the 19-digit product of the share total and the cash to be exact
    (∀ t0 : UInt32, Vault.Reachable v t0 →
      r.shares.toRat.den = 1 ∧ 0 ≤ r.shares.toRat ∧
      ((∃ p : Number, p.isNormalized ∧ p.toRat = v.sharesTotal.toRat * assetsRecovered'.toRat) →
        v.idealSharesClawback waiveUnrealizedLoss assetsRecovered'.toRat - 1 < r.shares.toRat) ∧
      r.shares.toRat ≤ v.idealSharesClawback waiveUnrealizedLoss assetsRecovered'.toRat) ∧
    -- on any valid vault. The ideal for the cash need not be whole here, so the floor needs the gap as in
    -- `clawback_sharesDestroyed`
    ∀ netAssetValue : Number, v.assetsTotalForWithdrawal waiveUnrealizedLoss = .ok netAssetValue →
      -- the asset's maximum fits an int64 amount, as C++ caps every MPT maximum
      (v.numericType.isIntegral = true → v.numericType.maxValue.toNat ≤ maxRep.toNat) →
      (∀ n : ℤ, v.idealSharesWithdrawAt netAssetValue.toRat assetsRecovered'.toRat * sharesε <
        |v.idealSharesWithdrawAt netAssetValue.toRat assetsRecovered'.toRat - n|) →
      r.shares.toRat.den = 1 ∧ 0 ≤ r.shares.toRat ∧
      v.idealSharesWithdrawAt netAssetValue.toRat assetsRecovered'.toRat - 1 < r.shares.toRat ∧
      r.shares.toRat ≤ v.idealSharesWithdrawAt netAssetValue.toRat assetsRecovered'.toRat :=
  ⟨fun t0 hr => Vault.clawback_sharesDestroyed_clamped_floor_proof v assets holderShares sharesDestroyed
      assetsRecovered assetsRecovered' waiveUnrealizedLoss assetsRecoveredNumber t0 hr
      (Vault.Reachable.maxValue_fits v t0 hr
        (Vault.Reachable.clawback_sharesTotal_pos_of_nonzero v t0 hr assets holderShares waiveUnrealizedLoss hznz
          hnn r hok))
      hshares hassets hnum hgt hclamped hznz hnn r hok,
    fun netAssetValue hnav hmax hgap => shares_floor_of_gap _ _ _ _ le_rfl sharesε_nonneg le_rfl
      (Vault.clawback_sharesDestroyed_clamped_total_proof v assets holderShares sharesDestroyed assetsRecovered
        assetsRecovered' waiveUnrealizedLoss assetsRecoveredNumber netAssetValue hnav hmax hshares hassets hnum
        hgt hclamped hznz hnn r hok) hgap⟩

/-- A zero clawback amount whose recovery fits the cash claws back the holder's whole balance, which is nonzero:
exactly `holderShares` are destroyed, and the recovery is the priced one snapped to the grid of the cash it leaves. -/
theorem Vault.clawback_zero_all_shares (v : Vault)
    (assets holderShares assetsRecovered reported : STAmount) (waiveUnrealizedLoss : Bool)
    (assetsRecoveredNumber : Number)
    (hhs : holderShares.ShareBalance) -- the holder's balance of the vault's shares
    (hsole : waiveUnrealizedLoss = true ↔ v.IsSoleShareholder holderShares) -- only the sole holder waives
    (hz : assets.isZero = true)
    (hassets : v.sharesToAssetsWithdraw holderShares waiveUnrealizedLoss = .ok assetsRecovered)
    (hnum : assetsRecovered.toNumber .to_nearest = .ok assetsRecoveredNumber)
    (hle : assetsRecoveredNumber.operator_gt v.assetsAvailable = false)
    (hclamp : clampToSumExponent v.assetsAvailable assetsRecovered.operator_neg v.baseExponent = .ok reported)
    (hnn : 0 ≤ assets.toRat) (r : VaultWithAmounts)
    (hok : (v.clawback assets holderShares waiveUnrealizedLoss hnn).run = .ok (.ok r)) :
    r.shares = holderShares ∧ r.assets.toRat = reported.toRat ∧
    holderShares.isZero = false :=
  Vault.clawback_zero_all_shares_proof v assets holderShares assetsRecovered reported waiveUnrealizedLoss
    assetsRecoveredNumber hhs hsole hz hassets hnum hle hclamp hnn r hok

/-- Clawback -> the recovery never exceeds the cash nor the destroyed shares' worth, and for a nonzero clawed amount on
a reachable vault falls short of it by less than one base unit. -/
theorem Vault.clawback_assetsRecovered (v : Vault) (assets holderShares : STAmount)
    (waiveUnrealizedLoss : Bool) (hnn : 0 ≤ assets.toRat)
    (r : VaultWithAmounts) (hok : (v.clawback assets holderShares waiveUnrealizedLoss hnn).run = .ok (.ok r)) :
    -- on a reachable vault, a nonzero canonical amount. Priced to nearest, the upper side needs a worth of whole base
    -- units
    (∀ t0 : UInt32, Vault.Reachable v t0 →
      assets.Canonical → -- a clawback amount is canonical
      assets.isZero = false →
      r.assets.toRat ≤ v.toExact.assetsAvailable ∧
      0 ≤ r.assets.toRat ∧
      ((∃ k : ℤ, v.idealAssetsClawback waiveUnrealizedLoss r.shares.toRat = k * 10 ^ v.baseExponent) →
        r.assets.toRat ≤ v.idealAssetsClawback waiveUnrealizedLoss r.shares.toRat) ∧
      v.idealAssetsClawback waiveUnrealizedLoss r.shares.toRat - r.assets.toRat < (10 : ℚ) ^ v.baseExponent ∧
      (r.assets.isZero = true →
        v.numericType.isIntegral = true ∧
          v.idealAssetsClawback waiveUnrealizedLoss r.shares.toRat * (1 - sharesε) ≤ 1 / 2)) ∧
    -- the upper side on any valid vault, against the worth at the computed net asset value. The whole worth and the
    -- Open-limit bound as in `sharesToAssetsWithdraw_bounds`
    ∀ netAssetValue : Number, v.assetsTotalForWithdrawal waiveUnrealizedLoss = .ok netAssetValue →
      assets.CanonicalOrZero → -- a clawback amount is canonical, or zero to claw back the holding
      holderShares.ShareBalance → -- the holder's balance of the vault's shares
      -- the asset's maximum fits an int64 amount, as C++ caps every MPT maximum
      (v.numericType.isIntegral = true → v.numericType.maxValue.toNat ≤ maxRep.toNat) →
      r.assets.toRat ≤ v.toExact.assetsAvailable ∧
      0 ≤ r.assets.toRat ∧
      ((∃ k : ℤ, v.idealAssetsWithdrawAt netAssetValue.toRat r.shares.toRat = k * 10 ^ v.baseExponent) →
        v.idealAssetsWithdrawAt netAssetValue.toRat r.shares.toRat ≤ 9 * 10 ^ 15 * (10 : ℚ) ^ v.baseExponent →
        r.assets.toRat ≤ v.idealAssetsWithdrawAt netAssetValue.toRat r.shares.toRat) :=
  ⟨fun t0 hr hc hznz => Vault.clawback_assetsRecovered_intended_proof v assets holderShares waiveUnrealizedLoss t0 hr
      hc hznz hnn
      (Vault.Reachable.maxValue_fits v t0 hr
        (Vault.Reachable.clawback_sharesTotal_pos_of_nonzero v t0 hr assets holderShares waiveUnrealizedLoss hznz
          hnn r hok))
      r hok,
    fun netAssetValue hnav hc hhs hmax => Vault.clawback_assetsRecovered_intended_total_proof v assets holderShares
      waiveUnrealizedLoss netAssetValue hnav hc hhs hnn hmax r hok⟩

/-- On a reachable vault, for an integral asset and a nonzero clawed amount, the recovery falls short of the ideal
by at most half a unit. `hexact` - the 19-digit price is exact: the worth and the worth times the share total fit. -/
theorem Vault.clawback_assetsRecovered_integral (v : Vault) (assets holderShares : STAmount)
    (waiveUnrealizedLoss : Bool) (t0 : UInt32) (hr : Vault.Reachable v t0)
    (hint : v.numericType.isIntegral = true) (hznz : assets.isZero = false)
    (hc : assets.Canonical) -- a clawback amount is canonical
    (hnn : 0 ≤ assets.toRat)
    (r : VaultWithAmounts) (hok : (v.clawback assets holderShares waiveUnrealizedLoss hnn).run = .ok (.ok r))
    (hexact : (∃ q : Number, q.isNormalized ∧
        q.toRat = v.idealAssetsClawback waiveUnrealizedLoss r.shares.toRat * (v.toExact.sharesTotal : ℚ)) ∧
      ∃ q : Number, q.isNormalized ∧ q.toRat = v.idealAssetsClawback waiveUnrealizedLoss r.shares.toRat) :
    v.idealAssetsClawback waiveUnrealizedLoss r.shares.toRat - r.assets.toRat ≤ 1 / 2 :=
  Vault.clawback_assetsRecovered_integral_proof v assets holderShares waiveUnrealizedLoss t0 hr hint hznz hc hnn r hok
    hexact

/-- Witness for `clawback_sharesDestroyed`: on a reachable vault a clawback destroys one share less than the
ideal, which is whole. -/
theorem Vault.clawback_sharesDestroyed_truncation_attained :
    ∃ (v : Vault) (t0 : UInt32) (assets holderShares sharesDestroyed assetsRecovered : STAmount)
      (waiveUnrealizedLoss : Bool) (assetsRecoveredNumber : Number) (hnn : 0 ≤ assets.toRat)
      (r : VaultWithAmounts),
      Vault.Reachable v t0 ∧ assets.Canonical ∧
      assetsToSharesWithdraw v assets true waiveUnrealizedLoss = .ok sharesDestroyed ∧
      v.sharesToAssetsWithdraw sharesDestroyed waiveUnrealizedLoss = .ok assetsRecovered ∧
      assetsRecovered.toNumber .to_nearest = .ok assetsRecoveredNumber ∧
      assetsRecoveredNumber.operator_gt v.assetsAvailable = false ∧ assets.isZero = false ∧
      (v.clawback assets holderShares waiveUnrealizedLoss hnn).run = .ok (.ok r) ∧
      r.shares.toRat ≤ v.idealSharesClawback waiveUnrealizedLoss assets.toRat - 1 :=
  Vault.clawback_sharesDestroyed_witness

/-- Witness for `clawback_sharesDestroyed`: on a reachable vault a clawback destroys more shares than the
ideal, which sits just below a whole share. -/
theorem Vault.clawback_sharesDestroyed_relative_attained :
    ∃ (v : Vault) (t0 : UInt32) (assets holderShares sharesDestroyed assetsRecovered : STAmount)
      (waiveUnrealizedLoss : Bool) (assetsRecoveredNumber : Number) (hnn : 0 ≤ assets.toRat)
      (r : VaultWithAmounts),
      Vault.Reachable v t0 ∧ assets.Canonical ∧
      assetsToSharesWithdraw v assets true waiveUnrealizedLoss = .ok sharesDestroyed ∧
      v.sharesToAssetsWithdraw sharesDestroyed waiveUnrealizedLoss = .ok assetsRecovered ∧
      assetsRecovered.toNumber .to_nearest = .ok assetsRecoveredNumber ∧
      assetsRecoveredNumber.operator_gt v.assetsAvailable = false ∧ assets.isZero = false ∧
      (v.clawback assets holderShares waiveUnrealizedLoss hnn).run = .ok (.ok r) ∧
      v.idealSharesClawback waiveUnrealizedLoss assets.toRat < r.shares.toRat :=
  Vault.clawback_sharesDestroyed_upper_witness

/-- Witness for `clawback_sharesDestroyed` on any valid vault: a clawback destroys one share less than the ideal at
the computed net asset value, which is whole. -/
theorem Vault.clawback_sharesDestroyed_total_truncation_attained :
    ∃ (v : Vault) (assets holderShares sharesDestroyed assetsRecovered : STAmount)
      (waiveUnrealizedLoss : Bool) (assetsRecoveredNumber netAssetValue : Number) (hnn : 0 ≤ assets.toRat)
      (r : VaultWithAmounts),
      v.assetsTotalForWithdrawal waiveUnrealizedLoss = .ok netAssetValue ∧ assets.Canonical ∧
      assetsToSharesWithdraw v assets true waiveUnrealizedLoss = .ok sharesDestroyed ∧
      v.sharesToAssetsWithdraw sharesDestroyed waiveUnrealizedLoss = .ok assetsRecovered ∧
      assetsRecovered.toNumber .to_nearest = .ok assetsRecoveredNumber ∧
      assetsRecoveredNumber.operator_gt v.assetsAvailable = false ∧ assets.isZero = false ∧
      (v.clawback assets holderShares waiveUnrealizedLoss hnn).run = .ok (.ok r) ∧
      r.shares.toRat ≤ v.idealSharesWithdrawAt netAssetValue.toRat assets.toRat - 1 :=
  Vault.clawback_sharesDestroyed_total_witness

/-- Witness for `clawback_sharesDestroyed` on any valid vault: a clawback destroys more shares than the ideal at
the computed net asset value. -/
theorem Vault.clawback_sharesDestroyed_total_relative_attained :
    ∃ (v : Vault) (assets holderShares sharesDestroyed assetsRecovered : STAmount)
      (waiveUnrealizedLoss : Bool) (assetsRecoveredNumber netAssetValue : Number) (hnn : 0 ≤ assets.toRat)
      (r : VaultWithAmounts),
      v.assetsTotalForWithdrawal waiveUnrealizedLoss = .ok netAssetValue ∧ assets.Canonical ∧
      assetsToSharesWithdraw v assets true waiveUnrealizedLoss = .ok sharesDestroyed ∧
      v.sharesToAssetsWithdraw sharesDestroyed waiveUnrealizedLoss = .ok assetsRecovered ∧
      assetsRecovered.toNumber .to_nearest = .ok assetsRecoveredNumber ∧
      assetsRecoveredNumber.operator_gt v.assetsAvailable = false ∧ assets.isZero = false ∧
      (v.clawback assets holderShares waiveUnrealizedLoss hnn).run = .ok (.ok r) ∧
      v.idealSharesWithdrawAt netAssetValue.toRat assets.toRat < r.shares.toRat :=
  Vault.clawback_sharesDestroyed_total_upper_witness

/-- Witness for `clawback_sharesDestroyed_clamped`: on a reachable vault a recovery capped at the cash destroys
one share less than the ideal for the cash, as the share total times the cash needs 20 digits. -/
theorem Vault.clawback_sharesDestroyed_clamped_attained :
    ∃ (v : Vault) (t0 : UInt32) (assets holderShares sharesDestroyed assetsRecovered assetsRecovered' : STAmount)
      (waiveUnrealizedLoss : Bool) (assetsRecoveredNumber : Number) (hnn : 0 ≤ assets.toRat)
      (r : VaultWithAmounts),
      Vault.Reachable v t0 ∧
      assetsToSharesWithdraw v assets true waiveUnrealizedLoss = .ok sharesDestroyed ∧
      v.sharesToAssetsWithdraw sharesDestroyed waiveUnrealizedLoss = .ok assetsRecovered ∧
      assetsRecovered.toNumber .to_nearest = .ok assetsRecoveredNumber ∧
      assetsRecoveredNumber.operator_gt v.assetsAvailable = true ∧
      STAmount.ofNumber v.numericType v.assetsAvailable .to_nearest = .ok assetsRecovered' ∧
      assets.isZero = false ∧
      (v.clawback assets holderShares waiveUnrealizedLoss hnn).run = .ok (.ok r) ∧
      r.shares.toRat ≤ v.idealSharesClawback waiveUnrealizedLoss assetsRecovered'.toRat - 1 := by
  obtain ⟨v, t0, assets, holderShares, sharesDestroyed, assetsRecovered, assetsRecovered', waiveUnrealizedLoss,
    assetsRecoveredNumber, hnn, r, hr, -, hshares, hassets, hnum, hgt, hclamped, hznz, hok, heq⟩ :=
    Vault.clawback_sharesDestroyed_clamped_witness
  exact ⟨v, t0, assets, holderShares, sharesDestroyed, assetsRecovered, assetsRecovered', waiveUnrealizedLoss,
    assetsRecoveredNumber, hnn, r, hr, hshares, hassets, hnum, hgt, hclamped, hznz, hok, heq⟩

/-- Witness for `clawback_sharesDestroyed_clamped`: on a reachable vault a capped recovery destroys exactly the
ideal for the cash, all 3 shares of a vault holding 3. -/
theorem Vault.clawback_sharesDestroyed_clamped_upper_attained :
    ∃ (v : Vault) (t0 : UInt32) (assets holderShares sharesDestroyed assetsRecovered assetsRecovered' : STAmount)
      (waiveUnrealizedLoss : Bool) (assetsRecoveredNumber : Number) (hnn : 0 ≤ assets.toRat)
      (r : VaultWithAmounts),
      Vault.Reachable v t0 ∧
      assetsToSharesWithdraw v assets true waiveUnrealizedLoss = .ok sharesDestroyed ∧
      v.sharesToAssetsWithdraw sharesDestroyed waiveUnrealizedLoss = .ok assetsRecovered ∧
      assetsRecovered.toNumber .to_nearest = .ok assetsRecoveredNumber ∧
      assetsRecoveredNumber.operator_gt v.assetsAvailable = true ∧
      STAmount.ofNumber v.numericType v.assetsAvailable .to_nearest = .ok assetsRecovered' ∧
      assets.isZero = false ∧
      (v.clawback assets holderShares waiveUnrealizedLoss hnn).run = .ok (.ok r) ∧
      r.shares.toRat = v.idealSharesClawback waiveUnrealizedLoss assetsRecovered'.toRat :=
  Vault.clawback_sharesDestroyed_clamped_upper_witness

/-- Witness for `clawback_sharesDestroyed_clamped` on any valid vault: a capped recovery destroys one share less
than the ideal for the cash at the computed net asset value. -/
theorem Vault.clawback_sharesDestroyed_clamped_total_attained :
    ∃ (v : Vault) (assets holderShares sharesDestroyed assetsRecovered assetsRecovered' : STAmount)
      (waiveUnrealizedLoss : Bool) (assetsRecoveredNumber netAssetValue : Number) (hnn : 0 ≤ assets.toRat)
      (r : VaultWithAmounts),
      v.assetsTotalForWithdrawal waiveUnrealizedLoss = .ok netAssetValue ∧
      -- the asset's maximum fits an int64 amount, as C++ caps every MPT maximum
      (v.numericType.isIntegral = true → v.numericType.maxValue.toNat ≤ maxRep.toNat) ∧
      assetsToSharesWithdraw v assets true waiveUnrealizedLoss = .ok sharesDestroyed ∧
      v.sharesToAssetsWithdraw sharesDestroyed waiveUnrealizedLoss = .ok assetsRecovered ∧
      assetsRecovered.toNumber .to_nearest = .ok assetsRecoveredNumber ∧
      assetsRecoveredNumber.operator_gt v.assetsAvailable = true ∧
      STAmount.ofNumber v.numericType v.assetsAvailable .to_nearest = .ok assetsRecovered' ∧
      assets.isZero = false ∧
      (v.clawback assets holderShares waiveUnrealizedLoss hnn).run = .ok (.ok r) ∧
      r.shares.toRat ≤ v.idealSharesWithdrawAt netAssetValue.toRat assetsRecovered'.toRat - 1 :=
  Vault.clawback_sharesDestroyed_clamped_total_witness

/-- Witness for `clawback_sharesDestroyed_clamped` on any valid vault: with cash 1 and `3000000000000000002` shares a
capped recovery destroys more shares than the ideal for the cash at the computed net asset value. -/
theorem Vault.clawback_sharesDestroyed_clamped_total_relative_attained :
    ∃ (v : Vault) (assets holderShares sharesDestroyed assetsRecovered assetsRecovered' : STAmount)
      (waiveUnrealizedLoss : Bool) (assetsRecoveredNumber netAssetValue : Number) (hnn : 0 ≤ assets.toRat)
      (r : VaultWithAmounts),
      v.assetsTotalForWithdrawal waiveUnrealizedLoss = .ok netAssetValue ∧
      -- the asset's maximum fits an int64 amount, as C++ caps every MPT maximum
      (v.numericType.isIntegral = true → v.numericType.maxValue.toNat ≤ maxRep.toNat) ∧
      assetsToSharesWithdraw v assets true waiveUnrealizedLoss = .ok sharesDestroyed ∧
      v.sharesToAssetsWithdraw sharesDestroyed waiveUnrealizedLoss = .ok assetsRecovered ∧
      assetsRecovered.toNumber .to_nearest = .ok assetsRecoveredNumber ∧
      assetsRecoveredNumber.operator_gt v.assetsAvailable = true ∧
      STAmount.ofNumber v.numericType v.assetsAvailable .to_nearest = .ok assetsRecovered' ∧
      assets.isZero = false ∧
      (v.clawback assets holderShares waiveUnrealizedLoss hnn).run = .ok (.ok r) ∧
      v.idealSharesWithdrawAt netAssetValue.toRat assetsRecovered'.toRat < r.shares.toRat :=
  Vault.clawback_sharesDestroyed_clamped_total_upper_witness

/-- Witness for `clawback_assetsRecovered`: on a reachable vault a run recovers more than the destroyed shares'
worth, half a unit above it (`2` for `1.5`). -/
theorem Vault.clawback_assetsRecovered_overshoot_attained :
    ∃ (v : Vault) (t0 : UInt32) (assets holderShares : STAmount) (waiveUnrealizedLoss : Bool)
      (hnn : 0 ≤ assets.toRat) (r : VaultWithAmounts),
      Vault.Reachable v t0 ∧ assets.Canonical ∧ assets.isZero = false ∧
      (v.clawback assets holderShares waiveUnrealizedLoss hnn).run = .ok (.ok r) ∧
      v.idealAssetsClawback waiveUnrealizedLoss r.shares.toRat < r.assets.toRat := by
  obtain ⟨v, t0, assets, holderShares, waiveUnrealizedLoss, hnn, r, hr, hc, hznz, -, hok, heq⟩ :=
    Vault.clawback_assetsRecovered_upper_witness
  exact ⟨v, t0, assets, holderShares, waiveUnrealizedLoss, hnn, r, hr, hc, hznz, hok, heq⟩

/-- Witness for the lower side of `clawback_assetsRecovered`: a recovery floored onto the base grid falls short of
the shares' worth by all but `10⁻¹⁵` of a base unit. -/
theorem Vault.clawback_assetsRecovered_clamp_attained :
    ∃ (v : Vault) (t0 : UInt32) (assets holderShares : STAmount) (waiveUnrealizedLoss : Bool)
      (hnn : 0 ≤ assets.toRat) (r : VaultWithAmounts),
      Vault.Reachable v t0 ∧ assets.Canonical ∧ assets.isZero = false ∧
      (v.clawback assets holderShares waiveUnrealizedLoss hnn).run = .ok (.ok r) ∧
      v.idealAssetsClawback waiveUnrealizedLoss r.shares.toRat - r.assets.toRat =
        (1 - 1 / 10 ^ 15) * (10 : ℚ) ^ v.baseExponent := by
  obtain ⟨v, t0, assets, holderShares, waiveUnrealizedLoss, hnn, r, hr, hc, hznz, -, hok, heq⟩ :=
    Vault.clawback_assetsRecovered_clamp_witness
  exact ⟨v, t0, assets, holderShares, waiveUnrealizedLoss, hnn, r, hr, hc, hznz, hok, heq⟩

/-- Witness for `clawback_assetsRecovered` on any valid vault: a run recovers more than the worth at the computed net
asset value, half a unit above it. -/
theorem Vault.clawback_assetsRecovered_total_attained :
    ∃ (v : Vault) (assets holderShares : STAmount) (waiveUnrealizedLoss : Bool) (netAssetValue : Number)
      (hnn : 0 ≤ assets.toRat) (r : VaultWithAmounts),
      v.assetsTotalForWithdrawal waiveUnrealizedLoss = .ok netAssetValue ∧ assets.CanonicalOrZero ∧
      holderShares.ShareBalance ∧
      -- the asset's maximum fits an int64 amount, as C++ caps every MPT maximum
      (v.numericType.isIntegral = true → v.numericType.maxValue.toNat ≤ maxRep.toNat) ∧
      (v.clawback assets holderShares waiveUnrealizedLoss hnn).run = .ok (.ok r) ∧
      v.idealAssetsWithdrawAt netAssetValue.toRat r.shares.toRat ≤ 9 * 10 ^ 15 * (10 : ℚ) ^ v.baseExponent ∧
      v.idealAssetsWithdrawAt netAssetValue.toRat r.shares.toRat < r.assets.toRat :=
  Vault.clawback_assetsRecovered_total_witness

/-- Witness for `clawback_assetsRecovered_integral`: on a reachable integral vault a run recovers more than half a
unit below the destroyed shares' worth (`8341197431023684` for `8341197431023684.5040…`). -/
theorem Vault.clawback_assetsRecovered_integral_attained :
    ∃ (v : Vault) (t0 : UInt32) (assets holderShares : STAmount) (waiveUnrealizedLoss : Bool)
      (hnn : 0 ≤ assets.toRat) (r : VaultWithAmounts),
      Vault.Reachable v t0 ∧ v.numericType.isIntegral = true ∧ assets.Canonical ∧ assets.isZero = false ∧
      (v.clawback assets holderShares waiveUnrealizedLoss hnn).run = .ok (.ok r) ∧
      1 / 2 < v.idealAssetsClawback waiveUnrealizedLoss r.shares.toRat - r.assets.toRat := by
  obtain ⟨v, t0, assets, holderShares, waiveUnrealizedLoss, hnn, r, hr, hint, hc, hznz, -, hok, heq⟩ :=
    Vault.clawback_assetsRecovered_integral_witness
  exact ⟨v, t0, assets, holderShares, waiveUnrealizedLoss, hnn, r, hr, hint, hc, hznz, hok, heq⟩

end XRPL.Model.SingleAssetVault
