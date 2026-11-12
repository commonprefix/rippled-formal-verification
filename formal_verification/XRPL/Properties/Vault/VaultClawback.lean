import XRPL.Properties.Vault.Defs
import XRPL.Properties.Vault.VaultValid
import XRPL.Model.Vault.VaultClawback
import XRPL.Properties.Approx
import XRPL.Properties.Vault.Common.ClawbackDefs
import XRPL.Properties.Vault.Common.ReachableDefs
import XRPL.Properties.Vault.Proofs.ClawbackUpdates
import XRPL.Properties.Vault.Proofs.ClawbackTightWitness
import XRPL.Properties.Vault.Proofs.MaxValueFits
import XRPL.Properties.Vault.Proofs.ShareFloor
import XRPL.Properties.Vault.Proofs.ClawbackShareFloor
import XRPL.Properties.Vault.Proofs.DilutionWitness

/-! # `Vault.clawback` accuracy

The relative error is `sharesε`: a clawback prices shares and assets with two
correctly-rounded `Number` stages, a `mul` and a `div`, which together stay within
`sharesε = 1.1·10⁻¹⁸` of the exact quotient. -/

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol

variable (rv : RawVault) (v : Vault)

/-- Clawback on any lawful vault with amount ≠ 0 -> sharesDestroyed = ⌊idealShares⌋ at the computed net asset value,
for the amount, or for the cash when the amount is priced above it. -/
theorem Vault.clawback_sharesDestroyed (v : Vault) :
    (∀ (assets holderShares sharesDestroyed assetsRecovered : STAmount) (waiveUnrealizedLoss : Bool)
      (assetsRecoveredNumber netAssetValue : Number),
      assets.Canonical → -- a clawback amount is canonical
      v.assetsTotalForWithdrawal waiveUnrealizedLoss = .ok netAssetValue →
      assetsToSharesWithdraw v assets true waiveUnrealizedLoss = .ok sharesDestroyed →
      v.sharesToAssetsWithdraw sharesDestroyed waiveUnrealizedLoss = .ok assetsRecovered →
      assetsRecovered.toNumber .to_nearest = .ok assetsRecoveredNumber →
      assetsRecoveredNumber.operator_gt v.assetsAvailable = false →
      assets.isZero = false →
      ∀ (hnn : 0 ≤ assets.toRat) (r : VaultWithAmounts),
      (v.clawback assets holderShares waiveUnrealizedLoss hnn).run = .ok (.ok r) →
      -- the 19-digit price can cross a whole number within `sharesε` of the ideal
      (∀ n : ℤ, v.idealSharesWithdrawAt netAssetValue.toRat assets.toRat * sharesε <
        |v.idealSharesWithdrawAt netAssetValue.toRat assets.toRat - n|) →
      r.shares.toRat = ⌊v.idealSharesWithdrawAt netAssetValue.toRat assets.toRat⌋) ∧
    -- priced above the cash, the clawback is capped at the cash
    ∀ (assets holderShares sharesDestroyed assetsRecovered assetsRecovered' : STAmount)
      (waiveUnrealizedLoss : Bool) (assetsRecoveredNumber netAssetValue : Number),
      v.assetsTotalForWithdrawal waiveUnrealizedLoss = .ok netAssetValue →
      -- the asset's maximum fits an int64 amount, as C++ caps every MPT maximum
      (v.numericType.isIntegral = true → v.numericType.maxValue.toNat ≤ maxRep.toNat) →
      assetsToSharesWithdraw v assets true waiveUnrealizedLoss = .ok sharesDestroyed →
      v.sharesToAssetsWithdraw sharesDestroyed waiveUnrealizedLoss = .ok assetsRecovered →
      assetsRecovered.toNumber .to_nearest = .ok assetsRecoveredNumber →
      assetsRecoveredNumber.operator_gt v.assetsAvailable = true →
      STAmount.ofNumber v.numericType v.assetsAvailable .to_nearest = .ok assetsRecovered' →
      assets.isZero = false →
      ∀ (hnn : 0 ≤ assets.toRat) (r : VaultWithAmounts),
      (v.clawback assets holderShares waiveUnrealizedLoss hnn).run = .ok (.ok r) →
      -- the 19-digit price can cross a whole number within `sharesε` of the ideal
      (∀ n : ℤ, v.idealSharesWithdrawAt netAssetValue.toRat assetsRecovered'.toRat * sharesε <
        |v.idealSharesWithdrawAt netAssetValue.toRat assetsRecovered'.toRat - n|) →
      r.shares.toRat = ⌊v.idealSharesWithdrawAt netAssetValue.toRat assetsRecovered'.toRat⌋ :=
  ⟨fun assets holderShares sharesDestroyed assetsRecovered waiveUnrealizedLoss assetsRecoveredNumber netAssetValue
      hc hnav hshares hassets hnum hle hznz hnn r hok hgap =>
    let h := shares_floor_of_gap _ _ _ _ le_rfl sharesε_nonneg le_rfl
      (Vault.clawback_sharesDestroyed_total_proof v assets holderShares sharesDestroyed assetsRecovered
        waiveUnrealizedLoss assetsRecoveredNumber netAssetValue hnav hc hshares hassets hnum hle hznz hnn r hok) hgap
    shares_eq_floor _ _ h.1 h.2.2.1 h.2.2.2,
    fun assets holderShares sharesDestroyed assetsRecovered assetsRecovered' waiveUnrealizedLoss assetsRecoveredNumber
      netAssetValue hnav hmax hshares hassets hnum hgt hclamped hznz hnn r hok hgap =>
    let h := shares_floor_of_gap _ _ _ _ le_rfl sharesε_nonneg le_rfl
      (Vault.clawback_sharesDestroyed_clamped_total_proof v assets holderShares sharesDestroyed assetsRecovered
        assetsRecovered' waiveUnrealizedLoss assetsRecoveredNumber netAssetValue hnav hmax hshares hassets hnum
        hgt hclamped hznz hnn r hok) hgap
    shares_eq_floor _ _ h.1 h.2.2.1 h.2.2.2⟩

/-- Clawback on any lawful vault, with amount = 0 -> sharesDestroyed = the holder's whole balance ≠ 0, and
assetsRecovered − sharesWorth ≤ 0. -/
theorem Vault.clawback_zero_all_shares (v : Vault)
    (assets holderShares assetsRecovered reported : STAmount) (waiveUnrealizedLoss : Bool)
    (assetsRecoveredNumber : Number)
    (hhs : holderShares.ShareBalance) -- the holder's balance of the vault's shares
    (hsole : waiveUnrealizedLoss = true ↔ v.IsSoleShareholder holderShares) -- only the sole holder waives
    (hz : assets.isZero = true)
    (hassets : v.sharesToAssetsWithdraw holderShares waiveUnrealizedLoss = .ok assetsRecovered)
    (hnum : assetsRecovered.toNumber .to_nearest = .ok assetsRecoveredNumber)
    -- the holding, priced to nearest, fits AssetsAvailable
    (hle : assetsRecoveredNumber.operator_gt v.assetsAvailable = false)
    (hclamp : clampToSumExponent v.assetsAvailable assetsRecovered.operator_neg v.baseExponent = .ok reported)
    (hnn : 0 ≤ assets.toRat) (r : VaultWithAmounts)
    (hok : (v.clawback assets holderShares waiveUnrealizedLoss hnn).run = .ok (.ok r)) :
    r.shares = holderShares ∧ r.assets.toRat = reported.toRat ∧
    holderShares.isZero = false ∧
    -- the asset's maximum fits an int64 amount, as C++ caps every MPT maximum. Priced to nearest, the upper side
    -- needs a worth of whole base units, within the Open limit (FV_M2_3)
    ((v.numericType.isIntegral = true → v.numericType.maxValue.toNat ≤ maxRep.toNat) →
      ∀ netAssetValue : Number, v.assetsTotalForWithdrawal waiveUnrealizedLoss = .ok netAssetValue →
        (∃ k : ℤ, v.idealAssetsWithdrawAt netAssetValue.toRat r.shares.toRat = k * 10 ^ v.baseExponent) →
        v.idealAssetsWithdrawAt netAssetValue.toRat r.shares.toRat ≤ 9 * 10 ^ 15 * (10 : ℚ) ^ v.baseExponent →
        r.assets.toRat ≤ v.idealAssetsWithdrawAt netAssetValue.toRat r.shares.toRat) :=
  have h := Vault.clawback_zero_all_shares_proof v assets holderShares assetsRecovered reported waiveUnrealizedLoss
    assetsRecoveredNumber hhs hsole hz hassets hnum hle hclamp hnn r hok
  ⟨h.1, h.2.1, h.2.2, fun hmax netAssetValue hnav hk hlim =>
    (Vault.clawback_assetsRecovered_intended_total_proof v assets holderShares waiveUnrealizedLoss netAssetValue hnav
      (Or.inr hz) hhs hnn hmax r hok).2.2 hk hlim⟩

/-- Witness: a run where a clawback with amount = 0 recovers more than sharesWorth. A one-share holding worth `1.5`
recovers `2`. -/
theorem Vault.clawback_zero_all_shares_attained :
    ∃ (v : Vault) (assets holderShares : STAmount) (waiveUnrealizedLoss : Bool) (t0 : UInt32)
      (hnn : 0 ≤ assets.toRat) (r : VaultWithAmounts) (netAssetValue : Number),
      Vault.Reachable v t0 ∧ holderShares.ShareBalance ∧ assets.isZero = true ∧
      (v.numericType.isIntegral = true → v.numericType.maxValue.toNat ≤ maxRep.toNat) ∧
      (v.clawback assets holderShares waiveUnrealizedLoss hnn).run = .ok (.ok r) ∧
      r.shares.toRat = holderShares.toRat ∧
      v.assetsTotalForWithdrawal waiveUnrealizedLoss = .ok netAssetValue ∧
      v.idealAssetsWithdrawAt netAssetValue.toRat r.shares.toRat < r.assets.toRat :=
  Vault.clawback_zero_overshoot_witness

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
    -- the upper side on any lawful vault, against the worth at the computed net asset value. Priced to nearest, it
    -- needs a worth of whole base units, within the Open limit
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

/-- Witness for `clawback_sharesDestroyed`: on a reachable vault a clawback destroys fewer shares than the ideal rounded
down. -/
theorem Vault.clawback_sharesDestroyed_truncation_attained :
    ∃ (v : Vault) (t0 : UInt32) (assets holderShares sharesDestroyed assetsRecovered : STAmount)
      (waiveUnrealizedLoss : Bool) (assetsRecoveredNumber netAssetValue : Number) (hnn : 0 ≤ assets.toRat)
      (r : VaultWithAmounts),
      Vault.Reachable v t0 ∧ v.assetsTotalForWithdrawal waiveUnrealizedLoss = .ok netAssetValue ∧ assets.Canonical ∧
      assetsToSharesWithdraw v assets true waiveUnrealizedLoss = .ok sharesDestroyed ∧
      v.sharesToAssetsWithdraw sharesDestroyed waiveUnrealizedLoss = .ok assetsRecovered ∧
      assetsRecovered.toNumber .to_nearest = .ok assetsRecoveredNumber ∧
      assetsRecoveredNumber.operator_gt v.assetsAvailable = false ∧ assets.isZero = false ∧
      (v.clawback assets holderShares waiveUnrealizedLoss hnn).run = .ok (.ok r) ∧
      r.shares.toRat < ⌊v.idealSharesWithdrawAt netAssetValue.toRat assets.toRat⌋ :=
  Vault.clawback_sharesDestroyed_witness

/-- Witness for `clawback_sharesDestroyed`: on a reachable vault a clawback destroys more shares than the ideal rounded
down, the ideal sitting just below a whole share. -/
theorem Vault.clawback_sharesDestroyed_relative_attained :
    ∃ (v : Vault) (t0 : UInt32) (assets holderShares sharesDestroyed assetsRecovered : STAmount)
      (waiveUnrealizedLoss : Bool) (assetsRecoveredNumber netAssetValue : Number) (hnn : 0 ≤ assets.toRat)
      (r : VaultWithAmounts),
      Vault.Reachable v t0 ∧ v.assetsTotalForWithdrawal waiveUnrealizedLoss = .ok netAssetValue ∧ assets.Canonical ∧
      assetsToSharesWithdraw v assets true waiveUnrealizedLoss = .ok sharesDestroyed ∧
      v.sharesToAssetsWithdraw sharesDestroyed waiveUnrealizedLoss = .ok assetsRecovered ∧
      assetsRecovered.toNumber .to_nearest = .ok assetsRecoveredNumber ∧
      assetsRecoveredNumber.operator_gt v.assetsAvailable = false ∧ assets.isZero = false ∧
      (v.clawback assets holderShares waiveUnrealizedLoss hnn).run = .ok (.ok r) ∧
      ⌊v.idealSharesWithdrawAt netAssetValue.toRat assets.toRat⌋ < r.shares.toRat :=
  Vault.clawback_sharesDestroyed_upper_witness

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

end XRPL.Model.SingleAssetVault
