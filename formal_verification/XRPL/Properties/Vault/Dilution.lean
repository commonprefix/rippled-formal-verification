import XRPL.Properties.Vault.Defs
import XRPL.Properties.Vault.VaultDeposit
import XRPL.Model.Vault.VaultWithdraw
import XRPL.Model.Vault.VaultBurn
import XRPL.Model.Vault.VaultClawback
import XRPL.Properties.Vault.Common.WithdrawDefs
import XRPL.Properties.Vault.Common.ReachableDefs
import XRPL.Properties.Vault.Proofs.PerShareValue
import XRPL.Properties.Vault.Proofs.DilutionWitness
import XRPL.Properties.Vault.Proofs.DilutionReachWitness
import XRPL.Properties.Vault.Proofs.MaxValueFits
import XRPL.Properties.Vault.Proofs.Support.VaultBalances
import XRPL.Properties.Vault.Proofs.PerShareFloor

/-! # Operations do not dilute shareholders (except the rounding error)

Per-share value is `withdrawNav / sharesTotal`. Each theorem states, cross-multiplied to avoid division,
that an operation lowers it by at most a rounding term per share. For a withdrawal or a clawback that term
also holds `sharesε` of the burned shares' worth. The history bound keeps the relative factor
`1 - sharesε` per step, which needs each withdrawal or clawback to leave at least half the shares. -/

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol

/-- Deposit -> per-share value falls by less than one base unit per existing share for an IOU and never for an integral
asset on a reachable vault, and on any valid vault also by what the computed total and the cash update round away. -/
theorem Vault.deposit_no_dilution (v : Vault) (amountDeposit : STAmount) (t : UInt32)
    (hpos : 0 < amountDeposit.toRat)
    (hcanon : amountDeposit.Canonical) -- a transaction amount is a canonical amount
    (r : VaultWithAmounts) (hok : (v.deposit amountDeposit false t hpos).run = .ok (.ok r))
    (hSsz : (v.toExact.sharesTotal : ℚ) + r.shares.toRat ≤ 2 ^ 63 - 1) : -- the MPT maximum
    -- on a reachable vault. An integral charge rounds to nearest, so it needs a whole worth
    (∀ t0 : UInt32, Vault.Reachable v t0 →
      amountDeposit.mNumericType = v.numericType → -- of the vault's asset
      ((0 : ℚ) < (v.toExact.sharesTotal : ℚ) →
        r.vault'.withdrawNav * (v.toExact.sharesTotal : ℚ) >
          v.withdrawNav * (r.vault'.toExact.sharesTotal : ℚ) -
            (10 : ℚ) ^ v.baseExponent * (v.toExact.sharesTotal : ℚ)) ∧
      ((∃ k : ℤ, v.idealChargeDeposit r.shares.toRat = k * 10 ^ v.baseExponent) →
        v.numericType.isIntegral = true →
        r.vault'.withdrawNav * (v.toExact.sharesTotal : ℚ) ≥ v.withdrawNav * (r.vault'.toExact.sharesTotal : ℚ))) ∧
    -- on any valid vault. The integral side also needs the worth within the Open limit, as in `deposit_charge_total`
    ∀ assetsTotal : Number, v.assetsTotal = .ok assetsTotal →
      ((0 : ℚ) < (v.toExact.sharesTotal : ℚ) →
        r.vault'.withdrawNav * (v.toExact.sharesTotal : ℚ) >
          v.withdrawNav * (r.vault'.toExact.sharesTotal : ℚ) -
            ((10 : ℚ) ^ v.baseExponent + (v.toExact.assetsTotal - assetsTotal.toRat) * r.shares.toRat /
                (v.toExact.sharesTotal : ℚ) +
              (v.assetsAvailable.toRat + r.assets.toRat - r.vault'.assetsAvailable.toRat)) *
              (v.toExact.sharesTotal : ℚ)) ∧
      ((∃ k : ℤ, v.idealChargeDepositAt assetsTotal.toRat r.shares.toRat = k * 10 ^ v.baseExponent) →
        v.idealChargeDepositAt assetsTotal.toRat r.shares.toRat ≤ 9 * 10 ^ 15 * (10 : ℚ) ^ v.baseExponent →
        v.numericType.isIntegral = true →
        r.vault'.withdrawNav * (v.toExact.sharesTotal : ℚ) ≥
          v.withdrawNav * (r.vault'.toExact.sharesTotal : ℚ) -
            ((v.toExact.assetsTotal - assetsTotal.toRat) * r.shares.toRat / (v.toExact.sharesTotal : ℚ) +
              (v.assetsAvailable.toRat + r.assets.toRat - r.vault'.assetsAvailable.toRat)) *
              (v.toExact.sharesTotal : ℚ)) :=
  ⟨fun t0 hr hty =>
    Vault.Reachable.deposit_no_dilution_intended_proof v amountDeposit t t0 hpos hr hcanon hty r hok hSsz,
    fun assetsTotal hat =>
    Vault.deposit_no_dilution_intended_total_proof v amountDeposit t assetsTotal hat hpos hcanon r hok hSsz⟩

/-- A donation strictly increases per-share value: assets come in, the share
total does not move. -/
theorem Vault.deposit_donation_no_dilution (v : Vault) (amountDeposit : STAmount) (t t0 : UInt32)
    (hpos : 0 < amountDeposit.toRat)
    (hr : Vault.Reachable v t0)
    (hcanon : amountDeposit.Canonical) -- a transaction amount is a canonical amount
    (hty : amountDeposit.mNumericType = v.numericType) -- of the vault's asset
    (r : VaultWithAmounts) (hok : (v.deposit amountDeposit true t hpos).run = .ok (.ok r)) :
    v.withdrawNav < r.vault'.withdrawNav ∧
    r.vault'.toExact.sharesTotal = v.toExact.sharesTotal :=
  Vault.deposit_donation_no_dilution_proof v amountDeposit t t0 hpos hr hcanon hty
    (Vault.maxValue_fits_of_canonical v amountDeposit hcanon hty) r hok

/-- `deposit_donation_no_dilution` on any valid vault: per-share value rises by the donation, less
only the cash the update rounds away. -/
theorem Vault.deposit_donation_no_dilution_total (v : Vault) (amountDeposit : STAmount) (t : UInt32)
    (hpos : 0 < amountDeposit.toRat)
    (hcanon : amountDeposit.Canonical) -- a transaction amount is a canonical amount
    (hty : amountDeposit.mNumericType = v.numericType) -- of the vault's asset
    (r : VaultWithAmounts) (hok : (v.deposit amountDeposit true t hpos).run = .ok (.ok r)) :
    v.withdrawNav < r.vault'.withdrawNav +
        (v.assetsAvailable.toRat + r.assets.toRat - r.vault'.assetsAvailable.toRat) ∧
    r.vault'.toExact.sharesTotal = v.toExact.sharesTotal :=
  Vault.deposit_donation_no_dilution_total_proof v amountDeposit t hpos hcanon hty r hok

/-- Withdrawal -> per-share value never falls on a reachable vault, and on any valid vault falls at most by what the
computed net asset value and the cash update round away. -/
theorem Vault.withdraw_no_dilution (v : Vault) (amount : WithdrawAmount) (waiveUnrealizedLoss : Bool) (t : UInt32)
    (hpos : 0 < amount.amount.toRat)
    (hc : amount.amount.Canonical) -- a transaction amount is a canonical amount
    (hty : amount.InAsset v.numericType) -- of the vault's asset, or its shares
    (r : VaultWithAmounts) (hok : (v.withdraw amount waiveUnrealizedLoss t hpos).run = .ok (.ok r)) :
    -- on a reachable vault. The price rounds to nearest, so the payout stays at or below the burned shares' worth only
    -- when that worth is a whole number of base units
    (∀ t0 : UInt32, Vault.Reachable v t0 →
      (∃ k : ℤ, v.idealAssetsWithdraw waiveUnrealizedLoss r.shares.toRat = k * 10 ^ v.baseExponent) →
      r.vault'.withdrawNav * (v.toExact.sharesTotal : ℚ) ≥ v.withdrawNav * (r.vault'.toExact.sharesTotal : ℚ)) ∧
    -- on any valid vault. The whole worth and the Open-limit bound as in `sharesToAssetsWithdraw_bounds`
    ∀ netAssetValue : Number, v.assetsTotalForWithdrawal waiveUnrealizedLoss = .ok netAssetValue →
      -- the asset's maximum fits an int64 amount, as C++ caps every MPT maximum
      (v.numericType.isIntegral = true → v.numericType.maxValue.toNat ≤ maxRep.toNat) →
      (∃ k : ℤ, v.idealAssetsWithdrawAt netAssetValue.toRat r.shares.toRat = k * 10 ^ v.baseExponent) →
      v.idealAssetsWithdrawAt netAssetValue.toRat r.shares.toRat ≤ 9 * 10 ^ 15 * (10 : ℚ) ^ v.baseExponent →
      r.vault'.withdrawNav * (v.toExact.sharesTotal : ℚ) ≥
        v.withdrawNav * (r.vault'.toExact.sharesTotal : ℚ) -
          (v.assetsAvailable.toRat - r.assets.toRat - r.vault'.assetsAvailable.toRat) * (v.toExact.sharesTotal : ℚ) -
          (netAssetValue.toRat - v.withdrawNav) * r.shares.toRat :=
  ⟨fun t0 hr hworth => Vault.Reachable.withdraw_no_dilution_intended_proof v amount waiveUnrealizedLoss t t0 hpos hr hc
      hty (Vault.Reachable.maxValue_fits v t0 hr
        (Vault.withdraw_sharesTotal_pos v amount waiveUnrealizedLoss t hpos hc hty r hok)) r hok hworth,
    fun netAssetValue hnav hmax hworth hsmall => Vault.withdraw_no_dilution_intended_total_proof v amount
      waiveUnrealizedLoss t netAssetValue hnav hpos hc hty hmax r hok hworth hsmall⟩

/-- Clawback, also for a zero amount -> per-share value never falls on a reachable vault, and on any valid vault falls
at most by what the computed net asset value and the cash update round away. -/
theorem Vault.clawback_no_dilution (v : Vault) (assets holderShares : STAmount) (waiveUnrealizedLoss : Bool)
    (hnn : 0 ≤ assets.toRat)
    (hc : assets.CanonicalOrZero) -- a clawback amount is canonical, or zero to claw back the holding
    (hhs : holderShares.ShareBalance) -- the holder's balance of the vault's shares
    (r : VaultWithAmounts) (hok : (v.clawback assets holderShares waiveUnrealizedLoss hnn).run = .ok (.ok r)) :
    -- on a reachable vault. The recovery stays at or below the destroyed shares' worth only when that worth is a whole
    -- number of base units
    (∀ t0 : UInt32, Vault.Reachable v t0 →
      (∃ k : ℤ, v.idealAssetsWithdraw waiveUnrealizedLoss r.shares.toRat = k * 10 ^ v.baseExponent) →
      r.vault'.withdrawNav * (v.toExact.sharesTotal : ℚ) ≥ v.withdrawNav * (r.vault'.toExact.sharesTotal : ℚ)) ∧
    -- on any valid vault. The whole worth and the Open-limit bound as in `sharesToAssetsWithdraw_bounds`
    ∀ netAssetValue : Number, v.assetsTotalForWithdrawal waiveUnrealizedLoss = .ok netAssetValue →
      -- the asset's maximum fits an int64 amount, as C++ caps every MPT maximum
      (v.numericType.isIntegral = true → v.numericType.maxValue.toNat ≤ maxRep.toNat) →
      (∃ k : ℤ, v.idealAssetsWithdrawAt netAssetValue.toRat r.shares.toRat = k * 10 ^ v.baseExponent) →
      v.idealAssetsWithdrawAt netAssetValue.toRat r.shares.toRat ≤ 9 * 10 ^ 15 * (10 : ℚ) ^ v.baseExponent →
      r.vault'.withdrawNav * (v.toExact.sharesTotal : ℚ) ≥
        v.withdrawNav * (r.vault'.toExact.sharesTotal : ℚ) -
          (v.assetsAvailable.toRat - r.assets.toRat - r.vault'.assetsAvailable.toRat) * (v.toExact.sharesTotal : ℚ) -
          (netAssetValue.toRat - v.withdrawNav) * r.shares.toRat :=
  ⟨fun t0 hr hworth => Vault.Reachable.clawback_no_dilution_intended_proof v assets holderShares waiveUnrealizedLoss
      t0 hnn hr hc hhs
      (Vault.Reachable.maxValue_fits v t0 hr
        (Vault.Reachable.clawback_sharesTotal_pos v t0 hr assets holderShares waiveUnrealizedLoss hhs hnn r hok))
      r hok hworth,
    fun netAssetValue hnav hmax hworth hsmall => Vault.clawback_no_dilution_intended_total_proof v assets holderShares
      waiveUnrealizedLoss netAssetValue hnav hnn hc hhs hmax r hok hworth hsmall⟩

/-- From a reachable vault, over any operations that leave shares, the per-share value drops only through IOU
deposits, by less than one base unit per share each. `h` - `whole` gives each other step the one-step `hworth`. -/
theorem Vault.ReachableFromIn.no_dilution (v : Vault) (t0 : UInt32) (hr : Vault.Reachable v t0)
    (t : UInt32) (n : ℕ) (D : ℚ) (w : Vault) (h : Vault.ReachableFromIn true v t w n D) :
    w.withdrawNav / (w.toExact.sharesTotal : ℚ) ≥ v.withdrawNav / (v.toExact.sharesTotal : ℚ) - D :=
  Vault.ReachableFromIn.no_dilution_intended_proof v t0 hr t n D w h

/-- Witness for the grid term of `deposit_no_dilution`: on a reachable vault a deposit lowers per-share value by all
but `10⁻¹⁵` of one base step spread over the share total after it. -/
theorem Vault.deposit_no_dilution_grid_attained :
    ∃ (v : Vault) (amountDeposit : STAmount) (t t0 : UInt32) (hpos : 0 < amountDeposit.toRat)
      (r : VaultWithAmounts),
      Vault.Reachable v t0 ∧ amountDeposit.Canonical ∧ amountDeposit.mNumericType = v.numericType ∧
      (v.deposit amountDeposit false t hpos).run = .ok (.ok r) ∧
      (v.toExact.sharesTotal : ℚ) + r.shares.toRat ≤ 2 ^ 63 - 1 ∧
      r.vault'.withdrawNav * (v.toExact.sharesTotal : ℚ) =
        v.withdrawNav * (r.vault'.toExact.sharesTotal : ℚ) -
          (1 - 1 / 10 ^ 15) * (10 : ℚ) ^ v.baseExponent * (v.toExact.sharesTotal : ℚ) := by
  obtain ⟨v, amountDeposit, t, t0, hpos, r, hr, hcanon, hty, -, hok, hSsz, heq⟩ :=
    Vault.deposit_no_dilution_grid_witness
  exact ⟨v, amountDeposit, t, t0, hpos, r, hr, hcanon, hty, hok, hSsz, heq⟩

/-- Witness for the grid term of `deposit_no_dilution` on any valid vault: a deposit lowers per-share value by all
but `10⁻¹⁵` of one base step plus the residues, spread over the share total after it. -/
theorem Vault.deposit_no_dilution_total_grid_attained :
    ∃ (v : Vault) (amountDeposit : STAmount) (t : UInt32) (assetsTotal : Number)
      (hpos : 0 < amountDeposit.toRat) (r : VaultWithAmounts),
      v.assetsTotal = .ok assetsTotal ∧ amountDeposit.Canonical ∧
      (v.deposit amountDeposit false t hpos).run = .ok (.ok r) ∧
      (v.toExact.sharesTotal : ℚ) + r.shares.toRat ≤ 2 ^ 63 - 1 ∧
      r.vault'.withdrawNav * (v.toExact.sharesTotal : ℚ) =
        v.withdrawNav * (r.vault'.toExact.sharesTotal : ℚ) -
          (1 - 1 / 10 ^ 15) * ((10 : ℚ) ^ v.baseExponent +
            (v.toExact.assetsTotal - assetsTotal.toRat) * r.shares.toRat / (v.toExact.sharesTotal : ℚ) +
            (v.assetsAvailable.toRat + r.assets.toRat - r.vault'.assetsAvailable.toRat)) *
            (v.toExact.sharesTotal : ℚ) :=
  Vault.deposit_no_dilution_total_grid_witness

/-- Witness for `deposit_no_dilution`: on a reachable integral vault a deposit charged half a unit below the issued
share's worth (`2` for `2.5`) lowers per-share value. -/
theorem Vault.deposit_no_dilution_integral_attained :
    ∃ (v : Vault) (amountDeposit : STAmount) (t t0 : UInt32) (hpos : 0 < amountDeposit.toRat)
      (r : VaultWithAmounts),
      Vault.Reachable v t0 ∧ amountDeposit.Canonical ∧ amountDeposit.mNumericType = v.numericType ∧
      (v.deposit amountDeposit false t hpos).run = .ok (.ok r) ∧
      (v.toExact.sharesTotal : ℚ) + r.shares.toRat ≤ 2 ^ 63 - 1 ∧ v.numericType.isIntegral = true ∧
      r.vault'.withdrawNav * (v.toExact.sharesTotal : ℚ) < v.withdrawNav * (r.vault'.toExact.sharesTotal : ℚ) :=
  Vault.deposit_no_dilution_integral_witness

/-- Witness for `deposit_no_dilution` on any valid vault: the same integral deposit lowers per-share value beyond the
residues, which vanish here. -/
theorem Vault.deposit_no_dilution_total_integral_attained :
    ∃ (v : Vault) (amountDeposit : STAmount) (t : UInt32) (assetsTotal : Number)
      (hpos : 0 < amountDeposit.toRat) (r : VaultWithAmounts),
      v.assetsTotal = .ok assetsTotal ∧ amountDeposit.Canonical ∧
      (v.deposit amountDeposit false t hpos).run = .ok (.ok r) ∧
      (v.toExact.sharesTotal : ℚ) + r.shares.toRat ≤ 2 ^ 63 - 1 ∧
      v.idealChargeDepositAt assetsTotal.toRat r.shares.toRat ≤ 9 * 10 ^ 15 * (10 : ℚ) ^ v.baseExponent ∧
      v.numericType.isIntegral = true ∧
      r.vault'.withdrawNav * (v.toExact.sharesTotal : ℚ) <
        v.withdrawNav * (r.vault'.toExact.sharesTotal : ℚ) -
          ((v.toExact.assetsTotal - assetsTotal.toRat) * r.shares.toRat / (v.toExact.sharesTotal : ℚ) +
            (v.assetsAvailable.toRat + r.assets.toRat - r.vault'.assetsAvailable.toRat)) *
            (v.toExact.sharesTotal : ℚ) :=
  Vault.deposit_no_dilution_total_integral_witness

/-- Witness for `withdraw_no_dilution`: on a reachable vault a withdrawal of one of 2 shares, worth `1.5`, for `2`
lowers per-share value by half a unit. -/
theorem Vault.withdraw_no_dilution_half_ulp_attained :
    ∃ (v : Vault) (amount : WithdrawAmount) (waiveUnrealizedLoss : Bool) (t t0 : UInt32)
      (hpos : 0 < amount.amount.toRat) (r : VaultWithAmounts),
      Vault.Reachable v t0 ∧ amount.amount.Canonical ∧ amount.InAsset v.numericType ∧
      (v.withdraw amount waiveUnrealizedLoss t hpos).run = .ok (.ok r) ∧
      r.vault'.withdrawNav * (v.toExact.sharesTotal : ℚ) < v.withdrawNav * (r.vault'.toExact.sharesTotal : ℚ) := by
  obtain ⟨v, amount, waiveUnrealizedLoss, t, t0, hpos, r, hr, hc, hty, -, hok, heq⟩ :=
    Vault.withdraw_no_dilution_half_ulp_witness
  exact ⟨v, amount, waiveUnrealizedLoss, t, t0, hpos, r, hr, hc, hty, hok, heq⟩

/-- Witness for `withdraw_no_dilution`: on a reachable vault the 19-digit pricing overpays a withdrawal by more than
half a unit, and per-share value falls by more than half a unit. -/
theorem Vault.withdraw_no_dilution_relative_attained :
    ∃ (v : Vault) (amount : WithdrawAmount) (waiveUnrealizedLoss : Bool) (t t0 : UInt32)
      (hpos : 0 < amount.amount.toRat) (r : VaultWithAmounts),
      Vault.Reachable v t0 ∧ amount.amount.Canonical ∧ amount.InAsset v.numericType ∧
      (v.withdraw amount waiveUnrealizedLoss t hpos).run = .ok (.ok r) ∧
      r.vault'.withdrawNav * (v.toExact.sharesTotal : ℚ) < v.withdrawNav * (r.vault'.toExact.sharesTotal : ℚ) := by
  obtain ⟨v, amount, waiveUnrealizedLoss, t, t0, hpos, r, hr, hc, hty, -, hok, hlt⟩ :=
    Vault.withdraw_no_dilution_relative_witness
  exact ⟨v, amount, waiveUnrealizedLoss, t, t0, hpos, r, hr, hc, hty, hok, hlt⟩

/-- Witness for `withdraw_no_dilution` on any valid vault: a withdrawal of one of 2 shares, worth `1.5`, for `2`
lowers per-share value by half a unit beyond the residues, which vanish here. -/
theorem Vault.withdraw_no_dilution_total_half_ulp_attained :
    ∃ (v : Vault) (amount : WithdrawAmount) (waiveUnrealizedLoss : Bool) (t : UInt32) (netAssetValue : Number)
      (hpos : 0 < amount.amount.toRat) (r : VaultWithAmounts),
      v.assetsTotalForWithdrawal waiveUnrealizedLoss = .ok netAssetValue ∧
      amount.amount.Canonical ∧ amount.InAsset v.numericType ∧
      -- the asset's maximum fits an int64 amount, as C++ caps every MPT maximum
      (v.numericType.isIntegral = true → v.numericType.maxValue.toNat ≤ maxRep.toNat) ∧
      (v.withdraw amount waiveUnrealizedLoss t hpos).run = .ok (.ok r) ∧
      v.idealAssetsWithdrawAt netAssetValue.toRat r.shares.toRat ≤ 9 * 10 ^ 15 * (10 : ℚ) ^ v.baseExponent ∧
      r.vault'.withdrawNav * (v.toExact.sharesTotal : ℚ) <
        v.withdrawNav * (r.vault'.toExact.sharesTotal : ℚ) -
          (v.assetsAvailable.toRat - r.assets.toRat - r.vault'.assetsAvailable.toRat) * (v.toExact.sharesTotal : ℚ) -
          (netAssetValue.toRat - v.withdrawNav) * r.shares.toRat :=
  Vault.withdraw_no_dilution_total_half_ulp_witness

/-- Witness for `clawback_no_dilution`: on a reachable vault a clawback of one of 2 shares, worth `1.5`,
recovering `2` lowers per-share value by half a unit. -/
theorem Vault.clawback_no_dilution_half_ulp_attained :
    ∃ (v : Vault) (assets holderShares : STAmount) (waiveUnrealizedLoss : Bool) (t0 : UInt32)
      (hnn : 0 ≤ assets.toRat) (r : VaultWithAmounts),
      Vault.Reachable v t0 ∧ assets.CanonicalOrZero ∧ holderShares.ShareBalance ∧
      (v.clawback assets holderShares waiveUnrealizedLoss hnn).run = .ok (.ok r) ∧
      r.vault'.withdrawNav * (v.toExact.sharesTotal : ℚ) < v.withdrawNav * (r.vault'.toExact.sharesTotal : ℚ) := by
  obtain ⟨v, assets, holderShares, waiveUnrealizedLoss, t0, hnn, r, hr, hc, hhs, -, hok, heq⟩ :=
    Vault.clawback_no_dilution_half_ulp_witness
  exact ⟨v, assets, holderShares, waiveUnrealizedLoss, t0, hnn, r, hr, hc, hhs, hok, heq⟩

/-- Witness for `clawback_no_dilution`: on a reachable vault the 19-digit pricing over-recovers by more than half
a unit, and per-share value falls by more than half a unit. -/
theorem Vault.clawback_no_dilution_relative_attained :
    ∃ (v : Vault) (assets holderShares : STAmount) (waiveUnrealizedLoss : Bool) (t0 : UInt32)
      (hnn : 0 ≤ assets.toRat) (r : VaultWithAmounts),
      Vault.Reachable v t0 ∧ assets.CanonicalOrZero ∧ holderShares.ShareBalance ∧
      (v.clawback assets holderShares waiveUnrealizedLoss hnn).run = .ok (.ok r) ∧
      r.vault'.withdrawNav * (v.toExact.sharesTotal : ℚ) < v.withdrawNav * (r.vault'.toExact.sharesTotal : ℚ) := by
  obtain ⟨v, assets, holderShares, waiveUnrealizedLoss, t0, hnn, r, hr, hc, hhs, -, hok, hlt⟩ :=
    Vault.clawback_no_dilution_relative_witness
  exact ⟨v, assets, holderShares, waiveUnrealizedLoss, t0, hnn, r, hr, hc, hhs, hok, hlt⟩

/-- Witness for `clawback_no_dilution` on the zero-amount arm: a zero amount claws a one-share holding, worth
`1.5`, recovering `2`, and per-share value falls. -/
theorem Vault.clawback_no_dilution_zero_half_ulp_attained :
    ∃ (v : Vault) (assets holderShares : STAmount) (waiveUnrealizedLoss : Bool) (t0 : UInt32)
      (hnn : 0 ≤ assets.toRat) (r : VaultWithAmounts),
      Vault.Reachable v t0 ∧ assets.CanonicalOrZero ∧ holderShares.ShareBalance ∧
      assets.isZero = true ∧
      (v.clawback assets holderShares waiveUnrealizedLoss hnn).run = .ok (.ok r) ∧
      r.shares.toRat = holderShares.toRat ∧
      r.vault'.withdrawNav * (v.toExact.sharesTotal : ℚ) < v.withdrawNav * (r.vault'.toExact.sharesTotal : ℚ) := by
  obtain ⟨v, assets, holderShares, waiveUnrealizedLoss, t0, hnn, r, hr, hc, hhs, -, hz, hok, hrs, heq⟩ :=
    Vault.clawback_no_dilution_zero_half_ulp_witness
  exact ⟨v, assets, holderShares, waiveUnrealizedLoss, t0, hnn, r, hr, hc, hhs, hz, hok, hrs, heq⟩

/-- Witness for `clawback_no_dilution` on any valid vault: a clawback of one of 2 shares, worth `1.5`, recovering
`2` lowers per-share value by half a unit beyond the residues, which vanish here. -/
theorem Vault.clawback_no_dilution_total_half_ulp_attained :
    ∃ (v : Vault) (assets holderShares : STAmount) (waiveUnrealizedLoss : Bool) (netAssetValue : Number)
      (hnn : 0 ≤ assets.toRat) (r : VaultWithAmounts),
      v.assetsTotalForWithdrawal waiveUnrealizedLoss = .ok netAssetValue ∧
      assets.CanonicalOrZero ∧ holderShares.ShareBalance ∧
      -- the asset's maximum fits an int64 amount, as C++ caps every MPT maximum
      (v.numericType.isIntegral = true → v.numericType.maxValue.toNat ≤ maxRep.toNat) ∧
      (v.clawback assets holderShares waiveUnrealizedLoss hnn).run = .ok (.ok r) ∧
      v.idealAssetsWithdrawAt netAssetValue.toRat r.shares.toRat ≤ 9 * 10 ^ 15 * (10 : ℚ) ^ v.baseExponent ∧
      r.vault'.withdrawNav * (v.toExact.sharesTotal : ℚ) <
        v.withdrawNav * (r.vault'.toExact.sharesTotal : ℚ) -
          (v.assetsAvailable.toRat - r.assets.toRat - r.vault'.assetsAvailable.toRat) * (v.toExact.sharesTotal : ℚ) -
          (netAssetValue.toRat - v.withdrawNav) * r.shares.toRat :=
  Vault.clawback_no_dilution_total_half_ulp_witness

/-- Witness for `ReachableFromIn.no_dilution`: from 7 assets and 4 shares, two withdrawals that each overpay by half
a unit, worths `3.5` and `1.5` not whole, lower per-share value `7/4 → 3/2 → 1` with a zero budget. -/
theorem Vault.ReachableFromIn.dilution_attained :
    ∃ (v : Vault) (t0 t : UInt32) (n : ℕ) (D : ℚ) (w : Vault),
      Vault.Reachable v t0 ∧ Vault.ReachableFromIn false v t w n D ∧ 1 < n ∧
      w.withdrawNav / (w.toExact.sharesTotal : ℚ) < v.withdrawNav / (v.toExact.sharesTotal : ℚ) - D :=
  Vault.ReachableFromIn.dilution_witness

end XRPL.Model.SingleAssetVault
