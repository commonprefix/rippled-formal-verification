import XRPL.Properties.Vault.Defs
import XRPL.Properties.Vault.VaultDeposit
import XRPL.Model.Vault.VaultWithdraw
import XRPL.Model.Vault.VaultBurn
import XRPL.Model.Vault.VaultClawback
import XRPL.Properties.Vault.Common.WithdrawDefs
import XRPL.Properties.Vault.Common.ReachableDefs
import XRPL.Properties.Vault.Proofs.PerShareValue
import XRPL.Properties.Vault.Proofs.DepositExits
import XRPL.Properties.Vault.Proofs.DilutionWitness
import XRPL.Properties.Vault.Proofs.DilutionReachWitness
import XRPL.Properties.Vault.Proofs.MaxValueFits
import XRPL.Properties.Vault.Proofs.Support.VaultBalances
import XRPL.Properties.Vault.Proofs.PerShareFloor

/-! # Operations do not dilute shareholders

Per-share value is `withdrawNav / sharesTotal`. Each theorem states, cross-multiplied to avoid division, that an
operation keeps it when the amount it moves is worth a whole number of base units. -/

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol

/-- Vault transaction -> per-share value never falls on a deposit, a withdrawal or a clawback, also with a zero
amount, and a donation raises it. -/
theorem Vault.no_dilution (v : Vault) (t0 : UInt32) (hr : Vault.Reachable v t0) :
    (∀ (amountDeposit : STAmount) (t : UInt32) (hpos : 0 < amountDeposit.toRat),
      amountDeposit.Canonical → -- a transaction amount is a canonical amount
      amountDeposit.mNumericType = v.numericType → -- of the vault's asset
      ∀ r : VaultWithAmounts, (v.deposit amountDeposit false t hpos).run = .ok (.ok r) →
      (v.toExact.sharesTotal : ℚ) + r.shares.toRat ≤ 2 ^ 63 - 1 → -- the MPT maximum
      -- the charge rounds, so it matches the issued shares' worth only when that worth is a whole number of base
      -- units
      (∃ k : ℤ, v.idealChargeDeposit r.shares.toRat = k * 10 ^ v.baseExponent) →
      r.vault'.withdrawNav * (v.toExact.sharesTotal : ℚ) ≥ v.withdrawNav * (r.vault'.toExact.sharesTotal : ℚ)) ∧
    -- a donation: assets come in, the share total does not move and is ≠ 0
    (∀ (amountDeposit : STAmount) (t : UInt32) (hpos : 0 < amountDeposit.toRat),
      amountDeposit.Canonical → -- a transaction amount is a canonical amount
      amountDeposit.mNumericType = v.numericType → -- of the vault's asset
      ∀ r : VaultWithAmounts, (v.deposit amountDeposit true t hpos).run = .ok (.ok r) →
      v.withdrawNav < r.vault'.withdrawNav ∧
        r.vault'.toExact.sharesTotal = v.toExact.sharesTotal ∧ 0 < v.toExact.sharesTotal) ∧
    (∀ (amount : WithdrawAmount) (waiveUnrealizedLoss : Bool) (t : UInt32) (hpos : 0 < amount.amount.toRat),
      amount.amount.Canonical → -- a transaction amount is a canonical amount
      amount.InAsset v.numericType → -- of the vault's asset, or its shares
      ∀ r : VaultWithAmounts, (v.withdraw amount waiveUnrealizedLoss t hpos).run = .ok (.ok r) →
      -- the price rounds to nearest, so the payout stays at or below the redeemed shares' worth only when that
      -- worth is a whole number of base units
      (∃ k : ℤ, v.idealAssetsWithdraw waiveUnrealizedLoss r.shares.toRat = k * 10 ^ v.baseExponent) →
      r.vault'.withdrawNav * (v.toExact.sharesTotal : ℚ) ≥ v.withdrawNav * (r.vault'.toExact.sharesTotal : ℚ)) ∧
    ∀ (assets holderShares : STAmount) (waiveUnrealizedLoss : Bool) (hnn : 0 ≤ assets.toRat),
      assets.CanonicalOrZero → -- a clawback amount is canonical, or zero to claw back the holding
      holderShares.ShareBalance → -- the holder's balance of the vault's shares
      ∀ r : VaultWithAmounts, (v.clawback assets holderShares waiveUnrealizedLoss hnn).run = .ok (.ok r) →
      -- the recovery stays at or below the destroyed shares' worth only when that worth is a whole number of base
      -- units
      (∃ k : ℤ, v.idealAssetsWithdraw waiveUnrealizedLoss r.shares.toRat = k * 10 ^ v.baseExponent) →
      r.vault'.withdrawNav * (v.toExact.sharesTotal : ℚ) ≥ v.withdrawNav * (r.vault'.toExact.sharesTotal : ℚ) :=
  ⟨fun amountDeposit t hpos hcanon hty r hok hSsz hworth =>
    Vault.Reachable.deposit_no_dilution_intended_proof v amountDeposit t t0 hpos hr hcanon hty r hok hSsz hworth,
    fun amountDeposit t hpos hcanon hty r hok =>
      have h := Vault.deposit_donation_no_dilution_proof v amountDeposit t t0 hpos hr hcanon hty
        (Vault.maxValue_fits_of_canonical v amountDeposit hcanon hty) r hok
      ⟨h.1, h.2, Vault.deposit_donation_sharesTotal_pos v amountDeposit t hpos r hok⟩,
    fun amount waiveUnrealizedLoss t hpos hc hty r hok hworth =>
      Vault.Reachable.withdraw_no_dilution_intended_proof v amount waiveUnrealizedLoss t t0 hpos hr hc hty
        (Vault.Reachable.maxValue_fits v t0 hr
          (Vault.withdraw_sharesTotal_pos v amount waiveUnrealizedLoss t hpos hc hty r hok)) r hok hworth,
    fun assets holderShares waiveUnrealizedLoss hnn hc hhs r hok hworth =>
      Vault.Reachable.clawback_no_dilution_intended_proof v assets holderShares waiveUnrealizedLoss t0 hnn hr hc hhs
        (Vault.Reachable.maxValue_fits v t0 hr
          (Vault.Reachable.clawback_sharesTotal_pos v t0 hr assets holderShares waiveUnrealizedLoss hhs hnn r hok))
        r hok hworth⟩

/-- From a reachable vault, over any operations that leave shares, the per-share value never falls. `h` - `whole` gives
each step the one-step `hworth`. -/
theorem Vault.ReachableFromIn.no_dilution (v : Vault) (t0 : UInt32) (hr : Vault.Reachable v t0)
    (t : UInt32) (n : ℕ) (w : Vault) (h : Vault.ReachableFromIn true v t w n) :
    w.withdrawNav / (w.toExact.sharesTotal : ℚ) ≥ v.withdrawNav / (v.toExact.sharesTotal : ℚ) :=
  Vault.ReachableFromIn.no_dilution_intended_proof v t0 hr t n w h

/-- Witness for `no_dilution` on a deposit: on a reachable IOU vault a deposit charged the worth rounded down lowers
per-share value. -/
theorem Vault.no_dilution_deposit_grid_attained :
    ∃ (v : Vault) (amountDeposit : STAmount) (t t0 : UInt32) (hpos : 0 < amountDeposit.toRat)
      (r : VaultWithAmounts),
      Vault.Reachable v t0 ∧ amountDeposit.Canonical ∧ amountDeposit.mNumericType = v.numericType ∧
      (v.deposit amountDeposit false t hpos).run = .ok (.ok r) ∧
      (v.toExact.sharesTotal : ℚ) + r.shares.toRat ≤ 2 ^ 63 - 1 ∧ v.numericType.isIntegral = false ∧
      r.vault'.withdrawNav * (v.toExact.sharesTotal : ℚ) < v.withdrawNav * (r.vault'.toExact.sharesTotal : ℚ) := by
  obtain ⟨v, amountDeposit, t, t0, hpos, r, hr, hcanon, hty, -, hok, hSsz, hiou, heq⟩ :=
    Vault.deposit_no_dilution_grid_witness
  exact ⟨v, amountDeposit, t, t0, hpos, r, hr, hcanon, hty, hok, hSsz, hiou, heq⟩

/-- Witness for `no_dilution` on a deposit: on a reachable integral vault a deposit charged half a unit below the issued
share's worth (`2` for `2.5`) lowers per-share value. -/
theorem Vault.no_dilution_deposit_integral_attained :
    ∃ (v : Vault) (amountDeposit : STAmount) (t t0 : UInt32) (hpos : 0 < amountDeposit.toRat)
      (r : VaultWithAmounts),
      Vault.Reachable v t0 ∧ amountDeposit.Canonical ∧ amountDeposit.mNumericType = v.numericType ∧
      (v.deposit amountDeposit false t hpos).run = .ok (.ok r) ∧
      (v.toExact.sharesTotal : ℚ) + r.shares.toRat ≤ 2 ^ 63 - 1 ∧ v.numericType.isIntegral = true ∧
      r.vault'.withdrawNav * (v.toExact.sharesTotal : ℚ) < v.withdrawNav * (r.vault'.toExact.sharesTotal : ℚ) :=
  Vault.deposit_no_dilution_integral_witness

/-- Witness for `no_dilution` on a withdrawal: on a reachable vault a withdrawal of one of 2 shares, worth `1.5`,
for `2` lowers per-share value by half a unit. -/
theorem Vault.no_dilution_withdraw_half_ulp_attained :
    ∃ (v : Vault) (amount : WithdrawAmount) (waiveUnrealizedLoss : Bool) (t t0 : UInt32)
      (hpos : 0 < amount.amount.toRat) (r : VaultWithAmounts),
      Vault.Reachable v t0 ∧ amount.amount.Canonical ∧ amount.InAsset v.numericType ∧
      (v.withdraw amount waiveUnrealizedLoss t hpos).run = .ok (.ok r) ∧
      r.vault'.withdrawNav * (v.toExact.sharesTotal : ℚ) < v.withdrawNav * (r.vault'.toExact.sharesTotal : ℚ) := by
  obtain ⟨v, amount, waiveUnrealizedLoss, t, t0, hpos, r, hr, hc, hty, -, hok, heq⟩ :=
    Vault.withdraw_no_dilution_half_ulp_witness
  exact ⟨v, amount, waiveUnrealizedLoss, t, t0, hpos, r, hr, hc, hty, hok, heq⟩

/-- Witness for `no_dilution` on a clawback: on a reachable vault a clawback of one of 2 shares, worth `1.5`,
recovering `2` lowers per-share value by half a unit. -/
theorem Vault.no_dilution_clawback_half_ulp_attained :
    ∃ (v : Vault) (assets holderShares : STAmount) (waiveUnrealizedLoss : Bool) (t0 : UInt32)
      (hnn : 0 ≤ assets.toRat) (r : VaultWithAmounts),
      Vault.Reachable v t0 ∧ assets.CanonicalOrZero ∧ holderShares.ShareBalance ∧
      (v.clawback assets holderShares waiveUnrealizedLoss hnn).run = .ok (.ok r) ∧
      r.vault'.withdrawNav * (v.toExact.sharesTotal : ℚ) < v.withdrawNav * (r.vault'.toExact.sharesTotal : ℚ) := by
  obtain ⟨v, assets, holderShares, waiveUnrealizedLoss, t0, hnn, r, hr, hc, hhs, -, hok, heq⟩ :=
    Vault.clawback_no_dilution_half_ulp_witness
  exact ⟨v, assets, holderShares, waiveUnrealizedLoss, t0, hnn, r, hr, hc, hhs, hok, heq⟩

/-- Witness for `no_dilution` on a clawback with a zero amount: a zero amount claws a one-share holding, worth
`1.5`, recovering `2`, and per-share value falls. -/
theorem Vault.no_dilution_clawback_zero_half_ulp_attained :
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

/-- Witness for `ReachableFromIn.no_dilution`: from 7 assets and 4 shares, two withdrawals that each overpay by half
a unit, worths `3.5` and `1.5` not whole, lower per-share value `7/4 → 3/2 → 1`. -/
theorem Vault.ReachableFromIn.dilution_attained :
    ∃ (v : Vault) (t0 t : UInt32) (n : ℕ) (w : Vault),
      Vault.Reachable v t0 ∧ Vault.ReachableFromIn false v t w n ∧ 1 < n ∧
      w.withdrawNav / (w.toExact.sharesTotal : ℚ) < v.withdrawNav / (v.toExact.sharesTotal : ℚ) :=
  Vault.ReachableFromIn.dilution_witness

end XRPL.Model.SingleAssetVault
