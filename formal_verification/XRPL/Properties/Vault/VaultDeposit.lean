import XRPL.Properties.Vault.Defs
import XRPL.Properties.Vault.VaultValid
import XRPL.Model.Vault.VaultDeposit
import XRPL.Properties.Approx
import XRPL.Properties.Protocol.STAmount.Common.DiscreteDefs
import XRPL.Properties.Vault.Common.DepositDefs
import XRPL.Properties.Vault.Common.ReachableDefs
import XRPL.Properties.Vault.Common.ClawbackDefs
import XRPL.Properties.Vault.Proofs.DepositRounding
import XRPL.Properties.Vault.Proofs.DepositAccuracy
import XRPL.Properties.Vault.Proofs.DepositTight
import XRPL.Properties.Vault.Proofs.DepositLimit
import XRPL.Properties.Vault.Proofs.DepositCharge
import XRPL.Properties.Vault.Proofs.Support.ReachableHistory
import XRPL.Properties.Protocol.Number.Add.RoundsToRepresentable
import XRPL.Properties.Vault.Proofs.DepositTightWitness
import XRPL.Properties.Vault.Proofs.ShareWorth
import XRPL.Properties.Vault.Proofs.ShareFloor
import XRPL.Properties.Vault.Proofs.DepositChargeFloor

/-! # `Vault.deposit` accuracy -/

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol

variable (v : Vault)

/-- `roundedAmount` is nonzero, an IOU `amountDeposit` rounded down to the exponent of the vault total plus the amount,
never below the base exponent, and an integral `amountDeposit` unchanged. -/
theorem Vault.roundedDepositAmount_bounds (amountDeposit : STAmount)
    (hcanon : amountDeposit.integral = false → amountDeposit.IOUCanonical) -- an IOU request is canonical
    (hpos : 0 < amountDeposit.toRat) :
    (∀ roundedAmount : STAmount, (v.roundedDepositAmount amountDeposit).run = .ok (.ok roundedAmount) →
      (amountDeposit.integral = false → ∃ e : ℤ, v.depositExponent amountDeposit = .ok e ∧ v.baseExponent ≤ e ∧
        RoundsToRepresentableAt roundedAmount amountDeposit.toRat e .downward) ∧
      roundedAmount.isZero = false) ∧
    ∀ assetsTotal : Number, amountDeposit.integral = true →
      v.assetsTotal = .ok assetsTotal → -- the vault total does not overflow, as on every reachable vault
      (v.roundedDepositAmount amountDeposit).run = .ok (.ok amountDeposit) :=
  ⟨fun roundedAmount hrounded =>
    Vault.roundedDepositAmount_bounds_proof v amountDeposit roundedAmount hcanon hpos hrounded,
    fun assetsTotal hint hat => Vault.roundedDepositAmount_integral_proof v amountDeposit assetsTotal hint hpos hat⟩

/-- A successful donation takes exactly `roundedAmount` and issues no shares. -/
theorem Vault.deposit_donation (amountDeposit roundedAmount : STAmount) (t : UInt32)
    (hpos : 0 < amountDeposit.toRat)
    (hcanon : amountDeposit.Canonical) -- a transaction amount is a canonical amount
    (hrounded : (v.roundedDepositAmount amountDeposit).run = .ok (.ok roundedAmount))
    (r : VaultWithAmounts) (hok : (v.deposit amountDeposit true t hpos).run = .ok (.ok r)) :
    r.assets = roundedAmount ∧ r.shares = STAmount.zero .int64 :=
  Vault.deposit_donation_proof v amountDeposit roundedAmount t hpos hcanon hrounded r hok

/-- A larger rounded amount never buys fewer shares from the same vault. -/
theorem Vault.deposit_shares_monotone (v : Vault)
    (amountDeposit₁ amountDeposit₂ roundedAmount₁ roundedAmount₂ : STAmount) (t₁ t₂ : UInt32)
    -- transaction amounts are canonical amounts
    (hcanon₁ : amountDeposit₁.Canonical) (hcanon₂ : amountDeposit₂.Canonical)
    (hpos₁ : 0 < amountDeposit₁.toRat) (hpos₂ : 0 < amountDeposit₂.toRat)
    (hrounded₁ : (v.roundedDepositAmount amountDeposit₁).run = .ok (.ok roundedAmount₁))
    (hrounded₂ : (v.roundedDepositAmount amountDeposit₂).run = .ok (.ok roundedAmount₂))
    (r₁ r₂ : VaultWithAmounts)
    (hok₁ : (v.deposit amountDeposit₁ false t₁ hpos₁).run = .ok (.ok r₁))
    (hok₂ : (v.deposit amountDeposit₂ false t₂ hpos₂).run = .ok (.ok r₂))
    (hle : roundedAmount₁.toRat ≤ roundedAmount₂.toRat) :
    r₁.shares.toRat ≤ r₂.shares.toRat :=
  Vault.deposit_shares_monotone_proof v amountDeposit₁ amountDeposit₂ roundedAmount₁ roundedAmount₂ t₁ t₂
    hcanon₁ hcanon₂ hpos₁ hpos₂ hrounded₁ hrounded₂ r₁ r₂ hok₁ hok₂ hle

/-- Deposit on any lawful vault -> the shares created are the ideal at the computed total rounded down. -/
theorem Vault.deposit_sharesCreated (v : Vault) (amountDeposit roundedAmount : STAmount) (t : UInt32)
    (assetsTotal : Number) (hposA : 0 < amountDeposit.toRat)
    (hcanon : amountDeposit.Canonical) -- a transaction amount is a canonical amount
    (hat : v.assetsTotal = .ok assetsTotal)
    (hrounded : (v.roundedDepositAmount amountDeposit).run = .ok (.ok roundedAmount))
    (r : VaultWithAmounts) (hok : (v.deposit amountDeposit false t hposA).run = .ok (.ok r))
    -- C++ mints the shares only if the share issuance stays within its maximum, 2⁶³ − 1
    (hmint : v.sharesTotal.toRat + r.shares.toRat ≤ maxRep.toNat)
    -- the 19-digit price can cross a whole number within `sharesε` relatively of the ideal
    (hgap : ∀ n : ℤ, v.idealSharesDepositAt assetsTotal.toRat roundedAmount.toRat * sharesε <
      |v.idealSharesDepositAt assetsTotal.toRat roundedAmount.toRat - n|) :
    r.shares.toRat = ⌊v.idealSharesDepositAt assetsTotal.toRat roundedAmount.toRat⌋ :=
  let h := shares_floor_of_gap _ _ _ _ sharesShortε_le sharesOverε_nonneg sharesOverε_le
    (Vault.deposit_sharesCreated_total_proof v amountDeposit roundedAmount t hcanon hposA assetsTotal hat hrounded r hok
      hmint) hgap
  shares_eq_floor _ _ h.1 h.2.2.1 h.2.2.2

/-- Deposit on any lawful vault, the shares' worth within the Open limit -> the charge is at most the request and under
a base unit below the worth, an IOU charge at most a whole worth, an integral one at least it and under a unit above. -/
theorem Vault.deposit_charge (v : Vault) (amountDeposit : STAmount) (t : UInt32) (assetsTotal : Number)
    (hpos : 0 < amountDeposit.toRat)
    (hcanon : amountDeposit.Canonical) -- a transaction amount is a canonical amount
    (hat : v.assetsTotal = .ok assetsTotal)
    (r : VaultWithAmounts) (hok : (v.deposit amountDeposit false t hpos).run = .ok (.ok r))
    -- past the Open limit the 19-digit price can err by more than a unit
    (hsmall : v.idealChargeDepositAt assetsTotal.toRat r.shares.toRat ≤ 9 * 10 ^ 15 * (10 : ℚ) ^ v.baseExponent) :
    r.assets.toRat ≤ amountDeposit.toRat ∧
    v.idealChargeDepositAt assetsTotal.toRat r.shares.toRat - (10 : ℚ) ^ v.baseExponent < r.assets.toRat ∧
    (v.numericType.isIntegral = true → r.assets.toRat - v.idealChargeDepositAt assetsTotal.toRat r.shares.toRat < 1) ∧
    -- a price rounds to nearest, so each side needs a worth of whole base units
    ((∃ k : ℤ, v.idealChargeDepositAt assetsTotal.toRat r.shares.toRat = k * 10 ^ v.baseExponent) →
      (v.numericType.isIntegral = false → r.assets.toRat ≤ v.idealChargeDepositAt assetsTotal.toRat r.shares.toRat) ∧
      (v.numericType.isIntegral = true → v.idealChargeDepositAt assetsTotal.toRat r.shares.toRat ≤ r.assets.toRat)) :=
  Vault.deposit_charge_intended_total_proof v amountDeposit t hcanon hpos assetsTotal hat r hok hsmall

/-- A deposit into a reachable vault is rejected for passing a limit only when the charge it
would take brings the total over the vault's maximum or over the Open-zone limit. -/
theorem Vault.deposit_under_maximum (v : Vault) (amountDeposit : STAmount) (isDonation : Bool)
    (t t0 : UInt32) (hpos : 0 < amountDeposit.toRat) (hr : Vault.Reachable v t0)
    (hcanon : amountDeposit.Canonical) -- a transaction amount is a canonical amount
    (hty : amountDeposit.mNumericType = v.numericType) -- of the vault's asset
    (hok : (v.deposit amountDeposit isDonation t hpos).run = .ok (.error .tecLIMIT_EXCEEDED)) :
    ∃ (roundedAmount : STAmount) (amounts : VaultAmounts),
      (v.roundedDepositAmount amountDeposit).run = .ok (.ok roundedAmount) ∧
      (computeDeposit v roundedAmount isDonation).run = .ok (.ok amounts) ∧
      (9 * (10 : ℚ) ^ (15 + v.baseExponent) < v.toExact.assetsTotal + amounts.assets.toRat ∨
        ∃ m ∈ v.assetsMaximum, m.toRat < v.toExact.assetsTotal + amounts.assets.toRat) :=
  Vault.deposit_under_maximum_proof v amountDeposit isDonation t t0 hpos hr hcanon hty hok

/-- Shortfall witness for `deposit_sharesCreated`: on a reachable vault a deposit creates fewer shares than the ideal
rounded down. -/
theorem Vault.deposit_sharesCreated_shortfall_attained :
    ∃ (v : Vault) (t t0 : UInt32) (amountDeposit roundedAmount : STAmount) (assetsTotal : Number)
      (hposA : 0 < amountDeposit.toRat) (r : VaultWithAmounts),
      Vault.Reachable v t0 ∧ amountDeposit.Canonical ∧ v.assetsTotal = .ok assetsTotal ∧
      (v.roundedDepositAmount amountDeposit).run = .ok (.ok roundedAmount) ∧
      (v.deposit amountDeposit false t hposA).run = .ok (.ok r) ∧
      v.sharesTotal.toRat + r.shares.toRat ≤ maxRep.toNat ∧
      r.shares.toRat < ⌊v.idealSharesDepositAt assetsTotal.toRat roundedAmount.toRat⌋ :=
  Vault.deposit_sharesCreated_shortfall_witness

/-- Overshoot witness for `deposit_sharesCreated`: on a reachable vault a deposit creates more shares than the ideal
rounded down. -/
theorem Vault.deposit_sharesCreated_overshoot_attained :
    ∃ (v : Vault) (t t0 : UInt32) (amountDeposit roundedAmount : STAmount) (assetsTotal : Number)
      (hposA : 0 < amountDeposit.toRat) (r : VaultWithAmounts),
      Vault.Reachable v t0 ∧ amountDeposit.Canonical ∧ v.assetsTotal = .ok assetsTotal ∧
      (v.roundedDepositAmount amountDeposit).run = .ok (.ok roundedAmount) ∧
      (v.deposit amountDeposit false t hposA).run = .ok (.ok r) ∧
      v.sharesTotal.toRat + r.shares.toRat ≤ maxRep.toNat ∧
      ⌊v.idealSharesDepositAt assetsTotal.toRat roundedAmount.toRat⌋ < r.shares.toRat :=
  Vault.deposit_sharesCreated_overshoot_witness

/-- Witness for `deposit_charge`: on a reachable IOU vault a run charges more than the issued shares' worth, half a
base unit above it (`1000000000000004` for `1000000000000003.5`). -/
theorem Vault.deposit_charge_overcharge_frac_attained :
    ∃ (v : Vault) (t t0 : UInt32) (amountDeposit : STAmount) (assetsTotal : Number)
      (hpos : 0 < amountDeposit.toRat) (r : VaultWithAmounts),
      Vault.Reachable v t0 ∧ amountDeposit.Canonical ∧ v.assetsTotal = .ok assetsTotal ∧
      (v.deposit amountDeposit false t hpos).run = .ok (.ok r) ∧
      v.idealChargeDepositAt assetsTotal.toRat r.shares.toRat ≤ 9 * 10 ^ 15 * (10 : ℚ) ^ v.baseExponent ∧
      v.numericType.isIntegral = false ∧
      v.idealChargeDepositAt assetsTotal.toRat r.shares.toRat < r.assets.toRat :=
  Vault.deposit_charge_overcharge_frac_witness

/-- Witness for `deposit_charge`: on a reachable integral vault a run charges less than the issued shares' worth,
half a unit below it (`2` for `2.5`). -/
theorem Vault.deposit_charge_undercharge_integral_attained :
    ∃ (v : Vault) (t t0 : UInt32) (amountDeposit : STAmount) (assetsTotal : Number)
      (hpos : 0 < amountDeposit.toRat) (r : VaultWithAmounts),
      Vault.Reachable v t0 ∧ amountDeposit.Canonical ∧ v.assetsTotal = .ok assetsTotal ∧
      (v.deposit amountDeposit false t hpos).run = .ok (.ok r) ∧
      v.idealChargeDepositAt assetsTotal.toRat r.shares.toRat ≤ 9 * 10 ^ 15 * (10 : ℚ) ^ v.baseExponent ∧
      v.numericType.isIntegral = true ∧
      r.assets.toRat < v.idealChargeDepositAt assetsTotal.toRat r.shares.toRat :=
  Vault.deposit_charge_undercharge_integral_witness

end XRPL.Model.SingleAssetVault
