import XRPL.Properties.Vault.Defs
import XRPL.Properties.Vault.VaultValid
import XRPL.Model.Vault.VaultDeposit
import XRPL.Properties.Approx
import XRPL.Properties.Protocol.STAmount.Common.DiscreteDefs
import XRPL.Properties.Vault.Common.DepositDefs
import XRPL.Properties.Vault.Common.ReachableDefs
import XRPL.Properties.Vault.Proofs.Ideal
import XRPL.Properties.Vault.Proofs.DepositRounding
import XRPL.Properties.Vault.Proofs.DepositAccuracy
import XRPL.Properties.Vault.Proofs.DepositTight
import XRPL.Properties.Vault.Proofs.DepositLimit
import XRPL.Properties.Vault.Proofs.DepositCharge
import XRPL.Properties.Vault.Proofs.DepositWitness
import XRPL.Properties.Vault.Proofs.DepositTightWitness
import XRPL.Properties.Vault.Proofs.ShareWorth
import XRPL.Properties.Vault.Proofs.ShareFloor
import XRPL.Properties.Vault.Proofs.DepositChargeFloor

/-! # `Vault.deposit` accuracy -/

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol

variable (v : Vault)

/-- `roundedAmount` is `amountDeposit` with every digit below some grid step `10 ^ s` dropped, nonzero, and the grid
step never exceeds it, so the leading digit is kept. An integral `amountDeposit` passes through unchanged. -/
theorem Vault.roundedDepositAmount_bounds (amountDeposit : STAmount)
    (hcanon : amountDeposit.integral = false → amountDeposit.IOUCanonical) -- an IOU request is canonical
    (hpos : 0 < amountDeposit.toRat) :
    (∀ roundedAmount : STAmount, (v.roundedDepositAmount amountDeposit).run = .ok (.ok roundedAmount) →
      (∃ s : ℤ, RoundsToRepresentableAt roundedAmount amountDeposit.toRat s .downward ∧
        (10 : ℚ) ^ s ≤ |roundedAmount.toRat|) ∧
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

/-- When the vault's exchange rate still equals `10 ^ scale`, the ideal share amount is the empty-vault
formula, so the empty vault is a special case of the general pricing, not a different rule. -/
theorem Vault.idealSharesDeposit_initial_rate (v : Vault) (amount : ℚ)
    (hrate : (v.toExact.sharesTotal : ℚ) = v.depositNav * (10 : ℚ) ^ v.scale.toNat) :
    v.idealSharesDeposit amount = amount * (10 : ℚ) ^ v.scale.toNat :=
  Vault.idealSharesDeposit_initial_rate_proof v amount hrate

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

/-- Deposit -> the shares issued are the ideal rounded down, never above it and less than one share below. On any
valid vault the upper side is measured against the shares priced at the total the model computes. -/
theorem Vault.deposit_sharesIssued (v : Vault) (amountDeposit roundedAmount : STAmount) (t : UInt32)
    (hposA : 0 < amountDeposit.toRat)
    (hcanon : amountDeposit.Canonical) -- a transaction amount is a canonical amount
    (hrounded : (v.roundedDepositAmount amountDeposit).run = .ok (.ok roundedAmount))
    (r : VaultWithAmounts) (hok : (v.deposit amountDeposit false t hposA).run = .ok (.ok r))
    -- the 19-digit price can cross a whole number within `sharesε` relatively of the ideal
    (hgap : ∀ n : ℤ, v.idealSharesDeposit roundedAmount.toRat * sharesε <
      |v.idealSharesDeposit roundedAmount.toRat - n|) :
    (∀ t0 : UInt32, Vault.Reachable v t0 →
      r.shares.toRat.den = 1 ∧ 0 ≤ r.shares.toRat ∧
      v.idealSharesDeposit roundedAmount.toRat - 1 < r.shares.toRat ∧
      r.shares.toRat ≤ v.idealSharesDeposit roundedAmount.toRat) ∧
    -- on any valid vault. C++ mints the shares only if the share issuance stays within its maximum, 2⁶³ − 1, and the
    -- floor needs the gap also at the computed total, the side the upper bound is measured against
    ∀ assetsTotal : Number, v.assetsTotal = .ok assetsTotal →
      v.sharesTotal.toRat + r.shares.toRat ≤ maxRep.toNat →
      (∀ n : ℤ, v.idealSharesDepositAt assetsTotal.toRat roundedAmount.toRat * sharesε <
        |v.idealSharesDepositAt assetsTotal.toRat roundedAmount.toRat - n|) →
      r.shares.toRat.den = 1 ∧ 0 ≤ r.shares.toRat ∧
      v.idealSharesDeposit roundedAmount.toRat - 1 < r.shares.toRat ∧
      r.shares.toRat ≤ v.idealSharesDepositAt assetsTotal.toRat roundedAmount.toRat :=
  ⟨fun t0 hr => shares_floor_of_gap _ _ _ _ sharesShortε_le sharesOverε_nonneg sharesOverε_le
      (Vault.deposit_sharesIssued_proof v amountDeposit roundedAmount t hcanon hposA
        (Vault.Reachable.depositNavExact_proof v t0 hr) hrounded r hok
        (Vault.Reachable.deposit_mint_fits_maxRep v t0 hr amountDeposit t hposA hcanon r hok)) hgap,
    fun assetsTotal hat hmint hgapAt =>
      let h := Vault.deposit_sharesIssued_total_proof v amountDeposit roundedAmount t hcanon hposA assetsTotal hat
        hrounded r hok hmint
      ⟨h.1, h.2.1, ideal_sub_one_lt_of_gap _ _ _ h.1
          (Vault.idealSharesDeposit_nonneg v _
            (Vault.deposit_rounded_pos v amountDeposit roundedAmount t hposA hcanon hrounded r hok).le)
          sharesShortε_le h.2.2.1 hgap,
        shares_le_ideal_of_gap _ _ _ h.1 h.2.1 sharesOverε_nonneg sharesOverε_le h.2.2.2 hgapAt⟩⟩

/-- The charge is at most the request, an IOU charge at most the worth and under a base unit below, an integral one
at least it and at most half a unit above. `hworth`, `hexact` - a whole worth, a 19-digit exact price. -/
theorem Vault.deposit_charge (v : Vault) (amountDeposit : STAmount) (t t0 : UInt32)
    (hpos : 0 < amountDeposit.toRat) (hr : Vault.Reachable v t0)
    (hcanon : amountDeposit.Canonical) -- a transaction amount is a canonical amount
    (r : VaultWithAmounts) (hok : (v.deposit amountDeposit false t hpos).run = .ok (.ok r)) :
    r.assets.toRat ≤ amountDeposit.toRat ∧
    v.idealChargeDeposit r.shares.toRat - (10 : ℚ) ^ v.baseExponent < r.assets.toRat ∧
    (r.assets.isZero = true →
      v.numericType.isIntegral = true ∧ v.idealChargeDeposit r.shares.toRat * (1 - sharesε) ≤ 1 / 2) ∧
    (v.numericType.isIntegral = true →
      ((∃ q : Number, q.isNormalized ∧ q.toRat = v.idealChargeDeposit r.shares.toRat * (v.toExact.sharesTotal : ℚ)) ∧
        ∃ q : Number, q.isNormalized ∧ q.toRat = v.idealChargeDeposit r.shares.toRat) →
      r.assets.toRat - v.idealChargeDeposit r.shares.toRat ≤ 1 / 2) ∧
    ((∃ k : ℤ, v.idealChargeDeposit r.shares.toRat = k * 10 ^ v.baseExponent) →
      (v.numericType.isIntegral = false → r.assets.toRat ≤ v.idealChargeDeposit r.shares.toRat) ∧
      (v.numericType.isIntegral = true → v.idealChargeDeposit r.shares.toRat ≤ r.assets.toRat)) :=
  Vault.Reachable.deposit_charge_intended_proof v amountDeposit t t0 hpos hr hcanon r hok

/-- The same on any valid vault, against the charge at the computed total. `hsmall` - past the Open limit the 19-digit
price can err by more than a unit. `hworth`, `hexact` - as in `deposit_charge`, at the computed total. -/
theorem Vault.deposit_charge_total (v : Vault) (amountDeposit : STAmount) (t : UInt32) (assetsTotal : Number)
    (hpos : 0 < amountDeposit.toRat)
    (hcanon : amountDeposit.Canonical) -- a transaction amount is a canonical amount
    (hat : v.assetsTotal = .ok assetsTotal)
    (r : VaultWithAmounts) (hok : (v.deposit amountDeposit false t hpos).run = .ok (.ok r))
    (hsmall : v.idealChargeDepositAt assetsTotal.toRat r.shares.toRat ≤ 9 * 10 ^ 15 * (10 : ℚ) ^ v.baseExponent) :
    r.assets.toRat ≤ amountDeposit.toRat ∧
    v.idealChargeDepositAt assetsTotal.toRat r.shares.toRat - (10 : ℚ) ^ v.baseExponent < r.assets.toRat ∧
    (r.assets.isZero = true →
      v.numericType.isIntegral = true ∧
        v.idealChargeDepositAt assetsTotal.toRat r.shares.toRat * (1 - sharesε) ≤ 1 / 2) ∧
    (v.numericType.isIntegral = true →
      ((∃ q : Number, q.isNormalized ∧
          q.toRat = v.idealChargeDepositAt assetsTotal.toRat r.shares.toRat * (v.toExact.sharesTotal : ℚ)) ∧
        ∃ q : Number, q.isNormalized ∧ q.toRat = v.idealChargeDepositAt assetsTotal.toRat r.shares.toRat) →
      r.assets.toRat - v.idealChargeDeposit r.shares.toRat ≤ 1 / 2) ∧
    ((∃ k : ℤ, v.idealChargeDepositAt assetsTotal.toRat r.shares.toRat = k * 10 ^ v.baseExponent) →
      (v.numericType.isIntegral = false → r.assets.toRat ≤ v.idealChargeDepositAt assetsTotal.toRat r.shares.toRat) ∧
      (v.numericType.isIntegral = true → v.idealChargeDepositAt assetsTotal.toRat r.shares.toRat ≤ r.assets.toRat)) :=
  Vault.deposit_charge_intended_total_proof v amountDeposit t hcanon hpos assetsTotal hat r hok hsmall

/-- For an integral asset, the amount taken exceeds the value of the issued shares by at most half a unit.
`hexact` - the 19-digit price at the computed total is exact: the worth and the worth times the share total fit. -/
theorem Vault.deposit_charge_integral (v : Vault) (amountDeposit : STAmount) (t : UInt32) (assetsTotal : Number)
    (hpos : 0 < amountDeposit.toRat)
    (hcanon : amountDeposit.Canonical) -- a transaction amount is a canonical amount
    (hint : v.numericType.isIntegral = true)
    (hat : v.assetsTotal = .ok assetsTotal)
    (r : VaultWithAmounts) (hok : (v.deposit amountDeposit false t hpos).run = .ok (.ok r))
    (hexact : ((∃ q : Number, q.isNormalized ∧
        q.toRat = v.idealChargeDepositAt assetsTotal.toRat r.shares.toRat * (v.toExact.sharesTotal : ℚ)) ∧
      ∃ q : Number, q.isNormalized ∧ q.toRat = v.idealChargeDepositAt assetsTotal.toRat r.shares.toRat)) :
    r.assets.toRat - v.idealChargeDeposit r.shares.toRat ≤ 1 / 2 :=
  Vault.deposit_charge_integral_intended_proof v amountDeposit t assetsTotal hat hcanon hint hpos r hok hexact

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

/-- Witness for `roundedDepositAmount_bounds`: a deposit of `1.5` rounds down to `1`. -/
theorem Vault.roundedDepositAmount_truncation_attained :
    ∃ (v : Vault) (amountDeposit roundedAmount : STAmount),
      (amountDeposit.integral = false → amountDeposit.IOUCanonical) ∧ 0 < amountDeposit.toRat ∧
      (v.roundedDepositAmount amountDeposit).run = .ok (.ok roundedAmount) ∧
      roundedAmount.toRat < amountDeposit.toRat :=
  Vault.roundedDepositAmount_truncation_witness

/-- Shortfall witness for `deposit_sharesIssued`: on a reachable vault a deposit issues more than one share less
than the ideal. -/
theorem Vault.deposit_sharesIssued_shortfall_attained :
    ∃ (v : Vault) (t t0 : UInt32) (amountDeposit roundedAmount : STAmount) (hposA : 0 < amountDeposit.toRat)
      (r : VaultWithAmounts),
      Vault.Reachable v t0 ∧ amountDeposit.Canonical ∧
      (v.roundedDepositAmount amountDeposit).run = .ok (.ok roundedAmount) ∧
      (v.deposit amountDeposit false t hposA).run = .ok (.ok r) ∧
      r.shares.toRat ≤ v.idealSharesDeposit roundedAmount.toRat - 1 := by
  obtain ⟨v, t, t0, amountDeposit, roundedAmount, hposA, r, hr, hc, hra, hok, -, h⟩ :=
    Vault.deposit_sharesIssued_shortfall_witness
  exact ⟨v, t, t0, amountDeposit, roundedAmount, hposA, r, hr, hc, hra, hok, h⟩

/-- Overshoot witness for `deposit_sharesIssued`: on a reachable vault a deposit issues more shares than the
ideal. -/
theorem Vault.deposit_sharesIssued_overshoot_attained :
    ∃ (v : Vault) (t t0 : UInt32) (amountDeposit roundedAmount : STAmount) (hposA : 0 < amountDeposit.toRat)
      (r : VaultWithAmounts),
      Vault.Reachable v t0 ∧ amountDeposit.Canonical ∧
      (v.roundedDepositAmount amountDeposit).run = .ok (.ok roundedAmount) ∧
      (v.deposit amountDeposit false t hposA).run = .ok (.ok r) ∧
      v.idealSharesDeposit roundedAmount.toRat < r.shares.toRat := by
  obtain ⟨v, t, t0, amountDeposit, roundedAmount, hposA, r, hr, hc, hra, hok, -, h⟩ :=
    Vault.deposit_sharesIssued_overshoot_witness
  exact ⟨v, t, t0, amountDeposit, roundedAmount, hposA, r, hr, hc, hra, hok, h⟩

/-- Shortfall witness for `deposit_sharesIssued` on any valid vault: a deposit issues more than one share less than the
ideal. -/
theorem Vault.deposit_sharesIssued_total_shortfall_attained :
    ∃ (v : Vault) (t : UInt32) (amountDeposit roundedAmount : STAmount) (assetsTotal : Number)
      (hposA : 0 < amountDeposit.toRat) (r : VaultWithAmounts),
      amountDeposit.Canonical ∧ v.assetsTotal = .ok assetsTotal ∧
      (v.roundedDepositAmount amountDeposit).run = .ok (.ok roundedAmount) ∧
      (v.deposit amountDeposit false t hposA).run = .ok (.ok r) ∧
      v.sharesTotal.toRat + r.shares.toRat ≤ maxRep.toNat ∧
      r.shares.toRat ≤ v.idealSharesDeposit roundedAmount.toRat - 1 :=
  Vault.deposit_sharesIssued_total_shortfall_witness

/-- Overshoot witness for `deposit_sharesIssued` on any valid vault: a deposit issues more than the shares priced at
the computed total. -/
theorem Vault.deposit_sharesIssued_total_overshoot_attained :
    ∃ (v : Vault) (t : UInt32) (amountDeposit roundedAmount : STAmount) (assetsTotal : Number)
      (hposA : 0 < amountDeposit.toRat) (r : VaultWithAmounts),
      amountDeposit.Canonical ∧ v.assetsTotal = .ok assetsTotal ∧
      (v.roundedDepositAmount amountDeposit).run = .ok (.ok roundedAmount) ∧
      (v.deposit amountDeposit false t hposA).run = .ok (.ok r) ∧
      v.sharesTotal.toRat + r.shares.toRat ≤ maxRep.toNat ∧
      v.idealSharesDepositAt assetsTotal.toRat roundedAmount.toRat < r.shares.toRat :=
  Vault.deposit_sharesIssued_total_overshoot_witness

/-- Witness for the IOU shortfall side of `deposit_charge`: on a reachable vault a run's charge falls short of the
issued shares' worth by all but `10⁻¹⁵` of one step of the base grid. -/
theorem Vault.deposit_charge_undercharge_attained :
    ∃ (v : Vault) (t t0 : UInt32) (amountDeposit : STAmount) (hpos : 0 < amountDeposit.toRat)
      (r : VaultWithAmounts),
      Vault.Reachable v t0 ∧ amountDeposit.Canonical ∧
      (v.deposit amountDeposit false t hpos).run = .ok (.ok r) ∧
      v.idealChargeDeposit r.shares.toRat - r.assets.toRat = (1 - 1 / 10 ^ 15) * (10 : ℚ) ^ v.baseExponent :=
  Vault.deposit_charge_lower_witness

/-- Witness for the integral excess side of `deposit_charge`: on a reachable integral vault a run's charge exceeds
the issued shares' worth by more than half a unit (`8999999999987162` for `8999999999987161.4947…`). -/
theorem Vault.deposit_charge_overcharge_attained :
    ∃ (v : Vault) (t t0 : UInt32) (amountDeposit : STAmount) (hpos : 0 < amountDeposit.toRat)
      (r : VaultWithAmounts),
      Vault.Reachable v t0 ∧ amountDeposit.Canonical ∧
      (v.deposit amountDeposit false t hpos).run = .ok (.ok r) ∧
      v.numericType.isIntegral = true ∧ 1 / 2 < r.assets.toRat - v.idealChargeDeposit r.shares.toRat :=
  Vault.deposit_charge_upper_witness

/-- Witness for `deposit_charge`: on a reachable IOU vault a run charges more than the issued shares' worth, half a
base unit above it (`1000000000000004` for `1000000000000003.5`). -/
theorem Vault.deposit_charge_overcharge_frac_attained :
    ∃ (v : Vault) (t t0 : UInt32) (amountDeposit : STAmount) (hpos : 0 < amountDeposit.toRat)
      (r : VaultWithAmounts),
      Vault.Reachable v t0 ∧ amountDeposit.Canonical ∧
      (v.deposit amountDeposit false t hpos).run = .ok (.ok r) ∧
      v.numericType.isIntegral = false ∧ v.idealChargeDeposit r.shares.toRat < r.assets.toRat :=
  Vault.deposit_charge_overcharge_frac_witness

/-- Witness for `deposit_charge`: on a reachable integral vault a run charges less than the issued shares' worth,
half a unit below it (`2` for `2.5`). -/
theorem Vault.deposit_charge_undercharge_integral_attained :
    ∃ (v : Vault) (t t0 : UInt32) (amountDeposit : STAmount) (hpos : 0 < amountDeposit.toRat)
      (r : VaultWithAmounts),
      Vault.Reachable v t0 ∧ amountDeposit.Canonical ∧
      (v.deposit amountDeposit false t hpos).run = .ok (.ok r) ∧
      v.numericType.isIntegral = true ∧ r.assets.toRat < v.idealChargeDeposit r.shares.toRat :=
  Vault.deposit_charge_undercharge_integral_witness

/-- Witness for the IOU shortfall side of `deposit_charge_total`: a run's charge falls short of the worth at the
computed total by all but `10⁻¹⁵` of one step of the base grid. -/
theorem Vault.deposit_charge_total_undercharge_attained :
    ∃ (v : Vault) (t : UInt32) (amountDeposit : STAmount) (assetsTotal : Number)
      (hpos : 0 < amountDeposit.toRat) (r : VaultWithAmounts),
      amountDeposit.Canonical ∧ v.assetsTotal = .ok assetsTotal ∧
      (v.deposit amountDeposit false t hpos).run = .ok (.ok r) ∧
      v.idealChargeDepositAt assetsTotal.toRat r.shares.toRat ≤ 9 * 10 ^ 15 * (10 : ℚ) ^ v.baseExponent ∧
      v.idealChargeDepositAt assetsTotal.toRat r.shares.toRat - r.assets.toRat =
        (1 - 1 / 10 ^ 15) * (10 : ℚ) ^ v.baseExponent :=
  Vault.deposit_charge_total_lower_witness

/-- Witness for the integral excess side of `deposit_charge_total`: an integral run's charge exceeds the issued
shares' worth by more than half a unit. -/
theorem Vault.deposit_charge_total_overcharge_attained :
    ∃ (v : Vault) (t : UInt32) (amountDeposit : STAmount) (assetsTotal : Number)
      (hpos : 0 < amountDeposit.toRat) (r : VaultWithAmounts),
      amountDeposit.Canonical ∧ v.assetsTotal = .ok assetsTotal ∧
      (v.deposit amountDeposit false t hpos).run = .ok (.ok r) ∧
      v.idealChargeDepositAt assetsTotal.toRat r.shares.toRat ≤ 9 * 10 ^ 15 * (10 : ℚ) ^ v.baseExponent ∧
      v.numericType.isIntegral = true ∧ 1 / 2 < r.assets.toRat - v.idealChargeDeposit r.shares.toRat :=
  Vault.deposit_charge_total_upper_witness

/-- Witness for `deposit_charge_total`: an IOU run charges more than the worth at the computed total. -/
theorem Vault.deposit_charge_total_overcharge_frac_attained :
    ∃ (v : Vault) (t : UInt32) (amountDeposit : STAmount) (assetsTotal : Number)
      (hpos : 0 < amountDeposit.toRat) (r : VaultWithAmounts),
      amountDeposit.Canonical ∧ v.assetsTotal = .ok assetsTotal ∧
      (v.deposit amountDeposit false t hpos).run = .ok (.ok r) ∧
      v.idealChargeDepositAt assetsTotal.toRat r.shares.toRat ≤ 9 * 10 ^ 15 * (10 : ℚ) ^ v.baseExponent ∧
      v.numericType.isIntegral = false ∧
      v.idealChargeDepositAt assetsTotal.toRat r.shares.toRat < r.assets.toRat :=
  Vault.deposit_charge_total_overcharge_frac_witness

/-- Witness for `deposit_charge_total`: an integral run charges less than the worth at the computed total. -/
theorem Vault.deposit_charge_total_undercharge_integral_attained :
    ∃ (v : Vault) (t : UInt32) (amountDeposit : STAmount) (assetsTotal : Number)
      (hpos : 0 < amountDeposit.toRat) (r : VaultWithAmounts),
      amountDeposit.Canonical ∧ v.assetsTotal = .ok assetsTotal ∧
      (v.deposit amountDeposit false t hpos).run = .ok (.ok r) ∧
      v.idealChargeDepositAt assetsTotal.toRat r.shares.toRat ≤ 9 * 10 ^ 15 * (10 : ℚ) ^ v.baseExponent ∧
      v.numericType.isIntegral = true ∧
      r.assets.toRat < v.idealChargeDepositAt assetsTotal.toRat r.shares.toRat :=
  Vault.deposit_charge_total_undercharge_integral_witness

/-- Witness for `deposit_charge_integral`: a run's charge exceeds the issued shares' worth by more than half a
unit. -/
theorem Vault.deposit_charge_integral_attained :
    ∃ (v : Vault) (t : UInt32) (amountDeposit : STAmount) (assetsTotal : Number) (hpos : 0 < amountDeposit.toRat)
      (r : VaultWithAmounts),
      amountDeposit.Canonical ∧ v.numericType.isIntegral = true ∧ v.assetsTotal = .ok assetsTotal ∧
      (v.deposit amountDeposit false t hpos).run = .ok (.ok r) ∧
      1 / 2 < r.assets.toRat - v.idealChargeDeposit r.shares.toRat :=
  Vault.deposit_charge_integral_witness

end XRPL.Model.SingleAssetVault
