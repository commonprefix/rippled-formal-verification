import XRPL.Properties.Vault.Defs
import XRPL.Properties.Vault.VaultValid
import XRPL.Model.Vault.VaultWithdraw
import XRPL.Properties.Approx
import XRPL.Properties.Protocol.STAmount.Common.DiscreteDefs
import XRPL.Properties.Vault.Common.WithdrawDefs
import XRPL.Properties.Vault.Common.ReachableDefs
import XRPL.Properties.Vault.Proofs.WithdrawPricing
import XRPL.Properties.Vault.Proofs.WithdrawTight
import XRPL.Properties.Vault.Proofs.WithdrawFee
import XRPL.Properties.Vault.Proofs.WithdrawPayoutFloor
import XRPL.Properties.Vault.Proofs.WithdrawPricingWitness
import XRPL.Properties.Vault.Proofs.WithdrawTightWitness
import XRPL.Properties.Vault.Proofs.MaxValueFits
import XRPL.Properties.Vault.Proofs.ShareFloor
import XRPL.Properties.Vault.Proofs.PricedWorth

/-! # `Vault.withdraw` accuracy

The withdraw exchange prices with two correctly-rounded `Number` stages, a `mul`
and a `div`, which together stay within `sharesε = 1.1·10⁻¹⁸` of the exact
quotient. On a reachable vault a payout that leaves shares is exactly the priced amount less the exact
early-exit fee, floored onto the base grid. The last withdrawal pays all the cash, with no fee. -/

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol

variable (v : Vault)

/-- The assets priced for the burned shares never exceed their worth, and a nonzero price falls short of it by at most
half a unit of its last digit, on a reachable vault and, at the computed net asset value, on any valid vault. -/
theorem Vault.sharesToAssetsWithdraw_bounds (v : Vault) (shares assets : STAmount) (waiveUnrealizedLoss : Bool)
    (hnn : 0 ≤ shares.toRat) -- nonnegative shares, negative ones price negatively
    (hc : shares.Canonical) -- shares stored canonically, so `shares.toNumber` is value-exact
    (hok : v.sharesToAssetsWithdraw shares waiveUnrealizedLoss = .ok assets) :
    -- on a reachable vault, for issued shares only. The upper side needs a whole worth, the lower side an exact price
    (∀ t0 : UInt32, Vault.Reachable v t0 → shares.toRat ≤ v.toExact.sharesTotal →
      0 ≤ assets.toRat ∧
      ((∃ k : ℤ, v.idealAssetsWithdraw waiveUnrealizedLoss shares.toRat = k * 10 ^ v.baseExponent) →
        assets.toRat ≤ v.idealAssetsWithdraw waiveUnrealizedLoss shares.toRat) ∧
      (assets.isZero = false →
        ((∃ q : Number, q.isNormalized ∧
            q.toRat = v.idealAssetsWithdraw waiveUnrealizedLoss shares.toRat * (v.toExact.sharesTotal : ℚ)) ∧
          ∃ q : Number, q.isNormalized ∧ q.toRat = v.idealAssetsWithdraw waiveUnrealizedLoss shares.toRat) →
        v.idealAssetsWithdraw waiveUnrealizedLoss shares.toRat - assets.toRat ≤ 1 / 2 * (10 : ℚ) ^ assets.exponent)) ∧
    -- on any valid vault, against the computed net asset value. Past the Open limit the 19-digit price can err by more
    -- than a unit. The whole worth and the exact price as in the line above
    ∀ netAssetValue : Number, v.assetsTotalForWithdrawal waiveUnrealizedLoss = .ok netAssetValue →
      -- the asset's maximum fits an int64 amount, as C++ caps every MPT maximum
      (v.numericType.isIntegral = true → v.numericType.maxValue.toNat ≤ maxRep.toNat) →
      v.idealAssetsWithdrawAt netAssetValue.toRat shares.toRat ≤ 9 * 10 ^ 15 * (10 : ℚ) ^ v.baseExponent →
      0 ≤ assets.toRat ∧
      ((∃ k : ℤ, v.idealAssetsWithdrawAt netAssetValue.toRat shares.toRat = k * 10 ^ v.baseExponent) →
        assets.toRat ≤ v.idealAssetsWithdrawAt netAssetValue.toRat shares.toRat) ∧
      (assets.isZero = false →
        ((∃ q : Number, q.isNormalized ∧
            q.toRat = v.idealAssetsWithdrawAt netAssetValue.toRat shares.toRat * (v.toExact.sharesTotal : ℚ)) ∧
          ∃ q : Number, q.isNormalized ∧ q.toRat = v.idealAssetsWithdrawAt netAssetValue.toRat shares.toRat) →
        v.idealAssetsWithdrawAt netAssetValue.toRat shares.toRat - assets.toRat ≤
          1 / 2 * (10 : ℚ) ^ assets.exponent) :=
  ⟨fun t0 hr hle =>
    Vault.Reachable.sharesToAssetsWithdraw_intended_proof v t0 hr shares assets waiveUnrealizedLoss hnn hc hle hok,
    fun netAssetValue hnav hmax hsmall =>
    Vault.sharesToAssetsWithdraw_intended_total_proof v hmax shares assets waiveUnrealizedLoss netAssetValue hnav hnn
      hc hok hsmall⟩

/-- The net asset value a withdrawal prices at: the cash plus the deployed assets rounded down to a
`Number`, then less the loss (none when waived) rounded to a neighbouring `Number`. -/
theorem Vault.assetsTotalForWithdrawal_steps (v : Vault) (waiveUnrealizedLoss : Bool)
    (netAssetValue : Number) (hnav : v.assetsTotalForWithdrawal waiveUnrealizedLoss = .ok netAssetValue) :
    ∃ assetsTotal : Number, v.assetsTotal = .ok assetsTotal ∧
      assetsTotal.RoundsToRepresentable (v.assetsAvailable.toRat + v.assetsDeployed.toRat) .downward ∧
      netAssetValue.RoundsToRepresentable
        (assetsTotal.toRat - (if waiveUnrealizedLoss then 0 else v.lossUnrealized.toRat)) .to_nearest :=
  Vault.assetsTotalForWithdrawal_steps_proof v waiveUnrealizedLoss netAssetValue hnav

/-- A successful withdrawal that names shares burns exactly the named shares. -/
theorem Vault.withdraw_sharesBurned_exact (shares : STAmount) (waiveUnrealizedLoss : Bool) (t : UInt32)
    (hpos : 0 < shares.toRat)
    (r : VaultWithAmounts)
    (hok : (v.withdraw (.vaultShares shares) waiveUnrealizedLoss t hpos).run = .ok (.ok r)) :
    r.shares = shares :=
  Vault.withdraw_sharesBurned_exact_proof v shares waiveUnrealizedLoss t hpos r hok

/-- Withdrawing by assets burns the ideal share amount rounded down, a whole positive number, on a reachable vault
and, at the net asset value the model computes, on any valid vault. -/
theorem Vault.withdraw_sharesBurned (v : Vault) (assets : STAmount) (waiveUnrealizedLoss : Bool) (t : UInt32)
    (hpos : 0 < assets.toRat)
    (hc : assets.Canonical) -- a transaction amount is a canonical amount
    (r : VaultWithAmounts)
    (hok : (v.withdraw (.vaultAssets assets) waiveUnrealizedLoss t hpos).run = .ok (.ok r)) :
    -- on a reachable vault. The 19-digit price can cross a whole number within `sharesε` relatively of the ideal
    (∀ t0 : UInt32, Vault.Reachable v t0 →
      (∀ n : ℤ, v.idealSharesWithdraw waiveUnrealizedLoss assets.toRat * sharesε <
        |v.idealSharesWithdraw waiveUnrealizedLoss assets.toRat - n|) →
      r.shares.toRat.den = 1 ∧ 0 < r.shares.toRat ∧
      r.shares.toRat ≤ v.idealSharesWithdraw waiveUnrealizedLoss assets.toRat ∧
      v.idealSharesWithdraw waiveUnrealizedLoss assets.toRat - 1 < r.shares.toRat) ∧
    -- on any valid vault, with the gap as in the line above at the computed net asset value
    ∀ netAssetValue : Number, v.assetsTotalForWithdrawal waiveUnrealizedLoss = .ok netAssetValue →
      (∀ n : ℤ, v.idealSharesWithdrawAt netAssetValue.toRat assets.toRat * sharesε <
        |v.idealSharesWithdrawAt netAssetValue.toRat assets.toRat - n|) →
      r.shares.toRat.den = 1 ∧ 0 < r.shares.toRat ∧
      r.shares.toRat ≤ v.idealSharesWithdrawAt netAssetValue.toRat assets.toRat ∧
      v.idealSharesWithdrawAt netAssetValue.toRat assets.toRat - 1 < r.shares.toRat :=
  ⟨fun t0 hr hgap =>
    let h := Vault.withdraw_sharesBurned_proof v assets waiveUnrealizedLoss t hpos hc
      (Vault.Reachable.withdrawNavExact_proof v t0 hr waiveUnrealizedLoss) r hok
    have hle := shares_le_ideal_of_gap _ _ _ h.1 h.2.1.le sharesε_nonneg le_rfl h.2.2.1 hgap
    ⟨h.1, h.2.1, hle, ideal_sub_one_lt_of_gap _ _ _ h.1 (h.2.1.le.trans hle) le_rfl h.2.2.2 hgap⟩,
    fun netAssetValue hnav hgap =>
    let h := Vault.withdraw_sharesBurned_total_proof v assets waiveUnrealizedLoss t netAssetValue hnav hpos hc r hok
    have hle := shares_le_ideal_of_gap _ _ _ h.1 h.2.1.le sharesε_nonneg le_rfl h.2.2.1 hgap
    ⟨h.1, h.2.1, hle, ideal_sub_one_lt_of_gap _ _ _ h.1 (h.2.1.le.trans hle) le_rfl h.2.2.2 hgap⟩⟩

/-- A withdrawal that does not burn every share -> it pays the priced amount less the early-exit fee floored to whole
base units on a reachable vault, less than one unit short for an integral asset, and never more on any valid vault. -/
theorem Vault.withdraw_payout (v : Vault) (amount : WithdrawAmount) (waiveUnrealizedLoss : Bool) (t : UInt32)
    (hpos : 0 < amount.amount.toRat)
    (hc : amount.amount.Canonical) -- a transaction amount is a canonical amount
    (hty : amount.InAsset v.numericType) -- of the vault's asset, or its shares
    (r : VaultWithAmounts) (hok : (v.withdraw amount waiveUnrealizedLoss t hpos).run = .ok (.ok r))
    (hlt : r.shares.toRat < v.toExact.sharesTotal) :
    (∀ t0 : UInt32, Vault.Reachable v t0 →
      ∃ priced : STAmount, v.sharesToAssetsWithdraw r.shares waiveUnrealizedLoss = .ok priced ∧
        r.assets.toRat = (⌊priced.toRat * (1 - (v.earlyExitFeeRateAt t).toNat / 100000) /
          10 ^ v.baseExponent⌋ : ℚ) * 10 ^ v.baseExponent) ∧
    (∀ t0 : UInt32, Vault.Reachable v t0 → v.numericType.isIntegral = true →
      ∃ priced : STAmount, v.sharesToAssetsWithdraw r.shares waiveUnrealizedLoss = .ok priced ∧
        priced.toRat * (1 - (v.earlyExitFeeRateAt t).toNat / 100000) - r.assets.toRat < 1) ∧
    -- on any valid vault. The asset's maximum fits an int64 amount, as C++ caps every MPT maximum
    ((v.numericType.isIntegral = true → v.numericType.maxValue.toNat ≤ maxRep.toNat) →
      ∃ priced : STAmount, v.sharesToAssetsWithdraw r.shares waiveUnrealizedLoss = .ok priced ∧
        r.assets.toRat ≤ priced.toRat * (1 - (v.earlyExitFeeRateAt t).toNat / 100000)) :=
  ⟨fun t0 hr => Vault.Reachable.withdraw_payout_floor_proof v amount waiveUnrealizedLoss t t0 hpos hr hc hty
      (Vault.Reachable.maxValue_fits v t0 hr
        (Vault.withdraw_sharesTotal_pos v amount waiveUnrealizedLoss t hpos hc hty r hok)) r hok hlt,
    fun t0 hr hint => by
      obtain ⟨priced, hpr, h⟩ := Vault.withdraw_payout_integral_proof v amount waiveUnrealizedLoss t t0 hpos hr hc
        hty hint (Vault.Reachable.maxValue_fits v t0 hr
          (Vault.withdraw_sharesTotal_pos v amount waiveUnrealizedLoss t hpos hc hty r hok)) r hok hlt
      exact ⟨priced, hpr, by linarith⟩,
    fun hmax => Vault.withdraw_payout_le_proof v amount waiveUnrealizedLoss t hpos hc hty hmax r hok hlt⟩

/-- At the same time, burning more shares never pays less from the same vault. -/
theorem Vault.withdraw_payout_monotone (v : Vault) (amount₁ amount₂ : WithdrawAmount)
    (waiveUnrealizedLoss : Bool) (t t0 : UInt32)
    (hpos₁ : 0 < amount₁.amount.toRat) (hpos₂ : 0 < amount₂.amount.toRat) (hr : Vault.Reachable v t0)
    (hc₁ : amount₁.amount.Canonical) (hc₂ : amount₂.amount.Canonical)
    (hty₁ : amount₁.InAsset v.numericType) (hty₂ : amount₂.InAsset v.numericType)
    (r₁ r₂ : VaultWithAmounts)
    (hok₁ : (v.withdraw amount₁ waiveUnrealizedLoss t hpos₁).run = .ok (.ok r₁))
    (hok₂ : (v.withdraw amount₂ waiveUnrealizedLoss t hpos₂).run = .ok (.ok r₂))
    (hle : r₁.shares.toRat ≤ r₂.shares.toRat) :
    r₁.assets.toRat ≤ r₂.assets.toRat :=
  Vault.withdraw_payout_monotone_proof v amount₁ amount₂ waiveUnrealizedLoss t t0 hpos₁ hpos₂ hr hc₁ hc₂
    hty₁ hty₂
    (Vault.Reachable.maxValue_fits v t0 hr
      (Vault.withdraw_sharesTotal_pos v amount₁ waiveUnrealizedLoss t hpos₁ hc₁ hty₁ r₁ hok₁))
    r₁ r₂ hok₁ hok₂ hle

/-- A withdrawal under a 100% early-exit fee that does not burn every share pays nothing: the cash
stays in the vault and the shares are burned. -/
theorem Vault.withdraw_full_fee (v : Vault) (amount : WithdrawAmount) (waiveUnrealizedLoss : Bool)
    (t t0 : UInt32) (hpos : 0 < amount.amount.toRat) (hr : Vault.Reachable v t0)
    (hc : amount.amount.Canonical) -- a transaction amount is a canonical amount
    (hty : amount.InAsset v.numericType) -- of the vault's asset, or its shares
    (r : VaultWithAmounts) (hok : (v.withdraw amount waiveUnrealizedLoss t hpos).run = .ok (.ok r))
    (hfee : v.earlyExitFeeRateAt t = maxEarlyExitFeeRate) (hlt : r.shares.toRat < v.toExact.sharesTotal) :
    r.assets.toRat = 0 ∧ r.vault'.assetsAvailable.toRat = v.assetsAvailable.toRat ∧
      (r.vault'.toExact.sharesTotal : ℚ) = v.toExact.sharesTotal - r.shares.toRat :=
  Vault.withdraw_full_fee_proof v amount waiveUnrealizedLoss t t0 hpos hr hc hty
    (Vault.Reachable.maxValue_fits v t0 hr
      (Vault.withdraw_sharesTotal_pos v amount waiveUnrealizedLoss t hpos hc hty r hok)) r hok hfee hlt

/-- A withdrawal that pays something strictly lowers the cash and the vault total. -/
theorem Vault.withdraw_payout_decreases_assets (v : Vault) (amount : WithdrawAmount)
    (waiveUnrealizedLoss : Bool) (t : UInt32) (hpos : 0 < amount.amount.toRat)
    (hc : amount.amount.Canonical) -- a transaction amount is a canonical amount
    (hty : amount.InAsset v.numericType) -- of the vault's asset, or its shares
    -- the asset's maximum fits an int64 amount, as C++ caps every MPT maximum
    (hmax : v.numericType.isIntegral = true → v.numericType.maxValue.toNat ≤ maxRep.toNat)
    (r : VaultWithAmounts) (hok : (v.withdraw amount waiveUnrealizedLoss t hpos).run = .ok (.ok r))
    (hpay : 0 < r.assets.toRat) :
    r.vault'.assetsAvailable.toRat < v.assetsAvailable.toRat ∧
      r.vault'.toExact.assetsTotal < v.toExact.assetsTotal :=
  Vault.withdraw_payout_decreases_assets_proof v amount waiveUnrealizedLoss t hpos hc hty hmax r hok hpay

/-- On a reachable vault a withdrawal of at most every share is never refused for insufficient funds. -/
theorem Vault.withdraw_under_available (v : Vault) (shares : STAmount) (waiveUnrealizedLoss : Bool)
    (t t0 : UInt32) (hpos : 0 < (WithdrawAmount.vaultShares shares).amount.toRat)
    (hr : Vault.Reachable v t0)
    (hc : shares.Canonical) -- a transaction amount is a canonical amount
    (hle : shares.toRat ≤ v.toExact.sharesTotal) :
    (v.withdraw (.vaultShares shares) waiveUnrealizedLoss t hpos).run ≠ .ok (.error .tecINSUFFICIENT_FUNDS) :=
  Vault.withdraw_under_available_proof v shares waiveUnrealizedLoss t t0 hpos hr hc
    (Vault.Reachable.maxValue_fits v t0 hr (lt_of_lt_of_le hpos hle)) hle

/-- A successful withdrawal empties the vault exactly when it burns every share: no cash and no shares
remain, and every other field is unchanged. -/
theorem Vault.withdraw_final_iff (v : Vault) (amount : WithdrawAmount) (waiveUnrealizedLoss : Bool)
    (t : UInt32) (hpos : 0 < amount.amount.toRat)
    (hc : amount.amount.Canonical) -- a transaction amount is a canonical amount
    (hty : amount.InAsset v.numericType) -- of the vault's asset, or its shares
    (r : VaultWithAmounts) (hok : (v.withdraw amount waiveUnrealizedLoss t hpos).run = .ok (.ok r)) :
    r.shares.toRat = v.toExact.sharesTotal ↔
      r.vault'.toRawVault = { v.toRawVault with assetsAvailable := Number.zero, sharesTotal := Number.zero } :=
  Vault.withdraw_final_iff_proof v amount waiveUnrealizedLoss t hpos hc hty r hok

/-- A withdrawal that burns every share pays exactly their worth: all the cash. -/
theorem Vault.withdraw_final_payout (v : Vault) (amount : WithdrawAmount) (waiveUnrealizedLoss : Bool)
    (t t0 : UInt32) (hpos : 0 < amount.amount.toRat) (hr : Vault.Reachable v t0)
    (hc : amount.amount.Canonical) -- a transaction amount is a canonical amount
    (hty : amount.InAsset v.numericType) -- of the vault's asset, or its shares
    (r : VaultWithAmounts) (hok : (v.withdraw amount waiveUnrealizedLoss t hpos).run = .ok (.ok r))
    (hfinal : r.shares.toRat = v.toExact.sharesTotal) :
    r.assets.toRat = v.idealAssetsWithdraw waiveUnrealizedLoss r.shares.toRat :=
  Vault.withdraw_final_payout_proof v amount waiveUnrealizedLoss t t0 hpos hr hc hty
    (Vault.Reachable.maxValue_fits v t0 hr
      (Vault.withdraw_sharesTotal_pos v amount waiveUnrealizedLoss t hpos hc hty r hok)) r hok hfinal

/-- Witness for `sharesToAssetsWithdraw_bounds`: on a reachable integral vault a run prices above the shares'
worth, half a unit above it (`2` for `1.5`). -/
theorem Vault.sharesToAssetsWithdraw_overshoot_attained :
    ∃ (v : Vault) (t0 : UInt32) (shares assets : STAmount) (waiveUnrealizedLoss : Bool),
      Vault.Reachable v t0 ∧ 0 ≤ shares.toRat ∧ shares.Canonical ∧ shares.toRat ≤ v.toExact.sharesTotal ∧
      v.sharesToAssetsWithdraw shares waiveUnrealizedLoss = .ok assets ∧
      v.idealAssetsWithdraw waiveUnrealizedLoss shares.toRat < assets.toRat :=
  Vault.sharesToAssetsWithdraw_overshoot_witness

/-- Fractional witness for `sharesToAssetsWithdraw_bounds`: a run prices above the shares' worth, half a 16-digit
unit above it (`1000000000000002` for `1000000000000001.5`). -/
theorem Vault.sharesToAssetsWithdraw_overshoot_frac_attained :
    ∃ (v : Vault) (t0 : UInt32) (shares assets : STAmount) (waiveUnrealizedLoss : Bool),
      v.numericType = .fractional ∧ Vault.Reachable v t0 ∧ 0 ≤ shares.toRat ∧ shares.Canonical ∧
      shares.toRat ≤ v.toExact.sharesTotal ∧
      v.sharesToAssetsWithdraw shares waiveUnrealizedLoss = .ok assets ∧
      v.idealAssetsWithdraw waiveUnrealizedLoss shares.toRat < assets.toRat :=
  Vault.sharesToAssetsWithdraw_overshoot_frac_witness

/-- Witness for the lower side of `sharesToAssetsWithdraw_bounds`: on a reachable integral vault a nonzero price is
more than half a unit below the shares' worth (`8341197431023684` for `8341197431023684.5040…`). -/
theorem Vault.sharesToAssetsWithdraw_shortfall_attained :
    ∃ (v : Vault) (t0 : UInt32) (shares assets : STAmount) (waiveUnrealizedLoss : Bool),
      Vault.Reachable v t0 ∧ 0 ≤ shares.toRat ∧ shares.Canonical ∧ shares.toRat ≤ v.toExact.sharesTotal ∧
      v.sharesToAssetsWithdraw shares waiveUnrealizedLoss = .ok assets ∧ assets.isZero = false ∧
      (1 / 2 : ℚ) * (10 : ℚ) ^ assets.exponent <
        v.idealAssetsWithdraw waiveUnrealizedLoss shares.toRat - assets.toRat :=
  Vault.sharesToAssetsWithdraw_shortfall_witness

/-- Fractional witness for the lower side of `sharesToAssetsWithdraw_bounds`: the same run on an IOU vault of scale 0
prices more than half a 16-digit unit below the shares' worth. -/
theorem Vault.sharesToAssetsWithdraw_shortfall_frac_attained :
    ∃ (v : Vault) (t0 : UInt32) (shares assets : STAmount) (waiveUnrealizedLoss : Bool),
      v.numericType = .fractional ∧ Vault.Reachable v t0 ∧ 0 ≤ shares.toRat ∧ shares.Canonical ∧
      shares.toRat ≤ v.toExact.sharesTotal ∧
      v.sharesToAssetsWithdraw shares waiveUnrealizedLoss = .ok assets ∧ assets.isZero = false ∧
      (1 / 2 : ℚ) * (10 : ℚ) ^ assets.exponent <
        v.idealAssetsWithdraw waiveUnrealizedLoss shares.toRat - assets.toRat :=
  Vault.sharesToAssetsWithdraw_shortfall_frac_witness

/-- Witness for `sharesToAssetsWithdraw_bounds` on any valid vault: a run prices above the shares' worth at the
computed net asset value, half a unit above it. -/
theorem Vault.sharesToAssetsWithdraw_total_overshoot_attained :
    ∃ (v : Vault) (shares assets : STAmount) (waiveUnrealizedLoss : Bool) (netAssetValue : Number),
      v.assetsTotalForWithdrawal waiveUnrealizedLoss = .ok netAssetValue ∧ 0 ≤ shares.toRat ∧
      shares.Canonical ∧
      -- the asset's maximum fits an int64 amount, as C++ caps every MPT maximum
      (v.numericType.isIntegral = true → v.numericType.maxValue.toNat ≤ maxRep.toNat) ∧
      v.sharesToAssetsWithdraw shares waiveUnrealizedLoss = .ok assets ∧
      v.idealAssetsWithdrawAt netAssetValue.toRat shares.toRat ≤ 9 * 10 ^ 15 * (10 : ℚ) ^ v.baseExponent ∧
      v.idealAssetsWithdrawAt netAssetValue.toRat shares.toRat < assets.toRat :=
  Vault.sharesToAssetsWithdraw_total_witness

/-- Witness for `sharesToAssetsWithdraw_bounds` on any valid vault: within the Open limit a nonzero price falls more
than half a unit below the worth at the computed net asset value. -/
theorem Vault.sharesToAssetsWithdraw_total_shortfall_attained :
    ∃ (v : Vault) (shares assets : STAmount) (waiveUnrealizedLoss : Bool) (netAssetValue : Number),
      v.assetsTotalForWithdrawal waiveUnrealizedLoss = .ok netAssetValue ∧ 0 ≤ shares.toRat ∧
      shares.Canonical ∧
      -- the asset's maximum fits an int64 amount, as C++ caps every MPT maximum
      (v.numericType.isIntegral = true → v.numericType.maxValue.toNat ≤ maxRep.toNat) ∧
      v.sharesToAssetsWithdraw shares waiveUnrealizedLoss = .ok assets ∧
      v.idealAssetsWithdrawAt netAssetValue.toRat shares.toRat ≤ 9 * 10 ^ 15 * (10 : ℚ) ^ v.baseExponent ∧
      assets.isZero = false ∧
      (1 / 2 : ℚ) * (10 : ℚ) ^ assets.exponent <
        v.idealAssetsWithdrawAt netAssetValue.toRat shares.toRat - assets.toRat :=
  Vault.sharesToAssetsWithdraw_total_shortfall_witness

/-- Witness for `withdraw_sharesBurned`: on a reachable vault a withdrawal by assets burns one share less than
the ideal, which is whole. -/
theorem Vault.withdraw_sharesBurned_truncation_attained :
    ∃ (v : Vault) (t t0 : UInt32) (assets : STAmount) (waiveUnrealizedLoss : Bool)
      (hpos : 0 < assets.toRat) (r : VaultWithAmounts),
      Vault.Reachable v t0 ∧ assets.Canonical ∧
      (v.withdraw (.vaultAssets assets) waiveUnrealizedLoss t hpos).run = .ok (.ok r) ∧
      r.shares.toRat ≤ v.idealSharesWithdraw waiveUnrealizedLoss assets.toRat - 1 :=
  Vault.withdraw_sharesBurned_witness

/-- Witness for `withdraw_sharesBurned`: on a reachable vault a run burns more shares than the ideal, which sits
just below a whole share. -/
theorem Vault.withdraw_sharesBurned_relative_attained :
    ∃ (v : Vault) (t t0 : UInt32) (assets : STAmount) (waiveUnrealizedLoss : Bool)
      (hpos : 0 < assets.toRat) (r : VaultWithAmounts),
      Vault.Reachable v t0 ∧ assets.Canonical ∧
      (v.withdraw (.vaultAssets assets) waiveUnrealizedLoss t hpos).run = .ok (.ok r) ∧
      v.idealSharesWithdraw waiveUnrealizedLoss assets.toRat < r.shares.toRat :=
  Vault.withdraw_sharesBurned_sharp_witness

/-- Witness for `withdraw_sharesBurned` on any valid vault: a run burns one share less than the ideal at the
computed net asset value, which is whole. -/
theorem Vault.withdraw_sharesBurned_total_truncation_attained :
    ∃ (v : Vault) (t : UInt32) (assets : STAmount) (waiveUnrealizedLoss : Bool) (netAssetValue : Number)
      (hpos : 0 < assets.toRat) (r : VaultWithAmounts),
      v.assetsTotalForWithdrawal waiveUnrealizedLoss = .ok netAssetValue ∧ assets.Canonical ∧
      (v.withdraw (.vaultAssets assets) waiveUnrealizedLoss t hpos).run = .ok (.ok r) ∧
      r.shares.toRat ≤ v.idealSharesWithdrawAt netAssetValue.toRat assets.toRat - 1 :=
  Vault.withdraw_sharesBurned_total_witness

/-- Witness for `withdraw_sharesBurned` on any valid vault: a run burns more shares than the ideal at the computed
net asset value. -/
theorem Vault.withdraw_sharesBurned_total_relative_attained :
    ∃ (v : Vault) (t : UInt32) (assets : STAmount) (waiveUnrealizedLoss : Bool) (netAssetValue : Number)
      (hpos : 0 < assets.toRat) (r : VaultWithAmounts),
      v.assetsTotalForWithdrawal waiveUnrealizedLoss = .ok netAssetValue ∧ assets.Canonical ∧
      (v.withdraw (.vaultAssets assets) waiveUnrealizedLoss t hpos).run = .ok (.ok r) ∧
      v.idealSharesWithdrawAt netAssetValue.toRat assets.toRat < r.shares.toRat :=
  Vault.withdraw_sharesBurned_total_sharp_witness

/-- Witness for `withdraw_payout` on any valid vault: with no fee a run pays the whole priced amount. -/
theorem Vault.withdraw_payout_total_attained :
    ∃ (v : Vault) (t : UInt32) (amount : WithdrawAmount) (waiveUnrealizedLoss : Bool)
      (hpos : 0 < amount.amount.toRat) (r : VaultWithAmounts),
      amount.amount.Canonical ∧ amount.InAsset v.numericType ∧
      (v.numericType.isIntegral = true → v.numericType.maxValue.toNat ≤ maxRep.toNat) ∧
      (v.withdraw amount waiveUnrealizedLoss t hpos).run = .ok (.ok r) ∧
      r.shares.toRat < v.toExact.sharesTotal ∧
      ∃ priced : STAmount, v.sharesToAssetsWithdraw r.shares waiveUnrealizedLoss = .ok priced ∧
        r.assets.toRat = priced.toRat * (1 - (v.earlyExitFeeRateAt t).toNat / 100000) :=
  Vault.withdraw_payout_total_witness

/-- Witness for the integral line of `withdraw_payout`: on a reachable integral vault a run falls short by
exactly `1 - 10⁻⁵` of a unit. -/
theorem Vault.withdraw_payout_integral_attained :
    ∃ (v : Vault) (t t0 : UInt32) (amount : WithdrawAmount) (waiveUnrealizedLoss : Bool)
      (hpos : 0 < amount.amount.toRat) (r : VaultWithAmounts),
      Vault.Reachable v t0 ∧ amount.amount.Canonical ∧ amount.InAsset v.numericType ∧
      v.numericType.isIntegral = true ∧
      (v.withdraw amount waiveUnrealizedLoss t hpos).run = .ok (.ok r) ∧
      r.shares.toRat < v.toExact.sharesTotal ∧
      ∃ priced : STAmount, v.sharesToAssetsWithdraw r.shares waiveUnrealizedLoss = .ok priced ∧
        priced.toRat * (1 - (v.earlyExitFeeRateAt t).toNat / 100000) - r.assets.toRat = 1 - 1 / 10 ^ 5 :=
  Vault.withdraw_payout_integral_witness

end XRPL.Model.SingleAssetVault
