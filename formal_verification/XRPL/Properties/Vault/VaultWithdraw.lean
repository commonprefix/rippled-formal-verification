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

/-- Pricing shares on any lawful vault, their worth within the Open limit -> the price is at most a whole worth at the
computed net asset value, and a nonzero price is less than one unit of its last digit below the worth. -/
theorem Vault.sharesToAssetsWithdraw_bounds (v : Vault) (shares assets : STAmount) (waiveUnrealizedLoss : Bool)
    (netAssetValue : Number)
    (hnn : 0 ≤ shares.toRat) -- nonnegative shares, negative ones price negatively
    (hc : shares.Canonical) -- shares stored canonically, so `shares.toNumber` is value-exact
    (hnav : v.assetsTotalForWithdrawal waiveUnrealizedLoss = .ok netAssetValue)
    -- the asset's maximum fits an int64 amount, as C++ caps every MPT maximum
    (hmax : v.numericType.isIntegral = true → v.numericType.maxValue.toNat ≤ maxRep.toNat)
    -- past the Open limit the 19-digit price can err by more than a unit
    (hsmall : v.idealAssetsWithdrawAt netAssetValue.toRat shares.toRat ≤ 9 * 10 ^ 15 * (10 : ℚ) ^ v.baseExponent)
    (hok : v.sharesToAssetsWithdraw shares waiveUnrealizedLoss = .ok assets) :
    0 ≤ assets.toRat ∧
    -- a price rounds to nearest, so the upper side needs a whole worth
    ((∃ k : ℤ, v.idealAssetsWithdrawAt netAssetValue.toRat shares.toRat = k * 10 ^ v.baseExponent) →
      assets.toRat ≤ v.idealAssetsWithdrawAt netAssetValue.toRat shares.toRat) ∧
    (assets.isZero = false →
      v.idealAssetsWithdrawAt netAssetValue.toRat shares.toRat - assets.toRat < (10 : ℚ) ^ assets.exponent) :=
  Vault.sharesToAssetsWithdraw_intended_total_proof v hmax shares assets waiveUnrealizedLoss netAssetValue hnav hnn
    hc hok hsmall

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
theorem Vault.withdraw_sharesRedeemed_exact (shares : STAmount) (waiveUnrealizedLoss : Bool) (t : UInt32)
    (hpos : 0 < shares.toRat)
    (r : VaultWithAmounts)
    (hok : (v.withdraw (.vaultShares shares) waiveUnrealizedLoss t hpos).run = .ok (.ok r)) :
    r.shares = shares :=
  Vault.withdraw_sharesRedeemed_exact_proof v shares waiveUnrealizedLoss t hpos r hok

/-- Withdrawing by assets on any lawful vault redeems a positive number of shares, the ideal at the computed net asset
value rounded down. -/
theorem Vault.withdraw_sharesRedeemed (v : Vault) (assets : STAmount) (waiveUnrealizedLoss : Bool) (t : UInt32)
    (netAssetValue : Number) (hpos : 0 < assets.toRat)
    (hc : assets.Canonical) -- a transaction amount is a canonical amount
    (hnav : v.assetsTotalForWithdrawal waiveUnrealizedLoss = .ok netAssetValue)
    (r : VaultWithAmounts)
    (hok : (v.withdraw (.vaultAssets assets) waiveUnrealizedLoss t hpos).run = .ok (.ok r))
    -- the 19-digit price can cross a whole number within `sharesε` relatively of the ideal
    (hgap : ∀ n : ℤ, v.idealSharesWithdrawAt netAssetValue.toRat assets.toRat * sharesε <
      |v.idealSharesWithdrawAt netAssetValue.toRat assets.toRat - n|) :
    0 < r.shares.toRat ∧ r.shares.toRat = ⌊v.idealSharesWithdrawAt netAssetValue.toRat assets.toRat⌋ :=
  let h := Vault.withdraw_sharesRedeemed_total_proof v assets waiveUnrealizedLoss t netAssetValue hnav hpos hc r hok
  have hle := shares_le_ideal_of_gap _ _ _ h.1 h.2.1.le sharesε_nonneg le_rfl h.2.2.1 hgap
  ⟨h.2.1, shares_eq_floor _ _ h.1
    (ideal_sub_one_lt_of_gap _ _ _ h.1 (h.2.1.le.trans hle) le_rfl h.2.2.2 hgap) hle⟩

/-- A withdrawal that does not redeem every share -> it pays the priced amount less the early-exit fee floored to whole
base units on a reachable vault, and never more on any lawful vault. -/
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
    -- on any lawful vault. The asset's maximum fits an int64 amount, as C++ caps every MPT maximum
    ((v.numericType.isIntegral = true → v.numericType.maxValue.toNat ≤ maxRep.toNat) →
      ∃ priced : STAmount, v.sharesToAssetsWithdraw r.shares waiveUnrealizedLoss = .ok priced ∧
        r.assets.toRat ≤ priced.toRat * (1 - (v.earlyExitFeeRateAt t).toNat / 100000)) :=
  ⟨fun t0 hr => Vault.Reachable.withdraw_payout_floor_proof v amount waiveUnrealizedLoss t t0 hpos hr hc hty
      (Vault.Reachable.maxValue_fits v t0 hr
        (Vault.withdraw_sharesTotal_pos v amount waiveUnrealizedLoss t hpos hc hty r hok)) r hok hlt,
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

/-- Witness for `sharesToAssetsWithdraw_bounds`: on a reachable integral vault a run prices above the shares'
worth, half a unit above it (`2` for `1.5`). -/
theorem Vault.sharesToAssetsWithdraw_overshoot_attained :
    ∃ (v : Vault) (t0 : UInt32) (shares assets : STAmount) (waiveUnrealizedLoss : Bool) (netAssetValue : Number),
      Vault.Reachable v t0 ∧ 0 ≤ shares.toRat ∧ shares.Canonical ∧
      v.assetsTotalForWithdrawal waiveUnrealizedLoss = .ok netAssetValue ∧
      -- the asset's maximum fits an int64 amount, as C++ caps every MPT maximum
      (v.numericType.isIntegral = true → v.numericType.maxValue.toNat ≤ maxRep.toNat) ∧
      v.idealAssetsWithdrawAt netAssetValue.toRat shares.toRat ≤ 9 * 10 ^ 15 * (10 : ℚ) ^ v.baseExponent ∧
      v.sharesToAssetsWithdraw shares waiveUnrealizedLoss = .ok assets ∧
      v.idealAssetsWithdrawAt netAssetValue.toRat shares.toRat < assets.toRat :=
  Vault.sharesToAssetsWithdraw_overshoot_witness

/-- Witness for `withdraw_sharesRedeemed`: on a reachable vault a withdrawal by assets redeems fewer shares than the
ideal rounded down. -/
theorem Vault.withdraw_sharesRedeemed_truncation_attained :
    ∃ (v : Vault) (t t0 : UInt32) (assets : STAmount) (waiveUnrealizedLoss : Bool) (netAssetValue : Number)
      (hpos : 0 < assets.toRat) (r : VaultWithAmounts),
      Vault.Reachable v t0 ∧ assets.Canonical ∧
      v.assetsTotalForWithdrawal waiveUnrealizedLoss = .ok netAssetValue ∧
      (v.withdraw (.vaultAssets assets) waiveUnrealizedLoss t hpos).run = .ok (.ok r) ∧
      r.shares.toRat < ⌊v.idealSharesWithdrawAt netAssetValue.toRat assets.toRat⌋ :=
  Vault.withdraw_sharesRedeemed_witness

/-- Witness for `withdraw_sharesRedeemed`: on a reachable vault a run redeems more shares than the ideal rounded down,
the ideal sitting just below a whole share. -/
theorem Vault.withdraw_sharesRedeemed_relative_attained :
    ∃ (v : Vault) (t t0 : UInt32) (assets : STAmount) (waiveUnrealizedLoss : Bool) (netAssetValue : Number)
      (hpos : 0 < assets.toRat) (r : VaultWithAmounts),
      Vault.Reachable v t0 ∧ assets.Canonical ∧
      v.assetsTotalForWithdrawal waiveUnrealizedLoss = .ok netAssetValue ∧
      (v.withdraw (.vaultAssets assets) waiveUnrealizedLoss t hpos).run = .ok (.ok r) ∧
      ⌊v.idealSharesWithdrawAt netAssetValue.toRat assets.toRat⌋ < r.shares.toRat :=
  Vault.withdraw_sharesRedeemed_sharp_witness

/-- Witness for `withdraw_payout` on any lawful vault: with no fee a run pays the whole priced amount. -/
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

end XRPL.Model.SingleAssetVault
