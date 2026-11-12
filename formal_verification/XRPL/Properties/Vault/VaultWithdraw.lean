import XRPL.Properties.Vault.Defs
import XRPL.Properties.Vault.Common.GuardProofs
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

/-- Every lawful vault -> insolvent ⟺ AssetsTotal = 0 and SharesTotal > 0, AssetsTotal = ⌊AssetsAvailable +
AssetsDeployed⌋, and netAssetValue = ⌊AssetsTotal − LossUnrealized⌉ unless the loss is waived. -/
theorem Vault.lawful_totals (v : Vault) :
    (v.isInsolvent = true ↔ v.toExact.assetsTotal = 0 ∧ 0 < v.toExact.sharesTotal) ∧
    ∀ (waiveUnrealizedLoss : Bool) (netAssetValue : Number),
      v.assetsTotalForWithdrawal waiveUnrealizedLoss = .ok netAssetValue →
      ∃ assetsTotal : Number, v.assetsTotal = .ok assetsTotal ∧
        assetsTotal.RoundsToRepresentable (v.assetsAvailable.toRat + v.assetsDeployed.toRat) .downward ∧
        netAssetValue.RoundsToRepresentable
          (assetsTotal.toRat - (if waiveUnrealizedLoss then 0 else v.lossUnrealized.toRat)) .to_nearest ∧
        netAssetValue.RoundsToNearest
          (assetsTotal.toRat - (if waiveUnrealizedLoss then 0 else v.lossUnrealized.toRat)) :=
  ⟨Vault.isInsolvent_iff_proof v, Vault.assetsTotalForWithdrawal_steps_proof v⟩

/-- Withdrawal on any lawful vault -> by shares, sharesRedeemed = the requested shares, and by assets,
sharesRedeemed = ⌊idealShares⌋ > 0. -/
theorem Vault.withdraw_sharesRedeemed (v : Vault) :
    (∀ (shares : STAmount) (waiveUnrealizedLoss : Bool) (t : UInt32) (hpos : 0 < shares.toRat)
      (r : VaultWithAmounts),
      (v.withdraw (.vaultShares shares) waiveUnrealizedLoss t hpos).run = .ok (.ok r) → r.shares = shares) ∧
    ∀ (assets : STAmount) (waiveUnrealizedLoss : Bool) (t : UInt32) (netAssetValue : Number)
      (hpos : 0 < assets.toRat),
      assets.Canonical → -- a transaction amount is a canonical amount
      v.assetsTotalForWithdrawal waiveUnrealizedLoss = .ok netAssetValue →
      ∀ r : VaultWithAmounts, (v.withdraw (.vaultAssets assets) waiveUnrealizedLoss t hpos).run = .ok (.ok r) →
      -- the 19-digit price can cross a whole number within `sharesε` relatively of the ideal
      (∀ n : ℤ, v.idealSharesWithdrawAt netAssetValue.toRat assets.toRat * sharesε <
        |v.idealSharesWithdrawAt netAssetValue.toRat assets.toRat - n|) →
      0 < r.shares.toRat ∧ r.shares.toRat = ⌊v.idealSharesWithdrawAt netAssetValue.toRat assets.toRat⌋ :=
  ⟨fun shares waiveUnrealizedLoss t hpos r hok =>
    Vault.withdraw_sharesRedeemed_exact_proof v shares waiveUnrealizedLoss t hpos r hok,
    fun assets waiveUnrealizedLoss t netAssetValue hpos hc hnav r hok hgap =>
    let h := Vault.withdraw_sharesRedeemed_total_proof v assets waiveUnrealizedLoss t netAssetValue hnav hpos hc r hok
    have hle := shares_le_ideal_of_gap _ _ _ h.1 h.2.1.le sharesε_nonneg le_rfl h.2.2.1 hgap
    ⟨h.2.1, shares_eq_floor _ _ h.1
      (ideal_sub_one_lt_of_gap _ _ _ h.1 (h.2.1.le.trans hle) le_rfl h.2.2.2 hgap) hle⟩⟩

/-- Withdrawal with sharesRedeemed < SharesTotal -> assetsWithdrawn = ⌊sharesWorth × (1 − feeRate)⌋ in whole base
units, and a larger sharesRedeemed never lowers it. -/
theorem Vault.withdraw_payout (v : Vault) :
    (∀ (amount : WithdrawAmount) (waiveUnrealizedLoss : Bool) (t : UInt32) (hpos : 0 < amount.amount.toRat),
      amount.amount.Canonical → -- a transaction amount is a canonical amount
      amount.InAsset v.numericType → -- of the vault's asset, or its shares
      ∀ r : VaultWithAmounts, (v.withdraw amount waiveUnrealizedLoss t hpos).run = .ok (.ok r) →
      r.shares.toRat < v.toExact.sharesTotal →
      -- C++ prices the shares to nearest, so the payout is ⌊price × (1 − feeRate)⌋ rather than of sharesWorth (FV_M2_3)
      (∀ t0 : UInt32, Vault.Reachable v t0 →
        ∃ priced : STAmount, v.sharesToAssetsWithdraw r.shares waiveUnrealizedLoss = .ok priced ∧
          r.assets.toRat = (⌊priced.toRat * (1 - (v.earlyExitFeeRateAt t).toNat / 100000) /
            10 ^ v.baseExponent⌋ : ℚ) * 10 ^ v.baseExponent) ∧
      -- with no fee. Priced to nearest, the upper side needs a worth of whole base units
      (∀ t0 : UInt32, Vault.Reachable v t0 → v.earlyExitFeeRateAt t = 0 →
        ∀ netAssetValue : Number, v.assetsTotalForWithdrawal waiveUnrealizedLoss = .ok netAssetValue →
          ((∃ k : ℤ, v.idealAssetsWithdrawAt netAssetValue.toRat r.shares.toRat = k * 10 ^ v.baseExponent) →
            r.assets.toRat ≤ v.idealAssetsWithdrawAt netAssetValue.toRat r.shares.toRat) ∧
          v.idealAssetsWithdrawAt netAssetValue.toRat r.shares.toRat - r.assets.toRat <
            (10 : ℚ) ^ v.baseExponent) ∧
      -- on any lawful vault. The asset's maximum fits an int64 amount, as C++ caps every MPT maximum
      ((v.numericType.isIntegral = true → v.numericType.maxValue.toNat ≤ maxRep.toNat) →
        ∃ priced : STAmount, v.sharesToAssetsWithdraw r.shares waiveUnrealizedLoss = .ok priced ∧
          r.assets.toRat ≤ priced.toRat * (1 - (v.earlyExitFeeRateAt t).toNat / 100000))) ∧
    -- from the same vault at the same time
    ∀ (amount₁ amount₂ : WithdrawAmount) (waiveUnrealizedLoss : Bool) (t t0 : UInt32)
      (hpos₁ : 0 < amount₁.amount.toRat) (hpos₂ : 0 < amount₂.amount.toRat),
      Vault.Reachable v t0 → amount₁.amount.Canonical → amount₂.amount.Canonical →
      amount₁.InAsset v.numericType → amount₂.InAsset v.numericType →
      ∀ r₁ r₂ : VaultWithAmounts,
      (v.withdraw amount₁ waiveUnrealizedLoss t hpos₁).run = .ok (.ok r₁) →
      (v.withdraw amount₂ waiveUnrealizedLoss t hpos₂).run = .ok (.ok r₂) →
      r₁.shares.toRat ≤ r₂.shares.toRat → r₁.assets.toRat ≤ r₂.assets.toRat :=
  ⟨fun amount waiveUnrealizedLoss t hpos hc hty r hok hlt =>
    ⟨fun t0 hr => Vault.Reachable.withdraw_payout_floor_proof v amount waiveUnrealizedLoss t t0 hpos hr hc hty
        (Vault.Reachable.maxValue_fits v t0 hr
          (Vault.withdraw_sharesTotal_pos v amount waiveUnrealizedLoss t hpos hc hty r hok)) r hok hlt,
      fun t0 hr hfee netAssetValue hnav => Vault.Reachable.withdraw_payout_worth_proof v amount waiveUnrealizedLoss t
        t0 hpos hr hc hty r hok hlt hfee netAssetValue hnav,
      fun hmax => Vault.withdraw_payout_le_proof v amount waiveUnrealizedLoss t hpos hc hty hmax r hok hlt⟩,
    fun amount₁ amount₂ waiveUnrealizedLoss t t0 hpos₁ hpos₂ hr hc₁ hc₂ hty₁ hty₂ r₁ r₂ hok₁ hok₂ hle =>
    Vault.withdraw_payout_monotone_proof v amount₁ amount₂ waiveUnrealizedLoss t t0 hpos₁ hpos₂ hr hc₁ hc₂
      hty₁ hty₂
      (Vault.Reachable.maxValue_fits v t0 hr
        (Vault.withdraw_sharesTotal_pos v amount₁ waiveUnrealizedLoss t hpos₁ hc₁ hty₁ r₁ hok₁))
      r₁ r₂ hok₁ hok₂ hle⟩

/-- Witness for `withdraw_payout` with no fee: on a reachable integral vault a withdrawal of one share worth `1.5`
pays `2`, half a unit above the worth. -/
theorem Vault.withdraw_payout_worth_attained :
    ∃ (v : Vault) (t t0 : UInt32) (amount : WithdrawAmount) (waiveUnrealizedLoss : Bool)
      (hpos : 0 < amount.amount.toRat) (r : VaultWithAmounts) (netAssetValue : Number),
      Vault.Reachable v t0 ∧ amount.amount.Canonical ∧ amount.InAsset v.numericType ∧
      (v.withdraw amount waiveUnrealizedLoss t hpos).run = .ok (.ok r) ∧
      r.shares.toRat < v.toExact.sharesTotal ∧ v.earlyExitFeeRateAt t = 0 ∧
      v.assetsTotalForWithdrawal waiveUnrealizedLoss = .ok netAssetValue ∧
      v.idealAssetsWithdrawAt netAssetValue.toRat r.shares.toRat < r.assets.toRat :=
  Vault.withdraw_payout_worth_witness

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

end XRPL.Model.SingleAssetVault
