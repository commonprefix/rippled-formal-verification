import XRPL.Properties.Vault.Common.ReachableDefs
import XRPL.Properties.Vault.Proofs.Reachable
import XRPL.Properties.Vault.Proofs.MaxValueFits
import XRPL.Properties.Vault.Proofs.Support.VaultBalances
import XRPL.Properties.Vault.Proofs.ShareWorth

/-! # Vault reachability

`Vault.Reachable v t` holds when `v` results from `Vault.create` and a sequence of successful vault
transactions, the last at parent close time `t`. Vault transactions never lend, so a reachable vault
keeps its cash in the Open zone, and every cash update on it is exact. -/

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol

/-- Every vault reachable by vault transactions is lawful. -/
theorem Vault.Reachable.lawful (v : Vault) (t : UInt32) (_hr : Vault.Reachable v t) :
    v.toRawVault.WF ∧ v.toRawVault.Valid :=
  ⟨v.wf, v.valid⟩

/-- Every reachable vault -> AssetsDeployed = AssetsReserved = LossUnrealized = YieldUnrealized = 0, AssetsTotal =
AssetsAvailable ≤ the Open limit (9·10^15 base units), and every share is worth at least one base unit of cash. -/
theorem Vault.Reachable.vault_fields (v : Vault) (t : UInt32) (hr : Vault.Reachable v t) :
    (v.toExact.assetsDeployed = 0 ∧ v.toExact.assetsReserved = 0 ∧ v.toExact.lossUnrealized = 0 ∧
      v.toExact.yieldUnrealized = 0) ∧
    v.assetsTotal = .ok v.assetsAvailable ∧
    v.assetsAvailable.toRat ≤ 9 * (10 : ℚ) ^ (15 + v.baseExponent) ∧
    (v.toExact.sharesTotal : ℚ) * 10 ^ v.baseExponent ≤ v.assetsAvailable.toRat :=
  ⟨Vault.Reachable.lendingFields_zero_proof v t hr, Vault.Reachable.asset_parity_proof v t hr,
    Vault.Reachable.assetsAvailable_le_openLimit_proof v t hr, Vault.Reachable.sharesTotal_le_cash_proof v t hr⟩

/-- On a reachable vault -> a deposit adds exactly its charge and minted shares, a withdrawal or clawback subtracts
exactly its payout and burned shares. A deposit never decreases the cash, withdrawal and clawback never increase it. -/
theorem Vault.vault_updates_exact (v : Vault) (t0 : UInt32) (hr : Vault.Reachable v t0) :
    (∀ (amount : STAmount) (isDonation : Bool) (t : UInt32) (hpos : 0 < amount.toRat),
      amount.Canonical → -- a transaction amount is a canonical amount
      amount.mNumericType = v.numericType → -- of the vault's asset
      ∀ r : VaultWithAmounts, (v.deposit amount isDonation t hpos).run = .ok (.ok r) →
        r.vault'.assetsAvailable.toRat = v.assetsAvailable.toRat + r.assets.toRat ∧
          (r.vault'.toExact.sharesTotal : ℚ) = v.toExact.sharesTotal + r.shares.toRat ∧
          v.assetsAvailable.toRat ≤ r.vault'.assetsAvailable.toRat) ∧
    (∀ (amount : WithdrawAmount) (waive : Bool) (t : UInt32) (hpos : 0 < amount.amount.toRat),
      amount.amount.Canonical → -- a transaction amount is a canonical amount
      amount.InAsset v.numericType → -- of the vault's asset or of its shares
      ∀ r : VaultWithAmounts, (v.withdraw amount waive t hpos).run = .ok (.ok r) →
        r.vault'.assetsAvailable.toRat = v.assetsAvailable.toRat - r.assets.toRat ∧
          (r.vault'.toExact.sharesTotal : ℚ) = v.toExact.sharesTotal - r.shares.toRat ∧
          r.vault'.assetsAvailable.toRat ≤ v.assetsAvailable.toRat) ∧
    ∀ (assets holderShares : STAmount) (waive : Bool) (hnn : 0 ≤ assets.toRat),
      assets.CanonicalOrZero → -- a clawback amount is canonical, or zero to claw back the holding
      holderShares.ShareBalance →
      ∀ r : VaultWithAmounts, (v.clawback assets holderShares waive hnn).run = .ok (.ok r) →
        r.vault'.assetsAvailable.toRat = v.assetsAvailable.toRat - r.assets.toRat ∧
          (r.vault'.toExact.sharesTotal : ℚ) = v.toExact.sharesTotal - r.shares.toRat ∧
          r.vault'.assetsAvailable.toRat ≤ v.assetsAvailable.toRat := by
  refine ⟨fun amount isDonation t hpos hc hty r hok => ?_, fun amount waive t hpos hc hty r hok => ?_,
    fun assets holderShares waive hnn hc hhs r hok => ?_⟩
  · have hmax := Vault.maxValue_fits_of_canonical v amount hc hty
    obtain ⟨hA, hS⟩ := Vault.deposit_vault_updates_exact_proof v amount isDonation t t0 hpos hr hc hty hmax r hok
      (Vault.Reachable.deposit_mint_fits_proof v t0 hr amount isDonation t hpos hc hty r hok)
    -- the charge is nonnegative
    obtain ⟨ra, amounts, -, hra, hcomp, -, -, -, hras, -⟩ := Vault.deposit_ok_reduces v amount isDonation t hpos r hok
    obtain ⟨hra1, hra2, -⟩ := v.roundedDepositAmount_form amount ra hc hty hra
    have h0 := (computeDeposit_assets_form v ra isDonation amounts hra1 hra2 hmax hcomp).2.2
    rw [← hras] at h0
    exact ⟨hA, hS, by linarith⟩
  · have hmax := Vault.Reachable.maxValue_fits v t0 hr
      (Vault.withdraw_sharesTotal_pos v amount waive t hpos hc hty r hok)
    obtain ⟨hA, hS⟩ := Vault.withdraw_vault_updates_exact_proof v amount waive t t0 hpos hr hc hty hmax r hok
    -- the payout is whole base units
    obtain ⟨-, ⟨j, hj⟩, -⟩ :=
      Vault.withdraw_payout_units v amount waive t hpos (Vault.Reachable.openZone_proof v t0 hr hmax) hmax r hok
    have h0 : 0 ≤ r.assets.toRat := by rw [hj]; positivity
    exact ⟨hA, hS, by linarith⟩
  · have hmax := Vault.Reachable.maxValue_fits v t0 hr
      (Vault.Reachable.clawback_sharesTotal_pos v t0 hr assets holderShares waive hhs hnn r hok)
    obtain ⟨hA, hS⟩ := Vault.clawback_vault_updates_exact_proof v assets holderShares waive t0 hnn hr hc hhs hmax r hok
    have h0 := Vault.clawback_assets_nonneg v assets holderShares waive hnn hc hhs hmax r hok
    exact ⟨hA, hS, by linarith⟩

end XRPL.Model.SingleAssetVault
