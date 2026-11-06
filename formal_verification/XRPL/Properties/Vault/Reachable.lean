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

/-- Every vault reachable from creation by a sequence of operations is lawful. -/
theorem Vault.Reachable.lawful (v : Vault) (t : UInt32) (_hr : Vault.Reachable v t) :
    v.toRawVault.WF ∧ v.toRawVault.Valid :=
  ⟨v.wf, v.valid⟩

/-- Every reachable vault -> AssetsTotal = AssetsAvailable, LossUnrealized = 0, the cash is within the Open limit
(9·10^15 base units), and every share is worth at least one base unit of cash. -/
theorem Vault.Reachable.vault_fields (v : Vault) (t : UInt32) (hr : Vault.Reachable v t) :
    v.assetsTotal = .ok v.assetsAvailable ∧
    v.toExact.lossUnrealized = 0 ∧
    v.assetsAvailable.toRat ≤ 9 * (10 : ℚ) ^ (15 + v.baseExponent) ∧
    (v.toExact.sharesTotal : ℚ) * 10 ^ v.baseExponent ≤ v.assetsAvailable.toRat :=
  ⟨Vault.Reachable.asset_parity_proof v t hr, Vault.Reachable.lossUnrealized_zero_proof v t hr,
    Vault.Reachable.assetsAvailable_le_openLimit_proof v t hr, Vault.Reachable.sharesTotal_le_cash_proof v t hr⟩

/-- On a reachable vault -> a deposit adds exactly its charge to the cash and its minted shares to the share total,
and a withdrawal or a clawback subtracts exactly its payout and its burned shares. -/
theorem Vault.vault_updates_exact (v : Vault) (t0 : UInt32) (hr : Vault.Reachable v t0) :
    (∀ (amount : STAmount) (isDonation : Bool) (t : UInt32) (hpos : 0 < amount.toRat),
      amount.Canonical → -- a transaction amount is a canonical amount
      amount.mNumericType = v.numericType → -- of the vault's asset
      ∀ r : VaultWithAmounts, (v.deposit amount isDonation t hpos).run = .ok (.ok r) →
        r.vault'.assetsAvailable.toRat = v.assetsAvailable.toRat + r.assets.toRat ∧
          (r.vault'.toExact.sharesTotal : ℚ) = v.toExact.sharesTotal + r.shares.toRat) ∧
    (∀ (amount : WithdrawAmount) (waive : Bool) (t : UInt32) (hpos : 0 < amount.amount.toRat),
      amount.amount.Canonical → -- a transaction amount is a canonical amount
      amount.InAsset v.numericType → -- of the vault's asset or of its shares
      ∀ r : VaultWithAmounts, (v.withdraw amount waive t hpos).run = .ok (.ok r) →
        r.vault'.assetsAvailable.toRat = v.assetsAvailable.toRat - r.assets.toRat ∧
          (r.vault'.toExact.sharesTotal : ℚ) = v.toExact.sharesTotal - r.shares.toRat) ∧
    ∀ (assets holderShares : STAmount) (waive : Bool) (hnn : 0 ≤ assets.toRat),
      assets.CanonicalOrZero → -- a clawback amount is canonical, or zero to claw back the holding
      holderShares.ShareBalance →
      ∀ r : VaultWithAmounts, (v.clawback assets holderShares waive hnn).run = .ok (.ok r) →
        r.vault'.assetsAvailable.toRat = v.assetsAvailable.toRat - r.assets.toRat ∧
          (r.vault'.toExact.sharesTotal : ℚ) = v.toExact.sharesTotal - r.shares.toRat :=
  ⟨fun amount isDonation t hpos hc hty r hok =>
    Vault.deposit_vault_updates_exact_proof v amount isDonation t t0 hpos hr hc hty
      (Vault.maxValue_fits_of_canonical v amount hc hty) r hok
      (Vault.Reachable.deposit_mint_fits_proof v t0 hr amount isDonation t hpos hc hty r hok),
    fun amount waive t hpos hc hty r hok =>
    Vault.withdraw_vault_updates_exact_proof v amount waive t t0 hpos hr hc hty
      (Vault.Reachable.maxValue_fits v t0 hr (Vault.withdraw_sharesTotal_pos v amount waive t hpos hc hty r hok)) r hok,
    fun assets holderShares waive hnn hc hhs r hok =>
    Vault.clawback_vault_updates_exact_proof v assets holderShares waive t0 hnn hr hc hhs
      (Vault.Reachable.maxValue_fits v t0 hr
        (Vault.Reachable.clawback_sharesTotal_pos v t0 hr assets holderShares waive hhs hnn r hok)) r hok⟩

end XRPL.Model.SingleAssetVault
