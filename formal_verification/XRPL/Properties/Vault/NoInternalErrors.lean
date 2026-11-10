import XRPL.Properties.Vault.Proofs.NoInternalErrors
import XRPL.Properties.Vault.Proofs.NoPathDry
import XRPL.Properties.Vault.Proofs.NoInternalErrorsWitness

/-! # Internal errors on a reachable vault

On a reachable vault a deposit, a withdrawal and a clawback never return `tecINTERNAL` or `tecPATH_DRY` within the
Open limit. Past it a deposit can return both, and a withdrawal and a clawback `tecPATH_DRY`. -/

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol

/-- Vault transaction on a reachable vault -> no `tecINTERNAL`, a deposit when its XRP or MPT amount is at most
`2.28·10^17` units, and no `tecPATH_DRY` within the Open limit. -/
theorem Vault.Reachable.no_internal_errors (v : Vault) (t0 : UInt32) (hr : Vault.Reachable v t0) :
    (∀ (amount : STAmount) (isDonation : Bool) (t : UInt32) (hpos : 0 < amount.toRat),
      amount.Canonical → amount.mNumericType = v.numericType → -- a canonical amount of the vault's asset
      -- past `2.28·10^17` units the 19-digit share price can round above the amount
      (v.numericType.isIntegral = true → amount.toRat ≤ 228 * 10 ^ 15) →
      (v.deposit amount isDonation t hpos).run ≠ .ok (.error .tecINTERNAL)) ∧
    (∀ (amount : WithdrawAmount) (waive : Bool) (t : UInt32) (hpos : 0 < amount.amount.toRat),
      (v.withdraw amount waive t hpos).run ≠ .ok (.error .tecINTERNAL)) ∧
    (∀ (assets holderShares : STAmount) (waive : Bool) (hnn : 0 ≤ assets.toRat),
      (v.clawback assets holderShares waive hnn).run ≠ .ok (.error .tecINTERNAL)) ∧
    (∀ (amount : STAmount) (isDonation : Bool) (t : UInt32) (hpos : 0 < amount.toRat),
      amount.Canonical → amount.mNumericType = v.numericType → -- a canonical amount of the vault's asset
      amount.toRat ≤ 9 * 10 ^ (15 + v.baseExponent) → -- within the Open limit
      (v.deposit amount isDonation t hpos).run ≠ .ok (.error .tecPATH_DRY)) ∧
    (∀ (amount : WithdrawAmount) (waive : Bool) (t : UInt32) (hpos : 0 < amount.amount.toRat),
      amount.amount.Canonical →
      (∀ assets, amount = .vaultAssets assets → assets.toRat ≤ 9 * 10 ^ (15 + v.baseExponent)) →
      (∀ shares, amount = .vaultShares shares → shares.toRat ≤ v.toExact.sharesTotal) →
      (v.withdraw amount waive t hpos).run ≠ .ok (.error .tecPATH_DRY)) ∧
    ∀ (assets holderShares : STAmount) (waive : Bool) (hnn : 0 ≤ assets.toRat),
      -- a canonical amount, or zero to claw back the holding
      assets.CanonicalOrZero → holderShares.ShareBalance →
      assets.toRat ≤ 9 * 10 ^ (15 + v.baseExponent) → holderShares.toRat ≤ v.toExact.sharesTotal →
      (v.clawback assets holderShares waive hnn).run ≠ .ok (.error .tecPATH_DRY) :=
  ⟨fun amount isDonation t hpos hc hty hsmall =>
      Vault.deposit_no_internal_proof v amount isDonation t hpos hc hty hsmall,
    fun amount waive t hpos => Vault.withdraw_no_internal_proof v amount waive t hpos,
    fun assets holderShares waive hnn =>
      Vault.Reachable.clawback_no_internal_proof v t0 hr assets holderShares waive hnn,
    fun amount isDonation t hpos hc hty hl =>
      Vault.Reachable.deposit_no_path_dry_proof v t0 hr amount isDonation t hpos hc hty hl,
    fun amount waive t hpos hc hassets hshares =>
      Vault.Reachable.withdraw_no_path_dry_proof v t0 hr amount waive t hpos hc hassets hshares,
    fun assets holderShares waive hnn hc hhs hl hhl =>
      Vault.Reachable.clawback_no_path_dry_proof v t0 hr assets holderShares waive hnn hc hl hhs hhl⟩

/-- Witness for `no_internal_errors`: on a reachable MPT vault of 2 units a deposit of `5000000000000000003` prices
`5000000000000000005` shares worth `5000000000000000005` and returns `tecINTERNAL`. -/
theorem Vault.Reachable.no_internal_errors_deposit_attained :
    ∃ (v : Vault) (t0 t : UInt32) (amount shares assets : STAmount) (hpos : 0 < amount.toRat),
      Vault.Reachable v t0 ∧ amount.Canonical ∧ amount.mNumericType = v.numericType ∧
      v.numericType.isIntegral = true ∧ amount.toRat = 5000000000000000003 ∧
      assetsToSharesDeposit v amount = .ok shares ∧ sharesToAssetsDeposit v shares = .ok assets ∧
      shares.toRat = 5000000000000000005 ∧ assets.toRat = 5000000000000000005 ∧
      (v.deposit amount false t hpos).run = .ok (.error .tecINTERNAL) :=
  Vault.deposit_internal_witness

/-- Witness for `no_internal_errors`: on a reachable scale-10 IOU vault of 10 assets and `10^11` shares a deposit of
`10^9`, past the Open limit, prices `10^19` shares and returns `tecPATH_DRY`. -/
theorem Vault.Reachable.no_internal_errors_deposit_path_dry_attained :
    ∃ (v : Vault) (t0 t : UInt32) (amount : STAmount) (hpos : 0 < amount.toRat),
      Vault.Reachable v t0 ∧ amount.Canonical ∧ amount.mNumericType = v.numericType ∧
      9 * 10 ^ (15 + v.baseExponent) < amount.toRat ∧
      (v.deposit amount false t hpos).run = .ok (.error .tecPATH_DRY) :=
  Vault.deposit_path_dry_witness

/-- Witness for `no_internal_errors`: on the same vault a withdrawal of `10^9`, past the Open limit, by a holder of
half the shares returns `tecPATH_DRY`. -/
theorem Vault.Reachable.no_internal_errors_withdraw_path_dry_attained :
    ∃ (v : Vault) (t0 t : UInt32) (amount : WithdrawAmount) (holderShares : STAmount) (waive : Bool)
      (hpos : 0 < amount.amount.toRat),
      Vault.Reachable v t0 ∧ amount.amount.Canonical ∧ amount.InAsset v.numericType ∧ holderShares.ShareBalance ∧
      (waive = true ↔ v.IsSoleShareholder holderShares) ∧ holderShares.toRat ≤ v.toExact.sharesTotal ∧
      (∃ assets, amount = .vaultAssets assets ∧ 9 * 10 ^ (15 + v.baseExponent) < assets.toRat) ∧
      (v.withdraw amount waive t hpos).run = .ok (.error .tecPATH_DRY) :=
  Vault.withdraw_path_dry_witness

/-- Witness for `no_internal_errors`: on the same vault a clawback of `10^9`, past the Open limit, from a holder of
half the shares returns `tecPATH_DRY`. -/
theorem Vault.Reachable.no_internal_errors_clawback_path_dry_attained :
    ∃ (v : Vault) (t0 : UInt32) (assets holderShares : STAmount) (waive : Bool) (hnn : 0 ≤ assets.toRat),
      Vault.Reachable v t0 ∧ assets.CanonicalOrZero ∧ assets.mNumericType = v.numericType ∧
      holderShares.ShareBalance ∧ (waive = true ↔ v.IsSoleShareholder holderShares) ∧
      holderShares.toRat ≤ v.toExact.sharesTotal ∧ 9 * 10 ^ (15 + v.baseExponent) < assets.toRat ∧
      (v.clawback assets holderShares waive hnn).run = .ok (.error .tecPATH_DRY) :=
  Vault.clawback_path_dry_witness

end XRPL.Model.SingleAssetVault
