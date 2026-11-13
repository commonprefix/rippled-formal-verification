import XRPL.Properties.Vault.Common.ReachableDefs

/-! # Sums over a sequence of vault transactions

`Vault.Flows w t u t' deposited withdrawn recovered created redeemed destroyed` says that `u` at time `t'` results from
`w` at time `t` by vault transactions, each with the facts C++ guarantees (the steps of `Vault.Reachable`), and adds up
what they move: the assets deposited, withdrawn and clawed back, and the shares created, redeemed and destroyed. -/

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol

/-- `u` at `t'` results from `w` at `t` by vault transactions that move the summed assets and shares. -/
inductive Vault.Flows (w : Vault) (t : UInt32) :
    Vault → UInt32 → (deposited withdrawn recovered created redeemed destroyed : ℚ) → Prop where
  | refl : Vault.Flows w t w t 0 0 0 0 0 0
  | deposit (u : Vault) (t₁ t' : UInt32) (D W C SC SR SD : ℚ) (amount : STAmount) (isDonation : Bool)
      (r : VaultWithAmounts) :
      Vault.Flows w t u t₁ D W C SC SR SD → t₁ ≤ t' →
      amount.Canonical → amount.mNumericType = u.numericType →
      (hpos : 0 < amount.toRat) → (u.deposit amount isDonation t' hpos).run = .ok (.ok r) →
      (u.toExact.sharesTotal : ℚ) + r.shares.toRat ≤ 2 ^ 63 - 1 → -- the MPT maximum
      Vault.Flows w t r.vault' t' (D + r.assets.toRat) W C (SC + r.shares.toRat) SR SD
  | withdraw (u : Vault) (t₁ t' : UInt32) (D W C SC SR SD : ℚ) (amount : WithdrawAmount)
      (holderShares : STAmount) (waive : Bool) (r : VaultWithAmounts) :
      Vault.Flows w t u t₁ D W C SC SR SD → t₁ ≤ t' →
      amount.amount.Canonical → amount.InAsset u.numericType → holderShares.ShareBalance →
      (waive = true ↔ u.IsSoleShareholder holderShares) →
      (hpos : 0 < amount.amount.toRat) → (u.withdraw amount waive t' hpos).run = .ok (.ok r) →
      r.shares.toRat ≤ holderShares.toRat →
      Vault.Flows w t r.vault' t' D (W + r.assets.toRat) C SC (SR + r.shares.toRat) SD
  | clawback (u : Vault) (t₁ t' : UInt32) (D W C SC SR SD : ℚ) (assets holderShares : STAmount) (waive : Bool)
      (r : VaultWithAmounts) :
      Vault.Flows w t u t₁ D W C SC SR SD → t₁ ≤ t' →
      assets.CanonicalOrZero → assets.mNumericType = u.numericType → holderShares.ShareBalance →
      (waive = true ↔ u.IsSoleShareholder holderShares) →
      (hnn : 0 ≤ assets.toRat) → (u.clawback assets holderShares waive hnn).run = .ok (.ok r) →
      r.shares.toRat ≤ holderShares.toRat →
      Vault.Flows w t r.vault' t' D W (C + r.assets.toRat) SC SR (SD + r.shares.toRat)
  | burnShares (u : Vault) (t₁ t' : UInt32) (D W C SC SR SD : ℚ)
      (amount holderShares sharesTotalAmount : STAmount) (u' : Vault) :
      Vault.Flows w t u t₁ D W C SC SR SD → t₁ ≤ t' →
      holderShares.ShareBalance →
      (u.canBurnShares amount holderShares).run = .ok (.ok sharesTotalAmount) →
      (u.burnShares holderShares).run = .ok (.ok u') →
      Vault.Flows w t u' t' D W C SC SR (SD + holderShares.toRat)
  | update (u : Vault) (t₁ t' : UInt32) (D W C SC SR SD : ℚ) (assetsMaximum : Option Number)
      (blockDeposit : Option Bool) (u' : Vault) :
      Vault.Flows w t u t₁ D W C SC SR SD → t₁ ≤ t' →
      u.canVaultUpdate assetsMaximum blockDeposit = .ok .tesSUCCESS →
      u.update assetsMaximum blockDeposit = .ok u' →
      Vault.Flows w t u' t' D W C SC SR SD

/-- Transactions from a reachable vault lead to a reachable vault. -/
lemma Vault.Flows.reachable {w : Vault} {t : UInt32} (hr : Vault.Reachable w t) {u : Vault} {t' : UInt32}
    {D W C SC SR SD : ℚ} (h : Vault.Flows w t u t' D W C SC SR SD) : Vault.Reachable u t' := by
  induction h with
  | refl => exact hr
  | deposit u t₁ t' _ _ _ _ _ _ amount isDonation r _ hle hc hty hpos hok hmint ih =>
    exact .deposit u t₁ t' amount isDonation r ih hle hc hty hpos hok hmint
  | withdraw u t₁ t' _ _ _ _ _ _ amount holderShares waive r _ hle hc hty hhs hsole hpos hok hheld ih =>
    exact .withdraw u t₁ t' amount holderShares waive r ih hle hc hty hhs hsole hpos hok hheld
  | clawback u t₁ t' _ _ _ _ _ _ assets holderShares waive r _ hle hc hty hhs hsole hnn hok hheld ih =>
    exact .clawback u t₁ t' assets holderShares waive r ih hle hc hty hhs hsole hnn hok hheld
  | burnShares u t₁ t' _ _ _ _ _ _ amount holderShares sharesTotalAmount u' _ hle hhs hcan hok ih =>
    exact .burnShares u t₁ t' amount holderShares sharesTotalAmount u' ih hle hhs hcan hok
  | update u t₁ t' _ _ _ _ _ _ assetsMaximum blockDeposit u' _ hle hcan hok ih =>
    exact .update u t₁ t' assetsMaximum blockDeposit u' ih hle hcan hok

end XRPL.Model.SingleAssetVault
