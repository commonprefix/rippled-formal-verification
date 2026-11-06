import XRPL.Properties.Vault.Common.WithdrawDefs
import XRPL.Model.Vault.VaultDeposit
import XRPL.Model.Vault.VaultWithdraw
import XRPL.Properties.Vault.Common.Create
import XRPL.Model.Vault.VaultBurn
import XRPL.Model.Vault.VaultClawback
import XRPL.Model.Vault.VaultSet

/-! # Reachability inductives

`Vault.Reachable` collects the states reachable from a `Vault.create` under the vault transactions,
with the parent ledger close time of the last one. Each step assumes only facts C++ guarantees: canonical
amounts of the right asset, canonical share balances, minting within the MPT maximum, a holder redeeming
at most its own shares, and only the sole shareholder waiving the unrealized loss. -/

namespace XRPL.Model.Protocol

/-- A holder's share balance: a canonical, nonnegative MPT amount. -/
structure STAmount.ShareBalance (s : STAmount) : Prop where
  int64 : s.mNumericType = .int64
  canonical : s.Canonical
  nonneg : s.negative = false

end XRPL.Model.Protocol

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol

/-- The amount a withdrawal names is in the vault's asset or in its shares. -/
def WithdrawAmount.InAsset (amount : WithdrawAmount) (nt : NumericType) : Prop :=
  match amount with
  | .vaultAssets assets => assets.mNumericType = nt
  | .vaultShares shares => shares.mNumericType = .int64

/-- C++ `isSoleShareholder`: the holder owns every outstanding share. -/
def Vault.IsSoleShareholder (v : Vault) (holderShares : STAmount) : Prop :=
  0 < (v.toExact.sharesTotal : ℚ) ∧ holderShares.toRat = v.toExact.sharesTotal

/-- The state a vault-only history keeps: nothing is lent out, and the cash is a whole number of
base units within the Open-zone limit, stored exactly. -/
structure Vault.OpenZone (v : Vault) : Prop where
  assetsDeployed : v.assetsDeployed = Number.zero
  lossUnrealized : v.lossUnrealized = Number.zero
  yieldUnrealized : v.yieldUnrealized = Number.zero
  cash : ∃ k : ℕ, k ≤ 9 * 10 ^ 15 ∧ v.assetsAvailable.toRat = (k : ℚ) * (10 : ℚ) ^ v.baseExponent
  cashExact : STAmount.isRounded v.numericType v.assetsAvailable = false

/-- Lawful states reachable from `Vault.create` under all transactions, with the parent ledger close time of the last
one. The transactions return `Vault`, so every reachable state is lawful by construction. -/
inductive Vault.Reachable : Vault → UInt32 → Prop where
  | create (scale : Option UInt8) (assetsMaximum : Option Number) (schedule : Option VaultSchedule)
      (earlyExitFeeRate : Option TenthBips32) (ownerCanBlockDeposit : Bool) (nt : NumericType)
      (t : UInt32) (v : Vault) :
      Vault.canCreate scale assetsMaximum schedule t nt = .ok .tesSUCCESS →
      Vault.create scale assetsMaximum schedule earlyExitFeeRate ownerCanBlockDeposit nt = .ok v →
      Vault.Reachable v t
  | deposit (v : Vault) (t t' : UInt32) (amount : STAmount) (isDonation : Bool)
      (r : VaultWithAmounts) :
      Vault.Reachable v t → t ≤ t' →
      amount.Canonical → amount.mNumericType = v.numericType →
      (hpos : 0 < amount.toRat) → (v.deposit amount isDonation t' hpos).run = .ok (.ok r) →
      (v.toExact.sharesTotal : ℚ) + r.shares.toRat ≤ 2 ^ 63 - 1 → -- the MPT maximum
      Vault.Reachable r.vault' t'
  | withdraw (v : Vault) (t t' : UInt32) (amount : WithdrawAmount) (holderShares : STAmount)
      (waive : Bool) (r : VaultWithAmounts) :
      Vault.Reachable v t → t ≤ t' →
      amount.amount.Canonical → amount.InAsset v.numericType → holderShares.ShareBalance →
      (waive = true ↔ v.IsSoleShareholder holderShares) →
      (hpos : 0 < amount.amount.toRat) → (v.withdraw amount waive t' hpos).run = .ok (.ok r) →
      r.shares.toRat ≤ holderShares.toRat →
      Vault.Reachable r.vault' t'
  | clawback (v : Vault) (t t' : UInt32) (assets holderShares : STAmount) (waive : Bool)
      (r : VaultWithAmounts) :
      Vault.Reachable v t → t ≤ t' →
      assets.CanonicalOrZero → assets.mNumericType = v.numericType → holderShares.ShareBalance →
      (waive = true ↔ v.IsSoleShareholder holderShares) →
      (hnn : 0 ≤ assets.toRat) → (v.clawback assets holderShares waive hnn).run = .ok (.ok r) →
      r.shares.toRat ≤ holderShares.toRat →
      Vault.Reachable r.vault' t'
  | burnShares (v : Vault) (t t' : UInt32) (amount holderShares sharesTotalAmount : STAmount)
      (v' : Vault) :
      Vault.Reachable v t → t ≤ t' →
      holderShares.ShareBalance →
      (v.canBurnShares amount holderShares).run = .ok (.ok sharesTotalAmount) →
      (v.burnShares holderShares).run = .ok (.ok v') →
      Vault.Reachable v' t'
  | update (v : Vault) (t t' : UInt32) (assetsMaximum : Option Number)
      (blockDeposit unblockDeposit : Bool) (v' : Vault) :
      Vault.Reachable v t → t ≤ t' →
      v.canVaultUpdate assetsMaximum blockDeposit unblockDeposit = .ok .tesSUCCESS →
      v.update assetsMaximum blockDeposit unblockDeposit = .ok v' →
      Vault.Reachable v' t'

/-- `u` results from `w` by `n` successful transactions, the last at parent close time `t`. With `whole`, deposits and
exits move a whole base-unit worth. -/
inductive Vault.ReachableFromIn (whole : Bool) : Vault → UInt32 → Vault → ℕ → Prop where
  | refl (w : Vault) (t : UInt32) : Vault.ReachableFromIn whole w t w 0
  | deposit (w u : Vault) (t t' : UInt32) (n : ℕ) (amount : STAmount) (isDonation : Bool)
      (r : VaultWithAmounts) :
      Vault.ReachableFromIn whole w t u n → t ≤ t' →
      amount.Canonical → amount.mNumericType = u.numericType →
      (hpos : 0 < amount.toRat) → (u.deposit amount isDonation t' hpos).run = .ok (.ok r) →
      (u.toExact.sharesTotal : ℚ) + r.shares.toRat ≤ 2 ^ 63 - 1 → -- the MPT maximum
      (whole = true → ∃ k : ℤ, u.idealChargeDeposit r.shares.toRat = k * 10 ^ u.baseExponent) →
      Vault.ReachableFromIn whole w t' r.vault' (n + 1)
  | withdraw (w u : Vault) (t t' : UInt32) (n : ℕ) (amount : WithdrawAmount)
      (holderShares : STAmount) (waive : Bool) (r : VaultWithAmounts) :
      Vault.ReachableFromIn whole w t u n → t ≤ t' →
      amount.amount.Canonical → amount.InAsset u.numericType → holderShares.ShareBalance →
      (waive = true ↔ u.IsSoleShareholder holderShares) →
      (hpos : 0 < amount.amount.toRat) → (u.withdraw amount waive t' hpos).run = .ok (.ok r) →
      r.shares.toRat ≤ holderShares.toRat →
      r.shares.toRat < (u.toExact.sharesTotal : ℚ) → -- shares remain
      (whole = true → ∃ k : ℤ, u.idealAssetsWithdraw waive r.shares.toRat = k * 10 ^ u.baseExponent) →
      Vault.ReachableFromIn whole w t' r.vault' (n + 1)
  | clawback (w u : Vault) (t t' : UInt32) (n : ℕ) (assets holderShares : STAmount) (waive : Bool)
      (r : VaultWithAmounts) :
      Vault.ReachableFromIn whole w t u n → t ≤ t' →
      assets.CanonicalOrZero → assets.mNumericType = u.numericType → holderShares.ShareBalance →
      (waive = true ↔ u.IsSoleShareholder holderShares) →
      (hnn : 0 ≤ assets.toRat) → (u.clawback assets holderShares waive hnn).run = .ok (.ok r) →
      r.shares.toRat ≤ holderShares.toRat →
      r.shares.toRat < (u.toExact.sharesTotal : ℚ) → -- shares remain
      (whole = true → ∃ k : ℤ, u.idealAssetsWithdraw waive r.shares.toRat = k * 10 ^ u.baseExponent) →
      Vault.ReachableFromIn whole w t' r.vault' (n + 1)
  | burnShares (w u : Vault) (t t' : UInt32) (n : ℕ)
      (amount holderShares sharesTotalAmount : STAmount) (u' : Vault) :
      Vault.ReachableFromIn whole w t u n → t ≤ t' →
      holderShares.ShareBalance →
      (u.canBurnShares amount holderShares).run = .ok (.ok sharesTotalAmount) →
      (u.burnShares holderShares).run = .ok (.ok u') →
      Vault.ReachableFromIn whole w t' u' (n + 1)
  | update (w u : Vault) (t t' : UInt32) (n : ℕ) (assetsMaximum : Option Number)
      (blockDeposit unblockDeposit : Bool) (u' : Vault) :
      Vault.ReachableFromIn whole w t u n → t ≤ t' →
      u.canVaultUpdate assetsMaximum blockDeposit unblockDeposit = .ok .tesSUCCESS →
      u.update assetsMaximum blockDeposit unblockDeposit = .ok u' →
      Vault.ReachableFromIn whole w t' u' (n + 1)

/-- Withdrawals from time `t` on that drain the vault to zero shares. `done`: no shares are left.
`step`: one successful non-loss-waiving withdrawal at a time `t'` no earlier than `t`, then the rest. -/
inductive CanEmpty : Vault → UInt32 → Prop where
  | done (v : Vault) (t : UInt32) : v.toExact.sharesTotal = 0 → CanEmpty v t
  | step (v : Vault) (t t' : UInt32) (amount : WithdrawAmount) (r : VaultWithAmounts) :
      t ≤ t' → (hpos : 0 < amount.amount.toRat) → (v.withdraw amount false t' hpos).run = .ok (.ok r) →
      CanEmpty r.vault' t' → CanEmpty v t

end XRPL.Model.SingleAssetVault
