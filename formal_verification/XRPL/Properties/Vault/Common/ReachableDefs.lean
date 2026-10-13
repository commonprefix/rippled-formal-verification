import XRPL.Properties.Vault.Common.WithdrawDefs
import XRPL.Model.Vault.VaultDeposit
import XRPL.Model.Vault.VaultWithdraw
import XRPL.Properties.Vault.Common.Create
import XRPL.Model.Vault.VaultBurn
import XRPL.Model.Vault.VaultClawback

/-! # Reachability inductives

The two inductive families the reachability and dilution proof trees induct on.
`Vault.Reachable` (used in `Reachable.lean`) collects the states reachable from a
`Vault.create_lawful` under the vault operations; `Vault.ReachableFromIn` (used in
`Dilution.lean`) additionally tracks the source vault, the operation count and the
accumulated per-share dilution budget, and
restricts to margin-respecting, non-loss-waiving histories. They live here, apart
from the headline files, so the induction proofs can be extracted into `Common`
without an import cycle. -/

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol

/-- Lawful states reachable from `Vault.create_lawful` under all operations. The ops
return `Vault`, so every reachable state is lawful by construction -/
inductive Vault.Reachable : Vault → Prop where
  | create (nt : NumericType) (scale : UInt8) (assetsMaximum : Option Number)
      (hmax_norm : ∀ m ∈ assetsMaximum, m.isNormalized)
      (hmax_pos : ∀ m ∈ assetsMaximum, 0 < m.toRat)
      (hscale_int : nt.isIntegral = true → scale = 0) (hscale_le : scale.toNat ≤ 18) :
      Vault.Reachable (Vault.create_lawful nt scale assetsMaximum hmax_norm hmax_pos hscale_int hscale_le)
  | deposit (v : Vault) (amount : STAmount) (isDonation : Bool) (r : DepositResult) :
      Vault.Reachable v → (hpos : 0 < amount.toRat) → v.deposit amount isDonation hpos = .ok r →
      amount.Canonical → -- the deposit amount is a stored-canonical user input
      (v.toExact.sharesTotal : ℚ) + r.sharesIssued.toRat ≤ 2 ^ 63 - 1 → -- share domain
      Vault.Reachable r.vault'
  | withdraw (v : Vault) (amount : WithdrawAmount) (waive : Bool) (r : WithdrawResult) :
      Vault.Reachable v → (hpos : 0 < amount.amount.toRat) → v.withdraw amount waive hpos = .ok r →
      r.sharesBurned.IntegralCanonical → -- the burned shares are canonical int64
      r.sharesBurned.mNumericType = .int64 →
      r.sharesBurned.negative = false →
      r.sharesBurned.toRat ≤ (v.toExact.sharesTotal : ℚ) → -- within the share total
      (v.toExact.sharesTotal : ℚ) ≤ 2 ^ 63 - 1 → -- share domain
      Vault.Reachable r.vault'
  | clawback (v : Vault) (assets holderShares : STAmount) (r : ClawbackResult) :
      Vault.Reachable v → (hnn : 0 ≤ assets.toRat) → v.clawback assets holderShares hnn = .ok r →
      assets.Canonical → -- the clawback amount is a stored-canonical user input
      holderShares.IntegralCanonical → -- the holder balance is a stored integral MPT amount
      holderShares.Canonical → -- and value-exact through toNumber
      holderShares.negative = false → -- a balance is nonnegative
      r.sharesDestroyed.toRat < (v.toExact.sharesTotal : ℚ) → -- strictly partial
      (v.toExact.sharesTotal : ℚ) ≤ 2 ^ 63 - 1 → -- share domain
      Vault.Reachable r.vault'
  | burnShares (v : Vault) (sharesDestroyed sharesTotalAmount : STAmount) (v' : Vault) :
      Vault.Reachable v →
      v.canBurnShares = .ok (.assets sharesTotalAmount) → -- the burn permission guard passed
      sharesDestroyed.IntegralCanonical → -- stored as a plain integral amount
      sharesDestroyed.negative = false →
      sharesDestroyed.toRat ≤ sharesTotalAmount.toRat → -- a holder cannot burn more than exists
      (v.toExact.sharesTotal : ℚ) ≤ 2 ^ 63 - 1 → -- share domain
      v.burnShares sharesDestroyed = .ok v' →
      Vault.Reachable v'

/-- `Vault.ReachableFromIn w v n D` holds when `v` results from `w` by `n`
successful operations, with `D` the sum over the steps of each step's
absolute dilution budget divided by the share total after it: `3/2·10^e` for a deposit
(`e` its post-deposit grid exponent), half a unit of the payout (recovery) for a
withdrawal (clawback), `0` for a burn. Loss-waiving withdrawals are excluded, and
withdrawals and clawbacks keep at least half the shares, matching
`withdraw_no_dilution` and `clawback_no_dilution`. -/
inductive Vault.ReachableFromIn : Vault → Vault → ℕ → ℚ → Prop where
  | refl (w : Vault) : Vault.ReachableFromIn w w 0 0
  | deposit (w u : Vault) (n : ℕ) (D : ℚ) (amount : STAmount) (isDonation : Bool)
      (r : DepositResult) (e : ℤ) :
      Vault.ReachableFromIn w u n D → (hpos : 0 < amount.toRat) →
      u.deposit amount isDonation hpos = .ok r → r.error = none →
      amount.Canonical → -- the deposit amount is a stored-canonical user input
      (u.toExact.sharesTotal : ℚ) + r.sharesIssued.toRat ≤ 2 ^ 63 - 1 → -- share domain
      postSumExponent u.assetsTotal amount = .ok e → -- the post-deposit grid exponent
      Vault.ReachableFromIn w r.vault' (n + 1)
        (D + 3 / 2 * (10 : ℚ) ^ e / (r.vault'.toExact.sharesTotal : ℚ))
  | withdraw (w u : Vault) (n : ℕ) (D : ℚ) (amount : WithdrawAmount) (r : WithdrawResult) :
      Vault.ReachableFromIn w u n D → (hpos : 0 < amount.amount.toRat) →
      u.withdraw amount false hpos = .ok r → r.error = none →
      0 ≤ r.sharesBurned.toRat → -- a real withdrawal burns a nonnegative share count
      r.sharesBurned.Canonical → -- value-exact through `toNumber`
      r.sharesBurned.mNumericType = .int64 → -- the `int64` share amount
      -- near-final margin: at least half the shares remain
      r.sharesBurned.toRat ≤ (u.toExact.sharesTotal : ℚ) / 2 →
      (u.toExact.sharesTotal : ℚ) ≤ 2 ^ 63 - 1 → -- share domain
      Vault.ReachableFromIn w r.vault' (n + 1)
        (D + 1 / 2 * (10 : ℚ) ^ r.assets'.exponent / (r.vault'.toExact.sharesTotal : ℚ))
  | clawback (w u : Vault) (n : ℕ) (D : ℚ) (assets holderShares : STAmount)
      (r : ClawbackResult) :
      Vault.ReachableFromIn w u n D → (hnn : 0 ≤ assets.toRat) →
      u.clawback assets holderShares hnn = .ok r → r.error = none →
      assets.Canonical → -- the clawed-back amount is a stored-canonical user input
      holderShares.IntegralCanonical → -- the holder balance is a stored integral MPT amount
      holderShares.Canonical → -- and value-exact through toNumber
      holderShares.negative = false → -- a balance is nonnegative
      -- near-final margin: at least half the shares remain
      r.sharesDestroyed.toRat ≤ (u.toExact.sharesTotal : ℚ) / 2 →
      (u.toExact.sharesTotal : ℚ) ≤ 2 ^ 63 - 1 → -- share domain
      Vault.ReachableFromIn w r.vault' (n + 1)
        (D + 1 / 2 * (10 : ℚ) ^ r.assetsRecovered.exponent / (r.vault'.toExact.sharesTotal : ℚ))
  | burnShares (w u : Vault) (n : ℕ) (D : ℚ) (sharesDestroyed sharesTotalAmount : STAmount)
      (u' : Vault) :
      Vault.ReachableFromIn w u n D →
      u.canBurnShares = .ok (.assets sharesTotalAmount) → -- the burn permission guard passed
      u.burnShares sharesDestroyed = .ok u' →
      Vault.ReachableFromIn w u' (n + 1) D

end XRPL.Model.SingleAssetVault
