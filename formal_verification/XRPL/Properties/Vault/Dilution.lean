import XRPL.Properties.Vault.Defs
import XRPL.Properties.Vault.VaultDeposit
import XRPL.Model.Vault.VaultWithdraw
import XRPL.Model.Vault.VaultBurn
import XRPL.Model.Vault.VaultClawback
import XRPL.Properties.Vault.Common.WithdrawDefs
import XRPL.Properties.Vault.Common.DilutionProofs
import XRPL.Properties.Vault.Common.DilutionWitness
import XRPL.Properties.Vault.Lawful
import XRPL.Properties.Vault.Unchanged
import XRPL.Properties.Vault.Common.ReachableDefs

/-! # Operations do not dilute shareholders (except the rounding error)

Per-share value is `withdrawNav / sharesTotal`. Each theorem states, in
cross-multiplied form to avoid division, that an operation cannot decrease it
by more than the factor `1 - depositε`. The residue comes from the interior
`Number` stages of the exchange computations rounding to nearest while only the
final conversion is directed, and from the stored totals rounding at 19
digits. A donation has no exchange computation and increases per-share value
strictly. Along a history of `n` operations the factor compounds to
`(1 - depositε) ^ n`. -/

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol

variable (v : Vault)

/-- A deposit cannot decrease per-share value by more than `1 - depositε`: the
upward charge rounding makes the depositor pay at least the issued shares'
worth, up to the interior rounding residue. -/
theorem Vault.deposit_no_dilution (amountDeposit : STAmount) (r : DepositResult)
    (hv : v.Lawful) -- the starting vault is lawful
    (hcanon : amountDeposit.Canonical) -- the deposit amount is stored canonically
    (hpos : 0 < amountDeposit.toRat) -- the deposited amount is positive, the preflight guard
    -- the vault carries no unrealized loss (so `withdrawNav = assetsTotal`; the state every
    -- modeled operation preserves). Without it the 19-digit stored-total rounding of
    -- `assetsTotal` is unbounded relative to a tiny `withdrawNav` and one deposit can dilute far
    -- past `depositε`, so this hypothesis is necessary, not merely convenient.
    (hL : v.lossUnrealized.toRat = 0)
    -- the taken amount does not underflow to the canonical zero (the `isZero = false`
    -- precondition class of `deposit_charge`; a deep fractional charge underflow issues shares
    -- for a zero charge and dilutes past `depositε`, so this is necessary, not convenient)
    (hcnz : r.amountDeposit'.isZero = false)
    (hSsz : v.sharesTotal.toRat + r.sharesIssued.toRat ≤ 2 ^ 63 - 1) -- share domain
    (hok : v.deposit amountDeposit false = .ok r) (herr : r.error = none) :
    r.vault'.withdrawNav * v.sharesTotal.toRat ≥
      v.withdrawNav * r.vault'.sharesTotal.toRat * (1 - depositε) :=
  Vault.deposit_no_dilution_proof v amountDeposit r hv hcanon hpos hL hcnz hSsz hok herr

/-- Witness: the `1 - depositε` factor in `deposit_no_dilution` cannot be
dropped, a deposit exists that strictly decreases per-share value. -/
theorem Vault.deposit_dilution_attained :
    ∃ (v : Vault) (amountDeposit : STAmount) (r : DepositResult),
      v.Lawful ∧ 0 < amountDeposit.toRat ∧
      v.deposit amountDeposit false = .ok r ∧ r.error = none ∧
      r.vault'.withdrawNav * v.sharesTotal.toRat <
        v.withdrawNav * r.vault'.sharesTotal.toRat :=
  deposit_dilution_witness

/-- A donation strictly increases per-share value: assets come in, the share
total does not move.

The strict increase splits on the donation amount's type. For a fractional amount
the vault's grid rounding (`roundToVaultExponent`) guarantees a surviving donation is
at least one grid step and stays visible in the sum, so `assetsTotal` strictly rises.
For an integral amount the `hint_dom` hypothesis restricts to the int64/native domain
where the add is exact (ULP = 1); it is necessary because `Vault.Lawful` is weaker than
reachability and admits an integral `assetsTotal` so large (e.g. `10^30`) that its ULP
would round a unit donation away, leaving per-share value unchanged. The hypothesis is
vacuous for fractional amounts and satisfied by every reachable integral vault. -/
theorem Vault.deposit_donation_no_dilution (amountDeposit : STAmount) (r : DepositResult)
    (hv : v.Lawful) -- the starting vault is lawful
    (hcanon : amountDeposit.Canonical) -- the deposit amount is stored canonically
    (hpos : 0 < amountDeposit.toRat) -- the deposited amount is positive, the preflight guard
    -- integer-domain bound for an integral donation: on an int64/native vault whose stored
    -- totals are whole numbers, the post-donation total stays in the int64 domain (exact add,
    -- ULP = 1). Vacuous for fractional amounts.
    (hint_dom : amountDeposit.integral = true →
      (v.numericType = .int64 ∨ v.numericType = .native) ∧
      amountDeposit.mNumericType = v.numericType ∧
      v.assetsTotal.toRat.den = 1 ∧ v.assetsAvailable.toRat.den = 1 ∧
      v.assetsTotal.toRat + amountDeposit.toRat ≤ 2 ^ 63 - 1)
    (hok : v.deposit amountDeposit true = .ok r) (herr : r.error = none) :
    v.withdrawNav < r.vault'.withdrawNav ∧
    r.vault'.sharesTotal.toRat = v.sharesTotal.toRat :=
  Vault.deposit_donation_no_dilution_proof v amountDeposit r hv hcanon hpos hint_dom hok herr

/-- A withdrawal cannot decrease per-share value by more than `1 - depositε`:
the downward payout rounding pays the leaver at most the burned shares' worth,
up to the interior rounding residue. Loss-waiving withdrawals are excluded,
they price the payout without the unrealized loss.

Two exits. The exact-final withdrawal (the burn equals the whole share total)
zeroes the vault, so `sharesTotal' = 0` and both sides are `0`; the margin
hypothesis is not consulted there. The non-final withdrawal reduces to the
per-share monotonicity core: the payout `p` is at most the burned shares' worth
`A·x/S` times `1 + 12/(2^63-3)` (the raw `mul`/`div` pricing stage), and the
stored `assetsTotal` drops to `assetsTotal - p` within the raw `6/(2^63-3)`
subtraction stage, whose sum is under `depositε`. The near-final margin
`sharesBurned ≤ sharesTotal/2` keeps at least half the shares in the vault to
absorb the interior overpay `~A·x·(12/(2^63-3))/S`, so the concentration on the
remaining holders stays within `depositε`. Without it a near-total withdrawal
concentrates the tiny overpay onto the few remaining shares and can exceed the
`depositε` window. -/
theorem Vault.withdraw_no_dilution (amount : WithdrawAmount) (r : WithdrawResult)
    (hv : v.Lawful) -- the starting vault is lawful
    -- the vault carries no unrealized loss (so `withdrawNav = assetsTotal`; the state every
    -- modeled operation preserves), as in `deposit_no_dilution`
    (hL : v.lossUnrealized.toRat = 0)
    -- the payout does not underflow to the canonical zero (mirrors `deposit_no_dilution`'s `hcnz`)
    (hcnz : r.assets'.isZero = false)
    (hnn : 0 ≤ r.sharesBurned.toRat) -- a real withdrawal burns a nonnegative share count
    (hc : r.sharesBurned.Canonical) -- burned shares canonical, so their `toNumber` is value-exact
    (hSnt : r.sharesBurned.mNumericType = .int64) -- burned shares are the `int64` share amount
    -- near-final margin: at least half the shares remain to absorb the interior overpay, so the
    -- concentration on the remaining holders stays within `depositε` (necessary, not convenient:
    -- a near-total withdrawal concentrates the overpay and can leave the window)
    (hmargin : r.sharesBurned.toRat ≤ v.sharesTotal.toRat / 2)
    (hSfit : v.sharesTotal.toRat ≤ 2 ^ 63 - 1) -- share domain
    (hok : v.withdraw amount false = .ok r) (herr : r.error = none) :
    r.vault'.withdrawNav * v.sharesTotal.toRat ≥
      v.withdrawNav * r.vault'.sharesTotal.toRat * (1 - depositε) :=
  Vault.withdraw_no_dilution_proof v amount r hv hL (Vault.withdrawNavExact_of_zero v hv false hL)
    hcnz hnn hc hSnt hmargin hSfit hok herr

/-- Witness: the `1 - depositε` factor in `withdraw_no_dilution` cannot be
dropped, a withdrawal exists that strictly decreases per-share value. -/
theorem Vault.withdraw_dilution_attained :
    ∃ (v : Vault) (amount : WithdrawAmount) (r : WithdrawResult),
      v.Lawful ∧
      v.withdraw amount false = .ok r ∧ r.error = none ∧
      r.vault'.withdrawNav * v.sharesTotal.toRat <
        v.withdrawNav * r.vault'.sharesTotal.toRat :=
  withdraw_dilution_witness

/-- A clawback cannot decrease per-share value by more than `1 - depositε`: it
prices its recovery with the same `sharesToAssetsWithdraw` pipeline as a
withdrawal (`idealAssetsClawback = idealAssetsWithdraw false`), so the argument is
identical to `withdraw_no_dilution`: the recovery is at most the destroyed shares'
worth times `1 + 12/(2^63-3)`, the stored `assetsTotal` drops within the raw
`6/(2^63-3)` subtraction stage, and the near-final margin `sharesDestroyed ≤
sharesTotal/2` keeps enough shares to absorb the interior overpay. A clawback is
always partial (no final exit). A zero amount claws the holder's entire share
balance and is covered: the holder balance side conditions make the destroyed
shares a nonzero canonical integer, so the margin keeps the share total positive. -/
theorem Vault.clawback_no_dilution (assets holderShares : STAmount) (r : ClawbackResult)
    (hv : v.Lawful) -- the starting vault is lawful
    -- the vault carries no unrealized loss (so `withdrawNav = assetsTotal`)
    (hL : v.lossUnrealized.toRat = 0)
    (hc : assets.Canonical) -- the clawed-back amount is stored canonically
    -- the holder balance passed to the run is a stored integral MPT amount,
    -- value-exact and nonnegative (it carries the zero amount claw all arm)
    (hSic : holderShares.IntegralCanonical) (hSc : holderShares.Canonical)
    (hSnn : holderShares.negative = false)
    -- near-final margin: at least half the shares remain to absorb the interior overpay
    (hmargin : r.sharesDestroyed.toRat ≤ v.sharesTotal.toRat / 2)
    (hSfit : v.sharesTotal.toRat ≤ 2 ^ 63 - 1) -- share domain
    (hok : v.clawback assets holderShares = .ok r) (herr : r.error = none) :
    r.vault'.withdrawNav * v.sharesTotal.toRat ≥
      v.withdrawNav * r.vault'.sharesTotal.toRat * (1 - depositε) :=
  Vault.clawback_no_dilution_proof v assets holderShares r hv hL
    (Vault.withdrawNavExact_of_zero v hv false hL) hc hSic hSc hSnn hmargin hSfit hok herr

/-- Witness: the `1 - depositε` factor in `clawback_no_dilution` cannot be
dropped, a clawback exists that strictly decreases per-share value. -/
theorem Vault.clawback_dilution_attained :
    ∃ (v : Vault) (assets holderShares : STAmount) (r : ClawbackResult),
      v.Lawful ∧
      v.clawback assets holderShares = .ok r ∧ r.error = none ∧
      r.vault'.withdrawNav * v.sharesTotal.toRat <
        v.withdrawNav * r.vault'.sharesTotal.toRat :=
  clawback_dilution_witness

/-- Witness: the `1 - depositε` factor binds on the zero-amount arm of
`clawback_no_dilution` too, a claw-all run exists that destroys exactly the
holder's balance (a canonical nonnegative integral amount, the side conditions
of the theorem) and strictly decreases per-share value. -/
theorem Vault.clawback_zero_dilution_attained :
    ∃ (v : Vault) (assets holderShares : STAmount) (r : ClawbackResult),
      v.Lawful ∧ assets.isZero = true ∧
      holderShares.IntegralCanonical ∧ holderShares.Canonical ∧
      holderShares.negative = false ∧
      v.clawback assets holderShares = .ok r ∧ r.error = none ∧
      r.sharesDestroyed = holderShares ∧
      r.vault'.withdrawNav * v.sharesTotal.toRat <
        v.withdrawNav * r.vault'.sharesTotal.toRat :=
  clawback_zero_dilution_witness

/-- Along any margin-respecting history of `n` operations from a lawful vault with no
unrealized loss, per-share value decreases by at most the compounded factor
`(1 - depositε) ^ n`.

The `loss = 0` base hypothesis is an induction invariant (every modeled operation
preserves it, and each step's `no_dilution` needs it). The near-final margins live in
the withdraw/clawback constructors of `ReachableFromIn`, so every step satisfies its
per-op `no_dilution`/strict-increase theorem. The proof is the compounding induction:
`refl` is the base `(1 - depositε)^0 = 1`; each step composes the prior factor with its
single-op factor via `deposit_no_dilution` (#1), the donation strict-increase (#3),
`withdraw_no_dilution` (#4), `clawback_no_dilution` (#6), and the `burnShares` share-only
decrease, carrying `Lawful` and `loss = 0` forward by the field preservation the success
reductions expose. -/
theorem Vault.ReachableFromIn.no_dilution (w : Vault) (n : ℕ)
    (hw : w.Lawful)
    (hwL : w.lossUnrealized.toRat = 0)
    -- vault-only operations keep both asset fields identical (no lending), the same record-level
    -- parity `Vault.Reachable` gets from `create`; it is preserved by every step and is needed to
    -- carry `Lawful` forward through the compounding induction (each `*_lawful` step consumes it)
    (hwAV : w.assetsAvailable = w.assetsTotal)
    (h : Vault.ReachableFromIn w v n) :
    v.withdrawNav * w.sharesTotal.toRat ≥
      w.withdrawNav * v.sharesTotal.toRat * (1 - depositε) ^ n :=
  Vault.ReachableFromIn.no_dilution_proof v w n hw hwL hwAV h

/-- Witness: dilution compounds, a history of more than one operation exists
whose total per-share value decrease is strict. -/
theorem Vault.ReachableFromIn.dilution_attained :
    ∃ (w u : Vault) (n : ℕ),
      w.Lawful ∧ 1 < n ∧ Vault.ReachableFromIn w u n ∧
      u.withdrawNav * w.sharesTotal.toRat <
        w.withdrawNav * u.sharesTotal.toRat :=
  dilution_attained_witness

end XRPL.Model.SingleAssetVault
