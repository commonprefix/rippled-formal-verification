import XRPL.Properties.Vault.Defs
import XRPL.Properties.Vault.VaultDeposit
import XRPL.Model.Vault.VaultWithdraw
import XRPL.Model.Vault.VaultBurn
import XRPL.Model.Vault.VaultClawback
import XRPL.Properties.Vault.Common.WithdrawDefs
import XRPL.Properties.Vault.Common.DilutionProofs
import XRPL.Properties.Vault.Common.DilutionWitness
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

/-- A deposit cannot decrease per-share value by more than `1 - depositε`: the
upward charge rounding makes the depositor pay at least the issued shares'
worth, up to the interior rounding residue. -/
theorem LawfulVault.deposit_no_dilution (lv : LawfulVault) (amountDeposit : STAmount) (r : DepositResult)
    -- the starting vault is lawful
    (hcanon : amountDeposit.Canonical) -- the deposit amount is stored canonically
    (hpos : 0 < amountDeposit.toRat) -- the deposited amount is positive, the preflight guard
    -- the vault carries no unrealized loss (so `withdrawNav = assetsTotal`; the state every
    -- modeled operation preserves). Without it the 19-digit stored-total rounding of
    -- `assetsTotal` is unbounded relative to a tiny `withdrawNav` and one deposit can dilute far
    -- past `depositε`, so this hypothesis is necessary, not merely convenient.
    (hL : lv.toExact.lossUnrealized = 0)
    -- the taken amount does not underflow to the canonical zero (the `isZero = false`
    -- precondition class of `deposit_charge`; a deep fractional charge underflow issues shares
    -- for a zero charge and dilutes past `depositε`, so this is necessary, not convenient)
    (hcnz : r.amountDeposit'.isZero = false)
    (hSsz : (lv.toExact.sharesTotal : ℚ) + r.sharesIssued.toRat ≤ 2 ^ 63 - 1) -- share domain
    (hok : lv.deposit amountDeposit false = .ok r) (herr : r.error = none) :
    r.vault'.withdrawNav * (lv.toExact.sharesTotal : ℚ) ≥
      lv.withdrawNav * (r.vault'.toExact.sharesTotal : ℚ) * (1 - depositε) :=
  LawfulVault.deposit_no_dilution_proof lv amountDeposit r hcanon hpos hL hcnz hSsz hok herr

/-- Witness: the `1 - depositε` factor in `deposit_no_dilution` cannot be
dropped, a deposit exists that strictly decreases per-share value. -/
theorem LawfulVault.deposit_dilution_attained :
    ∃ (lv : LawfulVault) (amountDeposit : STAmount) (r : DepositResult),
      0 < amountDeposit.toRat ∧
      lv.deposit amountDeposit false = .ok r ∧ r.error = none ∧
      r.vault'.withdrawNav * (lv.toExact.sharesTotal : ℚ) <
        lv.withdrawNav * (r.vault'.toExact.sharesTotal : ℚ) :=
  deposit_dilution_witness

/-- A donation strictly increases per-share value: assets come in, the share
total does not move.

The strict increase splits on the donation amount's type. For a fractional amount
the vault's grid rounding (`roundToVaultExponent`) guarantees a surviving donation is
at least one grid step and stays visible in the sum, so `assetsTotal` strictly rises.
For an integral amount the `hint_dom` hypothesis restricts to the int64/native domain
where the add is exact (ULP = 1); it is necessary because a `LawfulVault` is weaker than
a reachable one and admits an integral `assetsTotal` so large (e.g. `10^30`) that its ULP
would round a unit donation away, leaving per-share value unchanged. The hypothesis is
vacuous for fractional amounts and satisfied by every reachable integral vault. -/
theorem LawfulVault.deposit_donation_no_dilution (lv : LawfulVault) (amountDeposit : STAmount) (r : DepositResult)
    -- the starting vault is lawful
    (hcanon : amountDeposit.Canonical) -- the deposit amount is stored canonically
    (hpos : 0 < amountDeposit.toRat) -- the deposited amount is positive, the preflight guard
    -- integer-domain bound for an integral donation: on an int64/native vault whose stored
    -- totals are whole numbers, the post-donation total stays in the int64 domain (exact add,
    -- ULP = 1). Vacuous for fractional amounts.
    (hint_dom : amountDeposit.integral = true →
      (lv.numericType = .int64 ∨ lv.numericType = .native) ∧
      amountDeposit.mNumericType = lv.numericType ∧
      lv.assetsTotal.toRat.den = 1 ∧ lv.assetsAvailable.toRat.den = 1 ∧
      lv.toExact.assetsTotal + amountDeposit.toRat ≤ 2 ^ 63 - 1)
    (hok : lv.deposit amountDeposit true = .ok r) (herr : r.error = none) :
    lv.withdrawNav < r.vault'.withdrawNav ∧
    r.vault'.toExact.sharesTotal = lv.toExact.sharesTotal :=
  LawfulVault.deposit_donation_no_dilution_proof lv amountDeposit r hcanon hpos hint_dom hok herr

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
theorem LawfulVault.withdraw_no_dilution (lv : LawfulVault) (amount : WithdrawAmount) (r : WithdrawResult)
    -- the starting vault is lawful
    -- the vault carries no unrealized loss (so `withdrawNav = assetsTotal`; the state every
    -- modeled operation preserves), as in `deposit_no_dilution`
    (hL : lv.toExact.lossUnrealized = 0)
    -- the payout does not underflow to the canonical zero (mirrors `deposit_no_dilution`'s `hcnz`)
    (hcnz : r.assets'.isZero = false)
    (hnn : 0 ≤ r.sharesBurned.toRat) -- a real withdrawal burns a nonnegative share count
    (hc : r.sharesBurned.Canonical) -- burned shares canonical, so their `toNumber` is value-exact
    (hSnt : r.sharesBurned.mNumericType = .int64) -- burned shares are the `int64` share amount
    -- near-final margin: at least half the shares remain to absorb the interior overpay, so the
    -- concentration on the remaining holders stays within `depositε` (necessary, not convenient:
    -- a near-total withdrawal concentrates the overpay and can leave the window)
    (hmargin : r.sharesBurned.toRat ≤ (lv.toExact.sharesTotal : ℚ) / 2)
    (hSfit : (lv.toExact.sharesTotal : ℚ) ≤ 2 ^ 63 - 1) -- share domain
    (hok : lv.withdraw amount false = .ok r) (herr : r.error = none) :
    r.vault'.withdrawNav * (lv.toExact.sharesTotal : ℚ) ≥
      lv.withdrawNav * (r.vault'.toExact.sharesTotal : ℚ) * (1 - depositε) :=
  LawfulVault.withdraw_no_dilution_proof lv amount r hL (LawfulVault.withdrawNavExact_of_zero lv false hL)
    hcnz hnn hc hSnt hmargin hSfit hok herr

/-- Witness: the `1 - depositε` factor in `withdraw_no_dilution` cannot be
dropped, a withdrawal exists that strictly decreases per-share value. -/
theorem LawfulVault.withdraw_dilution_attained :
    ∃ (lv : LawfulVault) (amount : WithdrawAmount) (r : WithdrawResult),
      lv.withdraw amount false = .ok r ∧ r.error = none ∧
      r.vault'.withdrawNav * (lv.toExact.sharesTotal : ℚ) <
        lv.withdrawNav * (r.vault'.toExact.sharesTotal : ℚ) :=
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
theorem LawfulVault.clawback_no_dilution (lv : LawfulVault) (assets holderShares : STAmount) (r : ClawbackResult)
    -- the starting vault is lawful
    -- the vault carries no unrealized loss (so `withdrawNav = assetsTotal`)
    (hL : lv.toExact.lossUnrealized = 0)
    (hc : assets.Canonical) -- the clawed-back amount is stored canonically
    -- the holder balance passed to the run is a stored integral MPT amount,
    -- value-exact and nonnegative (it carries the zero amount claw all arm)
    (hSic : holderShares.IntegralCanonical) (hSc : holderShares.Canonical)
    (hSnn : holderShares.negative = false)
    -- near-final margin: at least half the shares remain to absorb the interior overpay
    (hmargin : r.sharesDestroyed.toRat ≤ (lv.toExact.sharesTotal : ℚ) / 2)
    (hSfit : (lv.toExact.sharesTotal : ℚ) ≤ 2 ^ 63 - 1) -- share domain
    (hok : lv.clawback assets holderShares = .ok r) (herr : r.error = none) :
    r.vault'.withdrawNav * (lv.toExact.sharesTotal : ℚ) ≥
      lv.withdrawNav * (r.vault'.toExact.sharesTotal : ℚ) * (1 - depositε) :=
  LawfulVault.clawback_no_dilution_proof lv assets holderShares r hL
    (LawfulVault.withdrawNavExact_of_zero lv false hL) hc hSic hSc hSnn hmargin hSfit hok herr

/-- Witness: the `1 - depositε` factor in `clawback_no_dilution` cannot be
dropped, a clawback exists that strictly decreases per-share value. -/
theorem LawfulVault.clawback_dilution_attained :
    ∃ (lv : LawfulVault) (assets holderShares : STAmount) (r : ClawbackResult),
      lv.clawback assets holderShares = .ok r ∧ r.error = none ∧
      r.vault'.withdrawNav * (lv.toExact.sharesTotal : ℚ) <
        lv.withdrawNav * (r.vault'.toExact.sharesTotal : ℚ) :=
  clawback_dilution_witness

/-- Witness: the `1 - depositε` factor binds on the zero-amount arm of
`clawback_no_dilution` too, a claw-all run exists that destroys exactly the
holder's balance (a canonical nonnegative integral amount, the side conditions
of the theorem) and strictly decreases per-share value. -/
theorem LawfulVault.clawback_zero_dilution_attained :
    ∃ (lv : LawfulVault) (assets holderShares : STAmount) (r : ClawbackResult),
      assets.isZero = true ∧
      holderShares.IntegralCanonical ∧ holderShares.Canonical ∧
      holderShares.negative = false ∧
      lv.clawback assets holderShares = .ok r ∧ r.error = none ∧
      r.sharesDestroyed = holderShares ∧
      r.vault'.withdrawNav * (lv.toExact.sharesTotal : ℚ) <
        lv.withdrawNav * (r.vault'.toExact.sharesTotal : ℚ) :=
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
theorem LawfulVault.ReachableFromIn.no_dilution (lv : LawfulVault) (n : ℕ) (v : LawfulVault)
    (hwL : lv.toExact.lossUnrealized = 0)
    -- vault-only operations keep both asset fields identical (no lending); this record-level
    -- parity comes from `create`, is preserved by every step, and carries the
    -- `loss = 0` invariant forward through the compounding induction
    (hwAV : lv.assetsAvailable = lv.assetsTotal)
    (h : LawfulVault.ReachableFromIn lv v n) :
    v.withdrawNav * (lv.toExact.sharesTotal : ℚ) ≥
      lv.withdrawNav * (v.toExact.sharesTotal : ℚ) * (1 - depositε) ^ n :=
  LawfulVault.ReachableFromIn.no_dilution_proof lv n v hwL hwAV h

/-- Witness: dilution compounds, a history of more than one operation exists
whose total per-share value decrease is strict. -/
theorem LawfulVault.ReachableFromIn.dilution_attained :
    ∃ (lw u : LawfulVault) (n : ℕ),
      1 < n ∧ LawfulVault.ReachableFromIn lw u n ∧
      u.withdrawNav * (lw.toExact.sharesTotal : ℚ) <
        lw.withdrawNav * (u.toExact.sharesTotal : ℚ) :=
  dilution_attained_witness

end XRPL.Model.SingleAssetVault
