import XRPL.Properties.Vault.Defs
import XRPL.Properties.Vault.VaultDeposit
import XRPL.Model.Vault.VaultWithdraw
import XRPL.Model.Vault.VaultBurn
import XRPL.Model.Vault.VaultClawback
import XRPL.Properties.Vault.Common.WithdrawDefs
import XRPL.Properties.Vault.Common.ReachableDefs
import XRPL.Properties.Vault.Proofs.Dilution.Deposit
import XRPL.Properties.Vault.Proofs.Dilution.Clawback
import XRPL.Properties.Vault.Proofs.DilutionWitness
import XRPL.Properties.Vault.Proofs.DilutionReach
import XRPL.Properties.Vault.Proofs.DilutionReachWitness

/-! # Operations do not dilute shareholders (except the rounding error)

Per-share value is `withdrawNav / sharesTotal`. Each theorem states, in
cross-multiplied form to avoid division, that an operation cannot decrease it by more
than a tiny relative factor plus an absolute rounding term per share, a few units in
the last digits:

* a deposit: `3/2` steps of the post-deposit grid `10^e` (half a step from the
  `to_nearest` charge pricing, one from the clamp that snaps the charge onto the grid
  while the shares priced before it are kept), with relative factor `1 - 3·10⁻¹⁸`;
* a withdrawal or a clawback that leaves at least half the shares: half a unit of the
  payout's (recovery's) last digit, the `to_nearest` pricing overshoot, with relative
  factor `1 - depositε`;
* a donation: none, per-share value strictly rises.

Along a margin-respecting history the relative factors compound and the absolute
terms add up, each divided by the share total after its step. -/

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol

/-- A deposit cannot decrease per-share value by more than `3·10⁻¹⁸` relatively plus
`3/2` steps of the post-deposit grid `10^e` per existing share: half a step from the
`to_nearest` charge pricing and one from the sum clamp, which snaps the charge down onto
the grid while the shares priced before it are kept. The relative residue comes from the
`mul`/`div` stages of the charge pricing (`2·10⁻¹⁸`) and the stored total's sum
(`10⁻¹⁸`); it cannot be dropped (`deposit_no_dilution_relative_attained`). -/
theorem Vault.deposit_no_dilution (v : Vault) (amountDeposit : STAmount) (r : DepositResult)
    -- the starting vault is lawful
    (hcanon : amountDeposit.Canonical) -- the deposit amount is stored canonically
    (hpos : 0 < amountDeposit.toRat) -- the deposited amount is positive, the preflight guard
    -- the vault carries no unrealized loss (so `withdrawNav = assetsTotal`; the state every
    -- modeled operation preserves). Without it the 19-digit stored-total rounding of
    -- `assetsTotal` is unbounded relative to a tiny `withdrawNav`, so this hypothesis is
    -- necessary, not merely convenient.
    (hL : v.toExact.lossUnrealized = 0)
    (hSsz : (v.toExact.sharesTotal : ℚ) + r.sharesIssued.toRat ≤ 2 ^ 63 - 1) -- share domain
    (hok : v.deposit amountDeposit false hpos = .ok r) (herr : r.error = none) :
    ∀ e, postSumExponent v.assetsTotal amountDeposit = .ok e →
      r.vault'.withdrawNav * (v.toExact.sharesTotal : ℚ) ≥
        v.withdrawNav * (r.vault'.toExact.sharesTotal : ℚ) * (1 - 3 / 10 ^ 18) -
          3 / 2 * (10 : ℚ) ^ e * (v.toExact.sharesTotal : ℚ) :=
  Vault.deposit_no_dilution_proof v amountDeposit r hcanon hpos hL hSsz hok herr

/-- Witness: the grid term of `deposit_no_dilution` is attained to within `2·10⁻¹⁵` of a
step. Assets `0.9999999999999995`, one share, deposit `10^15 + 1`: the charge `10^15 - 1`
buys shares worth `10^15 + 0.4999999999999995`. -/
theorem Vault.deposit_no_dilution_grid_attained :
    ∃ (v : Vault) (amountDeposit : STAmount) (hpos : 0 < amountDeposit.toRat)
      (r : DepositResult) (e : ℤ),
      amountDeposit.Canonical ∧ v.toExact.lossUnrealized = 0 ∧
      (v.toExact.sharesTotal : ℚ) + r.sharesIssued.toRat ≤ 2 ^ 63 - 1 ∧
      v.deposit amountDeposit false hpos = .ok r ∧ r.error = none ∧
      postSumExponent v.assetsTotal amountDeposit = .ok e ∧
      r.vault'.withdrawNav * (v.toExact.sharesTotal : ℚ) <
        v.withdrawNav * (r.vault'.toExact.sharesTotal : ℚ) -
          (3 / 2 - 2 / 10 ^ 15) * (10 : ℚ) ^ e * (v.toExact.sharesTotal : ℚ) :=
  Vault.deposit_no_dilution_grid_witness

/-- Witness: the relative term of `deposit_no_dilution` cannot be dropped. Assets
`4677880426214914.973`, `8916544631` shares, deposit `4727117026339798`: the clamp drops
almost a whole step of the total's off-grid digits, the pricing rounds down by almost half
a step, and the `Number` stages add `0.003` of a step, for a dilution of `1.5029` steps. -/
theorem Vault.deposit_no_dilution_relative_attained :
    ∃ (v : Vault) (amountDeposit : STAmount) (hpos : 0 < amountDeposit.toRat)
      (r : DepositResult) (e : ℤ),
      amountDeposit.Canonical ∧ v.toExact.lossUnrealized = 0 ∧
      (v.toExact.sharesTotal : ℚ) + r.sharesIssued.toRat ≤ 2 ^ 63 - 1 ∧
      v.deposit amountDeposit false hpos = .ok r ∧ r.error = none ∧
      postSumExponent v.assetsTotal amountDeposit = .ok e ∧
      r.vault'.withdrawNav * (v.toExact.sharesTotal : ℚ) <
        v.withdrawNav * (r.vault'.toExact.sharesTotal : ℚ) -
          3 / 2 * (10 : ℚ) ^ e * (v.toExact.sharesTotal : ℚ) :=
  Vault.deposit_no_dilution_relative_witness

/-- A donation strictly increases per-share value: assets come in, the share
total does not move.

The strict increase splits on the donation amount's type. For a fractional amount
the vault's grid rounding (`roundToVaultExponent`) guarantees a surviving donation is
at least one grid step and stays visible in the sum, so `assetsTotal` strictly rises.
For an integral amount the `hint_dom` hypothesis restricts to the int64/native domain
where the add is exact (ULP = 1); it is necessary because a `Vault` is weaker than
a reachable one and admits an integral `assetsTotal` so large (e.g. `10^30`) that its ULP
would round a unit donation away, leaving per-share value unchanged. The hypothesis is
vacuous for fractional amounts and satisfied by every reachable integral vault. -/
theorem Vault.deposit_donation_no_dilution (v : Vault) (amountDeposit : STAmount) (r : DepositResult)
    -- the starting vault is lawful
    (hcanon : amountDeposit.Canonical) -- the deposit amount is stored canonically
    (hpos : 0 < amountDeposit.toRat) -- the deposited amount is positive, the preflight guard
    -- integer-domain bound for an integral donation: on an int64/native vault whose stored
    -- totals are whole numbers, the post-donation total stays in the int64 domain (exact add,
    -- ULP = 1). Vacuous for fractional amounts.
    (hint_dom : amountDeposit.integral = true →
      (v.numericType = .int64 ∨ v.numericType = .native) ∧
      amountDeposit.mNumericType = v.numericType ∧
      v.assetsTotal.toRat.den = 1 ∧ v.assetsAvailable.toRat.den = 1 ∧
      v.toExact.assetsTotal + amountDeposit.toRat ≤ 2 ^ 63 - 1)
    (hok : v.deposit amountDeposit true hpos = .ok r) (herr : r.error = none) :
    v.withdrawNav < r.vault'.withdrawNav ∧
    r.vault'.toExact.sharesTotal = v.toExact.sharesTotal :=
  Vault.deposit_donation_no_dilution_proof v amountDeposit r hcanon hpos hint_dom hok herr

/-- A withdrawal that leaves at least half the shares cannot decrease per-share value by
more than `depositε` relatively plus half a unit of the payout's last digit per share:
the `to_nearest` pricing can pay the leaver up to half a unit more than the burned shares'
worth `A·x/S` (times `1 + depositε`), which the remaining holders absorb; the clamp only
lowers the payout. Loss-waiving withdrawals are excluded, they price the payout without
the unrealized loss.

The exact-final withdrawal zeroes the vault, so the left side is `0` and the right side
at most `0`. The
non-final one drops the stored totals by exactly the payout and the burned shares, and
the margin `sharesBurned ≤ sharesTotal/2` makes the relative overpay `depositε·A·x/S`
fit under `depositε` of the remaining value. Without it the bound fails: a near-total
withdrawal from an `int64` vault dilutes by more than three half units per share. -/
theorem Vault.withdraw_no_dilution (v : Vault) (amount : WithdrawAmount) (r : WithdrawResult)
    -- the starting vault is lawful
    -- the vault carries no unrealized loss (so `withdrawNav = assetsTotal`; the state every
    -- modeled operation preserves), as in `deposit_no_dilution`
    (hL : v.toExact.lossUnrealized = 0)
    (hnn : 0 ≤ r.sharesBurned.toRat) -- a real withdrawal burns a nonnegative share count
    (hc : r.sharesBurned.Canonical) -- burned shares canonical, so their `toNumber` is value-exact
    (hSnt : r.sharesBurned.mNumericType = .int64) -- burned shares are the `int64` share amount
    -- near-final margin: at least half the shares remain to absorb the relative overpay
    -- (necessary, not convenient: a near-total withdrawal leaves the bound)
    (hmargin : r.sharesBurned.toRat ≤ (v.toExact.sharesTotal : ℚ) / 2)
    (hSfit : (v.toExact.sharesTotal : ℚ) ≤ 2 ^ 63 - 1) -- share domain
    (hpos : 0 < amount.amount.toRat)
    (hok : v.withdraw amount false hpos = .ok r) (herr : r.error = none) :
    r.vault'.withdrawNav * (v.toExact.sharesTotal : ℚ) ≥
      v.withdrawNav * (r.vault'.toExact.sharesTotal : ℚ) * (1 - depositε) -
        1 / 2 * (10 : ℚ) ^ r.assets'.exponent * (v.toExact.sharesTotal : ℚ) :=
  Vault.withdraw_no_dilution_proof v amount r hL hnn hc hSnt hmargin hSfit hpos hok herr

/-- Witness: the half-unit term of `withdraw_no_dilution` is attained to within `10⁻¹⁵`
of it. An `int64` vault with 3 assets and 4 shares redeems 2 shares worth `1.5` for `2`. -/
theorem Vault.withdraw_no_dilution_half_ulp_attained :
    ∃ (v : Vault) (amount : WithdrawAmount) (hpos : 0 < amount.amount.toRat) (r : WithdrawResult),
      v.toExact.lossUnrealized = 0 ∧ 0 ≤ r.sharesBurned.toRat ∧
      r.sharesBurned.Canonical ∧ r.sharesBurned.mNumericType = .int64 ∧
      r.sharesBurned.toRat ≤ (v.toExact.sharesTotal : ℚ) / 2 ∧
      (v.toExact.sharesTotal : ℚ) ≤ 2 ^ 63 - 1 ∧
      v.withdraw amount false hpos = .ok r ∧ r.error = none ∧
      r.vault'.withdrawNav * (v.toExact.sharesTotal : ℚ) <
        v.withdrawNav * (r.vault'.toExact.sharesTotal : ℚ) * (1 - depositε) -
          (1 - 1 / 10 ^ 15) * (1 / 2 * (10 : ℚ) ^ r.assets'.exponent) *
            (v.toExact.sharesTotal : ℚ) :=
  Vault.withdraw_no_dilution_half_ulp_witness

/-- Witness: the relative term of `withdraw_no_dilution` cannot be dropped. On an `int64`
vault near `2^61` the `Number` pricing stages overpay by more than the half unit. -/
theorem Vault.withdraw_no_dilution_relative_attained :
    ∃ (v : Vault) (amount : WithdrawAmount) (hpos : 0 < amount.amount.toRat) (r : WithdrawResult),
      v.toExact.lossUnrealized = 0 ∧ 0 ≤ r.sharesBurned.toRat ∧
      r.sharesBurned.Canonical ∧ r.sharesBurned.mNumericType = .int64 ∧
      r.sharesBurned.toRat ≤ (v.toExact.sharesTotal : ℚ) / 2 ∧
      (v.toExact.sharesTotal : ℚ) ≤ 2 ^ 63 - 1 ∧
      v.withdraw amount false hpos = .ok r ∧ r.error = none ∧
      r.vault'.withdrawNav * (v.toExact.sharesTotal : ℚ) <
        v.withdrawNav * (r.vault'.toExact.sharesTotal : ℚ) -
          1 / 2 * (10 : ℚ) ^ r.assets'.exponent * (v.toExact.sharesTotal : ℚ) :=
  Vault.withdraw_no_dilution_relative_witness

/-- A clawback that leaves at least half the shares cannot decrease per-share value by
more than `depositε` relatively plus half a unit of the recovery's last digit per share:
it prices its recovery with the same `sharesToAssetsWithdraw` pipeline as a withdrawal
(`idealAssetsClawback = idealAssetsWithdraw false`), so the argument is that of
`withdraw_no_dilution`. A clawback is always partial (no final exit). A zero amount claws
the holder's entire share balance and is covered: the holder balance side conditions make
the destroyed shares a canonical integer, priced and clamped like any other. -/
theorem Vault.clawback_no_dilution (v : Vault) (assets holderShares : STAmount) (r : ClawbackResult)
    -- the starting vault is lawful
    -- the vault carries no unrealized loss (so `withdrawNav = assetsTotal`)
    (hL : v.toExact.lossUnrealized = 0)
    (hc : assets.Canonical) -- the clawed-back amount is stored canonically
    -- the holder balance passed to the run is a stored integral MPT amount,
    -- value-exact and nonnegative (it carries the zero amount claw all arm)
    (hSic : holderShares.IntegralCanonical) (hSc : holderShares.Canonical)
    (hSnn : holderShares.negative = false)
    -- near-final margin: at least half the shares remain to absorb the relative overpay
    (hmargin : r.sharesDestroyed.toRat ≤ (v.toExact.sharesTotal : ℚ) / 2)
    (hSfit : (v.toExact.sharesTotal : ℚ) ≤ 2 ^ 63 - 1) -- share domain
    (hnn : 0 ≤ assets.toRat)
    (hok : v.clawback assets holderShares hnn = .ok r) (herr : r.error = none) :
    r.vault'.withdrawNav * (v.toExact.sharesTotal : ℚ) ≥
      v.withdrawNav * (r.vault'.toExact.sharesTotal : ℚ) * (1 - depositε) -
        1 / 2 * (10 : ℚ) ^ r.assetsRecovered.exponent * (v.toExact.sharesTotal : ℚ) :=
  Vault.clawback_no_dilution_proof v assets holderShares r hL hc hSic hSc hSnn hmargin hSfit
    hnn hok herr

/-- Witness: the half-unit term of `clawback_no_dilution` is attained to within `10⁻¹⁵`
of it. An `int64` vault with 3 assets and 4 shares claws back 2 assets: 2 shares worth
`1.5` recover `2`. -/
theorem Vault.clawback_no_dilution_half_ulp_attained :
    ∃ (v : Vault) (assets holderShares : STAmount) (hnn : 0 ≤ assets.toRat) (r : ClawbackResult),
      v.toExact.lossUnrealized = 0 ∧ assets.Canonical ∧
      holderShares.IntegralCanonical ∧ holderShares.Canonical ∧ holderShares.negative = false ∧
      r.sharesDestroyed.toRat ≤ (v.toExact.sharesTotal : ℚ) / 2 ∧
      (v.toExact.sharesTotal : ℚ) ≤ 2 ^ 63 - 1 ∧
      v.clawback assets holderShares hnn = .ok r ∧ r.error = none ∧
      r.vault'.withdrawNav * (v.toExact.sharesTotal : ℚ) <
        v.withdrawNav * (r.vault'.toExact.sharesTotal : ℚ) * (1 - depositε) -
          (1 - 1 / 10 ^ 15) * (1 / 2 * (10 : ℚ) ^ r.assetsRecovered.exponent) *
            (v.toExact.sharesTotal : ℚ) :=
  Vault.clawback_no_dilution_half_ulp_witness

/-- Witness: the relative term of `clawback_no_dilution` cannot be dropped. On an `int64`
vault near `2^61` the `Number` pricing stages over-recover by more than the half unit. -/
theorem Vault.clawback_no_dilution_relative_attained :
    ∃ (v : Vault) (assets holderShares : STAmount) (hnn : 0 ≤ assets.toRat) (r : ClawbackResult),
      v.toExact.lossUnrealized = 0 ∧ assets.Canonical ∧
      holderShares.IntegralCanonical ∧ holderShares.Canonical ∧ holderShares.negative = false ∧
      r.sharesDestroyed.toRat ≤ (v.toExact.sharesTotal : ℚ) / 2 ∧
      (v.toExact.sharesTotal : ℚ) ≤ 2 ^ 63 - 1 ∧
      v.clawback assets holderShares hnn = .ok r ∧ r.error = none ∧
      r.vault'.withdrawNav * (v.toExact.sharesTotal : ℚ) <
        v.withdrawNav * (r.vault'.toExact.sharesTotal : ℚ) -
          1 / 2 * (10 : ℚ) ^ r.assetsRecovered.exponent * (v.toExact.sharesTotal : ℚ) :=
  Vault.clawback_no_dilution_relative_witness

/-- Witness: the half-unit term binds on the zero-amount arm too. An `int64` vault with 3
assets and 8 shares claws all of a 4-share holding, worth `1.5`, recovering `2`. -/
theorem Vault.clawback_no_dilution_zero_half_ulp_attained :
    ∃ (v : Vault) (assets holderShares : STAmount) (hnn : 0 ≤ assets.toRat) (r : ClawbackResult),
      v.toExact.lossUnrealized = 0 ∧ assets.Canonical ∧
      holderShares.IntegralCanonical ∧ holderShares.Canonical ∧ holderShares.negative = false ∧
      assets.isZero = true ∧ r.sharesDestroyed = holderShares ∧
      r.sharesDestroyed.toRat ≤ (v.toExact.sharesTotal : ℚ) / 2 ∧
      (v.toExact.sharesTotal : ℚ) ≤ 2 ^ 63 - 1 ∧
      v.clawback assets holderShares hnn = .ok r ∧ r.error = none ∧
      r.vault'.withdrawNav * (v.toExact.sharesTotal : ℚ) <
        v.withdrawNav * (r.vault'.toExact.sharesTotal : ℚ) * (1 - depositε) -
          (1 - 1 / 10 ^ 15) * (1 / 2 * (10 : ℚ) ^ r.assetsRecovered.exponent) *
            (v.toExact.sharesTotal : ℚ) :=
  Vault.clawback_no_dilution_zero_half_ulp_witness

/-- Along any successful, margin-respecting history of `n` operations from a vault with no
unrealized loss, per-share value (`withdrawNav / sharesTotal`, `0` on an empty vault) is at
least the starting one times `(1 - depositε) ^ n`, less the budget `D` that
`ReachableFromIn` accumulates: each step's absolute dilution term (`3/2·10^e` for a
deposit, half a unit of the payout or recovery for a withdrawal or clawback, `0` for a
burn) divided by the share total after the step.

The relative factors compound and the per-share absolute terms add up. An empty vault has
per-share value `0`, so a deposit into one dilutes no one, and a burn only runs on an
asset-less vault. The `loss = 0` hypothesis is an induction invariant: no step changes
`lossUnrealized`. -/
theorem Vault.ReachableFromIn.no_dilution (v : Vault) (n : ℕ) (D : ℚ) (w : Vault)
    (hwL : v.toExact.lossUnrealized = 0)
    (h : Vault.ReachableFromIn v w n D) :
    w.withdrawNav / (w.toExact.sharesTotal : ℚ) ≥
      v.withdrawNav / (v.toExact.sharesTotal : ℚ) * (1 - depositε) ^ n - D :=
  Vault.ReachableFromIn.no_dilution_proof v n D w hwL h

/-- Witness: the accumulated budget of `ReachableFromIn.no_dilution` is attained to within
`10⁻¹⁵` of it. An `int64` vault with 5 assets and 20 shares redeems 6 shares, then 7 of the
remaining 14, each worth `1.5` and paid `2`: per-share value falls `1/4 → 3/14 → 1/7`, by
exactly the budget `1/2/14 + 1/2/7 = 3/28`. -/
theorem Vault.ReachableFromIn.dilution_attained :
    ∃ (lw u : Vault) (n : ℕ) (D : ℚ),
      1 < n ∧ lw.toExact.lossUnrealized = 0 ∧ Vault.ReachableFromIn lw u n D ∧
      u.withdrawNav / (u.toExact.sharesTotal : ℚ) <
        lw.withdrawNav / (lw.toExact.sharesTotal : ℚ) * (1 - depositε) ^ n -
          (1 - 1 / 10 ^ 15) * D :=
  Vault.ReachableFromIn.dilution_witness

end XRPL.Model.SingleAssetVault
