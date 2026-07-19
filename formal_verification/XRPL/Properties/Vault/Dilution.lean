import XRPL.Properties.Vault.Defs
import XRPL.Properties.Vault.VaultDeposit
import XRPL.Model.Vault.VaultWithdraw
import XRPL.Model.Vault.VaultBurn
import XRPL.Model.Vault.VaultClawback

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

/-- Net asset value backing the shares for withdrawal:
`assetsTotal - interestUnrealized - lossUnrealized`. -/
def Vault.withdrawNav (v : Vault) : ℚ :=
  v.toExact.assetsTotal - v.toExact.interestUnrealized - v.toExact.lossUnrealized

/-- `Vault.ReachableFromIn w v n` holds when `v` results from `w` by `n`
operations that ran without a throw. Loss-waiving withdrawals are excluded,
matching `withdraw_no_dilution`. -/
inductive Vault.ReachableFromIn : Vault → Vault → ℕ → Prop where
  | refl (w : Vault) : Vault.ReachableFromIn w w 0
  | deposit (w u : Vault) (n : ℕ) (amount : STAmount) (isDonation : Bool)
      (r : DepositResult) :
      Vault.ReachableFromIn w u n → u.deposit amount isDonation = .ok r →
      Vault.ReachableFromIn w r.vault' (n + 1)
  | withdraw (w u : Vault) (n : ℕ) (amount : WithdrawAmount) (r : WithdrawResult) :
      Vault.ReachableFromIn w u n → u.withdraw amount false = .ok r →
      Vault.ReachableFromIn w r.vault' (n + 1)
  | clawback (w u : Vault) (n : ℕ) (assets : STAmount) (r : ClawbackResult) :
      Vault.ReachableFromIn w u n → u.clawback assets = .ok r →
      Vault.ReachableFromIn w r.vault' (n + 1)
  | burnShares (w u : Vault) (n : ℕ) (sharesDestroyed sharesTotalAmount : STAmount)
      (u' : Vault) :
      Vault.ReachableFromIn w u n →
      u.canBurnShares = .ok (.assets sharesTotalAmount) → -- the burn permission guard passed
      sharesDestroyed.toRat ≤ sharesTotalAmount.toRat → -- a holder cannot burn more than exists
      0 ≤ sharesDestroyed.toRat →
      sharesDestroyed.toRat.den = 1 → -- shares are an MPT amount, a whole number
      u.burnShares sharesDestroyed = .ok u' →
      Vault.ReachableFromIn w u' (n + 1)

variable (v : Vault)

/-- A deposit cannot decrease per-share value by more than `1 - depositε`: the
upward charge rounding makes the depositor pay at least the issued shares'
worth, up to the interior rounding residue. -/
theorem Vault.deposit_no_dilution (amountDeposit : STAmount) (r : DepositResult)
    (hv : v.Lawful) -- the starting vault is lawful
    (hpos : 0 < amountDeposit.toRat) -- the deposited amount is positive, the preflight guard
    (hok : v.deposit amountDeposit false = .ok r) (herr : r.error = none) :
    r.vault'.withdrawNav * (v.toExact.sharesTotal : ℚ) ≥
      v.withdrawNav * (r.vault'.toExact.sharesTotal : ℚ) * (1 - depositε) := sorry

/-- Witness: the `1 - depositε` factor in `deposit_no_dilution` cannot be
dropped, a deposit exists that strictly decreases per-share value. -/
theorem Vault.deposit_dilution_attained :
    ∃ (v : Vault) (amountDeposit : STAmount) (r : DepositResult),
      v.Lawful ∧ 0 < amountDeposit.toRat ∧
      v.deposit amountDeposit false = .ok r ∧ r.error = none ∧
      r.vault'.withdrawNav * (v.toExact.sharesTotal : ℚ) <
        v.withdrawNav * (r.vault'.toExact.sharesTotal : ℚ) := sorry

/-- A donation strictly increases per-share value: assets come in, the share
total does not move. -/
theorem Vault.deposit_donation_no_dilution (amountDeposit : STAmount) (r : DepositResult)
    (hv : v.Lawful) -- the starting vault is lawful
    (hpos : 0 < amountDeposit.toRat) -- the deposited amount is positive, the preflight guard
    (hok : v.deposit amountDeposit true = .ok r) (herr : r.error = none) :
    v.withdrawNav < r.vault'.withdrawNav ∧
    r.vault'.toExact.sharesTotal = v.toExact.sharesTotal := sorry

/-- A withdrawal cannot decrease per-share value by more than `1 - depositε`:
the downward payout rounding pays the leaver at most the burned shares' worth,
up to the interior rounding residue. Loss-waiving withdrawals are excluded,
they price the payout without the unrealized loss. -/
theorem Vault.withdraw_no_dilution (amount : WithdrawAmount) (r : WithdrawResult)
    (hv : v.Lawful) -- the starting vault is lawful
    (hok : v.withdraw amount false = .ok r) (herr : r.error = none) :
    r.vault'.withdrawNav * (v.toExact.sharesTotal : ℚ) ≥
      v.withdrawNav * (r.vault'.toExact.sharesTotal : ℚ) * (1 - depositε) := sorry

/-- Witness: the `1 - depositε` factor in `withdraw_no_dilution` cannot be
dropped, a withdrawal exists that strictly decreases per-share value. -/
theorem Vault.withdraw_dilution_attained :
    ∃ (v : Vault) (amount : WithdrawAmount) (r : WithdrawResult),
      v.Lawful ∧
      v.withdraw amount false = .ok r ∧ r.error = none ∧
      r.vault'.withdrawNav * (v.toExact.sharesTotal : ℚ) <
        v.withdrawNav * (r.vault'.toExact.sharesTotal : ℚ) := sorry

/-- A clawback cannot decrease per-share value by more than `1 - depositε`: it
prices with the same helpers as a withdrawal. -/
theorem Vault.clawback_no_dilution (assets : STAmount) (r : ClawbackResult)
    (hv : v.Lawful) -- the starting vault is lawful
    (hok : v.clawback assets = .ok r) (herr : r.error = none) :
    r.vault'.withdrawNav * (v.toExact.sharesTotal : ℚ) ≥
      v.withdrawNav * (r.vault'.toExact.sharesTotal : ℚ) * (1 - depositε) := sorry

/-- Witness: the `1 - depositε` factor in `clawback_no_dilution` cannot be
dropped, a clawback exists that strictly decreases per-share value. -/
theorem Vault.clawback_dilution_attained :
    ∃ (v : Vault) (assets : STAmount) (r : ClawbackResult),
      v.Lawful ∧
      v.clawback assets = .ok r ∧ r.error = none ∧
      r.vault'.withdrawNav * (v.toExact.sharesTotal : ℚ) <
        v.withdrawNav * (r.vault'.toExact.sharesTotal : ℚ) := sorry

/-- Along any history of `n` operations from a lawful vault, per-share value
decreases by at most the compounded factor `(1 - depositε) ^ n`. -/
theorem Vault.ReachableFromIn.no_dilution (w : Vault) (n : ℕ)
    (hw : w.Lawful) (h : Vault.ReachableFromIn w v n) :
    v.withdrawNav * (w.toExact.sharesTotal : ℚ) ≥
      w.withdrawNav * (v.toExact.sharesTotal : ℚ) * (1 - depositε) ^ n := sorry

/-- Witness: dilution compounds, a history of more than one operation exists
whose total per-share value decrease is strict. -/
theorem Vault.ReachableFromIn.dilution_attained :
    ∃ (w u : Vault) (n : ℕ),
      w.Lawful ∧ 1 < n ∧ Vault.ReachableFromIn w u n ∧
      u.withdrawNav * (w.toExact.sharesTotal : ℚ) <
        w.withdrawNav * (u.toExact.sharesTotal : ℚ) := sorry

end XRPL.Model.SingleAssetVault
