import XRPL.Properties.Vault.Defs
import XRPL.Properties.Vault.VaultDeposit
import XRPL.Model.Vault.VaultWithdraw
import XRPL.Properties.Vault.Common.RoundtripProofs

/-! # Depositing and redeeming returns the taken amount

In exact arithmetic the round trip is the identity: a deposit at the NAV rate
does not change the rate, so the issued shares are worth exactly the taken
amount, and redeeming them immediately pays it back. Everything else is
rounding, and the directed conversions make the error asymmetric: the charge
rounds up and the payout rounds down, so the round trip can never profit
beyond the stage error, and loses at most the rounding budget. -/

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol

variable (v : Vault)

/-- Depositing and immediately redeeming the issued shares returns the taken
amount up to rounding: never more than the stage error above it, and at most
the rounding budget below it. From an empty vault the redemption is the final
withdrawal and pays the charge back exactly.

The loss conjunct carries one ULP from each directed conversion. The payout's
downward `ofNumber` snap contributes `10 ^ assets'.exponent`; the charge's
upward `ofNumber` snap contributes `10 ^ amountDeposit'.exponent`, a genuinely
separate term because when `assets' < amountDeposit'` (the loss regime) the
charge sits in the same or a higher decade, so its ULP can exceed the payout's
by up to 10× and cannot be folded into it. Both are tight (coefficient one), the
raw three-stage composition (`19 + 6 + 12` over `2^63-3 ≈ 3.7·10^-18`) fitting
strictly inside the `2·depositε` relative budget. The loss bound is stated for a
nonzero payout: a payout that underflows to the canonical zero (a sub-grid share
worth) can lose up to one whole grid unit, which no relative-plus-ULP bound
covers, exactly as the per-op siblings gate their shortfall on `isZero = false`. -/
theorem Vault.deposit_withdraw_roundtrip (amountDeposit : STAmount)
    (r₁ : DepositResult) (r₂ : WithdrawResult)
    (hv : v.Lawful) -- the starting vault is lawful
    -- no unrealized loss, so the pricing is exact on both sides
    (hL : v.lossUnrealized.toRat = 0)
    (hpos : 0 < amountDeposit.toRat) -- the deposited amount is positive, the preflight guard
    (hcanon : amountDeposit.Canonical) -- the deposit amount is stored canonically
    (hAV : v.assetsAvailable = v.assetsTotal) -- nothing is lent out (no-lending parity)
    -- the taken amount is stored canonically and is nonnegative
    (hDc : r₁.amountDeposit'.ExactCanonical)
    (hDnn : 0 ≤ r₁.amountDeposit'.toRat)
    -- the post-deposit share total stays in the int64 domain
    (hSsz : v.sharesTotal.toRat + r₁.sharesIssued.toRat ≤ 2 ^ 63 - 1)
    (hok₁ : v.deposit amountDeposit false = .ok r₁) (herr₁ : r₁.error = none)
    -- the depositor redeems exactly the issued shares from the updated vault
    (hok₂ : r₁.vault'.withdraw (.vaultShares r₁.sharesIssued) false = .ok r₂)
    (herr₂ : r₂.error = none) :
    -- no profit beyond the stage error
    r₂.assets'.toRat ≤ r₁.amountDeposit'.toRat * (1 + 2 * depositε) ∧
    -- for a nonzero payout, the loss is at most the relative stage budget plus one
    -- ULP of the payout and one ULP of the charge (both directed snaps)
    (r₂.assets'.isZero = false →
      r₁.amountDeposit'.toRat - r₂.assets'.toRat ≤
        r₁.amountDeposit'.toRat * (2 * depositε)
          + (10 : ℚ) ^ r₂.assets'.exponent + (10 : ℚ) ^ r₁.amountDeposit'.exponent) :=
  Vault.deposit_withdraw_roundtrip_proof v amountDeposit r₁ r₂ hv hL hpos hcanon hAV
    hDc hDnn hSsz hok₁ herr₁ hok₂ herr₂

/-- Witness: the loss term in `deposit_withdraw_roundtrip` cannot be dropped,
a round trip exists whose returned amount misses the taken amount by more than
the relative stage error alone. -/
theorem Vault.deposit_withdraw_roundtrip_attained :
    ∃ (v : Vault) (amountDeposit : STAmount) (r₁ : DepositResult) (r₂ : WithdrawResult),
      v.Lawful ∧ 0 < amountDeposit.toRat ∧
      v.lossUnrealized.toRat = 0 ∧
      v.deposit amountDeposit false = .ok r₁ ∧ r₁.error = none ∧
      r₁.vault'.withdraw (.vaultShares r₁.sharesIssued) false = .ok r₂ ∧
      r₂.error = none ∧
      RoundsWithinWitness r₂.assets' r₁.amountDeposit'.toRat (2 * depositε) :=
  Vault.deposit_withdraw_roundtrip_attained_proof

end XRPL.Model.SingleAssetVault
