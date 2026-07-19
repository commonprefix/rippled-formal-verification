import XRPL.Properties.Vault.Defs
import XRPL.Properties.Vault.VaultDeposit
import XRPL.Model.Vault.VaultWithdraw

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
withdrawal and pays the charge back exactly. -/
theorem Vault.deposit_withdraw_roundtrip (amountDeposit : STAmount)
    (r₁ : DepositResult) (r₂ : WithdrawResult)
    (hv : v.Lawful) -- the starting vault is lawful
    -- no unrealized interest or loss, so the pricing is exact on both sides
    (hI : v.toExact.interestUnrealized = 0)
    (hL : v.toExact.lossUnrealized = 0)
    (hpos : 0 < amountDeposit.toRat) -- the deposited amount is positive, the preflight guard
    (hok₁ : v.deposit amountDeposit false = .ok r₁) (herr₁ : r₁.error = none)
    -- the depositor redeems exactly the issued shares from the updated vault
    (hok₂ : r₁.vault'.withdraw (.vaultShares r₁.sharesIssued) false = .ok r₂)
    (herr₂ : r₂.error = none) :
    -- no profit beyond the stage error
    r₂.assets'.toRat ≤ r₁.amountDeposit'.toRat * (1 + 2 * depositε) ∧
    -- the loss is at most the rounding budget: the relative stage errors plus
    -- 2 ULP of the payout
    r₁.amountDeposit'.toRat - r₂.assets'.toRat ≤
      r₁.amountDeposit'.toRat * (2 * depositε) + 2 * (10 : ℚ) ^ r₂.assets'.exponent := sorry

/-- Witness: the loss term in `deposit_withdraw_roundtrip` cannot be dropped,
a round trip exists whose returned amount misses the taken amount by more than
the relative stage error alone. -/
theorem Vault.deposit_withdraw_roundtrip_attained :
    ∃ (v : Vault) (amountDeposit : STAmount) (r₁ : DepositResult) (r₂ : WithdrawResult),
      v.Lawful ∧ 0 < amountDeposit.toRat ∧
      v.toExact.interestUnrealized = 0 ∧ v.toExact.lossUnrealized = 0 ∧
      v.deposit amountDeposit false = .ok r₁ ∧ r₁.error = none ∧
      r₁.vault'.withdraw (.vaultShares r₁.sharesIssued) false = .ok r₂ ∧
      r₂.error = none ∧
      RoundsWithinWitness r₂.assets' r₁.amountDeposit'.toRat (2 * depositε) := sorry

end XRPL.Model.SingleAssetVault
