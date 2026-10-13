import XRPL.Properties.Vault.Defs
import XRPL.Properties.Vault.VaultValid
import XRPL.Properties.Vault.VaultDeposit
import XRPL.Model.Vault.VaultWithdraw
import XRPL.Properties.Vault.Proofs.Roundtrip
import XRPL.Properties.Vault.Proofs.RoundtripWitness

/-! # Depositing and redeeming returns the taken amount

In exact arithmetic the round trip is the identity: a deposit at the NAV rate
does not change the rate, so the issued shares are worth exactly the taken
amount, and redeeming them immediately pays it back. Everything else is
rounding, and it can go either way. The deposit clamp snaps the charge down onto the
post-deposit grid while the shares are kept, so the depositor can gain up to one step of
that grid; the charge's own pricing and the redemption's pricing and clamp, which floors the
payout onto the post-redemption total's grid, bound the loss. Both come with a
`11/10·sharesε` relative term, which only an integral asset needs: there the charge and the
payout are integers rounded from `Number` quotients, and the quotients' relative error
moves the excess past one unit only for a charge beyond `10²⁰/121`. -/

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol

/-- Depositing and immediately redeeming the issued shares returns the taken amount up to
rounding, in both directions a few units of the last digits.

The gain is at most `11/10·sharesε` of the charge plus one step of the deposit's post-sum grid
`10^e`: the deposit clamp snaps the charge down below the priced amount by less than a step,
and the redemption, priced from the same total, never pays more than that priced amount plus
what the snapped digits leave in the total. The shortfall is at most `11/10·sharesε` of the
charge plus half a unit of the charge (its `to_nearest` pricing) plus the redemption's own
pricing and clamp error: half a unit of the payout, or one step of the post-redemption
total's grid less that, whichever is larger. From an empty vault the redemption is the
final withdrawal and returns the charge up to half a unit.

The relative term is needed only on an integral asset. There the charge and the payout are
integers rounded from `Number` quotients whose products each carry up to `5.4·10⁻¹⁹` relative
error. An excess of two units needs a charge above `10²⁰/121` (the quotients then sit on the
`0.1` grid, and a total at the int64 cap can round the sum one unit down), and beyond that
the excess over the absolute terms stays under `2·5.4·10⁻¹⁹` of the charge plus lower-order
terms, so `11/10·sharesε = 1.21·10⁻¹⁸` covers both. On a fractional asset the charge and the payout sit on
16-digit grids that absorb the relative error, and neither bound needs the term. -/
theorem Vault.deposit_withdraw_roundtrip (v : Vault) (amountDeposit : STAmount)
    (r₁ : DepositResult) (r₂ : WithdrawResult)
    -- the starting vault is lawful
    -- no unrealized loss, so the pricing is exact on both sides
    (hL : v.toExact.lossUnrealized = 0)
    (hpos : 0 < amountDeposit.toRat) -- the deposited amount is positive, the preflight guard
    (hcanon : amountDeposit.Canonical) -- the deposit amount is stored canonically
    -- the post-deposit share total stays in the int64 domain
    (hSsz : (v.toExact.sharesTotal : ℚ) + r₁.sharesIssued.toRat ≤ 2 ^ 63 - 1)
    (hok₁ : v.deposit amountDeposit false hpos = .ok r₁) (herr₁ : r₁.error = none)
    -- the depositor redeems exactly the issued shares from the updated vault
    (hpos₂ : 0 < r₁.sharesIssued.toRat)
    (hok₂ : r₁.vault'.withdraw (.vaultShares r₁.sharesIssued) false hpos₂ = .ok r₂)
    (herr₂ : r₂.error = none) :
    -- the gain: relative error, one step of the deposit's post-sum grid
    (∀ e, postSumExponent v.assetsTotal amountDeposit = .ok e →
      r₂.assets'.toRat - r₁.amountDeposit'.toRat ≤
        r₁.amountDeposit'.toRat * (11 / 10 * sharesε) + (10 : ℚ) ^ e) ∧
    -- the loss: relative error, the charge's half unit, the redemption's pricing and clamp
    ∃ atr' : STAmount,
      STAmount.ofNumber v.numericType r₂.vault'.assetsTotal .to_nearest = .ok atr' ∧
      r₁.amountDeposit'.toRat - r₂.assets'.toRat ≤
        r₁.amountDeposit'.toRat * (11 / 10 * sharesε) +
          1 / 2 * (10 : ℚ) ^ r₁.amountDeposit'.exponent +
          max (1 / 2 * (10 : ℚ) ^ r₂.assets'.exponent)
            ((10 : ℚ) ^ atr'.exponent - 1 / 2 * (10 : ℚ) ^ r₂.assets'.exponent) :=
  Vault.deposit_withdraw_roundtrip_proof v amountDeposit r₁ r₂ hL hpos hcanon
    hSsz hok₁ herr₁ hpos₂ hok₂ herr₂

/-- Witness: the grid term of the gain is attained to within `10⁻³` of a step. Assets
`0.05226787409550871997`, `9103484172306589553` shares, deposit `1.013126211318054·10⁻⁴`:
the redemption pays exactly one post-deposit grid step `10⁻¹⁷` more than the charge. -/
theorem Vault.deposit_withdraw_roundtrip_grid_attained :
    ∃ (v : Vault) (amountDeposit : STAmount) (hpos₁ : 0 < amountDeposit.toRat) (r₁ : DepositResult)
      (hpos₂ : 0 < r₁.sharesIssued.toRat) (r₂ : WithdrawResult) (e : ℤ),
      v.toExact.lossUnrealized = 0 ∧ amountDeposit.Canonical ∧
      (v.toExact.sharesTotal : ℚ) + r₁.sharesIssued.toRat ≤ 2 ^ 63 - 1 ∧
      v.deposit amountDeposit false hpos₁ = .ok r₁ ∧ r₁.error = none ∧
      r₁.vault'.withdraw (.vaultShares r₁.sharesIssued) false hpos₂ = .ok r₂ ∧ r₂.error = none ∧
      postSumExponent v.assetsTotal amountDeposit = .ok e ∧
      r₁.amountDeposit'.toRat * (11 / 10 * sharesε) + (1 - 1 / 10 ^ 3) * (10 : ℚ) ^ e <
        r₂.assets'.toRat - r₁.amountDeposit'.toRat :=
  Vault.deposit_withdraw_roundtrip_grid_witness

/-- Witness: the relative term of the gain is attained to `0.739` of its coefficient. An int64
vault with assets `8105303602029334769` and `825620` shares takes a deposit of
`1118015903333139619`: the charge `1118015903333139617` comes back with `2` units more, beyond
the grid term `1` by `8.944·10⁻¹⁹` of the charge, `0.7392` of `11/10·sharesε`. -/
theorem Vault.deposit_withdraw_roundtrip_gain_relative_attained :
    ∃ (v : Vault) (amountDeposit : STAmount) (hpos₁ : 0 < amountDeposit.toRat) (r₁ : DepositResult)
      (hpos₂ : 0 < r₁.sharesIssued.toRat) (r₂ : WithdrawResult) (e : ℤ),
      v.toExact.lossUnrealized = 0 ∧ amountDeposit.Canonical ∧
      (v.toExact.sharesTotal : ℚ) + r₁.sharesIssued.toRat ≤ 2 ^ 63 - 1 ∧
      v.deposit amountDeposit false hpos₁ = .ok r₁ ∧ r₁.error = none ∧
      r₁.vault'.withdraw (.vaultShares r₁.sharesIssued) false hpos₂ = .ok r₂ ∧ r₂.error = none ∧
      postSumExponent v.assetsTotal amountDeposit = .ok e ∧
      r₁.amountDeposit'.toRat * (11 / 10 * sharesε * (739 / 1000)) + (10 : ℚ) ^ e <
        r₂.assets'.toRat - r₁.amountDeposit'.toRat :=
  Vault.deposit_withdraw_roundtrip_gain_relative_witness

/-- Witness: the charge's half unit in the loss is attained to within `1/10` of it. Assets
`6883653336825134000`, `1216261656673286306` shares, deposit `1034173733286000`: the charge
is the full priced amount, the `Number` stages price the redeemed shares just below half a
unit under it, the payout rounds one unit down and the clamp floors it onto the `10³` grid,
a loss of `10³` against the clamp term `999.5`, `0.997` of the half unit beyond the other
terms. -/
theorem Vault.deposit_withdraw_roundtrip_charge_attained :
    ∃ (v : Vault) (amountDeposit : STAmount) (hpos₁ : 0 < amountDeposit.toRat) (r₁ : DepositResult)
      (hpos₂ : 0 < r₁.sharesIssued.toRat) (r₂ : WithdrawResult),
      v.toExact.lossUnrealized = 0 ∧ amountDeposit.Canonical ∧
      (v.toExact.sharesTotal : ℚ) + r₁.sharesIssued.toRat ≤ 2 ^ 63 - 1 ∧
      v.deposit amountDeposit false hpos₁ = .ok r₁ ∧ r₁.error = none ∧
      r₁.vault'.withdraw (.vaultShares r₁.sharesIssued) false hpos₂ = .ok r₂ ∧ r₂.error = none ∧
      ∃ atr' : STAmount,
        STAmount.ofNumber v.numericType r₂.vault'.assetsTotal .to_nearest = .ok atr' ∧
        r₁.amountDeposit'.toRat * (11 / 10 * sharesε) +
            9 / 10 * (1 / 2 * (10 : ℚ) ^ r₁.amountDeposit'.exponent) +
            max (1 / 2 * (10 : ℚ) ^ r₂.assets'.exponent)
              ((10 : ℚ) ^ atr'.exponent - 1 / 2 * (10 : ℚ) ^ r₂.assets'.exponent) <
          r₁.amountDeposit'.toRat - r₂.assets'.toRat :=
  Vault.deposit_withdraw_roundtrip_charge_witness

/-- Witness: the relative term of the loss is attained to `0.943` of its coefficient, and
`sharesε` alone would not do. An int64 vault with assets `8347723295201995554` and
`1054626202063077017` shares takes a deposit of `875648741652780254`: the whole deposit is
charged, the new total `maxRep + 1` is stored as `maxRep`, and the charge comes back `2` units
short, beyond the two half units by `1.142·10⁻¹⁸` of the charge, `0.9438` of `11/10·sharesε`. -/
theorem Vault.deposit_withdraw_roundtrip_loss_relative_attained :
    ∃ (v : Vault) (amountDeposit : STAmount) (hpos₁ : 0 < amountDeposit.toRat) (r₁ : DepositResult)
      (hpos₂ : 0 < r₁.sharesIssued.toRat) (r₂ : WithdrawResult),
      v.toExact.lossUnrealized = 0 ∧ amountDeposit.Canonical ∧
      (v.toExact.sharesTotal : ℚ) + r₁.sharesIssued.toRat ≤ 2 ^ 63 - 1 ∧
      v.deposit amountDeposit false hpos₁ = .ok r₁ ∧ r₁.error = none ∧
      r₁.vault'.withdraw (.vaultShares r₁.sharesIssued) false hpos₂ = .ok r₂ ∧ r₂.error = none ∧
      ∃ atr' : STAmount,
        STAmount.ofNumber v.numericType r₂.vault'.assetsTotal .to_nearest = .ok atr' ∧
        r₁.amountDeposit'.toRat * (11 / 10 * sharesε * (943 / 1000)) +
            1 / 2 * (10 : ℚ) ^ r₁.amountDeposit'.exponent +
            max (1 / 2 * (10 : ℚ) ^ r₂.assets'.exponent)
              ((10 : ℚ) ^ atr'.exponent - 1 / 2 * (10 : ℚ) ^ r₂.assets'.exponent) <
          r₁.amountDeposit'.toRat - r₂.assets'.toRat :=
  Vault.deposit_withdraw_roundtrip_loss_relative_witness

/-- Witness: the redemption clamp term of the loss is attained to within `1/100` of it.
Assets `2.342036172855940002`, `2.97798973141981651·10¹⁷` shares, deposit
`8.988384141736458·10⁻¹²`: the payout is floored onto the post-redemption grid `10⁻¹⁵`,
`0.998` of that step below the charge. -/
theorem Vault.deposit_withdraw_roundtrip_clamp_attained :
    ∃ (v : Vault) (amountDeposit : STAmount) (hpos₁ : 0 < amountDeposit.toRat) (r₁ : DepositResult)
      (hpos₂ : 0 < r₁.sharesIssued.toRat) (r₂ : WithdrawResult),
      v.toExact.lossUnrealized = 0 ∧ amountDeposit.Canonical ∧
      (v.toExact.sharesTotal : ℚ) + r₁.sharesIssued.toRat ≤ 2 ^ 63 - 1 ∧
      v.deposit amountDeposit false hpos₁ = .ok r₁ ∧ r₁.error = none ∧
      r₁.vault'.withdraw (.vaultShares r₁.sharesIssued) false hpos₂ = .ok r₂ ∧ r₂.error = none ∧
      ∃ atr' : STAmount,
        STAmount.ofNumber v.numericType r₂.vault'.assetsTotal .to_nearest = .ok atr' ∧
        r₁.amountDeposit'.toRat * (11 / 10 * sharesε) + 1 / 2 * (10 : ℚ) ^ r₁.amountDeposit'.exponent +
            99 / 100 * max (1 / 2 * (10 : ℚ) ^ r₂.assets'.exponent)
              ((10 : ℚ) ^ atr'.exponent - 1 / 2 * (10 : ℚ) ^ r₂.assets'.exponent) <
          r₁.amountDeposit'.toRat - r₂.assets'.toRat :=
  Vault.deposit_withdraw_roundtrip_clamp_witness

end XRPL.Model.SingleAssetVault
