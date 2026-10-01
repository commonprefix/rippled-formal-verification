import XRPL.Properties.Vault.Defs
import XRPL.Properties.Vault.VaultValid
import XRPL.Model.Vault.VaultDeposit
import XRPL.Properties.Approx
import XRPL.Properties.Protocol.STAmount.Common.DiscreteDefs
import XRPL.Properties.Vault.Common.DepositDefs
import XRPL.Properties.Vault.Proofs.Ideal
import XRPL.Properties.Vault.Proofs.DepositRounding
import XRPL.Properties.Vault.Proofs.DepositAccuracy
import XRPL.Properties.Vault.Proofs.DepositWitness
import XRPL.Properties.Vault.Proofs.DepositTight
import XRPL.Properties.Vault.Proofs.DepositTightWitness

/-! # `Vault.deposit` accuracy -/

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol

variable (v : Vault)

/-! ## `RawVault.roundedDepositAmount` -/

/-- `roundedAmount` is `amountDeposit` with every digit below some grid step
`10 ^ s` discarded and the digits above kept unchanged, and it is nonzero. As an
equation: `roundedAmount.toRat = ⌊amountDeposit.toRat / 10 ^ s⌋ * 10 ^ s`. The
grid step never exceeds the rounded amount itself (`10 ^ s ≤ |roundedAmount|`),
so the truncation always keeps the leading digit. A fractional `amountDeposit`
need only be canonical: no lower bound on its exponent is required, because the
result being nonzero (`.rounded`, so past the `tecPRECISION_LOSS` guard) already
forces the grid point to survive the 16-digit clamp. -/
theorem Vault.roundedDepositAmount_bounds (amountDeposit roundedAmount : STAmount)
    (hcanon : amountDeposit.integral = false → amountDeposit.IOUCanonical)
    (hrounded : v.roundedDepositAmount amountDeposit = .ok (.rounded roundedAmount)) :
    (∃ s : ℤ, RoundsToRepresentableAt roundedAmount amountDeposit.toRat s .downward ∧
      (10 : ℚ) ^ s ≤ |roundedAmount.toRat|) ∧
    roundedAmount.isZero = false :=
  Vault.roundedDepositAmount_bounds_proof v amountDeposit roundedAmount hcanon hrounded

/-- Witness: the truncation in `roundedDepositAmount_bounds` is not vacuous, a
lawful vault and an `amountDeposit` exist where digits are actually dropped. -/
theorem Vault.roundedDepositAmount_truncation_attained :
    ∃ (v : Vault) (amountDeposit roundedAmount : STAmount),
      v.roundedDepositAmount amountDeposit = .ok (.rounded roundedAmount) ∧
      roundedAmount.toRat < amountDeposit.toRat :=
  Vault.roundedDepositAmount_truncation_witness

/-- An integral `amountDeposit` passes through `roundedDepositAmount`
unchanged. -/
theorem Vault.roundedDepositAmount_integral (amountDeposit : STAmount)
    (hint : amountDeposit.integral = true) -- an integral vault's amounts are integral
    (hnz : amountDeposit.isZero = false) :
    v.roundedDepositAmount amountDeposit = .ok (.rounded amountDeposit) :=
  Vault.roundedDepositAmount_integral_proof v amountDeposit hint hnz

/-! ## `Vault.deposit` -/

/-- A successful donation takes exactly `roundedAmount` and issues no shares. -/
theorem Vault.deposit_donation (amountDeposit roundedAmount : STAmount) (r : DepositResult)
    (hrounded : v.roundedDepositAmount amountDeposit = .ok (.rounded roundedAmount))
    (hpos : 0 < amountDeposit.toRat)
    (hok : v.deposit amountDeposit true hpos = .ok r) (herr : r.error = none) :
    r.amountDeposit' = roundedAmount ∧ r.sharesIssued = STAmount.zero .int64 :=
  Vault.deposit_donation_proof v amountDeposit roundedAmount r hrounded hpos hok herr


/-- When the vault's exchange rate still equals `10 ^ scale`, the ideal share
amount is the empty-vault formula: pricing an empty vault at `10 ^ scale` is
the special case of the general formula, not a different rule. -/
theorem Vault.idealSharesDeposit_initial_rate (v : Vault) (amount : ℚ)
    -- the starting vault is lawful
    (hrate : (v.toExact.sharesTotal : ℚ) = v.depositNav * (10 : ℚ) ^ v.scale.toNat) :
    v.idealSharesDeposit amount = amount * (10 : ℚ) ^ v.scale.toNat :=
  Vault.idealSharesDeposit_initial_rate_proof v amount hrate

/-- A larger rounded amount never buys fewer shares from the same vault. -/
theorem Vault.deposit_shares_monotone (v : Vault)
    -- the starting vault is lawful
    (amountDeposit₁ amountDeposit₂ roundedAmount₁ roundedAmount₂ : STAmount)
    (r₁ r₂ : DepositResult)
    -- both rounded amounts are stored canonically and are positive
    (hcanon₁ : roundedAmount₁.Canonical) (hcanon₂ : roundedAmount₂.Canonical)
    (hposR₁ : 0 < roundedAmount₁.toRat) (hposR₂ : 0 < roundedAmount₂.toRat)
    -- both amounts round to a nonzero roundedAmount
    (hrounded₁ : v.roundedDepositAmount amountDeposit₁ = .ok (.rounded roundedAmount₁))
    (hrounded₂ : v.roundedDepositAmount amountDeposit₂ = .ok (.rounded roundedAmount₂))
    -- both deposits succeed, each starting from the same vault v.toRawVault
    (hpos₁ : 0 < amountDeposit₁.toRat)
    (hok₁ : v.deposit amountDeposit₁ false hpos₁ = .ok r₁) (herr₁ : r₁.error = none)
    (hpos₂ : 0 < amountDeposit₂.toRat)
    (hok₂ : v.deposit amountDeposit₂ false hpos₂ = .ok r₂) (herr₂ : r₂.error = none)
    -- the first rounded amount is at most the second
    (hle : roundedAmount₁.toRat ≤ roundedAmount₂.toRat) :
    -- the first deposit is issued at most as many shares
    r₁.sharesIssued.toRat ≤ r₂.sharesIssued.toRat :=
  Vault.deposit_shares_monotone_proof v amountDeposit₁ amountDeposit₂
    roundedAmount₁ roundedAmount₂ r₁ r₂ hcanon₁ hcanon₂ hposR₁ hposR₂
    hrounded₁ hrounded₂ hpos₁ hok₁ herr₁ hpos₂ hok₂ herr₂ hle

/-- Issued shares are a nonnegative integer matching `idealSharesDeposit` of
`roundedAmount` up to the two `Number` stages of the share pricing and the final
truncation: at most `sharesε` relatively above, less than one whole share
plus `sharesε` below. -/
theorem Vault.deposit_sharesIssued (v : Vault) (amountDeposit roundedAmount : STAmount) (r : DepositResult)
    -- the starting vault is lawful
    (hcanon : roundedAmount.Canonical) -- the rounded amount is stored canonically
    (hpos : 0 < roundedAmount.toRat) -- the rounded amount is positive, the preflight guard
    -- the net asset value clears the deep-underflow threshold of the Number line
    (hnav : 0 < v.toExact.assetsTotal → (10 : ℚ) ^ (-32700 : ℤ) ≤ v.depositNav)
    (hrounded : v.roundedDepositAmount amountDeposit = .ok (.rounded roundedAmount))
    (hposA : 0 < amountDeposit.toRat)
    (hok : v.deposit amountDeposit false hposA = .ok r) (herr : r.error = none) :
    r.sharesIssued.toRat.den = 1 ∧ 0 ≤ r.sharesIssued.toRat ∧
    v.idealSharesDeposit roundedAmount.toRat * (1 - sharesε) - 1 < r.sharesIssued.toRat ∧
    r.sharesIssued.toRat ≤ v.idealSharesDeposit roundedAmount.toRat * (1 + sharesε) :=
  Vault.deposit_sharesIssued_proof v amountDeposit roundedAmount r hcanon hpos hnav
    hrounded hposA hok herr

/-- Witness for the one-share truncation term of `deposit_sharesIssued`: a run falls
short of the ideal by more than `1 - 10⁻¹⁴` shares beyond the relative term (by
`1 - 2·10⁻¹⁵` in that run). -/
theorem Vault.deposit_sharesIssued_truncation_attained :
    ∃ (v : Vault) (amountDeposit roundedAmount : STAmount) (hpos : 0 < amountDeposit.toRat)
      (r : DepositResult),
      v.roundedDepositAmount amountDeposit = .ok (.rounded roundedAmount) ∧
      v.deposit amountDeposit false hpos = .ok r ∧ r.error = none ∧
      1 - 1 / 10 ^ 14 <
        v.idealSharesDeposit roundedAmount.toRat * (1 - sharesε) - r.sharesIssued.toRat :=
  Vault.deposit_sharesIssued_trunc_witness

/-- Witness for the relative `sharesε` term of `deposit_sharesIssued`: a run issues
more than `1.084·10⁻¹⁸` relatively above the ideal, `98.5%` of `sharesε = 1.1·10⁻¹⁸`. -/
theorem Vault.deposit_sharesIssued_relative_attained :
    ∃ (v : Vault) (amountDeposit roundedAmount : STAmount) (hpos : 0 < amountDeposit.toRat)
      (r : DepositResult),
      v.roundedDepositAmount amountDeposit = .ok (.rounded roundedAmount) ∧
      v.deposit amountDeposit false hpos = .ok r ∧ r.error = none ∧
      v.idealSharesDeposit roundedAmount.toRat * (1084 / 10 ^ 21) <
        r.sharesIssued.toRat - v.idealSharesDeposit roundedAmount.toRat :=
  Vault.deposit_sharesIssued_sharp_witness

/-- The taken amount `amountDeposit'` never exceeds `amountDeposit`. It falls short
of the issued shares' exact worth by at most `depositε` relatively plus `3/2` steps
of the post-deposit grid `10 ^ e` (half a step from the `.to_nearest` pricing, one
from the grid clamp); a taken amount that underflows to zero forces a sub-grid
ideal; and it overpays by at most `depositε` relatively plus half a unit of its
own last digit. -/
theorem Vault.deposit_charge (v : Vault) (amountDeposit : STAmount) (r : DepositResult)
    -- the starting vault is lawful
    (hcanon : amountDeposit.Canonical) -- the deposit amount is stored canonically
    (hpos : 0 < amountDeposit.toRat) -- the deposited amount is positive, the preflight guard
    (hok : v.deposit amountDeposit false hpos = .ok r) (herr : r.error = none) :
    r.amountDeposit'.toRat ≤ amountDeposit.toRat ∧
    -- the grid clamp can drop the charge by up to one step of the post-deposit grid
    (∀ e, postSumExponent v.assetsTotal amountDeposit = .ok e →
      v.idealChargeDeposit r.sharesIssued.toRat * (1 - depositε) - 3 / 2 * (10 : ℚ) ^ e ≤
        r.amountDeposit'.toRat) ∧
    (r.amountDeposit'.isZero = true →
      v.idealChargeDeposit r.sharesIssued.toRat * (1 - depositε) <
        if v.numericType.isIntegral then 1 else (10 : ℚ) ^ (-81 : ℤ)) ∧
    r.amountDeposit'.toRat - v.idealChargeDeposit r.sharesIssued.toRat ≤
      v.idealChargeDeposit r.sharesIssued.toRat * depositε +
        1 / 2 * (10 : ℚ) ^ r.amountDeposit'.exponent :=
  Vault.deposit_charge_proof v amountDeposit r hcanon hpos hok herr

/-- Witness for the `3/2`-grid-step term of the lower `deposit_charge` bound: a run's
charge falls short of the issued shares' worth by more than `3/2 - 10⁻¹⁵` steps of the
post-deposit grid (by `3/2 - 5·10⁻¹⁶` in that run). -/
theorem Vault.deposit_charge_undercharge_attained :
    ∃ (v : Vault) (amountDeposit : STAmount) (hpos : 0 < amountDeposit.toRat) (r : DepositResult)
      (e : ℤ),
      v.deposit amountDeposit false hpos = .ok r ∧ r.error = none ∧
      postSumExponent v.assetsTotal amountDeposit = .ok e ∧
      (3 / 2 - 1 / 10 ^ 15) * (10 : ℚ) ^ e <
        v.idealChargeDeposit r.sharesIssued.toRat - r.amountDeposit'.toRat :=
  Vault.deposit_charge_lower_witness

/-- Witness for the half-ULP term of the upper `deposit_charge` bound: a run's charge
exceeds the issued shares' worth by more than `1/2 - 10⁻¹⁵` of its last digit (by
`1/2 - 1/(6·10^15 + 2)` in that run). -/
theorem Vault.deposit_charge_overcharge_attained :
    ∃ (v : Vault) (amountDeposit : STAmount) (hpos : 0 < amountDeposit.toRat) (r : DepositResult),
      v.deposit amountDeposit false hpos = .ok r ∧ r.error = none ∧
      (1 / 2 - 1 / 10 ^ 15) * (10 : ℚ) ^ r.amountDeposit'.exponent <
        r.amountDeposit'.toRat - v.idealChargeDeposit r.sharesIssued.toRat :=
  Vault.deposit_charge_upper_witness

/-- Integral strengthening of `deposit_charge`: the overcharge stays below
one whole unit plus the stage error. -/
theorem Vault.deposit_charge_integral (v : Vault) (amountDeposit : STAmount) (r : DepositResult)
    -- the starting vault is lawful
    (hcanon : amountDeposit.Canonical) -- the deposit amount is stored canonically
    (hint : v.numericType.isIntegral = true) -- the vault holds an integral asset
    (hpos : 0 < amountDeposit.toRat) -- the deposited amount is positive, the preflight guard
    (hok : v.deposit amountDeposit false hpos = .ok r) (herr : r.error = none) :
    r.amountDeposit'.toRat - v.idealChargeDeposit r.sharesIssued.toRat ≤
      1 + v.idealChargeDeposit r.sharesIssued.toRat * depositε :=
  Vault.deposit_charge_integral_proof v amountDeposit r hcanon hint hpos hok herr

/-- Both stored totals are the old value plus `amountDeposit'`, up to the
`depositε` relative error of the `Number` addition, and the share total
update is exact whenever the sum is representable. -/
theorem Vault.deposit_vault_updates (v : Vault) (amountDeposit : STAmount) (isDonation : Bool)
    -- the starting vault is lawful
    (hcanon : amountDeposit.Canonical) -- the deposit amount is stored canonically
    (hpos : 0 < amountDeposit.toRat) -- the deposited amount is positive, the preflight guard
    (r : DepositResult)
    (hok : v.deposit amountDeposit isDonation hpos = .ok r) (herr : r.error = none) :
    -- assetsTotal' = assetsTotal + taken amount, within depositε
    RoundsWithin r.vault'.assetsTotal
      (v.toExact.assetsTotal + r.amountDeposit'.toRat) .to_nearest depositε ∧
    -- assetsAvailable' = assetsAvailable + taken amount, within depositε
    RoundsWithin r.vault'.assetsAvailable
      (v.toExact.assetsAvailable + r.amountDeposit'.toRat) .to_nearest depositε ∧
    -- sharesTotal' = sharesTotal + issued shares, exactly, whenever the
    -- sum fits in the share domain (int64)
    ((v.toExact.sharesTotal : ℚ) + r.sharesIssued.toRat ≤ 2 ^ 63 - 1 →
      (r.vault'.toExact.sharesTotal : ℚ) =
        (v.toExact.sharesTotal : ℚ) + r.sharesIssued.toRat) :=
  Vault.deposit_vault_updates_proof v amountDeposit isDonation hcanon hpos r hok herr

/-- Witness: the error term in `deposit_vault_updates` cannot be dropped, a run
exists where the stored total is not the exact sum. The int64 witness `wvDVU`
donates `9000000000000000006`; the stored total `18000000000000000010` differs
from the exact sum `18000000000000000013`. -/
theorem Vault.deposit_vault_updates_attained :
    ∃ (v : Vault) (amountDeposit : STAmount) (isDonation : Bool) (hpos : 0 < amountDeposit.toRat)
      (r : DepositResult),
      v.deposit amountDeposit isDonation hpos = .ok r ∧ r.error = none ∧
      r.vault'.assetsTotal.toRat ≠ v.toExact.assetsTotal + r.amountDeposit'.toRat :=
  Vault.deposit_vault_updates_witness

/-- Witness: a successful canonical deposit into a vault whose stored fields are all on
the asset grid can leave an `assetsTotal` off the grid, which `associateAsset` would round
on ledger. The grid clamp aligns the taken amount `99.99999999999994` with the post-deposit
grid, but the sum keeps the old total's `10⁻¹⁵` digit: `101.234567890123396` (18 digits). -/
theorem Vault.deposit_applied_delta_attained :
    ∃ (v : Vault) (amountDeposit : STAmount) (hpos : 0 < amountDeposit.toRat) (r : DepositResult),
      amountDeposit.Canonical ∧ ¬ v.assetsRounded ∧
      v.deposit amountDeposit false hpos = .ok r ∧ r.error = none ∧
      r.vault'.assetsRounded :=
  Vault.deposit_offgrid_witness

/-- Integral strengthening of `deposit_vault_updates`: in-domain integer
sums are stored exactly. -/
theorem Vault.deposit_vault_updates_integral (v : Vault) (amountDeposit : STAmount) (isDonation : Bool)
    -- the starting vault is lawful
    (r : DepositResult)
    (hnt : v.numericType = .int64 ∨ v.numericType = .native) -- the vault holds an integral asset
    (hcanon : amountDeposit.IntegralCanonical) -- an integral vault's amounts are integral
    (hty : amountDeposit.mNumericType = v.numericType) -- the deposit is in the vault's asset
    -- an integral vault's stored totals are integers
    (hdenA : v.assetsTotal.toRat.den = 1)
    (hdenAv : v.assetsAvailable.toRat.den = 1)
    (hpos : 0 < amountDeposit.toRat)
    (hok : v.deposit amountDeposit isDonation hpos = .ok r) (herr : r.error = none)
    -- the new total fits the asset domain (int64)
    (hsz : v.toExact.assetsTotal + r.amountDeposit'.toRat ≤ 2 ^ 63 - 1) :
    r.vault'.assetsTotal.toRat = v.toExact.assetsTotal + r.amountDeposit'.toRat ∧
    r.vault'.assetsAvailable.toRat = v.toExact.assetsAvailable + r.amountDeposit'.toRat :=
  Vault.deposit_vault_updates_integral_proof v amountDeposit isDonation r hnt hcanon hty
    hdenA hdenAv hpos hok herr hsz

/-- The `assetsMaximum` guard checks `assetsTotal'`, which the caller cannot
know in advance, but `assetsTotal + roundedAmount` bounds the true new total,
and rounding it cannot cross the maximum: a lawful `assetsMaximum` is
normalized, so it lies on the `Number` line, and rounding to nearest never
lands above a point of the line the true value was at or under. No error
margin is needed. -/
theorem Vault.deposit_under_maximum (v : Vault) (amountDeposit roundedAmount : STAmount) (isDonation : Bool)
    -- the starting vault is lawful
    (r : DepositResult)
    (hrounded : v.roundedDepositAmount amountDeposit = .ok (.rounded roundedAmount))
    (hcanon : amountDeposit.Canonical) -- the deposit amount is stored canonically
    (hpos : 0 < amountDeposit.toRat)
    (hok : v.deposit amountDeposit isDonation hpos = .ok r)
    -- assetsTotal + roundedAmount fits under the maximum m
    (hmargin : ∀ m ∈ v.assetsMaximum,
      v.toExact.assetsTotal + roundedAmount.toRat ≤ m.toRat) :
    -- the assetsMaximum guard cannot fire
    r.error ≠ some .tecLIMIT_EXCEEDED :=
  Vault.deposit_under_maximum_proof v amountDeposit roundedAmount isDonation r hrounded
    hcanon hpos hok hmargin

end XRPL.Model.SingleAssetVault
