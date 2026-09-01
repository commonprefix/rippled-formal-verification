import XRPL.Properties.Vault.Defs
import XRPL.Properties.Vault.LawfulVaultValid
import XRPL.Model.Vault.VaultDeposit
import XRPL.Properties.Approx
import XRPL.Properties.Protocol.STAmount.Common.DiscreteDefs
import XRPL.Properties.Vault.Common.DepositDefs
import XRPL.Properties.Vault.Common.DepositAccuracy
import XRPL.Properties.Vault.Common.WitnessSupport
import XRPL.Properties.Vault.Common.DepositWiring
import XRPL.Properties.Vault.Common.DepositChargeFrac
import XRPL.Properties.Vault.Common.DepositWitness
import XRPL.Properties.Vault.Common.DepositMono

/-! # `LawfulVault.deposit` accuracy -/

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol

variable (lv : LawfulVault)

/-! ## `RawVault.roundedDepositAmount` -/

/-- `roundedAmount` is `amountDeposit` with every digit below some grid step
`10 ^ s` discarded and the digits above kept unchanged, and it is nonzero. As an
equation: `roundedAmount.toRat = ⌊amountDeposit.toRat / 10 ^ s⌋ * 10 ^ s`. The
grid step never exceeds the rounded amount itself (`10 ^ s ≤ |roundedAmount|`),
so the truncation always keeps the leading digit. A fractional `amountDeposit`
need only be canonical: no lower bound on its exponent is required, because the
result being nonzero (`.rounded`, so past the `tecPRECISION_LOSS` guard) already
forces the grid point to survive the 16-digit clamp. -/
theorem LawfulVault.roundedDepositAmount_bounds (amountDeposit roundedAmount : STAmount)
    (hcanon : amountDeposit.integral = false → amountDeposit.IOUCanonical)
    (hrounded : lv.roundedDepositAmount amountDeposit = .ok (.rounded roundedAmount)) :
    (∃ s : ℤ, RoundsToRepresentableAt roundedAmount amountDeposit.toRat s .downward ∧
      (10 : ℚ) ^ s ≤ |roundedAmount.toRat|) ∧
    roundedAmount.isZero = false :=
  LawfulVault.roundedDepositAmount_bounds_proof lv amountDeposit roundedAmount hcanon hrounded

/-- Witness: the truncation in `roundedDepositAmount_bounds` is not vacuous, a
lawful vault and an `amountDeposit` exist where digits are actually dropped. -/
theorem LawfulVault.roundedDepositAmount_truncation_attained :
    ∃ (lv : LawfulVault) (amountDeposit roundedAmount : STAmount),
      lv.roundedDepositAmount amountDeposit = .ok (.rounded roundedAmount) ∧
      roundedAmount.toRat < amountDeposit.toRat :=
  LawfulVault.roundedDepositAmount_truncation_witness

/-- An integral `amountDeposit` passes through `roundedDepositAmount`
unchanged. -/
theorem LawfulVault.roundedDepositAmount_integral (amountDeposit : STAmount)
    (hint : amountDeposit.integral = true) -- an integral vault's amounts are integral
    (hnz : amountDeposit.isZero = false) :
    lv.roundedDepositAmount amountDeposit = .ok (.rounded amountDeposit) :=
  LawfulVault.roundedDepositAmount_integral_proof lv amountDeposit hint hnz

/-! ## `LawfulVault.deposit` -/

/-- A successful donation takes exactly `roundedAmount` and issues no shares. -/
theorem LawfulVault.deposit_donation (amountDeposit roundedAmount : STAmount) (r : DepositResult)
    (hrounded : lv.roundedDepositAmount amountDeposit = .ok (.rounded roundedAmount))
    (hok : lv.deposit amountDeposit true = .ok r) (herr : r.error = none) :
    r.amountDeposit' = roundedAmount ∧ r.sharesIssued = STAmount.zero .int64 :=
  LawfulVault.deposit_donation_proof lv amountDeposit roundedAmount r hrounded hok herr


/-- When the vault's exchange rate still equals `10 ^ scale`, the ideal share
amount is the empty-vault formula: pricing an empty vault at `10 ^ scale` is
the special case of the general formula, not a different rule. -/
theorem LawfulVault.idealSharesDeposit_initial_rate (lv : LawfulVault) (amount : ℚ)
    -- the starting vault is lawful
    (hrate : (lv.toExact.sharesTotal : ℚ) = lv.depositNav * (10 : ℚ) ^ lv.scale.toNat) :
    lv.idealSharesDeposit amount = amount * (10 : ℚ) ^ lv.scale.toNat :=
  LawfulVault.idealSharesDeposit_initial_rate_proof lv amount hrate

/-- A larger rounded amount never buys fewer shares from the same vault. -/
theorem LawfulVault.deposit_shares_monotone (lv : LawfulVault)
    -- the starting vault is lawful
    (amountDeposit₁ amountDeposit₂ roundedAmount₁ roundedAmount₂ : STAmount)
    (r₁ r₂ : DepositResult)
    -- both rounded amounts are stored canonically and are positive
    (hcanon₁ : roundedAmount₁.Canonical) (hcanon₂ : roundedAmount₂.Canonical)
    (hposR₁ : 0 < roundedAmount₁.toRat) (hposR₂ : 0 < roundedAmount₂.toRat)
    -- both amounts round to a nonzero roundedAmount
    (hrounded₁ : lv.roundedDepositAmount amountDeposit₁ = .ok (.rounded roundedAmount₁))
    (hrounded₂ : lv.roundedDepositAmount amountDeposit₂ = .ok (.rounded roundedAmount₂))
    -- both deposits succeed, each starting from the same vault lv.toRawVault
    (hok₁ : lv.deposit amountDeposit₁ false = .ok r₁) (herr₁ : r₁.error = none)
    (hok₂ : lv.deposit amountDeposit₂ false = .ok r₂) (herr₂ : r₂.error = none)
    -- the first rounded amount is at most the second
    (hle : roundedAmount₁.toRat ≤ roundedAmount₂.toRat) :
    -- the first deposit is issued at most as many shares
    r₁.sharesIssued.toRat ≤ r₂.sharesIssued.toRat :=
  LawfulVault.deposit_shares_monotone_proof lv amountDeposit₁ amountDeposit₂
    roundedAmount₁ roundedAmount₂ r₁ r₂ hcanon₁ hcanon₂ hposR₁ hposR₂
    hrounded₁ hrounded₂ hok₁ herr₁ hok₂ herr₂ hle

/-- Issued shares are a nonnegative integer matching `idealSharesDeposit` of
`roundedAmount` up to the `Number` stage error and the final truncation: at
most `depositε` relatively above, less than one whole share plus `depositε`
below. -/
theorem LawfulVault.deposit_sharesIssued (lv : LawfulVault) (amountDeposit roundedAmount : STAmount) (r : DepositResult)
    -- the starting vault is lawful
    (hcanon : roundedAmount.Canonical) -- the rounded amount is stored canonically
    (hpos : 0 < roundedAmount.toRat) -- the rounded amount is positive, the preflight guard
    -- the net asset value clears the deep-underflow threshold of the Number line
    (hnav : 0 < lv.toExact.assetsTotal → (10 : ℚ) ^ (-32700 : ℤ) ≤ lv.depositNav)
    (hrounded : lv.roundedDepositAmount amountDeposit = .ok (.rounded roundedAmount))
    (hok : lv.deposit amountDeposit false = .ok r) (herr : r.error = none) :
    r.sharesIssued.toRat.den = 1 ∧ 0 ≤ r.sharesIssued.toRat ∧
    lv.idealSharesDeposit roundedAmount.toRat * (1 - depositε) - 1 < r.sharesIssued.toRat ∧
    r.sharesIssued.toRat ≤ lv.idealSharesDeposit roundedAmount.toRat * (1 + depositε) :=
  LawfulVault.deposit_sharesIssued_proof lv amountDeposit roundedAmount r hcanon hpos hnav
    hrounded hok herr

/-- Witness: the truncation term in `deposit_sharesIssued` cannot be dropped, a
run exists whose share error exceeds the relative `depositε` bound alone. -/
theorem LawfulVault.deposit_sharesIssued_attained :
    ∃ (lv : LawfulVault) (amountDeposit roundedAmount : STAmount) (r : DepositResult),
      0 < amountDeposit.toRat ∧
      lv.roundedDepositAmount amountDeposit = .ok (.rounded roundedAmount) ∧
      lv.deposit amountDeposit false = .ok r ∧ r.error = none ∧
      RoundsWithinWitness r.sharesIssued
        (lv.idealSharesDeposit roundedAmount.toRat) depositε :=
  LawfulVault.deposit_sharesIssued_witness

/-- The taken amount `amountDeposit'` never exceeds `amountDeposit`, is at
most `depositε` relatively below the exact value of the issued shares, and
overpays it by at most the stage budget plus 2 ULP. -/
theorem LawfulVault.deposit_charge (lv : LawfulVault) (amountDeposit : STAmount) (r : DepositResult)
    -- the starting vault is lawful
    (hcanon : amountDeposit.Canonical) -- the deposit amount is stored canonically
    (hpos : 0 < amountDeposit.toRat) -- the deposited amount is positive, the preflight guard
    (hok : lv.deposit amountDeposit false = .ok r) (herr : r.error = none) :
    r.amountDeposit'.toRat ≤ amountDeposit.toRat ∧
    -- a nonzero taken amount is at most `depositε` relatively below the issued
    -- shares' exact worth
    (r.amountDeposit'.isZero = false →
      lv.idealChargeDeposit r.sharesIssued.toRat * (1 - depositε) ≤ r.amountDeposit'.toRat) ∧
    -- a taken amount that underflows to the canonical zero forces the ideal charge
    -- below the smallest representable positive of the vault's numeric type: one
    -- whole unit for an integral asset, `10⁻⁸¹` for a fractional one (the upward
    -- charge snap flushes a sub-grid ideal to zero while a share is still issued)
    (r.amountDeposit'.isZero = true →
      lv.idealChargeDeposit r.sharesIssued.toRat * (1 - depositε) <
        if lv.numericType.isIntegral then 1 else (10 : ℚ) ^ (-81 : ℤ)) ∧
    -- amountDeposit' overpays the issued shares' worth by at most the relative
    -- stage error plus 2 ULP (the other direction is already capped by the
    -- relative conjunct)
    r.amountDeposit'.toRat - lv.idealChargeDeposit r.sharesIssued.toRat ≤
      lv.idealChargeDeposit r.sharesIssued.toRat * depositε +
        2 * (10 : ℚ) ^ r.amountDeposit'.exponent :=
  LawfulVault.deposit_charge_proof lv amountDeposit r hcanon hpos hok herr

/-- Witness: the ULP term in `deposit_charge` cannot be dropped, a run exists
whose taken amount misses the exact share value by more than `depositε`
relative. -/
theorem LawfulVault.deposit_charge_attained :
    ∃ (lv : LawfulVault) (amountDeposit : STAmount) (r : DepositResult),
      0 < amountDeposit.toRat ∧
      lv.deposit amountDeposit false = .ok r ∧ r.error = none ∧
      RoundsWithinWitness r.amountDeposit'
        (lv.idealChargeDeposit r.sharesIssued.toRat) depositε :=
  LawfulVault.deposit_charge_witness

/-- Integral strengthening of `deposit_charge`: the overcharge stays below
one whole unit plus the stage error. -/
theorem LawfulVault.deposit_charge_integral (lv : LawfulVault) (amountDeposit : STAmount) (r : DepositResult)
    -- the starting vault is lawful
    (hcanon : amountDeposit.Canonical) -- the deposit amount is stored canonically
    (hint : lv.numericType.isIntegral = true) -- the vault holds an integral asset
    (hpos : 0 < amountDeposit.toRat) -- the deposited amount is positive, the preflight guard
    (hok : lv.deposit amountDeposit false = .ok r) (herr : r.error = none) :
    r.amountDeposit'.toRat - lv.idealChargeDeposit r.sharesIssued.toRat ≤
      1 + lv.idealChargeDeposit r.sharesIssued.toRat * depositε :=
  LawfulVault.deposit_charge_integral_proof lv amountDeposit r hcanon hint hpos hok herr

/-- Both stored totals are the old value plus `amountDeposit'`, up to the
`depositε` relative error of the `Number` addition, and the share total
update is exact whenever the sum is representable. -/
theorem LawfulVault.deposit_vault_updates (lv : LawfulVault) (amountDeposit : STAmount) (isDonation : Bool)
    -- the starting vault is lawful
    (hcanon : amountDeposit.Canonical) -- the deposit amount is stored canonically
    (hpos : 0 < amountDeposit.toRat) -- the deposited amount is positive, the preflight guard
    (r : DepositResult)
    (hok : lv.deposit amountDeposit isDonation = .ok r) (herr : r.error = none) :
    -- assetsTotal' = assetsTotal + taken amount, within depositε
    RoundsWithin r.vault'.assetsTotal
      (lv.toExact.assetsTotal + r.amountDeposit'.toRat) .to_nearest depositε ∧
    -- assetsAvailable' = assetsAvailable + taken amount, within depositε
    RoundsWithin r.vault'.assetsAvailable
      (lv.toExact.assetsAvailable + r.amountDeposit'.toRat) .to_nearest depositε ∧
    -- sharesTotal' = sharesTotal + issued shares, exactly, whenever the
    -- sum fits in the share domain (int64)
    ((lv.toExact.sharesTotal : ℚ) + r.sharesIssued.toRat ≤ 2 ^ 63 - 1 →
      (r.vault'.toExact.sharesTotal : ℚ) =
        (lv.toExact.sharesTotal : ℚ) + r.sharesIssued.toRat) :=
  LawfulVault.deposit_vault_updates_proof lv amountDeposit isDonation hcanon hpos r hok herr

/-- Witness: the error term in `deposit_vault_updates` cannot be dropped, a run
exists where the stored total is not the exact sum. The int64 witness `wvDVU`
donates `9000000000000000006`; the stored total `18000000000000000010` differs
from the exact sum `18000000000000000013`. -/
theorem LawfulVault.deposit_vault_updates_attained :
    ∃ (lv : LawfulVault) (amountDeposit : STAmount) (isDonation : Bool) (r : DepositResult),
      lv.deposit amountDeposit isDonation = .ok r ∧ r.error = none ∧
      r.vault'.assetsTotal.toRat ≠ lv.toExact.assetsTotal + r.amountDeposit'.toRat :=
  LawfulVault.deposit_vault_updates_witness

/-- Witness: the entry rounding runs on the requested amount but never on the
taken amount from the shares round-trip. A run exists where the request
`0.001` is on the vault grid, the taken amount `0.0009999999999998572` is not,
and the stored totals move by the different on-ledger amount
`0.000999999999999857`.
`amountDeposit''` - the taken amount `r.amountDeposit'` re-rounded to the vault scale -/
theorem LawfulVault.deposit_applied_delta_attained :
    ∃ (lv : LawfulVault) (amountDeposit amountDeposit'' : STAmount) (r : DepositResult)
      (deltaTotal : Number) (deltaAmount : STAmount),
      lv.roundedDepositAmount amountDeposit = .ok (.rounded amountDeposit) ∧
      lv.deposit amountDeposit false = .ok r ∧ r.error = none ∧
      roundToVaultExponent r.amountDeposit' lv.assetsTotal = .ok amountDeposit'' ∧
      amountDeposit''.operator_eq r.amountDeposit' = false ∧
      r.vault'.assetsTotal.operator_sub lv.assetsTotal .to_nearest = .ok deltaTotal ∧
      STAmount.ofNumber lv.numericType deltaTotal .to_nearest = .ok deltaAmount ∧
      deltaAmount.operator_eq r.amountDeposit' = false :=
  LawfulVault.deposit_applied_delta_witness

/-- Integral strengthening of `deposit_vault_updates`: in-domain integer
sums are stored exactly. -/
theorem LawfulVault.deposit_vault_updates_integral (lv : LawfulVault) (amountDeposit : STAmount) (isDonation : Bool)
    -- the starting vault is lawful
    (r : DepositResult)
    (hnt : lv.numericType = .int64 ∨ lv.numericType = .native) -- the vault holds an integral asset
    (hcanon : amountDeposit.IntegralCanonical) -- an integral vault's amounts are integral
    (hty : amountDeposit.mNumericType = lv.numericType) -- the deposit is in the vault's asset
    -- an integral vault's stored totals are integers
    (hdenA : lv.assetsTotal.toRat.den = 1)
    (hdenAv : lv.assetsAvailable.toRat.den = 1)
    (hok : lv.deposit amountDeposit isDonation = .ok r) (herr : r.error = none)
    -- the new total fits the asset domain (int64)
    (hsz : lv.toExact.assetsTotal + r.amountDeposit'.toRat ≤ 2 ^ 63 - 1) :
    r.vault'.assetsTotal.toRat = lv.toExact.assetsTotal + r.amountDeposit'.toRat ∧
    r.vault'.assetsAvailable.toRat = lv.toExact.assetsAvailable + r.amountDeposit'.toRat :=
  LawfulVault.deposit_vault_updates_integral_proof lv amountDeposit isDonation r hnt hcanon hty
    hdenA hdenAv hok herr hsz

/-- The `assetsMaximum` guard checks `assetsTotal'`, which the caller cannot
know in advance, but `assetsTotal + roundedAmount` bounds the true new total,
and rounding it cannot cross the maximum: a lawful `assetsMaximum` is
normalized, so it lies on the `Number` line, and rounding to nearest never
lands above a point of the line the true value was at or under. No error
margin is needed. -/
theorem LawfulVault.deposit_under_maximum (lv : LawfulVault) (amountDeposit roundedAmount : STAmount) (isDonation : Bool)
    -- the starting vault is lawful
    (r : DepositResult)
    (hrounded : lv.roundedDepositAmount amountDeposit = .ok (.rounded roundedAmount))
    (hcanon : amountDeposit.Canonical) -- the deposit amount is stored canonically
    (hok : lv.deposit amountDeposit isDonation = .ok r)
    -- assetsTotal + roundedAmount fits under the maximum m
    (hmargin : ∀ m ∈ lv.assetsMaximum,
      lv.toExact.assetsTotal + roundedAmount.toRat ≤ m.toRat) :
    -- the assetsMaximum guard cannot fire
    r.error ≠ some .tecLIMIT_EXCEEDED :=
  LawfulVault.deposit_under_maximum_proof lv amountDeposit roundedAmount isDonation r hrounded
    hcanon hok hmargin

end XRPL.Model.SingleAssetVault
