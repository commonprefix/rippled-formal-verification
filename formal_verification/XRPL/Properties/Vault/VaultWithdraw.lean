import XRPL.Properties.Vault.Defs
import XRPL.Properties.Vault.LawfulVaultValid
import XRPL.Model.Vault.VaultWithdraw
import XRPL.Properties.Approx
import XRPL.Properties.Protocol.STAmount.Common.DiscreteDefs
import XRPL.Properties.Vault.VaultDeposit
import XRPL.Properties.Vault.Common.WithdrawDefs
import XRPL.Properties.Vault.Common.WithdrawReduction
import XRPL.Properties.Vault.Common.WithdrawAccuracy
import XRPL.Properties.Vault.Common.WithdrawBounds
import XRPL.Properties.Vault.Common.WithdrawWitness
import XRPL.Properties.Vault.Common.WithdrawMono

/-! # `LawfulVault.withdraw` accuracy

Each `Number` stage of the withdraw exchange is correctly rounded within
`10 / (2 ^ 63 + 2)`, and under an exact pricing value no bound below composes
more than three stages, so the deposit budget `depositε = 10 ^ (-17)` covers
every composition and no separate withdraw constant is defined. -/

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol

variable (lv : LawfulVault)


/-! ## `LawfulVault.sharesToAssetsWithdraw` -/

/-- The returned amount is nonnegative, never exceeds the shares' worth by more than
`depositε` relatively, and when nonzero falls short of it by at most 2 ULP. The final
conversion rounds downward, marked "(waiting the C++ fix)" in the model, but
the interior stages round to nearest, so a plain upper bound by the worth
alone would be false. -/
theorem LawfulVault.sharesToAssetsWithdraw_bounds (lv : LawfulVault) (shares assets : STAmount)
    -- the starting vault is lawful
    (waiveUnrealizedLoss : Bool)
    (hnn : 0 ≤ shares.toRat) -- nonnegative shares, negative ones price negatively
    (hc : shares.Canonical) -- shares stored canonically, so `shares.toNumber` is value-exact
    -- the subtraction computing assetsTotal minus lossUnrealized
    -- does not round (automatic when loss is zero)
    (hnav : lv.WithdrawNavExact waiveUnrealizedLoss)
    (hok : lv.sharesToAssetsWithdraw shares waiveUnrealizedLoss = .ok assets) :
    0 ≤ assets.toRat ∧
    -- never pays more than the shares' worth, up to the stage error
    assets.toRat ≤ lv.idealAssetsWithdraw waiveUnrealizedLoss shares.toRat * (1 + depositε) ∧
    -- a nonzero returned amount underpays the shares' worth by at most the
    -- interior stage error plus 2 ULP (the other direction is already capped
    -- by the relative conjunct)
    (assets.isZero = false →
      lv.idealAssetsWithdraw waiveUnrealizedLoss shares.toRat - assets.toRat ≤
        lv.idealAssetsWithdraw waiveUnrealizedLoss shares.toRat * depositε +
          2 * (10 : ℚ) ^ assets.exponent) :=
  LawfulVault.sharesToAssetsWithdraw_bounds_proof lv shares assets waiveUnrealizedLoss hnn hc hnav hok

/-- Witness: the ULP term in `sharesToAssetsWithdraw_bounds` cannot be
dropped, a run exists whose returned amount misses the shares' worth by more than
`depositε` relative. -/
theorem LawfulVault.sharesToAssetsWithdraw_attained :
    ∃ (lv : LawfulVault) (shares assets : STAmount) (waiveUnrealizedLoss : Bool),
      0 < shares.toRat ∧
      lv.WithdrawNavExact waiveUnrealizedLoss ∧
      lv.sharesToAssetsWithdraw shares waiveUnrealizedLoss = .ok assets ∧
      RoundsWithinWitness assets
        (lv.idealAssetsWithdraw waiveUnrealizedLoss shares.toRat) depositε :=
  LawfulVault.sharesToAssetsWithdraw_witness

/-- `sharesToAssetsWithdraw_bounds` without the `WithdrawNavExact` hypothesis,
so it also holds when computing assetsTotal minus lossUnrealized rounds. That
rounding moves the price of every share, and the
worst case is `navSlack * shares / sharesTotal`, which is added to both
bounds. When `WithdrawNavExact` holds, `sharesToAssetsWithdraw_bounds` gives
the tighter bounds without the slack term. -/
theorem LawfulVault.sharesToAssetsWithdraw_total (lv : LawfulVault) (shares assets : STAmount)
    -- the starting vault is lawful
    (waiveUnrealizedLoss : Bool)
    (hnn : 0 ≤ shares.toRat) -- nonnegative shares, negative ones price negatively
    (hc : shares.Canonical) -- shares stored canonically, so `shares.toNumber` is value-exact
    (hok : lv.sharesToAssetsWithdraw shares waiveUnrealizedLoss = .ok assets) :
    -- never pays more than the shares' worth plus the slack, up to the stage error
    assets.toRat ≤
      (lv.idealAssetsWithdraw waiveUnrealizedLoss shares.toRat +
        lv.navSlack * shares.toRat / (lv.toExact.sharesTotal : ℚ)) * (1 + depositε) ∧
    -- a nonzero payout falls short of the shares' worth by at most the slack
    -- plus 2 ULP
    (assets.isZero = false →
      lv.idealAssetsWithdraw waiveUnrealizedLoss shares.toRat - assets.toRat ≤
        lv.navSlack * shares.toRat / (lv.toExact.sharesTotal : ℚ) * (1 + depositε) +
          2 * (10 : ℚ) ^ assets.exponent) :=
  LawfulVault.sharesToAssetsWithdraw_total_proof lv shares assets waiveUnrealizedLoss hnn hc hok

/-! ## `LawfulVault.withdraw` -/

/-- A successful withdrawal that names shares burns exactly the named amount.
Error records report zero, the contract in `Unchanged.lean`. -/
theorem LawfulVault.withdraw_sharesBurned_exact (shares : STAmount) (waiveUnrealizedLoss : Bool)
    (r : WithdrawResult)
    (hok : lv.withdraw (.vaultShares shares) waiveUnrealizedLoss = .ok r)
    (herr : r.error = none) :
    r.sharesBurned = shares :=
  LawfulVault.withdraw_sharesBurned_exact_proof lv shares waiveUnrealizedLoss r hok herr

/-- Shares burned by an asset-denominated withdrawal are a positive integer
matching `idealSharesWithdraw` of the named `assets` up to the `Number` stage
error and the final rounding to the nearest whole share. -/
theorem LawfulVault.withdraw_sharesBurned (lv : LawfulVault) (assets : STAmount) (waiveUnrealizedLoss : Bool)
    -- the starting vault is lawful
    (r : WithdrawResult)
    (hpos : 0 < assets.toRat) -- the withdrawn amount is positive, the preflight guard
    (hc : assets.Canonical) -- assets stored canonically, so `assets.toNumber` is value-exact
    -- the subtraction computing assetsTotal minus lossUnrealized
    -- does not round (automatic when loss is zero)
    (hnav : lv.WithdrawNavExact waiveUnrealizedLoss)
    (hok : lv.withdraw (.vaultAssets assets) waiveUnrealizedLoss = .ok r)
    (herr : r.error = none) :
    r.sharesBurned.toRat.den = 1 ∧ 0 < r.sharesBurned.toRat ∧
    |r.sharesBurned.toRat - lv.idealSharesWithdraw waiveUnrealizedLoss assets.toRat| ≤
      1 / 2 + lv.idealSharesWithdraw waiveUnrealizedLoss assets.toRat * depositε :=
  LawfulVault.withdraw_sharesBurned_proof lv assets waiveUnrealizedLoss r hpos hc hnav hok herr

/-- Witness: the half-share term in `withdraw_sharesBurned` cannot be dropped,
a run exists whose share error exceeds the relative `depositε` bound alone. -/
theorem LawfulVault.withdraw_sharesBurned_attained :
    ∃ (lv : LawfulVault) (assets : STAmount) (waiveUnrealizedLoss : Bool) (r : WithdrawResult),
      0 < assets.toRat ∧
      lv.WithdrawNavExact waiveUnrealizedLoss ∧
      lv.withdraw (.vaultAssets assets) waiveUnrealizedLoss = .ok r ∧ r.error = none ∧
      RoundsWithinWitness r.sharesBurned
        (lv.idealSharesWithdraw waiveUnrealizedLoss assets.toRat) depositε :=
  LawfulVault.withdraw_sharesBurned_witness

/-- The `assets'` of a successful non-final withdrawal is nonnegative, never
exceeds the burned shares' worth by more than `depositε` relatively, and when
nonzero falls short of it by at most 2 ULP. Both `WithdrawAmount` forms share
this bound, the asset-denominated form derives the burned shares first. -/
theorem LawfulVault.withdraw_payout (lv : LawfulVault) (amount : WithdrawAmount) (waiveUnrealizedLoss : Bool)
    -- the starting vault is lawful
    (sharesTotalAmount : STAmount) (r : WithdrawResult)
    (hnn : 0 ≤ r.sharesBurned.toRat) -- nonnegative shares, negative ones price negatively
    (hc : r.sharesBurned.Canonical) -- burned shares canonical, so their `toNumber` is value-exact
    -- the subtraction computing assetsTotal minus lossUnrealized
    -- does not round (automatic when loss is zero)
    (hnav : lv.WithdrawNavExact waiveUnrealizedLoss)
    (hok : lv.withdraw amount waiveUnrealizedLoss = .ok r) (herr : r.error = none)
    -- not the final withdrawal, which pays all of assetsAvailable instead
    (hst : STAmount.ofNumber .int64 lv.sharesTotal .to_nearest = .ok sharesTotalAmount)
    (hfin : r.sharesBurned.operator_eq sharesTotalAmount = false) :
    0 ≤ r.assets'.toRat ∧
    -- never pays more than the burned shares' worth, up to the stage error
    r.assets'.toRat ≤
      lv.idealAssetsWithdraw waiveUnrealizedLoss r.sharesBurned.toRat * (1 + depositε) ∧
    -- a nonzero assets' underpays the burned shares' worth by at most 2 ULP
    -- (the other direction is already capped by the relative conjunct)
    (r.assets'.isZero = false →
      lv.idealAssetsWithdraw waiveUnrealizedLoss r.sharesBurned.toRat - r.assets'.toRat ≤
        lv.idealAssetsWithdraw waiveUnrealizedLoss r.sharesBurned.toRat * depositε +
          2 * (10 : ℚ) ^ r.assets'.exponent) :=
  LawfulVault.withdraw_payout_proof lv amount waiveUnrealizedLoss sharesTotalAmount r
    hnn hc hnav hok herr hst hfin

/-- Witness: the ULP term in `withdraw_payout` cannot be dropped, a run exists
whose `assets'` misses the burned shares' worth by more than `depositε`
relative. -/
theorem LawfulVault.withdraw_payout_attained :
    ∃ (lv : LawfulVault) (amount : WithdrawAmount) (waiveUnrealizedLoss : Bool)
      (sharesTotalAmount : STAmount) (r : WithdrawResult),
      lv.WithdrawNavExact waiveUnrealizedLoss ∧
      lv.withdraw amount waiveUnrealizedLoss = .ok r ∧ r.error = none ∧
      STAmount.ofNumber .int64 lv.sharesTotal .to_nearest = .ok sharesTotalAmount ∧
      r.sharesBurned.operator_eq sharesTotalAmount = false ∧
      RoundsWithinWitness r.assets'
        (lv.idealAssetsWithdraw waiveUnrealizedLoss r.sharesBurned.toRat) depositε :=
  LawfulVault.withdraw_payout_witness

/-- Integral strengthening of `withdraw_payout`: the shortfall stays below
one whole unit plus the stage error, with no nonzero condition. -/
theorem LawfulVault.withdraw_payout_integral (lv : LawfulVault) (amount : WithdrawAmount) (waiveUnrealizedLoss : Bool)
    -- the starting vault is lawful
    (sharesTotalAmount : STAmount) (r : WithdrawResult)
    (hint : lv.numericType.isIntegral = true) -- the vault holds an integral asset
    (hnn : 0 ≤ r.sharesBurned.toRat) -- nonnegative shares, negative ones price negatively
    (hc : r.sharesBurned.Canonical) -- burned shares canonical, so their `toNumber` is value-exact
    -- the subtraction computing assetsTotal minus lossUnrealized
    -- does not round (automatic when loss is zero)
    (hnav : lv.WithdrawNavExact waiveUnrealizedLoss)
    (hok : lv.withdraw amount waiveUnrealizedLoss = .ok r) (herr : r.error = none)
    -- not the final withdrawal, which pays all of assetsAvailable instead
    (hst : STAmount.ofNumber .int64 lv.sharesTotal .to_nearest = .ok sharesTotalAmount)
    (hfin : r.sharesBurned.operator_eq sharesTotalAmount = false) :
    lv.idealAssetsWithdraw waiveUnrealizedLoss r.sharesBurned.toRat - r.assets'.toRat ≤
      1 + lv.idealAssetsWithdraw waiveUnrealizedLoss r.sharesBurned.toRat * depositε :=
  LawfulVault.withdraw_payout_integral_proof lv amount waiveUnrealizedLoss sharesTotalAmount r
    hint hnn hc hnav hok herr hst hfin

/-- More shares burned never pays less from the same vault. Every pricing
stage is a monotone function of the share amount: the exact products and
quotients are monotone, correct rounding is monotone, and the final downward
conversion is monotone. -/
theorem LawfulVault.withdraw_payout_monotone (lv : LawfulVault) (amount₁ amount₂ : WithdrawAmount)
    -- the starting vault is lawful
    (waiveUnrealizedLoss : Bool) (sharesTotalAmount : STAmount) (r₁ r₂ : WithdrawResult)
    -- the subtraction computing assetsTotal minus lossUnrealized
    -- does not round (automatic when loss is zero)
    (hnav : lv.WithdrawNavExact waiveUnrealizedLoss)
    -- the burned shares are stored canonically and are nonnegative
    (hcb₁ : r₁.sharesBurned.Canonical) (hcb₂ : r₂.sharesBurned.Canonical)
    (hnnb₁ : 0 ≤ r₁.sharesBurned.toRat) (hnnb₂ : 0 ≤ r₂.sharesBurned.toRat)
    -- both withdrawals succeed, each starting from the same vault lv.toRawVault
    (hok₁ : lv.withdraw amount₁ waiveUnrealizedLoss = .ok r₁) (herr₁ : r₁.error = none)
    (hok₂ : lv.withdraw amount₂ waiveUnrealizedLoss = .ok r₂) (herr₂ : r₂.error = none)
    -- neither run is the final withdrawal, which pays all of assetsAvailable instead
    (hst : STAmount.ofNumber .int64 lv.sharesTotal .to_nearest = .ok sharesTotalAmount)
    (hfin₁ : r₁.sharesBurned.operator_eq sharesTotalAmount = false)
    (hfin₂ : r₂.sharesBurned.operator_eq sharesTotalAmount = false)
    -- the first run burns at most as many shares
    (hle : r₁.sharesBurned.toRat ≤ r₂.sharesBurned.toRat) :
    -- the first run is paid at most as much
    r₁.assets'.toRat ≤ r₂.assets'.toRat :=
  LawfulVault.withdraw_payout_monotone_proof lv amount₁ amount₂ waiveUnrealizedLoss
    sharesTotalAmount r₁ r₂ hnav hcb₁ hcb₂ hnnb₁ hnnb₂
    hok₁ herr₁ hok₂ herr₂ hst hfin₁ hfin₂ hle

/-- Both stored asset fields are the old value minus `assets'`, up to the
`depositε` relative error of the `Number` subtraction, and the share total
update is exact whenever the stored total fits the share domain. -/
theorem LawfulVault.withdraw_vault_updates (lv : LawfulVault) (amount : WithdrawAmount) (waiveUnrealizedLoss : Bool)
    -- the starting vault is lawful
    (sharesTotalAmount : STAmount) (r : WithdrawResult)
    -- the payout is nonnegative (a computed downward `ofNumber` output on
    -- nonnegative shares; hypothesized like the integral sibling's `hnn`)
    (hpnn : 0 ≤ r.assets'.toRat)
    -- the burned shares are a nonnegative int64 amount, the by-shares echo of the
    -- user's requested amount (a real withdrawal burns a nonnegative integer count)
    (hnn : 0 ≤ r.sharesBurned.toRat)
    -- burned shares canonical (used by the exact share-total conjunct)
    (hc : r.sharesBurned.Canonical)
    (hSnt : r.sharesBurned.mNumericType = .int64)
    (hok : lv.withdraw amount waiveUnrealizedLoss = .ok r) (herr : r.error = none)
    -- not the final withdrawal, which zeroes the vault instead
    (hst : STAmount.ofNumber .int64 lv.sharesTotal .to_nearest = .ok sharesTotalAmount)
    (hfin : r.sharesBurned.operator_eq sharesTotalAmount = false) :
    -- assetsTotal' = assetsTotal - assets', within depositε
    RoundsWithin r.vault'.assetsTotal
      (lv.toExact.assetsTotal - r.assets'.toRat) .to_nearest depositε ∧
    -- assetsAvailable' = assetsAvailable - assets', within depositε
    RoundsWithin r.vault'.assetsAvailable
      (lv.toExact.assetsAvailable - r.assets'.toRat) .to_nearest depositε ∧
    -- sharesTotal' = sharesTotal - burned shares, exactly, whenever the
    -- stored total fits in the share domain (int64)
    ((lv.toExact.sharesTotal : ℚ) ≤ 2 ^ 63 - 1 →
      r.vault'.sharesTotal.toRat = (lv.toExact.sharesTotal : ℚ) - r.sharesBurned.toRat) :=
  LawfulVault.withdraw_vault_updates_proof lv amount waiveUnrealizedLoss sharesTotalAmount r
    hpnn hnn hc hSnt hok herr hst hfin

/-- Witness: the error term in `withdraw_vault_updates` cannot be dropped, a
non-final run exists where the stored total is not the exact difference. -/
theorem LawfulVault.withdraw_vault_updates_attained :
    ∃ (lv : LawfulVault) (amount : WithdrawAmount) (waiveUnrealizedLoss : Bool)
      (sharesTotalAmount : STAmount) (r : WithdrawResult),
      lv.withdraw amount waiveUnrealizedLoss = .ok r ∧ r.error = none ∧
      STAmount.ofNumber .int64 lv.sharesTotal .to_nearest = .ok sharesTotalAmount ∧
      r.sharesBurned.operator_eq sharesTotalAmount = false ∧
      r.vault'.assetsTotal.toRat ≠ lv.toExact.assetsTotal - r.assets'.toRat :=
  LawfulVault.withdraw_vault_updates_witness

/-- Witness: the payout from the shares round-trip is never rounded to the
vault scale, unlike a deposit request on entry. A run exists where re-rounding
the payout `0.0009999999999998571` would change it, and the stored totals move
by the different on-ledger amount `0.000999999999999857`.
`assets''` - the payout `r.assets'` re-rounded to the vault scale -/
theorem LawfulVault.withdraw_applied_delta_attained :
    ∃ (lv : LawfulVault) (amount : WithdrawAmount) (waiveUnrealizedLoss : Bool)
      (assets'' : STAmount) (r : WithdrawResult)
      (deltaTotal : Number) (deltaAmount : STAmount),
      lv.withdraw amount waiveUnrealizedLoss = .ok r ∧ r.error = none ∧
      roundToVaultExponent r.assets' lv.assetsTotal = .ok assets'' ∧
      assets''.operator_eq r.assets' = false ∧
      lv.assetsTotal.operator_sub r.vault'.assetsTotal .to_nearest = .ok deltaTotal ∧
      STAmount.ofNumber lv.numericType deltaTotal .to_nearest = .ok deltaAmount ∧
      deltaAmount.operator_eq r.assets' = false :=
  LawfulVault.withdraw_applied_delta_witness

/-- Integral strengthening of `withdraw_vault_updates`: in-domain integer
differences are stored exactly. -/
theorem LawfulVault.withdraw_vault_updates_integral (lv : LawfulVault) (amount : WithdrawAmount)
    -- the starting vault is lawful
    (waiveUnrealizedLoss : Bool) (sharesTotalAmount : STAmount) (r : WithdrawResult)
    (hint : lv.numericType.isIntegral = true) -- the vault holds an integral asset
    (hok : lv.withdraw amount waiveUnrealizedLoss = .ok r) (herr : r.error = none)
    (hnn : 0 ≤ r.assets'.toRat) -- a nonnegative payout, negative ones can leave the domain
    -- not the final withdrawal, which zeroes the vault instead
    (hst : STAmount.ofNumber .int64 lv.sharesTotal .to_nearest = .ok sharesTotalAmount)
    (hfin : r.sharesBurned.operator_eq sharesTotalAmount = false)
    -- the stored total fits the asset domain (int64)
    (hsz : lv.toExact.assetsTotal ≤ 2 ^ 63 - 1) :
    r.vault'.assetsTotal.toRat = lv.toExact.assetsTotal - r.assets'.toRat ∧
    r.vault'.assetsAvailable.toRat = lv.toExact.assetsAvailable - r.assets'.toRat :=
  LawfulVault.withdraw_vault_updates_integral_proof lv amount waiveUnrealizedLoss sharesTotalAmount r
    hint hok herr hnn hst hfin hsz

/-- A successful non-final withdrawal with a positive `assets'` strictly decreases
the stored `assetsTotal` and never increases the stored `assetsAvailable`: the guard
rejecting an `assets'` too small to move the rounded `assetsTotal` guarantees the
total moved, and both fields subtract the same non-negative payout. The
`assetsAvailable` bound stays at `≤`: its strict decrease is a finer-grid
tie-exclusion the `assetsTotal` guard alone does not transfer. -/
theorem LawfulVault.withdraw_payout_decreases_assets (lv : LawfulVault) (amount : WithdrawAmount)
    -- the starting vault is lawful
    (waiveUnrealizedLoss : Bool) (sharesTotalAmount : STAmount) (r : WithdrawResult)
    (hc : r.sharesBurned.Canonical) -- burned shares canonical, so the payout's `toNumber` is exact
    (hok : lv.withdraw amount waiveUnrealizedLoss = .ok r) (herr : r.error = none)
    (hpay : 0 < r.assets'.toRat) -- assets' is positive
    -- not the final withdrawal, which zeroes the vault instead
    (hst : STAmount.ofNumber .int64 lv.sharesTotal .to_nearest = .ok sharesTotalAmount)
    (hfin : r.sharesBurned.operator_eq sharesTotalAmount = false) :
    r.vault'.assetsTotal.toRat < lv.toExact.assetsTotal ∧
    r.vault'.assetsAvailable.toRat ≤ lv.toExact.assetsAvailable :=
  LawfulVault.withdraw_payout_decreases_assets_proof lv amount waiveUnrealizedLoss sharesTotalAmount r
    hc hok herr hpay hst hfin

/-- The `assetsAvailable` guard compares the stored value against the rounded
amount, which can exceed the named shares' worth by the interior stage error.
A `depositε` relative margin under `assetsAvailable` absorbs every overshoot,
so the guard cannot fire. -/
theorem LawfulVault.withdraw_under_available (lv : LawfulVault) (shares : STAmount) (waiveUnrealizedLoss : Bool)
    (r : WithdrawResult)
    -- the starting vault is lawful
    (hpos : 0 < shares.toRat) -- the withdrawn shares are positive, the preflight guard
    (hc : shares.Canonical) -- shares stored canonically, so `shares.toNumber` is value-exact
    -- the subtraction computing assetsTotal minus lossUnrealized
    -- does not round (automatic when loss is zero)
    (hnav : lv.WithdrawNavExact waiveUnrealizedLoss)
    (hok : lv.withdraw (.vaultShares shares) waiveUnrealizedLoss = .ok r)
    -- the named shares' worth fits under assetsAvailable with margin
    (hmargin : lv.idealAssetsWithdraw waiveUnrealizedLoss shares.toRat *
      (1 + depositε) ≤ lv.toExact.assetsAvailable) :
    -- the assetsAvailable guard cannot fire
    r.error ≠ some .tecINSUFFICIENT_FUNDS :=
  LawfulVault.withdraw_under_available_proof lv shares waiveUnrealizedLoss r hpos hc hnav hok hmargin


/-- A successful withdrawal empties the vault exactly when it burns the whole
share total: `sharesBurned` comparing equal to the stored share total is
equivalent to the result state having all three stored fields zero. A partial
burn always leaves a nonzero `sharesTotal'`, an over-burn a negative one. -/
theorem LawfulVault.withdraw_final_iff (lv : LawfulVault) (amount : WithdrawAmount) (waiveUnrealizedLoss : Bool)
    -- the starting vault is lawful
    (sharesTotalAmount : STAmount) (r : WithdrawResult)
    (hpos : 0 < r.sharesBurned.toRat) -- a positive burn (the meaningful by-shares input class)
    (hc : r.sharesBurned.Canonical) -- burned shares canonical (used by the `←` direction)
    (hSnt : r.sharesBurned.mNumericType = .int64) -- burned shares are the `int64` share amount
    (hok : lv.withdraw amount waiveUnrealizedLoss = .ok r) (herr : r.error = none)
    (hst : STAmount.ofNumber .int64 lv.sharesTotal .to_nearest = .ok sharesTotalAmount) :
    r.sharesBurned.operator_eq sharesTotalAmount = true ↔
      r.vault'.toRawVault = { lv.toRawVault with assetsTotal := Number.zero, assetsAvailable := Number.zero, sharesTotal := Number.zero } :=
  LawfulVault.withdraw_final_iff_proof lv amount waiveUnrealizedLoss sharesTotalAmount r
    hpos hc hSnt hok herr hst

/-- A final withdrawal pays all of `assetsAvailable`, and that amount obeys
the same bounds as a regular withdrawal of the same shares: at most the
shares' exact worth, at least the lower bound of `withdraw_payout`. It is
bounded on both sides because the computed amount passed the `assetsAvailable`
guard, and on a lawful vault `assetsAvailable` is at most the shares' exact
worth. -/
theorem LawfulVault.withdraw_final_payout (lv : LawfulVault) (amount : WithdrawAmount) (waiveUnrealizedLoss : Bool)
    -- the starting vault is lawful
    (r : WithdrawResult)
    (hpos : 0 < r.sharesBurned.toRat) -- a positive burn (the meaningful by-shares input class)
    (hc : r.sharesBurned.Canonical) -- burned shares canonical, so their `toNumber` is value-exact
    (hSnt : r.sharesBurned.mNumericType = .int64) -- burned shares are the `int64` share amount
    -- the subtraction computing assetsTotal minus lossUnrealized
    -- does not round (automatic when loss is zero)
    (hnav : lv.WithdrawNavExact waiveUnrealizedLoss)
    (hok : lv.withdraw amount waiveUnrealizedLoss = .ok r) (herr : r.error = none)
    -- the run was final: only the final branch zeroes the share total
    (hfinal : r.vault'.sharesTotal = Number.zero)
    -- `assetsAvailable` is representable at the vault's numeric type, so the final
    -- `ofNumber` pays exactly `assetsAvailable` and never rounds up past the shares'
    -- worth (holds on all reachable vaults; false on a Lawful-non-Reachable one)
    (hAAc : ∀ aa : STAmount,
      STAmount.ofNumber lv.numericType lv.assetsAvailable .to_nearest = .ok aa →
        aa.toRat = lv.assetsAvailable.toRat) :
    -- at most the whole share total's exact worth
    r.assets'.toRat ≤ lv.idealAssetsWithdraw waiveUnrealizedLoss r.sharesBurned.toRat ∧
    -- with assets available to pay, at least what the regular accuracy window
    -- guarantees for the same shares. When no assets are available the final payout is
    -- the zero record, whose `mOffset` (`-100`) sits below the smallest representable
    -- grid, so its `2` ULP slack is too fine to cover the shares' worth and the lower
    -- bound is gated on a positive available balance
    (0 < lv.toExact.assetsAvailable →
      lv.idealAssetsWithdraw waiveUnrealizedLoss r.sharesBurned.toRat * (1 - depositε) -
        2 * (10 : ℚ) ^ r.assets'.exponent ≤ r.assets'.toRat) :=
  LawfulVault.withdraw_final_payout_proof lv amount waiveUnrealizedLoss r hpos hc hSnt hnav
    hok herr hfinal hAAc

-- `LawfulVault.withdraw_can_empty` is FALSE as stated, so it is omitted rather than
-- assumed. A full-share redemption can hard-fail with `tecINSUFFICIENT_FUNDS`:
-- the interior to-nearest `mul`/`div` in `sharesToAssetsWithdraw` can overshoot
-- the priced payout by up to 1 ULP above `assetsAvailable`, and the funds guard
-- runs before the final-withdrawal branch, so it rejects the redemption. A sole
-- shareholder owning 100% of the vault can therefore be unable to exit in one
-- withdrawal even with nothing lent out. Confirmed by machine-checked witnesses
-- (see vault_bugs_confirmed.md). The former statement, for the record:
--
-- theorem LawfulVault.withdraw_can_empty (sharesTotalAmount : STAmount)
--     (lv.wf : lv.WF) (lv.exact : lv.toExact.Valid)
--     (hlent : lv.toExact.assetsTotal = lv.toExact.assetsAvailable)
--     (hst : STAmount.ofNumber .int64 lv.sharesTotal .to_nearest = .ok sharesTotalAmount) :
--     ∃ allAvailable : STAmount,
--       STAmount.ofNumber lv.numericType lv.assetsAvailable .to_nearest = .ok allAvailable ∧
--       lv.withdraw (.vaultShares sharesTotalAmount) false =
--         .ok ⟨none,
--           { lv.toRawVault with assetsTotal := Number.zero, assetsAvailable := Number.zero,
--                    sharesTotal := Number.zero },
--           allAvailable, sharesTotalAmount⟩

end XRPL.Model.SingleAssetVault
