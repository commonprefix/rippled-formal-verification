import XRPL.Properties.Vault.Defs
import XRPL.Model.Vault.VaultWithdraw
import XRPL.Properties.Approx
import XRPL.Properties.Protocol.STAmount.Common.DiscreteDefs
import XRPL.Properties.Vault.VaultDeposit
import XRPL.Properties.Vault.Dilution
import XRPL.Properties.Vault.Common.WithdrawDefs
import XRPL.Properties.Vault.Common.WithdrawReduction
import XRPL.Properties.Vault.Common.WithdrawAccuracy

/-! # `Vault.withdraw` accuracy

Each `Number` stage of the withdraw exchange is correctly rounded within
`10 / (2 ^ 63 + 2)`, and under an exact pricing value no bound below composes
more than three stages, so the deposit budget `depositε = 10 ^ (-17)` covers
every composition and no separate withdraw constant is defined. -/

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol

variable (v : Vault)


/-! ## `Vault.sharesToAssetsWithdraw` -/

/-- The returned amount is nonnegative, never exceeds the shares' worth by more than
`depositε` relatively, and when nonzero falls short of it by at most 2 ULP. The final
conversion rounds downward, marked "(waiting the C++ fix)" in the model, but
the interior stages round to nearest, so a plain upper bound by the worth
alone would be false. -/
theorem Vault.sharesToAssetsWithdraw_bounds (shares assets : STAmount)
    (hv : v.Lawful) -- the starting vault is lawful
    (waiveUnrealizedLoss : Bool)
    (hnn : 0 ≤ shares.toRat) -- nonnegative shares, negative ones price negatively
    -- the two subtractions computing assetsTotal - interestUnrealized - lossUnrealized
    -- do not round (automatic when interest and loss are both zero)
    (hnav : v.WithdrawNavExact waiveUnrealizedLoss)
    (hok : v.sharesToAssetsWithdraw shares waiveUnrealizedLoss = .ok assets) :
    0 ≤ assets.toRat ∧
    -- never pays more than the shares' worth, up to the stage error
    assets.toRat ≤ v.idealAssetsWithdraw waiveUnrealizedLoss shares.toRat * (1 + depositε) ∧
    -- a nonzero returned amount underpays the shares' worth by at most the
    -- interior stage error plus 2 ULP (the other direction is already capped
    -- by the relative conjunct)
    (assets.isZero = false →
      v.idealAssetsWithdraw waiveUnrealizedLoss shares.toRat - assets.toRat ≤
        v.idealAssetsWithdraw waiveUnrealizedLoss shares.toRat * depositε +
          2 * (10 : ℚ) ^ assets.exponent) := sorry

/-- Witness: the ULP term in `sharesToAssetsWithdraw_bounds` cannot be
dropped, a run exists whose returned amount misses the shares' worth by more than
`depositε` relative. -/
theorem Vault.sharesToAssetsWithdraw_attained :
    ∃ (v : Vault) (shares assets : STAmount) (waiveUnrealizedLoss : Bool),
      v.Lawful ∧ 0 < shares.toRat ∧
      v.WithdrawNavExact waiveUnrealizedLoss ∧
      v.sharesToAssetsWithdraw shares waiveUnrealizedLoss = .ok assets ∧
      RoundsWithinWitness assets
        (v.idealAssetsWithdraw waiveUnrealizedLoss shares.toRat) depositε := sorry

/-- `sharesToAssetsWithdraw_bounds` without the `WithdrawNavExact` hypothesis,
so it also holds when computing `assetsTotal - interestUnrealized -
lossUnrealized` rounds. That rounding moves the price of every share, and the
worst case is `navSlack * shares / sharesTotal`, which is added to both
bounds. When `WithdrawNavExact` holds, `sharesToAssetsWithdraw_bounds` gives
the tighter bounds without the slack term. -/
theorem Vault.sharesToAssetsWithdraw_total (shares assets : STAmount)
    (hv : v.Lawful) -- the starting vault is lawful
    (waiveUnrealizedLoss : Bool)
    (hnn : 0 ≤ shares.toRat) -- nonnegative shares, negative ones price negatively
    (hok : v.sharesToAssetsWithdraw shares waiveUnrealizedLoss = .ok assets) :
    -- never pays more than the shares' worth plus the slack, up to the stage error
    assets.toRat ≤
      (v.idealAssetsWithdraw waiveUnrealizedLoss shares.toRat +
        v.navSlack * shares.toRat / (v.toExact.sharesTotal : ℚ)) * (1 + depositε) ∧
    -- a nonzero payout falls short of the shares' worth by at most the slack
    -- plus 2 ULP
    (assets.isZero = false →
      v.idealAssetsWithdraw waiveUnrealizedLoss shares.toRat - assets.toRat ≤
        v.navSlack * shares.toRat / (v.toExact.sharesTotal : ℚ) * (1 + depositε) +
          2 * (10 : ℚ) ^ assets.exponent) := sorry

/-! ## `Vault.withdraw` -/

/-- A successful withdrawal that names shares burns exactly the named amount.
Error records report zero, the contract in `Unchanged.lean`. -/
theorem Vault.withdraw_sharesBurned_exact (shares : STAmount) (waiveUnrealizedLoss : Bool)
    (r : WithdrawResult)
    (hok : v.withdraw (.vaultShares shares) waiveUnrealizedLoss = .ok r)
    (herr : r.error = none) :
    r.sharesBurned = shares := by
  obtain ⟨cw, an, sta, hcomp, herr2, -, -, -, hsb, -⟩ :=
    Vault.withdraw_success_reduces v (.vaultShares shares) waiveUnrealizedLoss r hok herr
  obtain ⟨-, hshares⟩ :=
    computeWithdrawByShares_none_reduces v shares waiveUnrealizedLoss cw hcomp herr2
  rw [hsb, hshares]

/-- Shares burned by an asset-denominated withdrawal are a positive integer
matching `idealSharesWithdraw` of the named `assets` up to the `Number` stage
error and the final rounding to the nearest whole share. -/
theorem Vault.withdraw_sharesBurned (assets : STAmount) (waiveUnrealizedLoss : Bool)
    (hv : v.Lawful) -- the starting vault is lawful
    (r : WithdrawResult)
    (hpos : 0 < assets.toRat) -- the withdrawn amount is positive, the preflight guard
    -- the two subtractions computing assetsTotal - interestUnrealized - lossUnrealized
    -- do not round (automatic when interest and loss are both zero)
    (hnav : v.WithdrawNavExact waiveUnrealizedLoss)
    (hok : v.withdraw (.vaultAssets assets) waiveUnrealizedLoss = .ok r)
    (herr : r.error = none) :
    r.sharesBurned.toRat.den = 1 ∧ 0 < r.sharesBurned.toRat ∧
    |r.sharesBurned.toRat - v.idealSharesWithdraw waiveUnrealizedLoss assets.toRat| ≤
      1 / 2 + v.idealSharesWithdraw waiveUnrealizedLoss assets.toRat * depositε := sorry

/-- Witness: the half-share term in `withdraw_sharesBurned` cannot be dropped,
a run exists whose share error exceeds the relative `depositε` bound alone. -/
theorem Vault.withdraw_sharesBurned_attained :
    ∃ (v : Vault) (assets : STAmount) (waiveUnrealizedLoss : Bool) (r : WithdrawResult),
      v.Lawful ∧ 0 < assets.toRat ∧
      v.WithdrawNavExact waiveUnrealizedLoss ∧
      v.withdraw (.vaultAssets assets) waiveUnrealizedLoss = .ok r ∧ r.error = none ∧
      RoundsWithinWitness r.sharesBurned
        (v.idealSharesWithdraw waiveUnrealizedLoss assets.toRat) depositε := sorry

/-- The `assets'` of a successful non-final withdrawal is nonnegative, never
exceeds the burned shares' worth by more than `depositε` relatively, and when
nonzero falls short of it by at most 2 ULP. Both `WithdrawAmount` forms share
this bound, the asset-denominated form derives the burned shares first. -/
theorem Vault.withdraw_payout (amount : WithdrawAmount) (waiveUnrealizedLoss : Bool)
    (hv : v.Lawful) -- the starting vault is lawful
    (sharesTotalAmount : STAmount) (r : WithdrawResult)
    (hnn : 0 ≤ r.sharesBurned.toRat) -- nonnegative shares, negative ones price negatively
    -- the two subtractions computing assetsTotal - interestUnrealized - lossUnrealized
    -- do not round (automatic when interest and loss are both zero)
    (hnav : v.WithdrawNavExact waiveUnrealizedLoss)
    (hok : v.withdraw amount waiveUnrealizedLoss = .ok r) (herr : r.error = none)
    -- not the final withdrawal, which pays all of assetsAvailable instead
    (hst : STAmount.ofNumber .int64 v.sharesTotal .to_nearest = .ok sharesTotalAmount)
    (hfin : r.sharesBurned.operator_eq sharesTotalAmount = false) :
    0 ≤ r.assets'.toRat ∧
    -- never pays more than the burned shares' worth, up to the stage error
    r.assets'.toRat ≤
      v.idealAssetsWithdraw waiveUnrealizedLoss r.sharesBurned.toRat * (1 + depositε) ∧
    -- a nonzero assets' underpays the burned shares' worth by at most 2 ULP
    -- (the other direction is already capped by the relative conjunct)
    (r.assets'.isZero = false →
      v.idealAssetsWithdraw waiveUnrealizedLoss r.sharesBurned.toRat - r.assets'.toRat ≤
        v.idealAssetsWithdraw waiveUnrealizedLoss r.sharesBurned.toRat * depositε +
          2 * (10 : ℚ) ^ r.assets'.exponent) := sorry

/-- Witness: the ULP term in `withdraw_payout` cannot be dropped, a run exists
whose `assets'` misses the burned shares' worth by more than `depositε`
relative. -/
theorem Vault.withdraw_payout_attained :
    ∃ (v : Vault) (amount : WithdrawAmount) (waiveUnrealizedLoss : Bool)
      (sharesTotalAmount : STAmount) (r : WithdrawResult),
      v.Lawful ∧ v.WithdrawNavExact waiveUnrealizedLoss ∧
      v.withdraw amount waiveUnrealizedLoss = .ok r ∧ r.error = none ∧
      STAmount.ofNumber .int64 v.sharesTotal .to_nearest = .ok sharesTotalAmount ∧
      r.sharesBurned.operator_eq sharesTotalAmount = false ∧
      RoundsWithinWitness r.assets'
        (v.idealAssetsWithdraw waiveUnrealizedLoss r.sharesBurned.toRat) depositε := sorry

/-- Integral strengthening of `withdraw_payout`: the shortfall stays below
one whole unit plus the stage error, with no nonzero condition. -/
theorem Vault.withdraw_payout_integral (amount : WithdrawAmount) (waiveUnrealizedLoss : Bool)
    (hv : v.Lawful) -- the starting vault is lawful
    (sharesTotalAmount : STAmount) (r : WithdrawResult)
    (hint : v.numericType.isIntegral = true) -- the vault holds an integral asset
    (hnn : 0 ≤ r.sharesBurned.toRat) -- nonnegative shares, negative ones price negatively
    -- the two subtractions computing assetsTotal - interestUnrealized - lossUnrealized
    -- do not round (automatic when interest and loss are both zero)
    (hnav : v.WithdrawNavExact waiveUnrealizedLoss)
    (hok : v.withdraw amount waiveUnrealizedLoss = .ok r) (herr : r.error = none)
    -- not the final withdrawal, which pays all of assetsAvailable instead
    (hst : STAmount.ofNumber .int64 v.sharesTotal .to_nearest = .ok sharesTotalAmount)
    (hfin : r.sharesBurned.operator_eq sharesTotalAmount = false) :
    v.idealAssetsWithdraw waiveUnrealizedLoss r.sharesBurned.toRat - r.assets'.toRat ≤
      1 + v.idealAssetsWithdraw waiveUnrealizedLoss r.sharesBurned.toRat * depositε := sorry

/-- More shares burned never pays less from the same vault. Every pricing
stage is a monotone function of the share amount: the exact products and
quotients are monotone, correct rounding is monotone, and the final downward
conversion is monotone. -/
theorem Vault.withdraw_payout_monotone (amount₁ amount₂ : WithdrawAmount)
    (hv : v.Lawful) -- the starting vault is lawful
    (waiveUnrealizedLoss : Bool) (sharesTotalAmount : STAmount) (r₁ r₂ : WithdrawResult)
    -- the two subtractions computing assetsTotal - interestUnrealized - lossUnrealized
    -- do not round (automatic when interest and loss are both zero)
    (hnav : v.WithdrawNavExact waiveUnrealizedLoss)
    -- both withdrawals succeed, each starting from the same vault v
    (hok₁ : v.withdraw amount₁ waiveUnrealizedLoss = .ok r₁) (herr₁ : r₁.error = none)
    (hok₂ : v.withdraw amount₂ waiveUnrealizedLoss = .ok r₂) (herr₂ : r₂.error = none)
    -- neither run is the final withdrawal, which pays all of assetsAvailable instead
    (hst : STAmount.ofNumber .int64 v.sharesTotal .to_nearest = .ok sharesTotalAmount)
    (hfin₁ : r₁.sharesBurned.operator_eq sharesTotalAmount = false)
    (hfin₂ : r₂.sharesBurned.operator_eq sharesTotalAmount = false)
    -- the first run burns at most as many shares
    (hle : r₁.sharesBurned.toRat ≤ r₂.sharesBurned.toRat) :
    -- the first run is paid at most as much
    r₁.assets'.toRat ≤ r₂.assets'.toRat := sorry

/-- Both stored asset fields are the old value minus `assets'`, up to the
`depositε` relative error of the `Number` subtraction, and the share total
update is exact whenever the stored total fits the share domain. -/
theorem Vault.withdraw_vault_updates (amount : WithdrawAmount) (waiveUnrealizedLoss : Bool)
    (hv : v.Lawful) -- the starting vault is lawful
    (sharesTotalAmount : STAmount) (r : WithdrawResult)
    (hok : v.withdraw amount waiveUnrealizedLoss = .ok r) (herr : r.error = none)
    -- not the final withdrawal, which zeroes the vault instead
    (hst : STAmount.ofNumber .int64 v.sharesTotal .to_nearest = .ok sharesTotalAmount)
    (hfin : r.sharesBurned.operator_eq sharesTotalAmount = false) :
    -- assetsTotal' = assetsTotal - assets', within depositε
    RoundsWithin r.vault'.assetsTotal
      (v.toExact.assetsTotal - r.assets'.toRat) .to_nearest depositε ∧
    -- assetsAvailable' = assetsAvailable - assets', within depositε
    RoundsWithin r.vault'.assetsAvailable
      (v.toExact.assetsAvailable - r.assets'.toRat) .to_nearest depositε ∧
    -- sharesTotal' = sharesTotal - burned shares, exactly, whenever the
    -- stored total fits in the share domain (int64)
    ((v.toExact.sharesTotal : ℚ) ≤ 2 ^ 63 - 1 →
      r.vault'.sharesTotal.toRat = (v.toExact.sharesTotal : ℚ) - r.sharesBurned.toRat) := sorry

/-- Witness: the error term in `withdraw_vault_updates` cannot be dropped, a
non-final run exists where the stored total is not the exact difference. -/
theorem Vault.withdraw_vault_updates_attained :
    ∃ (v : Vault) (amount : WithdrawAmount) (waiveUnrealizedLoss : Bool)
      (sharesTotalAmount : STAmount) (r : WithdrawResult),
      v.Lawful ∧ v.withdraw amount waiveUnrealizedLoss = .ok r ∧ r.error = none ∧
      STAmount.ofNumber .int64 v.sharesTotal .to_nearest = .ok sharesTotalAmount ∧
      r.sharesBurned.operator_eq sharesTotalAmount = false ∧
      r.vault'.assetsTotal.toRat ≠ v.toExact.assetsTotal - r.assets'.toRat := sorry

/-- Integral strengthening of `withdraw_vault_updates`: in-domain integer
differences are stored exactly. -/
theorem Vault.withdraw_vault_updates_integral (amount : WithdrawAmount)
    (hv : v.Lawful) -- the starting vault is lawful
    (waiveUnrealizedLoss : Bool) (sharesTotalAmount : STAmount) (r : WithdrawResult)
    (hint : v.numericType.isIntegral = true) -- the vault holds an integral asset
    (hok : v.withdraw amount waiveUnrealizedLoss = .ok r) (herr : r.error = none)
    (hnn : 0 ≤ r.assets'.toRat) -- a nonnegative payout, negative ones can leave the domain
    -- not the final withdrawal, which zeroes the vault instead
    (hst : STAmount.ofNumber .int64 v.sharesTotal .to_nearest = .ok sharesTotalAmount)
    (hfin : r.sharesBurned.operator_eq sharesTotalAmount = false)
    -- the stored total fits the asset domain (int64)
    (hsz : v.toExact.assetsTotal ≤ 2 ^ 63 - 1) :
    r.vault'.assetsTotal.toRat = v.toExact.assetsTotal - r.assets'.toRat ∧
    r.vault'.assetsAvailable.toRat = v.toExact.assetsAvailable - r.assets'.toRat :=
  Vault.withdraw_vault_updates_integral_proof v amount waiveUnrealizedLoss sharesTotalAmount r
    hv hint hok herr hnn hst hfin hsz

/-- A successful non-final withdrawal with a positive `assets'` strictly
decreases both stored asset fields: the guard rejecting an `assets'` too small to
move the rounded `assetsTotal` guarantees the stored values moved. -/
theorem Vault.withdraw_payout_decreases_assets (amount : WithdrawAmount)
    (hv : v.Lawful) -- the starting vault is lawful
    (waiveUnrealizedLoss : Bool) (sharesTotalAmount : STAmount) (r : WithdrawResult)
    (hok : v.withdraw amount waiveUnrealizedLoss = .ok r) (herr : r.error = none)
    (hpay : 0 < r.assets'.toRat) -- assets' is positive
    -- not the final withdrawal, which zeroes the vault instead
    (hst : STAmount.ofNumber .int64 v.sharesTotal .to_nearest = .ok sharesTotalAmount)
    (hfin : r.sharesBurned.operator_eq sharesTotalAmount = false) :
    r.vault'.assetsTotal.toRat < v.toExact.assetsTotal ∧
    r.vault'.assetsAvailable.toRat < v.toExact.assetsAvailable := sorry

/-- The `assetsAvailable` guard compares the stored value against the rounded
amount, which can exceed the named shares' worth by the interior stage error.
A `depositε` relative margin under `assetsAvailable` absorbs every overshoot,
so the guard cannot fire. -/
theorem Vault.withdraw_under_available (shares : STAmount) (waiveUnrealizedLoss : Bool)
    (r : WithdrawResult)
    (hv : v.Lawful) -- the starting vault is lawful
    -- the two subtractions computing assetsTotal - interestUnrealized - lossUnrealized
    -- do not round (automatic when interest and loss are both zero)
    (hnav : v.WithdrawNavExact waiveUnrealizedLoss)
    (hok : v.withdraw (.vaultShares shares) waiveUnrealizedLoss = .ok r)
    -- the named shares' worth fits under assetsAvailable with margin
    (hmargin : v.idealAssetsWithdraw waiveUnrealizedLoss shares.toRat *
      (1 + depositε) ≤ v.toExact.assetsAvailable) :
    -- the assetsAvailable guard cannot fire
    r.error ≠ some .tecINSUFFICIENT_FUNDS := sorry


/-- A successful withdrawal empties the vault exactly when it burns the whole
share total: `sharesBurned` comparing equal to the stored share total is
equivalent to the result state having all three stored fields zero. A partial
burn always leaves a nonzero `sharesTotal'`, an over-burn a negative one. -/
theorem Vault.withdraw_final_iff (amount : WithdrawAmount) (waiveUnrealizedLoss : Bool)
    (hv : v.Lawful) -- the starting vault is lawful
    (sharesTotalAmount : STAmount) (r : WithdrawResult)
    (hok : v.withdraw amount waiveUnrealizedLoss = .ok r) (herr : r.error = none)
    (hst : STAmount.ofNumber .int64 v.sharesTotal .to_nearest = .ok sharesTotalAmount) :
    r.sharesBurned.operator_eq sharesTotalAmount = true ↔
      r.vault' = { v with assetsTotal := Number.zero, assetsAvailable := Number.zero,
                          sharesTotal := Number.zero } := sorry

/-- A final withdrawal pays all of `assetsAvailable`, and that amount obeys
the same bounds as a regular withdrawal of the same shares: at most the
shares' exact worth, at least the lower bound of `withdraw_payout`. It is
bounded on both sides because the computed amount passed the `assetsAvailable`
guard, and on a lawful vault `assetsAvailable` is at most the shares' exact
worth. -/
theorem Vault.withdraw_final_payout (amount : WithdrawAmount) (waiveUnrealizedLoss : Bool)
    (hv : v.Lawful) -- the starting vault is lawful
    (r : WithdrawResult)
    -- the two subtractions computing assetsTotal - interestUnrealized - lossUnrealized
    -- do not round (automatic when interest and loss are both zero)
    (hnav : v.WithdrawNavExact waiveUnrealizedLoss)
    (hok : v.withdraw amount waiveUnrealizedLoss = .ok r) (herr : r.error = none)
    -- the run was final: only the final branch zeroes the share total
    (hfinal : r.vault'.sharesTotal = Number.zero)
    -- the share total fits the int64 domain, so its conversion is exact
    (hfit : (v.toExact.sharesTotal : ℚ) ≤ 2 ^ 63 - 1) :
    -- at most the whole share total's exact worth
    r.assets'.toRat ≤ v.idealAssetsWithdraw waiveUnrealizedLoss r.sharesBurned.toRat ∧
    -- at least what the regular accuracy window guarantees for the same shares
    v.idealAssetsWithdraw waiveUnrealizedLoss r.sharesBurned.toRat * (1 - depositε) -
        2 * (10 : ℚ) ^ r.assets'.exponent ≤ r.assets'.toRat := sorry

/-- Withdrawing the whole share total empties any lawful vault with nothing
lent out: the run succeeds, pays all of `assetsAvailable`, and zeroes the
three stored fields. `assetsTotal = assetsAvailable` forces
`interestUnrealized` and `lossUnrealized` to zero by lawfulness. Lent assets
make the shares' worth exceed `assetsAvailable`, so the restriction is
necessary. -/
theorem Vault.withdraw_can_empty (sharesTotalAmount : STAmount)
    (hv : v.Lawful) -- the starting vault is lawful
    (hlent : v.toExact.assetsTotal = v.toExact.assetsAvailable) -- nothing lent out
    -- the share total converts to an int64 amount (it fits the share domain)
    (hst : STAmount.ofNumber .int64 v.sharesTotal .to_nearest = .ok sharesTotalAmount) :
    ∃ allAvailable : STAmount,
      STAmount.ofNumber v.numericType v.assetsAvailable .to_nearest = .ok allAvailable ∧
      v.withdraw (.vaultShares sharesTotalAmount) false =
        .ok ⟨none,
          { v with assetsTotal := Number.zero, assetsAvailable := Number.zero,
                   sharesTotal := Number.zero },
          allAvailable, sharesTotalAmount⟩ := sorry

end XRPL.Model.SingleAssetVault
