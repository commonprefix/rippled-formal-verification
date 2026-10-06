import XRPL.Properties.Vault.Defs
import XRPL.Properties.Vault.VaultValid
import XRPL.Model.Vault.VaultWithdraw
import XRPL.Properties.Approx
import XRPL.Properties.Protocol.STAmount.Common.DiscreteDefs
import XRPL.Properties.Vault.Common.WithdrawDefs
import XRPL.Properties.Vault.Proofs.WithdrawAccuracy
import XRPL.Properties.Vault.Proofs.WithdrawMono
import XRPL.Properties.Vault.Proofs.WithdrawPricing
import XRPL.Properties.Vault.Proofs.WithdrawPricingWitness
import XRPL.Properties.Vault.Proofs.ExactUpdates
import XRPL.Properties.Vault.Proofs.WithdrawTight
import XRPL.Properties.Vault.Proofs.WithdrawTightWitness

/-! # `Vault.withdraw` accuracy

Each `Number` stage of the withdraw exchange is correctly rounded within
`10 / (2 ^ 63 + 2)`, and under an exact pricing value no bound below composes
more than three stages, so the deposit budget `depositε = 10 ^ (-17)` covers
every composition and no separate withdraw constant is defined. -/

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol

variable (v : Vault)


/-! ## `Vault.sharesToAssetsWithdraw` -/

/-- The returned amount is nonnegative and matches the shares' worth up to
`depositε` relatively and half a ULP on either side: the final conversion rounds
to nearest, so it can pay half a ULP more than the worth. -/
theorem Vault.sharesToAssetsWithdraw_bounds (v : Vault) (shares assets : STAmount)
    -- the starting vault is lawful
    (waiveUnrealizedLoss : Bool)
    (hnn : 0 ≤ shares.toRat) -- nonnegative shares, negative ones price negatively
    (hc : shares.Canonical) -- shares stored canonically, so `shares.toNumber` is value-exact
    -- the subtraction computing assetsTotal minus lossUnrealized
    -- does not round (automatic when loss is zero)
    (hnav : v.WithdrawNavExact waiveUnrealizedLoss)
    (hok : v.sharesToAssetsWithdraw shares waiveUnrealizedLoss = .ok assets) :
    0 ≤ assets.toRat ∧
    -- overpays the shares' worth by at most the stage error plus half a ULP
    assets.toRat ≤ v.idealAssetsWithdraw waiveUnrealizedLoss shares.toRat * (1 + depositε) +
      (1 / 2 : ℚ) * (10 : ℚ) ^ assets.exponent ∧
    -- a nonzero returned amount underpays it by at most the stage error plus half a ULP
    (assets.isZero = false →
      v.idealAssetsWithdraw waiveUnrealizedLoss shares.toRat - assets.toRat ≤
        v.idealAssetsWithdraw waiveUnrealizedLoss shares.toRat * depositε +
          (1 / 2 : ℚ) * (10 : ℚ) ^ assets.exponent) :=
  Vault.sharesToAssetsWithdraw_bounds_proof v shares assets waiveUnrealizedLoss hnn hc hnav hok

/-- Witness for the upper half-ULP term of `sharesToAssetsWithdraw_bounds`: on an
integral vault a run pays exactly half a unit above the shares' worth (`2` for `1.5`),
within the relative term of the bound. -/
theorem Vault.sharesToAssetsWithdraw_overshoot_attained :
    ∃ (v : Vault) (shares assets : STAmount) (waiveUnrealizedLoss : Bool),
      0 < shares.toRat ∧
      v.WithdrawNavExact waiveUnrealizedLoss ∧
      v.sharesToAssetsWithdraw shares waiveUnrealizedLoss = .ok assets ∧
      assets.toRat = v.idealAssetsWithdraw waiveUnrealizedLoss shares.toRat +
        (1 / 2 : ℚ) * (10 : ℚ) ^ assets.exponent :=
  Vault.sharesToAssetsWithdraw_overshoot_witness

/-- Fractional witness for the upper half-ULP term of `sharesToAssetsWithdraw_bounds`: a
run pays exactly half a 16-digit ULP above the shares' worth
(`1.000000000000002` for `1.0000000000000015`). -/
theorem Vault.sharesToAssetsWithdraw_overshoot_frac_attained :
    ∃ (v : Vault) (shares assets : STAmount) (waiveUnrealizedLoss : Bool),
      v.numericType = .fractional ∧
      0 < shares.toRat ∧
      v.WithdrawNavExact waiveUnrealizedLoss ∧
      v.sharesToAssetsWithdraw shares waiveUnrealizedLoss = .ok assets ∧
      assets.toRat = v.idealAssetsWithdraw waiveUnrealizedLoss shares.toRat +
        (1 / 2 : ℚ) * (10 : ℚ) ^ assets.exponent :=
  Vault.sharesToAssetsWithdraw_overshoot_frac_witness

/-- Witness for the lower half-ULP term of `sharesToAssetsWithdraw_bounds`: on an
integral vault a nonzero payout is exactly half a unit below the shares' worth (`2` for
`2.5`), within the relative term of the bound. -/
theorem Vault.sharesToAssetsWithdraw_shortfall_attained :
    ∃ (v : Vault) (shares assets : STAmount) (waiveUnrealizedLoss : Bool),
      0 < shares.toRat ∧
      v.WithdrawNavExact waiveUnrealizedLoss ∧
      v.sharesToAssetsWithdraw shares waiveUnrealizedLoss = .ok assets ∧
      assets.isZero = false ∧
      v.idealAssetsWithdraw waiveUnrealizedLoss shares.toRat - assets.toRat =
        (1 / 2 : ℚ) * (10 : ℚ) ^ assets.exponent :=
  Vault.sharesToAssetsWithdraw_shortfall_witness

/-- Fractional witness for the lower half-ULP term of `sharesToAssetsWithdraw_bounds`: a
run pays exactly half a 16-digit ULP below the shares' worth (`1` for
`1.0000000000000005`). -/
theorem Vault.sharesToAssetsWithdraw_shortfall_frac_attained :
    ∃ (v : Vault) (shares assets : STAmount) (waiveUnrealizedLoss : Bool),
      v.numericType = .fractional ∧
      0 < shares.toRat ∧
      v.WithdrawNavExact waiveUnrealizedLoss ∧
      v.sharesToAssetsWithdraw shares waiveUnrealizedLoss = .ok assets ∧
      assets.isZero = false ∧
      v.idealAssetsWithdraw waiveUnrealizedLoss shares.toRat - assets.toRat =
        (1 / 2 : ℚ) * (10 : ℚ) ^ assets.exponent :=
  Vault.sharesToAssetsWithdraw_shortfall_frac_witness

/-- `sharesToAssetsWithdraw_bounds` without the `WithdrawNavExact` hypothesis,
so it also holds when computing assetsTotal minus lossUnrealized rounds. That
rounding moves the price of every share, and the
worst case is `navSlack * shares / sharesTotal`, which is added to both
bounds. When `WithdrawNavExact` holds, `sharesToAssetsWithdraw_bounds` gives
the tighter bounds without the slack term. -/
theorem Vault.sharesToAssetsWithdraw_total (v : Vault) (shares assets : STAmount)
    -- the starting vault is lawful
    (waiveUnrealizedLoss : Bool)
    (hnn : 0 ≤ shares.toRat) -- nonnegative shares, negative ones price negatively
    (hc : shares.Canonical) -- shares stored canonically, so `shares.toNumber` is value-exact
    (hok : v.sharesToAssetsWithdraw shares waiveUnrealizedLoss = .ok assets) :
    -- overpays the shares' worth plus the slack by at most the stage error plus half a ULP
    assets.toRat ≤
      (v.idealAssetsWithdraw waiveUnrealizedLoss shares.toRat +
        v.navSlack * shares.toRat / (v.toExact.sharesTotal : ℚ)) * (1 + depositε) +
      (1 / 2 : ℚ) * (10 : ℚ) ^ assets.exponent ∧
    -- a nonzero payout falls short of the shares' worth by at most the slack
    -- plus half a ULP
    (assets.isZero = false →
      v.idealAssetsWithdraw waiveUnrealizedLoss shares.toRat - assets.toRat ≤
        v.navSlack * shares.toRat / (v.toExact.sharesTotal : ℚ) * (1 + depositε) +
          (1 / 2 : ℚ) * (10 : ℚ) ^ assets.exponent) :=
  Vault.sharesToAssetsWithdraw_total_proof v shares assets waiveUnrealizedLoss hnn hc hok

/-- Witness for the upper half-ULP term of `sharesToAssetsWithdraw_total`: shrinking it by
`10⁻¹⁶` of a ULP breaks the upper conjunct. -/
theorem Vault.sharesToAssetsWithdraw_total_overshoot_attained :
    ∃ (v : Vault) (shares assets : STAmount) (waiveUnrealizedLoss : Bool),
      0 < shares.toRat ∧
      v.sharesToAssetsWithdraw shares waiveUnrealizedLoss = .ok assets ∧
      (v.idealAssetsWithdraw waiveUnrealizedLoss shares.toRat +
          v.navSlack * shares.toRat / (v.toExact.sharesTotal : ℚ)) * (1 + depositε) +
        (1 / 2 - (10 : ℚ) ^ (-16 : ℤ)) * (10 : ℚ) ^ assets.exponent < assets.toRat :=
  Vault.sharesToAssetsWithdraw_total_witness

/-- Witness for the lower half-ULP term of `sharesToAssetsWithdraw_total`: shrinking it by
`10⁻¹⁶` of a ULP breaks the lower conjunct. -/
theorem Vault.sharesToAssetsWithdraw_total_shortfall_attained :
    ∃ (v : Vault) (shares assets : STAmount) (waiveUnrealizedLoss : Bool),
      0 < shares.toRat ∧
      v.sharesToAssetsWithdraw shares waiveUnrealizedLoss = .ok assets ∧
      assets.isZero = false ∧
      v.navSlack * shares.toRat / (v.toExact.sharesTotal : ℚ) * (1 + depositε) +
        (1 / 2 - (10 : ℚ) ^ (-16 : ℤ)) * (10 : ℚ) ^ assets.exponent <
        v.idealAssetsWithdraw waiveUnrealizedLoss shares.toRat - assets.toRat :=
  Vault.sharesToAssetsWithdraw_total_shortfall_witness

/-! ## `Vault.withdraw` -/

/-- A successful withdrawal that names shares burns exactly the named amount.
Error records report zero, the contract in `Unchanged.lean`. -/
theorem Vault.withdraw_sharesBurned_exact (shares : STAmount) (waiveUnrealizedLoss : Bool)
    (r : WithdrawResult)
    (hpos : 0 < shares.toRat)
    (hok : v.withdraw (.vaultShares shares) waiveUnrealizedLoss hpos = .ok r)
    (herr : r.error = none) :
    r.sharesBurned = shares :=
  Vault.withdraw_sharesBurned_exact_proof v shares waiveUnrealizedLoss r hpos hok herr

/-- Withdrawing by assets burns a whole, positive number of shares: at most
`sharesε` relatively above the ideal share count (the two `.to_nearest` pricing
stages), and less than one share plus `sharesε` below it (shares are truncated). -/
theorem Vault.withdraw_sharesBurned (v : Vault) (assets : STAmount)
    (waiveUnrealizedLoss : Bool) (r : WithdrawResult)
    (hpos : 0 < assets.toRat) (hc : assets.Canonical)
    (hnav : v.WithdrawNavExact waiveUnrealizedLoss)
    (hok : v.withdraw (.vaultAssets assets) waiveUnrealizedLoss hpos = .ok r)
    (herr : r.error = none) :
    r.sharesBurned.toRat.den = 1 ∧ 0 < r.sharesBurned.toRat ∧
    r.sharesBurned.toRat ≤
      v.idealSharesWithdraw waiveUnrealizedLoss assets.toRat * (1 + sharesε) ∧
    v.idealSharesWithdraw waiveUnrealizedLoss assets.toRat * (1 - sharesε) - 1 <
      r.sharesBurned.toRat :=
  Vault.withdraw_sharesBurned_proof v assets waiveUnrealizedLoss r hpos hc hnav hok herr

/-- Witness for the one-share truncation term of `withdraw_sharesBurned`: a run burns more
than `1 - 10⁻¹⁴` shares below the ideal beyond the relative term (`1 - 10⁻¹⁵` short in
that run). -/
theorem Vault.withdraw_sharesBurned_truncation_attained :
    ∃ (v : Vault) (assets : STAmount) (waiveUnrealizedLoss : Bool) (hpos : 0 < assets.toRat)
      (r : WithdrawResult),
      assets.Canonical ∧ v.WithdrawNavExact waiveUnrealizedLoss ∧
      v.withdraw (.vaultAssets assets) waiveUnrealizedLoss hpos = .ok r ∧ r.error = none ∧
      v.idealSharesWithdraw waiveUnrealizedLoss assets.toRat * sharesε + (1 - 1 / 10 ^ 14) <
        v.idealSharesWithdraw waiveUnrealizedLoss assets.toRat - r.sharesBurned.toRat :=
  Vault.withdraw_sharesBurned_witness

/-- Witness for the relative `sharesε` term of `withdraw_sharesBurned`: a run burns
`1.0841995·10⁻¹⁸` relatively above the ideal, `98.56%` of `sharesε = 1.1·10⁻¹⁸`. -/
theorem Vault.withdraw_sharesBurned_relative_attained :
    ∃ (v : Vault) (assets : STAmount) (waiveUnrealizedLoss : Bool) (hpos : 0 < assets.toRat)
      (r : WithdrawResult),
      assets.Canonical ∧ v.WithdrawNavExact waiveUnrealizedLoss ∧
      v.withdraw (.vaultAssets assets) waiveUnrealizedLoss hpos = .ok r ∧ r.error = none ∧
      v.idealSharesWithdraw waiveUnrealizedLoss assets.toRat * (10841995 / 10 ^ 25) <
        r.sharesBurned.toRat - v.idealSharesWithdraw waiveUnrealizedLoss assets.toRat :=
  Vault.withdraw_sharesBurned_sharp_witness

/-- A non-final payout is nonnegative, exceeds the burned shares' worth by at most
the stage error plus half a ULP (`.to_nearest` pricing), and falls short of it by at
most the stage error plus the larger of half a ULP of the payout and one step of the
post-withdrawal total's grid less half a ULP (the grid clamp). -/
theorem Vault.withdraw_payout (v : Vault) (amount : WithdrawAmount)
    (waiveUnrealizedLoss : Bool) (sharesTotalAmount : STAmount) (r : WithdrawResult)
    (hnn : 0 ≤ r.sharesBurned.toRat) (hc : r.sharesBurned.Canonical)
    (hnav : v.WithdrawNavExact waiveUnrealizedLoss)
    (hpos : 0 < amount.amount.toRat)
    (hok : v.withdraw amount waiveUnrealizedLoss hpos = .ok r) (herr : r.error = none)
    (hst : STAmount.ofNumber .int64 v.sharesTotal .to_nearest = .ok sharesTotalAmount)
    (hfin : r.sharesBurned.operator_eq sharesTotalAmount = false) :
    0 ≤ r.assets'.toRat ∧
    r.assets'.toRat ≤
      v.idealAssetsWithdraw waiveUnrealizedLoss r.sharesBurned.toRat * (1 + depositε) +
        1 / 2 * (10 : ℚ) ^ r.assets'.exponent ∧
    ∃ atr' : STAmount,
      STAmount.ofNumber v.numericType r.vault'.assetsTotal .to_nearest = .ok atr' ∧
      v.idealAssetsWithdraw waiveUnrealizedLoss r.sharesBurned.toRat - r.assets'.toRat ≤
        v.idealAssetsWithdraw waiveUnrealizedLoss r.sharesBurned.toRat * depositε +
          max (1 / 2 * (10 : ℚ) ^ r.assets'.exponent)
            ((10 : ℚ) ^ atr'.exponent - 1 / 2 * (10 : ℚ) ^ r.assets'.exponent) :=
  Vault.withdraw_payout_proof v amount waiveUnrealizedLoss sharesTotalAmount r hnn hc hnav hpos hok
    herr hst hfin

/-- Witness for the upper half-ULP term of `withdraw_payout`: a run's payout exceeds the
burned shares' worth plus the relative term by all but `10⁻¹⁵` of the half-unit term. -/
theorem Vault.withdraw_payout_overshoot_attained :
    ∃ (v : Vault) (amount : WithdrawAmount) (waiveUnrealizedLoss : Bool)
      (hpos : 0 < amount.amount.toRat) (sharesTotalAmount : STAmount) (r : WithdrawResult),
      0 ≤ r.sharesBurned.toRat ∧ r.sharesBurned.Canonical ∧
      v.WithdrawNavExact waiveUnrealizedLoss ∧
      v.withdraw amount waiveUnrealizedLoss hpos = .ok r ∧ r.error = none ∧
      STAmount.ofNumber .int64 v.sharesTotal .to_nearest = .ok sharesTotalAmount ∧
      r.sharesBurned.operator_eq sharesTotalAmount = false ∧
      v.idealAssetsWithdraw waiveUnrealizedLoss r.sharesBurned.toRat * (1 + depositε) +
          (1 - 1 / 10 ^ 15) * (1 / 2 * (10 : ℚ) ^ r.assets'.exponent) < r.assets'.toRat :=
  Vault.withdraw_payout_overshoot_witness

/-- Witness for the half-ULP arm of the lower `withdraw_payout` bound: without the clamp a
run's payout falls short of the burned shares' worth by the relative term plus all but
`10⁻¹⁵` of the `max` term. -/
theorem Vault.withdraw_payout_round_attained :
    ∃ (v : Vault) (amount : WithdrawAmount) (waiveUnrealizedLoss : Bool)
      (hpos : 0 < amount.amount.toRat) (sharesTotalAmount : STAmount) (r : WithdrawResult),
      0 ≤ r.sharesBurned.toRat ∧ r.sharesBurned.Canonical ∧
      v.WithdrawNavExact waiveUnrealizedLoss ∧
      v.withdraw amount waiveUnrealizedLoss hpos = .ok r ∧ r.error = none ∧
      STAmount.ofNumber .int64 v.sharesTotal .to_nearest = .ok sharesTotalAmount ∧
      r.sharesBurned.operator_eq sharesTotalAmount = false ∧
      ∃ atr' : STAmount,
        STAmount.ofNumber v.numericType r.vault'.assetsTotal .to_nearest = .ok atr' ∧
        v.idealAssetsWithdraw waiveUnrealizedLoss r.sharesBurned.toRat * depositε +
            (1 - 1 / 10 ^ 15) * max (1 / 2 * (10 : ℚ) ^ r.assets'.exponent)
              ((10 : ℚ) ^ atr'.exponent - 1 / 2 * (10 : ℚ) ^ r.assets'.exponent) <
          v.idealAssetsWithdraw waiveUnrealizedLoss r.sharesBurned.toRat - r.assets'.toRat :=
  Vault.withdraw_payout_round_witness

/-- Witness for the grid-clamp arm of the lower `withdraw_payout` bound: a payout floored
onto the post-withdrawal grid falls short of the burned shares' worth by the relative term
plus all but `10⁻⁷` of the `max` term. -/
theorem Vault.withdraw_payout_clamp_attained :
    ∃ (v : Vault) (amount : WithdrawAmount) (waiveUnrealizedLoss : Bool)
      (hpos : 0 < amount.amount.toRat) (sharesTotalAmount : STAmount) (r : WithdrawResult),
      0 ≤ r.sharesBurned.toRat ∧ r.sharesBurned.Canonical ∧
      v.WithdrawNavExact waiveUnrealizedLoss ∧
      v.withdraw amount waiveUnrealizedLoss hpos = .ok r ∧ r.error = none ∧
      STAmount.ofNumber .int64 v.sharesTotal .to_nearest = .ok sharesTotalAmount ∧
      r.sharesBurned.operator_eq sharesTotalAmount = false ∧
      ∃ atr' : STAmount,
        STAmount.ofNumber v.numericType r.vault'.assetsTotal .to_nearest = .ok atr' ∧
        v.idealAssetsWithdraw waiveUnrealizedLoss r.sharesBurned.toRat * depositε +
            (1 - 1 / 10 ^ 7) * max (1 / 2 * (10 : ℚ) ^ r.assets'.exponent)
              ((10 : ℚ) ^ atr'.exponent - 1 / 2 * (10 : ℚ) ^ r.assets'.exponent) <
          v.idealAssetsWithdraw waiveUnrealizedLoss r.sharesBurned.toRat - r.assets'.toRat :=
  Vault.withdraw_payout_clamp_witness

/-- Integral strengthening of `withdraw_payout`: the shortfall stays below
one whole unit plus the stage error, with no nonzero condition. -/
theorem Vault.withdraw_payout_integral (v : Vault) (amount : WithdrawAmount) (waiveUnrealizedLoss : Bool)
    -- the starting vault is lawful
    (sharesTotalAmount : STAmount) (r : WithdrawResult)
    (hint : v.numericType.isIntegral = true) -- the vault holds an integral asset
    (hnn : 0 ≤ r.sharesBurned.toRat) -- nonnegative shares, negative ones price negatively
    (hc : r.sharesBurned.Canonical) -- burned shares canonical, so their `toNumber` is value-exact
    -- the subtraction computing assetsTotal minus lossUnrealized
    -- does not round (automatic when loss is zero)
    (hnav : v.WithdrawNavExact waiveUnrealizedLoss)
    (hpos : 0 < amount.amount.toRat)
    (hok : v.withdraw amount waiveUnrealizedLoss hpos = .ok r) (herr : r.error = none)
    -- not the final withdrawal, which pays all of assetsAvailable instead
    (hst : STAmount.ofNumber .int64 v.sharesTotal .to_nearest = .ok sharesTotalAmount)
    (hfin : r.sharesBurned.operator_eq sharesTotalAmount = false) :
    v.idealAssetsWithdraw waiveUnrealizedLoss r.sharesBurned.toRat - r.assets'.toRat ≤
      1 + v.idealAssetsWithdraw waiveUnrealizedLoss r.sharesBurned.toRat * depositε :=
  Vault.withdraw_payout_integral_proof v amount waiveUnrealizedLoss sharesTotalAmount r
    hint hnn hc hnav hpos hok herr hst hfin

/-- More shares burned never pays less from the same vault. Every pricing
stage is a monotone function of the share amount: the exact products and
quotients are monotone, correct rounding is monotone, and the final downward
conversion is monotone. -/
theorem Vault.withdraw_payout_monotone (v : Vault) (amount₁ amount₂ : WithdrawAmount)
    -- the starting vault is lawful
    (waiveUnrealizedLoss : Bool) (sharesTotalAmount : STAmount) (r₁ r₂ : WithdrawResult)
    -- the subtraction computing assetsTotal minus lossUnrealized
    -- does not round (automatic when loss is zero)
    (hnav : v.WithdrawNavExact waiveUnrealizedLoss)
    -- the burned shares are stored canonically and are nonnegative
    (hcb₁ : r₁.sharesBurned.Canonical) (hcb₂ : r₂.sharesBurned.Canonical)
    (hnnb₁ : 0 ≤ r₁.sharesBurned.toRat) (hnnb₂ : 0 ≤ r₂.sharesBurned.toRat)
    -- both withdrawals succeed, each starting from the same vault v.toRawVault
    (hpos₁ : 0 < amount₁.amount.toRat)
    (hok₁ : v.withdraw amount₁ waiveUnrealizedLoss hpos₁ = .ok r₁) (herr₁ : r₁.error = none)
    (hpos₂ : 0 < amount₂.amount.toRat)
    (hok₂ : v.withdraw amount₂ waiveUnrealizedLoss hpos₂ = .ok r₂) (herr₂ : r₂.error = none)
    -- neither run is the final withdrawal, which pays all of assetsAvailable instead
    (hst : STAmount.ofNumber .int64 v.sharesTotal .to_nearest = .ok sharesTotalAmount)
    (hfin₁ : r₁.sharesBurned.operator_eq sharesTotalAmount = false)
    (hfin₂ : r₂.sharesBurned.operator_eq sharesTotalAmount = false)
    -- the first run burns at most as many shares
    (hle : r₁.sharesBurned.toRat ≤ r₂.sharesBurned.toRat) :
    -- the first run is paid at most as much
    r₁.assets'.toRat ≤ r₂.assets'.toRat :=
  Vault.withdraw_payout_monotone_proof v amount₁ amount₂ waiveUnrealizedLoss
    sharesTotalAmount r₁ r₂ hnav hcb₁ hcb₂ hnnb₁ hnnb₂
    hpos₁ hok₁ herr₁ hpos₂ hok₂ herr₂ hst hfin₁ hfin₂ hle

/-- On a non-final withdrawal the stored total and available assets each drop by
exactly the recorded payout (the grid clamp puts the payout on the grid of the new
total, so the subtraction is exact), and the share total drops by exactly the burned
shares whenever it fits the share domain. -/
theorem Vault.withdraw_vault_updates (v : Vault) (amount : WithdrawAmount) (waiveUnrealizedLoss : Bool)
    -- the starting vault is lawful
    (sharesTotalAmount : STAmount) (r : WithdrawResult)
    -- the burned shares are a nonnegative int64 amount
    (hnn : 0 ≤ r.sharesBurned.toRat)
    -- burned shares canonical (used by the exact share-total conjunct)
    (hc : r.sharesBurned.Canonical)
    (hSnt : r.sharesBurned.mNumericType = .int64)
    (hpos : 0 < amount.amount.toRat)
    (hok : v.withdraw amount waiveUnrealizedLoss hpos = .ok r) (herr : r.error = none)
    -- not the final withdrawal, which zeroes the vault instead
    (hst : STAmount.ofNumber .int64 v.sharesTotal .to_nearest = .ok sharesTotalAmount)
    (hfin : r.sharesBurned.operator_eq sharesTotalAmount = false) :
    r.vault'.assetsTotal.toRat = v.toExact.assetsTotal - r.assets'.toRat ∧
    r.vault'.assetsAvailable.toRat = v.toExact.assetsAvailable - r.assets'.toRat ∧
    ((v.toExact.sharesTotal : ℚ) ≤ 2 ^ 63 - 1 →
      r.vault'.sharesTotal.toRat = (v.toExact.sharesTotal : ℚ) - r.sharesBurned.toRat) :=
  Vault.withdraw_vault_updates_proof v amount waiveUnrealizedLoss sharesTotalAmount r hnn hc hSnt
    hpos hok herr hst hfin

/-- Integral strengthening of `withdraw_vault_updates`: in-domain integer
differences are stored exactly. -/
theorem Vault.withdraw_vault_updates_integral (v : Vault) (amount : WithdrawAmount)
    -- the starting vault is lawful
    (waiveUnrealizedLoss : Bool) (sharesTotalAmount : STAmount) (r : WithdrawResult)
    (hint : v.numericType.isIntegral = true) -- the vault holds an integral asset
    (hpos : 0 < amount.amount.toRat)
    (hok : v.withdraw amount waiveUnrealizedLoss hpos = .ok r) (herr : r.error = none)
    (hnn : 0 ≤ r.assets'.toRat) -- a nonnegative payout, negative ones can leave the domain
    -- not the final withdrawal, which zeroes the vault instead
    (hst : STAmount.ofNumber .int64 v.sharesTotal .to_nearest = .ok sharesTotalAmount)
    (hfin : r.sharesBurned.operator_eq sharesTotalAmount = false)
    -- the stored total fits the asset domain (int64)
    (hsz : v.toExact.assetsTotal ≤ 2 ^ 63 - 1) :
    r.vault'.assetsTotal.toRat = v.toExact.assetsTotal - r.assets'.toRat ∧
    r.vault'.assetsAvailable.toRat = v.toExact.assetsAvailable - r.assets'.toRat :=
  Vault.withdraw_vault_updates_integral_proof v amount waiveUnrealizedLoss sharesTotalAmount r
    hint hpos hok herr hnn hst hfin hsz

/-- A successful non-final withdrawal with a positive `assets'` strictly decreases
the stored `assetsTotal` and never increases the stored `assetsAvailable`: the guard
rejecting an `assets'` too small to move the rounded `assetsTotal` guarantees the
total moved, and both fields subtract the same non-negative payout. The
`assetsAvailable` bound stays at `≤`: its strict decrease is a finer-grid
tie-exclusion the `assetsTotal` guard alone does not transfer. -/
theorem Vault.withdraw_payout_decreases_assets (v : Vault) (amount : WithdrawAmount)
    -- the starting vault is lawful
    (waiveUnrealizedLoss : Bool) (sharesTotalAmount : STAmount) (r : WithdrawResult)
    (hc : r.sharesBurned.Canonical) -- burned shares canonical, so the payout's `toNumber` is exact
    (hpos : 0 < amount.amount.toRat)
    (hok : v.withdraw amount waiveUnrealizedLoss hpos = .ok r) (herr : r.error = none)
    (hpay : 0 < r.assets'.toRat) -- assets' is positive
    -- not the final withdrawal, which zeroes the vault instead
    (hst : STAmount.ofNumber .int64 v.sharesTotal .to_nearest = .ok sharesTotalAmount)
    (hfin : r.sharesBurned.operator_eq sharesTotalAmount = false) :
    r.vault'.assetsTotal.toRat < v.toExact.assetsTotal ∧
    r.vault'.assetsAvailable.toRat ≤ v.toExact.assetsAvailable :=
  Vault.withdraw_payout_decreases_assets_proof v amount waiveUnrealizedLoss sharesTotalAmount r
    hc hpos hok herr hpay hst hfin

/-- If the burned shares' worth fits under `assetsAvailable` with a margin, the
`assetsAvailable` guard cannot fire. The payout rounds to nearest, so the margin
covers half a unit on an integral vault and half a 16-digit ULP relatively on a
fractional one. -/
theorem Vault.withdraw_under_available (v : Vault) (shares : STAmount) (waiveUnrealizedLoss : Bool)
    (r : WithdrawResult)
    -- the starting vault is lawful
    (hpos : 0 < shares.toRat) -- the withdrawn shares are positive, the preflight guard
    (hc : shares.Canonical) -- shares stored canonically, so `shares.toNumber` is value-exact
    -- the subtraction computing assetsTotal minus lossUnrealized
    -- does not round (automatic when loss is zero)
    (hnav : v.WithdrawNavExact waiveUnrealizedLoss)
    (hok : v.withdraw (.vaultShares shares) waiveUnrealizedLoss hpos = .ok r)
    -- the named shares' worth fits under assetsAvailable with margin
    (hmargin : (if v.numericType.isIntegral then
        v.idealAssetsWithdraw waiveUnrealizedLoss shares.toRat * (1 + depositε) + 1 / 2
      else v.idealAssetsWithdraw waiveUnrealizedLoss shares.toRat *
        (1 + (1 / 2 : ℚ) * (10 : ℚ) ^ (-15 : ℤ) + 2 * (10 : ℚ) ^ (-18 : ℤ))) ≤
      v.toExact.assetsAvailable) :
    -- the assetsAvailable guard cannot fire
    r.error ≠ some .tecINSUFFICIENT_FUNDS :=
  Vault.withdraw_under_available_proof v shares waiveUnrealizedLoss r hpos hc hnav hok hmargin

/-- Witness for the integral margin of `withdraw_under_available`: a margin of
`1/2 - 10⁻¹⁶` units, `10⁻¹⁶` short of the required `1/2`, lets the guard fire. -/
theorem Vault.withdraw_under_available_attained :
    ∃ (v : Vault) (shares : STAmount) (waiveUnrealizedLoss : Bool) (r : WithdrawResult)
      (hpos : 0 < shares.toRat),
      v.numericType.isIntegral = true ∧
      v.WithdrawNavExact waiveUnrealizedLoss ∧
      v.withdraw (.vaultShares shares) waiveUnrealizedLoss hpos = .ok r ∧
      v.idealAssetsWithdraw waiveUnrealizedLoss shares.toRat * (1 + depositε) +
        (1 / 2 - (10 : ℚ) ^ (-16 : ℤ)) ≤ v.toExact.assetsAvailable ∧
      r.error = some .tecINSUFFICIENT_FUNDS :=
  Vault.withdraw_under_available_witness

/-- Witness for the fractional margin of `withdraw_under_available`: a relative margin of
`4.98·10⁻¹⁶`, `99.2%` of the required `½·10⁻¹⁵ + 2·10⁻¹⁸`, lets the guard fire. -/
theorem Vault.withdraw_under_available_frac_attained :
    ∃ (v : Vault) (shares : STAmount) (waiveUnrealizedLoss : Bool) (r : WithdrawResult)
      (hpos : 0 < shares.toRat),
      v.numericType = .fractional ∧
      v.WithdrawNavExact waiveUnrealizedLoss ∧
      v.withdraw (.vaultShares shares) waiveUnrealizedLoss hpos = .ok r ∧
      v.idealAssetsWithdraw waiveUnrealizedLoss shares.toRat * (1 + 498 * (10 : ℚ) ^ (-18 : ℤ))
        ≤ v.toExact.assetsAvailable ∧
      r.error = some .tecINSUFFICIENT_FUNDS :=
  Vault.withdraw_under_available_frac_witness

/-- A successful withdrawal empties the vault exactly when it burns the whole
share total: `sharesBurned` comparing equal to the stored share total is
equivalent to the result state having all three stored fields zero. A partial
burn always leaves a nonzero `sharesTotal'`, an over-burn a negative one. -/
theorem Vault.withdraw_final_iff (v : Vault) (amount : WithdrawAmount) (waiveUnrealizedLoss : Bool)
    -- the starting vault is lawful
    (sharesTotalAmount : STAmount) (r : WithdrawResult)
    (hpos : 0 < r.sharesBurned.toRat) -- a positive burn (the meaningful by-shares input class)
    (hc : r.sharesBurned.Canonical) -- burned shares canonical (used by the `←` direction)
    (hSnt : r.sharesBurned.mNumericType = .int64) -- burned shares are the `int64` share amount
    (hposA : 0 < amount.amount.toRat)
    (hok : v.withdraw amount waiveUnrealizedLoss hposA = .ok r) (herr : r.error = none)
    (hst : STAmount.ofNumber .int64 v.sharesTotal .to_nearest = .ok sharesTotalAmount) :
    r.sharesBurned.operator_eq sharesTotalAmount = true ↔
      r.vault'.toRawVault = { v.toRawVault with assetsTotal := Number.zero, assetsAvailable := Number.zero, sharesTotal := Number.zero } :=
  Vault.withdraw_final_iff_proof v amount waiveUnrealizedLoss sharesTotalAmount r
    hpos hc hSnt hposA hok herr hst

/-- A final withdrawal pays all of `assetsAvailable`, and that amount obeys
the same bounds as a regular withdrawal of the same shares: at most the
shares' exact worth, at least the lower bound of `withdraw_payout`. It is
bounded on both sides because the computed amount passed the `assetsAvailable`
guard, and on a lawful vault `assetsAvailable` is at most the shares' exact
worth. -/
theorem Vault.withdraw_final_payout (v : Vault) (amount : WithdrawAmount) (waiveUnrealizedLoss : Bool)
    -- the starting vault is lawful
    (r : WithdrawResult)
    (hpos : 0 < r.sharesBurned.toRat) -- a positive burn (the meaningful by-shares input class)
    (hc : r.sharesBurned.Canonical) -- burned shares canonical, so their `toNumber` is value-exact
    (hSnt : r.sharesBurned.mNumericType = .int64) -- burned shares are the `int64` share amount
    -- the subtraction computing assetsTotal minus lossUnrealized
    -- does not round (automatic when loss is zero)
    (hnav : v.WithdrawNavExact waiveUnrealizedLoss)
    (hposA : 0 < amount.amount.toRat)
    (hok : v.withdraw amount waiveUnrealizedLoss hposA = .ok r) (herr : r.error = none)
    -- the run was final: only the final branch zeroes the share total
    (hfinal : r.vault'.sharesTotal = Number.zero)
    -- `assetsAvailable` is representable at the vault's numeric type, so the final
    -- `ofNumber` pays exactly `assetsAvailable` and never rounds up past the shares'
    -- worth (holds on all reachable vaults; false on a Lawful-non-Reachable one)
    (hAAc : ∀ aa : STAmount,
      STAmount.ofNumber v.numericType v.assetsAvailable .to_nearest = .ok aa →
        aa.toRat = v.assetsAvailable.toRat) :
    -- at most the whole share total's exact worth
    r.assets'.toRat ≤ v.idealAssetsWithdraw waiveUnrealizedLoss r.sharesBurned.toRat ∧
    -- with assets available to pay, at least what the regular accuracy window
    -- guarantees for the same shares. When no assets are available the final payout is
    -- the zero record, whose `mOffset` (`-100`) sits below the smallest representable
    -- grid, so its `2` ULP slack is too fine to cover the shares' worth and the lower
    -- bound is gated on a positive available balance
    (0 < v.toExact.assetsAvailable →
      v.idealAssetsWithdraw waiveUnrealizedLoss r.sharesBurned.toRat * (1 - depositε) -
        2 * (10 : ℚ) ^ r.assets'.exponent ≤ r.assets'.toRat) :=
  Vault.withdraw_final_payout_proof v amount waiveUnrealizedLoss r hpos hc hSnt hnav
    hposA hok herr hfinal hAAc

end XRPL.Model.SingleAssetVault
