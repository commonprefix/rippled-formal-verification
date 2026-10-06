import XRPL.Model.Vault.VaultWithdraw
import XRPL.Properties.Approx
import XRPL.Properties.Vault.Common.WithdrawDefs
import XRPL.Properties.Vault.Common.VaultDecidable

/-! # Witnesses for the `sharesToAssetsWithdraw` pricing bounds

* `wpA`: 3 assets / 7·10¹⁵ shares, redeeming 2333333333333333 shares is worth
  `0.99999999999999985714…`, priced `0.9999999999999999`; the miss exceeds `depositε`
  relative.
* `wpI`: an integral vault of 3 assets / 2 shares, one share is worth `1.5` and is
  priced `2` (ties to even), a full half unit above the worth.
* `wpF`: a fractional vault of `2.000000000000003` assets / 2 shares, one share is worth
  `1.0000000000000015` and is priced `1.000000000000002`, half a ULP above.
* `wpI5`: 5 assets / 2 shares, one share is worth `2.5` and is priced `2`, and
  `wpF5`: `2.000000000000001` assets / 2 shares, worth `1.0000000000000005`, priced `1`;
  both fall half a ULP short.
* The `wpI`/`wpF` runs overdraw an `assetsAvailable` just under the payout. -/

namespace XRPL.Model.SingleAssetVault.WdPrice

open XRPL.Model.Protocol

set_option linter.style.nativeDecide false

/-- A vault with no loss and `assetsAvailable` given separately. -/
def wRaw (nt : NumericType) (at_ av st : Number) : RawVault :=
  { assetsTotal := at_, assetsAvailable := av, assetsReserved := Number.zero
  , assetsMaximum := none, numericType := nt, scale := 0
  , sharesTotal := st, lossUnrealized := Number.zero }

def wvA : Vault := ⟨wRaw .fractional ⟨false, 3000000000000000000, -18⟩
  ⟨false, 3000000000000000000, -18⟩ ⟨false, 7000000000000000000, -3⟩,
  by native_decide, by native_decide⟩

def wshA : STAmount := STAmount.unchecked .int64 2333333333333333 0 false

def wpA : STAmount := STAmount.unchecked .fractional 9999999999999999 (-16) false

/-- Integral vault, `assetsAvailable = 3`. -/
def wvI : Vault := ⟨wRaw .int64 ⟨false, 3000000000000000000, -18⟩
  ⟨false, 3000000000000000000, -18⟩ ⟨false, 2000000000000000000, -18⟩,
  by native_decide, by native_decide⟩

/-- Integral vault, `assetsAvailable = 1.999999999999999999`. -/
def wvI' : Vault := ⟨wRaw .int64 ⟨false, 3000000000000000000, -18⟩
  ⟨false, 1999999999999999999, -18⟩ ⟨false, 2000000000000000000, -18⟩,
  by native_decide, by native_decide⟩

/-- Fractional vault, `assetsAvailable = 2.000000000000003`. -/
def wvF : Vault := ⟨wRaw .fractional ⟨false, 2000000000000003000, -18⟩
  ⟨false, 2000000000000003000, -18⟩ ⟨false, 2000000000000000000, -18⟩,
  by native_decide, by native_decide⟩

/-- Fractional vault, `assetsAvailable = 1.000000000000001999`. -/
def wvF' : Vault := ⟨wRaw .fractional ⟨false, 2000000000000003000, -18⟩
  ⟨false, 1000000000000001999, -18⟩ ⟨false, 2000000000000000000, -18⟩,
  by native_decide, by native_decide⟩

/-- Integral vault, 5 assets / 2 shares. -/
def wvI5 : Vault := ⟨wRaw .int64 ⟨false, 5000000000000000000, -18⟩
  ⟨false, 5000000000000000000, -18⟩ ⟨false, 2000000000000000000, -18⟩,
  by native_decide, by native_decide⟩

/-- Fractional vault, `2.000000000000001` assets / 2 shares. -/
def wvF5 : Vault := ⟨wRaw .fractional ⟨false, 2000000000000001000, -18⟩
  ⟨false, 2000000000000001000, -18⟩ ⟨false, 2000000000000000000, -18⟩,
  by native_decide, by native_decide⟩

def wpF5 : STAmount := STAmount.unchecked .fractional 1000000000000000 (-15) false

def wsh1 : STAmount := STAmount.unchecked .int64 1 0 false

def wpI : STAmount := STAmount.unchecked .int64 2 0 false

def wpF : STAmount := STAmount.unchecked .fractional 1000000000000002 (-15) false

end XRPL.Model.SingleAssetVault.WdPrice

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol WdPrice

set_option linter.style.nativeDecide false
set_option maxRecDepth 10000

/-- Witness for the half-ULP term of `Vault.sharesToAssetsWithdraw_bounds`: on an
integral vault the payout is exactly half a unit above the shares' worth. -/
lemma Vault.sharesToAssetsWithdraw_overshoot_witness :
    ∃ (v : Vault) (shares assets : STAmount) (waiveUnrealizedLoss : Bool),
      0 < shares.toRat ∧
      v.WithdrawNavExact waiveUnrealizedLoss ∧
      v.sharesToAssetsWithdraw shares waiveUnrealizedLoss = .ok assets ∧
      assets.toRat = v.idealAssetsWithdraw waiveUnrealizedLoss shares.toRat +
        (1 / 2 : ℚ) * (10 : ℚ) ^ assets.exponent :=
  ⟨wvI, wsh1, wpI, false, by native_decide,
    ⟨⟨false, 3000000000000000000, -18⟩, by native_decide, by native_decide⟩,
    by native_decide, by native_decide⟩

/-- The fractional analogue: half a 16-digit ULP above the shares' worth. -/
lemma Vault.sharesToAssetsWithdraw_overshoot_frac_witness :
    ∃ (v : Vault) (shares assets : STAmount) (waiveUnrealizedLoss : Bool),
      v.numericType = .fractional ∧
      0 < shares.toRat ∧
      v.WithdrawNavExact waiveUnrealizedLoss ∧
      v.sharesToAssetsWithdraw shares waiveUnrealizedLoss = .ok assets ∧
      assets.toRat = v.idealAssetsWithdraw waiveUnrealizedLoss shares.toRat +
        (1 / 2 : ℚ) * (10 : ℚ) ^ assets.exponent :=
  ⟨wvF, wsh1, wpF, false, rfl, by native_decide,
    ⟨⟨false, 2000000000000003000, -18⟩, by native_decide, by native_decide⟩,
    by native_decide, by native_decide⟩

/-- Witness for the lower half-ULP term of `Vault.sharesToAssetsWithdraw_bounds`: on an
integral vault a nonzero payout is exactly half a unit below the shares' worth. -/
lemma Vault.sharesToAssetsWithdraw_shortfall_witness :
    ∃ (v : Vault) (shares assets : STAmount) (waiveUnrealizedLoss : Bool),
      0 < shares.toRat ∧
      v.WithdrawNavExact waiveUnrealizedLoss ∧
      v.sharesToAssetsWithdraw shares waiveUnrealizedLoss = .ok assets ∧
      assets.isZero = false ∧
      v.idealAssetsWithdraw waiveUnrealizedLoss shares.toRat - assets.toRat =
        (1 / 2 : ℚ) * (10 : ℚ) ^ assets.exponent :=
  ⟨wvI5, wsh1, wpI, false, by native_decide,
    ⟨⟨false, 5000000000000000000, -18⟩, by native_decide, by native_decide⟩,
    by native_decide, by native_decide, by native_decide⟩

/-- The fractional analogue: half a 16-digit ULP below the shares' worth. -/
lemma Vault.sharesToAssetsWithdraw_shortfall_frac_witness :
    ∃ (v : Vault) (shares assets : STAmount) (waiveUnrealizedLoss : Bool),
      v.numericType = .fractional ∧
      0 < shares.toRat ∧
      v.WithdrawNavExact waiveUnrealizedLoss ∧
      v.sharesToAssetsWithdraw shares waiveUnrealizedLoss = .ok assets ∧
      assets.isZero = false ∧
      v.idealAssetsWithdraw waiveUnrealizedLoss shares.toRat - assets.toRat =
        (1 / 2 : ℚ) * (10 : ℚ) ^ assets.exponent :=
  ⟨wvF5, wsh1, wpF5, false, rfl, by native_decide,
    ⟨⟨false, 2000000000000001000, -18⟩, by native_decide, by native_decide⟩,
    by native_decide, by native_decide, by native_decide⟩

/-- Witness for the lower conjunct of `Vault.sharesToAssetsWithdraw_total`: shrinking the
half-ULP term by `10⁻¹⁶` breaks it. -/
lemma Vault.sharesToAssetsWithdraw_total_shortfall_witness :
    ∃ (v : Vault) (shares assets : STAmount) (waiveUnrealizedLoss : Bool),
      0 < shares.toRat ∧
      v.sharesToAssetsWithdraw shares waiveUnrealizedLoss = .ok assets ∧
      assets.isZero = false ∧
      v.navSlack * shares.toRat / (v.toExact.sharesTotal : ℚ) * (1 + depositε) +
        (1 / 2 - (10 : ℚ) ^ (-16 : ℤ)) * (10 : ℚ) ^ assets.exponent <
        v.idealAssetsWithdraw waiveUnrealizedLoss shares.toRat - assets.toRat :=
  ⟨wvI5, wsh1, wpI, false, by native_decide, by native_decide, by native_decide,
    by native_decide⟩

/-- Witness for `Vault.sharesToAssetsWithdraw_total`: shrinking the half-ULP term by
`10⁻¹⁶` breaks the upper conjunct. -/
lemma Vault.sharesToAssetsWithdraw_total_witness :
    ∃ (v : Vault) (shares assets : STAmount) (waiveUnrealizedLoss : Bool),
      0 < shares.toRat ∧
      v.sharesToAssetsWithdraw shares waiveUnrealizedLoss = .ok assets ∧
      (v.idealAssetsWithdraw waiveUnrealizedLoss shares.toRat +
          v.navSlack * shares.toRat / (v.toExact.sharesTotal : ℚ)) * (1 + depositε) +
        (1 / 2 - (10 : ℚ) ^ (-16 : ℤ)) * (10 : ℚ) ^ assets.exponent < assets.toRat :=
  ⟨wvI, wsh1, wpI, false, by native_decide, by native_decide, by native_decide⟩

/-- Witness for `Vault.withdraw_under_available`, integral half: a margin of
`1/2 - 10⁻¹⁶` units lets the guard fire. -/
lemma Vault.withdraw_under_available_witness :
    ∃ (v : Vault) (shares : STAmount) (waiveUnrealizedLoss : Bool) (r : WithdrawResult)
      (hpos : 0 < shares.toRat),
      v.numericType.isIntegral = true ∧
      v.WithdrawNavExact waiveUnrealizedLoss ∧
      v.withdraw (.vaultShares shares) waiveUnrealizedLoss hpos = .ok r ∧
      v.idealAssetsWithdraw waiveUnrealizedLoss shares.toRat * (1 + depositε) +
        (1 / 2 - (10 : ℚ) ^ (-16 : ℤ)) ≤ v.toExact.assetsAvailable ∧
      r.error = some .tecINSUFFICIENT_FUNDS :=
  ⟨wvI', wsh1, false, WithdrawResult.rejected wvI' .tecINSUFFICIENT_FUNDS, by native_decide,
    rfl, ⟨⟨false, 3000000000000000000, -18⟩, by native_decide, by native_decide⟩,
    by native_decide, by native_decide, rfl⟩

/-- Witness for `Vault.withdraw_under_available`, fractional half: a relative margin of
`4.98·10⁻¹⁶` (99.2% of `½·10⁻¹⁵ + 2·10⁻¹⁸`) lets the guard fire. -/
lemma Vault.withdraw_under_available_frac_witness :
    ∃ (v : Vault) (shares : STAmount) (waiveUnrealizedLoss : Bool) (r : WithdrawResult)
      (hpos : 0 < shares.toRat),
      v.numericType = .fractional ∧
      v.WithdrawNavExact waiveUnrealizedLoss ∧
      v.withdraw (.vaultShares shares) waiveUnrealizedLoss hpos = .ok r ∧
      v.idealAssetsWithdraw waiveUnrealizedLoss shares.toRat * (1 + 498 * (10 : ℚ) ^ (-18 : ℤ))
        ≤ v.toExact.assetsAvailable ∧
      r.error = some .tecINSUFFICIENT_FUNDS :=
  ⟨wvF', wsh1, false, WithdrawResult.rejected wvF' .tecINSUFFICIENT_FUNDS, by native_decide,
    rfl, ⟨⟨false, 2000000000000003000, -18⟩, by native_decide, by native_decide⟩,
    by native_decide, by native_decide, rfl⟩

end XRPL.Model.SingleAssetVault
