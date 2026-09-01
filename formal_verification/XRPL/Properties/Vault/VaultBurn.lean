import XRPL.Properties.Vault.Defs
import XRPL.Model.Vault.VaultBurn
import XRPL.Properties.Vault.Common.BurnAccuracy

/-! # `LawfulVault.burnShares` accuracy

Both statements are exact, so this file has no error bounds and no witness
theorems. -/

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol

/-! ## `RawVault.canBurnShares` -/

/-- The returned amount is the whole stored share total, exactly:
`sharesTotalAmount.toRat = sharesTotal`. A lawful vault stores `sharesTotal`
as a nonnegative integer, and every integer at most `2 ^ 63 - 1` converts to
an `int64` amount without rounding. -/
theorem LawfulVault.canBurnShares_assets_exact (lv : LawfulVault) (sharesTotalAmount : STAmount)
    (hok : lv.canBurnShares = .ok (.assets sharesTotalAmount))
    -- the share total fits the int64 amount domain
    (hfit : (lv.toExact.sharesTotal : ℚ) ≤ 2 ^ 63 - 1) :
    sharesTotalAmount.toRat = (lv.toExact.sharesTotal : ℚ) :=
  LawfulVault.canBurnShares_assets_exact_proof lv sharesTotalAmount hok hfit

/-! ## `LawfulVault.burnShares` -/

/-- `burnShares` stores exactly `sharesTotal - sharesDestroyed`. The
hypotheses keep the subtraction in the share domain: `sharesDestroyed` is a
canonically stored nonnegative integral amount at most `sharesTotal`, and
`sharesTotal` is at most `2 ^ 63 - 1`, so both operands and the difference
are integers a `Number` represents exactly. -/
theorem LawfulVault.burnShares_sharesTotal_exact (lv : LawfulVault) (sharesDestroyed : STAmount)
    (lv' : LawfulVault)
    (hok : lv.burnShares sharesDestroyed = .ok lv')
    (hcanon : sharesDestroyed.IntegralCanonical) -- stored as a plain integral amount
    (hnn : sharesDestroyed.negative = false)
    (hle : sharesDestroyed.toRat ≤ (lv.toExact.sharesTotal : ℚ))
    (hfit : (lv.toExact.sharesTotal : ℚ) ≤ 2 ^ 63 - 1) :
    (lv'.toExact.sharesTotal : ℚ) =
      (lv.toExact.sharesTotal : ℚ) - sharesDestroyed.toRat :=
  LawfulVault.burnShares_sharesTotal_exact_proof lv sharesDestroyed lv' hok hcanon hnn hle hfit

end XRPL.Model.SingleAssetVault
