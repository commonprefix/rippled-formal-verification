import XRPL.Properties.Vault.Defs
import XRPL.Model.Vault.VaultBurn
import XRPL.Properties.Vault.Common.BurnAccuracy

/-! # `Vault.burnShares` accuracy

Both statements are exact, so this file has no error bounds and no witness
theorems. -/

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol

variable (v : Vault)

/-! ## `Vault.canBurnShares` -/

/-- The returned amount is the whole stored share total, exactly:
`sharesTotalAmount.toRat = sharesTotal`. A lawful vault stores `sharesTotal`
as a nonnegative integer, and every integer at most `2 ^ 63 - 1` converts to
an `int64` amount without rounding. -/
theorem Vault.canBurnShares_assets_exact (sharesTotalAmount : STAmount)
    (hv : v.Lawful) -- the starting vault is lawful
    (hok : v.canBurnShares = .ok (.assets sharesTotalAmount))
    -- the share total fits the int64 amount domain
    (hfit : v.sharesTotal.toRat ≤ 2 ^ 63 - 1) :
    sharesTotalAmount.toRat = v.sharesTotal.toRat :=
  Vault.canBurnShares_assets_exact_proof v sharesTotalAmount hv hok hfit

/-! ## `Vault.burnShares` -/

/-- `burnShares` stores exactly `sharesTotal - sharesDestroyed`. The
hypotheses keep the subtraction in the share domain: `sharesDestroyed` is a
canonically stored nonnegative integral amount at most `sharesTotal`, and
`sharesTotal` is at most `2 ^ 63 - 1`, so both operands and the difference
are integers a `Number` represents exactly. -/
theorem Vault.burnShares_sharesTotal_exact (sharesDestroyed : STAmount) (vault' : Vault)
    (hv : v.Lawful) -- the starting vault is lawful
    (hok : v.burnShares sharesDestroyed = .ok vault')
    (hcanon : sharesDestroyed.IntegralCanonical) -- stored as a plain integral amount
    (hnn : sharesDestroyed.negative = false)
    (hle : sharesDestroyed.toRat ≤ v.sharesTotal.toRat)
    (hfit : v.sharesTotal.toRat ≤ 2 ^ 63 - 1) :
    vault'.sharesTotal.toRat =
      v.sharesTotal.toRat - sharesDestroyed.toRat :=
  Vault.burnShares_sharesTotal_exact_proof v sharesDestroyed vault' hv hok hcanon hnn hle hfit

end XRPL.Model.SingleAssetVault
