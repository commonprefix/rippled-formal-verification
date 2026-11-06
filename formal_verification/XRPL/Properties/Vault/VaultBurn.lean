import XRPL.Properties.Vault.Defs
import XRPL.Model.Vault.VaultBurn
import XRPL.Properties.Vault.Proofs.Burn

/-! # `Vault.burnShares` accuracy

Both statements are exact. -/

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol

/-- `burnShares` stores exactly `sharesTotal - sharesDestroyed`. Both are whole share counts a
`Number` holds exactly, and the destroyed shares are at most the total. -/
theorem Vault.burnShares_sharesTotal_exact (v : Vault) (sharesDestroyed : STAmount) (v' : Vault)
    (hok : (v.burnShares sharesDestroyed).run = .ok (.ok v'))
    -- the destroyed shares are a holder's balance: a canonical, nonnegative MPT amount within the share total
    (hcanon : sharesDestroyed.IntegralCanonical)
    (hnn : sharesDestroyed.negative = false)
    (hle : sharesDestroyed.toRat ≤ (v.toExact.sharesTotal : ℚ)) :
    (v'.toExact.sharesTotal : ℚ) = (v.toExact.sharesTotal : ℚ) - sharesDestroyed.toRat :=
  Vault.burnShares_sharesTotal_exact_proof v sharesDestroyed v' hok hcanon hnn hle

end XRPL.Model.SingleAssetVault
