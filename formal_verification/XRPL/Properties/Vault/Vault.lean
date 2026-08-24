import XRPL.Properties.Vault.Defs
import XRPL.Properties.Vault.Common.State

/-! # `Vault.isInsolvent`

On a lawful state, the insolvency query characterizes exactly one situation:
shares are outstanding while the vault holds no assets. -/

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol

/-- On a lawful state, `isInsolvent` holds exactly when the vault has no assets
but shares outstanding. -/
theorem Vault.isInsolvent_iff (v : Vault) (hv : v.Lawful) :
    v.isInsolvent = true ↔ v.assetsTotal.toRat = 0 ∧ 0 < v.sharesTotal.toRat :=
  Vault.isInsolvent_iff_proof v hv

end XRPL.Model.SingleAssetVault
