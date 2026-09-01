import XRPL.Properties.Vault.Defs
import XRPL.Properties.Vault.Common.State

/-! # `LawfulVault.isInsolvent`

On a lawful state, the insolvency query characterizes exactly one situation:
shares are outstanding while the vault holds no assets. -/

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol

/-- On a lawful state, `isInsolvent` holds exactly when the vault has no assets
but shares outstanding. -/
theorem LawfulVault.isInsolvent_iff (lv : LawfulVault) :
    lv.isInsolvent = true ↔ lv.toExact.assetsTotal = 0 ∧ 0 < lv.toExact.sharesTotal :=
  LawfulVault.isInsolvent_iff_proof lv

end XRPL.Model.SingleAssetVault
