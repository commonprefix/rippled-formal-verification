import XRPL.Properties.Vault.Defs
import XRPL.Properties.Protocol.Number.Common.ToRatLemmas
import XRPL.Properties.Protocol.Number.Signum.Signum

/-! # Lawful-state query characterizations (proofs) -/

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol

/-- On a lawful state, `isInsolvent` holds exactly when the vault has no assets
but shares outstanding. -/
theorem Vault.isInsolvent_iff_proof (v : Vault) (hv : v.Lawful) :
    v.isInsolvent = true ↔ v.assetsTotal.toRat = 0 ∧ 0 < v.sharesTotal.toRat := by
  unfold Vault.isInsolvent
  rw [Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq,
    Number.toRat_eq_zero_iff.symm, signum_eq_one_iff v.sharesTotal hv.wf.sharesTotal_norm]

end XRPL.Model.SingleAssetVault
