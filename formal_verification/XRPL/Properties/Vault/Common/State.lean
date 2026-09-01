import XRPL.Properties.Vault.Defs
import XRPL.Properties.Protocol.Number.Common.ToRatLemmas
import XRPL.Properties.Protocol.Number.Signum.Signum

/-! # Lawful-state query characterizations (proofs) -/

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol

/-- On a lawful state, `isInsolvent` holds exactly when the vault has no assets
but shares outstanding. -/
theorem LawfulVault.isInsolvent_iff_proof (lv : LawfulVault) :
    lv.isInsolvent = true ↔ lv.toExact.assetsTotal = 0 ∧ 0 < lv.toExact.sharesTotal := by
  unfold LawfulVault.isInsolvent
  unfold RawVault.toExact
  rw [Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq,
    Number.toRat_eq_zero_iff.symm, signum_eq_one_iff lv.sharesTotal lv.wf.sharesTotal_norm]
  have hcast : ((lv.sharesTotal.toRat.num.toNat : ℕ) : ℚ) = lv.sharesTotal.toRat :=
    RawVault.WF.toExact_sharesTotal lv.toRawVault lv.wf
  constructor
  · rintro ⟨ha, hs⟩
    refine ⟨ha, ?_⟩
    have : (0:ℚ) < ((lv.sharesTotal.toRat.num.toNat : ℕ) : ℚ) := by rw [hcast]; exact hs
    exact_mod_cast this
  · rintro ⟨ha, hs⟩
    refine ⟨ha, ?_⟩
    have : (0:ℚ) < ((lv.sharesTotal.toRat.num.toNat : ℕ) : ℚ) := by exact_mod_cast hs
    rw [hcast] at this; exact this

end XRPL.Model.SingleAssetVault
