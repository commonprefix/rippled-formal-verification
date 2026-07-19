import XRPL.Properties.Vault.Defs
import XRPL.Properties.Vault.Common.GuardProofs
import XRPL.Model.Vault.VaultDelete

/-! # `canVaultDelete` on lawful states -/

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol

theorem Vault.lawful_canVaultDelete_iff (v : Vault)
    (hv : v.Lawful) : -- the vault is lawful
    v.canVaultDelete = .tesSUCCESS ↔
      v.toExact.assetsTotal = 0 ∧ v.toExact.assetsAvailable = 0 ∧
      v.toExact.sharesTotal = 0 := by
  have hav := Number.operator_ne_zero_eq_false_iff v.assetsAvailable hv.wf.assetsAvailable_norm
  have hat := Number.operator_ne_zero_eq_false_iff v.assetsTotal hv.wf.assetsTotal_norm
  have hst := Number.operator_ne_zero_eq_false_iff v.sharesTotal hv.wf.sharesTotal_norm
  have hshares : v.toExact.sharesTotal = 0 ↔ v.sharesTotal.toRat = 0 := by
    rw [← Vault.WF.toExact_sharesTotal v hv.wf, Nat.cast_eq_zero]
  show v.canVaultDelete = .tesSUCCESS ↔
      v.assetsTotal.toRat = 0 ∧ v.assetsAvailable.toRat = 0 ∧ v.toExact.sharesTotal = 0
  rw [← hat, ← hav, hshares, ← hst]
  unfold Vault.canVaultDelete
  split_ifs with h1 h2 h3
  · refine iff_of_false (by decide) ?_
    rintro ⟨_, hav', _⟩; rw [h1] at hav'; exact absurd hav' (by decide)
  · refine iff_of_false (by decide) ?_
    rintro ⟨hat', _, _⟩; rw [h2] at hat'; exact absurd hat' (by decide)
  · refine iff_of_false (by decide) ?_
    rintro ⟨_, _, hst'⟩; rw [h3] at hst'; exact absurd hst' (by decide)
  · exact iff_of_true rfl
      ⟨Bool.eq_false_iff.mpr h2, Bool.eq_false_iff.mpr h1, Bool.eq_false_iff.mpr h3⟩

end XRPL.Model.SingleAssetVault

/-! ## `canVaultDelete` on arbitrary states -/

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol

/-- Every outcome of the check: `tecHAS_OBLIGATIONS` is the only rejection
`canVaultDelete` can return. -/
theorem Vault.canVaultDelete_error_codes (v : Vault) :
    v.canVaultDelete = .tesSUCCESS ∨
    v.canVaultDelete = .tecHAS_OBLIGATIONS := by
  unfold Vault.canVaultDelete
  split_ifs <;> first | exact Or.inl rfl | exact Or.inr rfl

/-- The check returns `tecHAS_OBLIGATIONS` exactly when one of the three stored
quantities differs from `Number.zero`. The vault is arbitrary and the comparison
is on the stored records. -/
theorem Vault.canVaultDelete_has_obligations_iff (v : Vault) :
    v.canVaultDelete = .tecHAS_OBLIGATIONS ↔
      (v.assetsAvailable ≠ Number.zero ∨ v.assetsTotal ≠ Number.zero ∨
        v.sharesTotal ≠ Number.zero) := by
  unfold Vault.canVaultDelete
  rw [← Number.operator_ne_iff_ne v.assetsAvailable, ← Number.operator_ne_iff_ne v.assetsTotal,
      ← Number.operator_ne_iff_ne v.sharesTotal]
  split_ifs with h1 h2 h3
  · exact iff_of_true rfl (Or.inl h1)
  · exact iff_of_true rfl (Or.inr (Or.inl h2))
  · exact iff_of_true rfl (Or.inr (Or.inr h3))
  · refine iff_of_false (by decide) ?_
    rintro (h | h | h)
    · exact h1 h
    · exact h2 h
    · exact h3 h

end XRPL.Model.SingleAssetVault
