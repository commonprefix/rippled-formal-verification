import XRPL.Properties.Vault.Defs
import XRPL.Properties.Vault.VaultValid
import XRPL.Properties.Protocol.Number.Compare.Compare
import XRPL.Properties.Protocol.Number.Common.ToRatLemmas
import XRPL.Properties.Protocol.Number.Signum.Signum
import XRPL.Model.Vault.VaultSet
import XRPL.Model.Vault.VaultDelete
import XRPL.Properties.Vault.Proofs.Walk

/-! # Vault state guards

Proof bodies of the `canVaultUpdate`, `canVaultDelete` and `isInsolvent` headlines, and the two facts about the
maximum an update sets. -/

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol

/-- The grid check runs first, so an off-grid maximum stops there. -/
lemma Vault.canVaultUpdate_off_grid_proof (v : Vault) (m : Number) (blockDeposit unblockDeposit : Bool)
    (hgrid : m.isOnExponentGrid v.baseExponent v.numericType = .ok false) :
    v.canVaultUpdate (some m) blockDeposit unblockDeposit = .ok .tecPRECISION_LOSS := by
  simp [Vault.canVaultUpdate, hgrid, bind, Except.bind, pure, Except.pure]

/-- With the maximum on the grid, the permission check is the next to fire. -/
lemma Vault.canVaultUpdate_no_permission_proof (v : Vault) (assetsMaximum : Option Number)
    (blockDeposit unblockDeposit : Bool)
    (hgrid : ∀ m ∈ assetsMaximum, m.isOnExponentGrid v.baseExponent v.numericType = .ok true)
    (howner : v.ownerCanBlockDeposit = false) (hflag : (blockDeposit || unblockDeposit) = true) :
    v.canVaultUpdate assetsMaximum blockDeposit unblockDeposit = .ok .tecNO_PERMISSION := by
  cases assetsMaximum with
  | none => simp [Vault.canVaultUpdate, howner, hflag, bind, Except.bind, pure, Except.pure]
  | some m =>
    simp [Vault.canVaultUpdate, hgrid m rfl, howner, hflag, bind, Except.bind, pure, Except.pure]

/-- With the grid and permission checks passed, a nonzero maximum below the total fails the limit check. -/
lemma Vault.canVaultUpdate_below_total_proof (v : Vault) (m assetsTotal : Number)
    (blockDeposit unblockDeposit : Bool)
    (hgrid : m.isOnExponentGrid v.baseExponent v.numericType = .ok true)
    (hperm : (!v.ownerCanBlockDeposit && (blockDeposit || unblockDeposit)) = false)
    (hat : v.assetsTotal = .ok assetsTotal)
    (hne : m.operator_ne Number.zero = true) (hlt : m.operator_lt assetsTotal = true) :
    v.canVaultUpdate (some m) blockDeposit unblockDeposit = .ok .tecLIMIT_EXCEEDED := by
  simp [Vault.canVaultUpdate, hgrid, hperm, hat, hne, hlt, bind, Except.bind, pure, Except.pure]

/-- Walks every exit of `canVaultUpdate`. -/
lemma Vault.canVaultUpdate_error_codes_proof (v : Vault) (assetsMaximum : Option Number)
    (blockDeposit unblockDeposit : Bool) (ter : TER)
    (hok : v.canVaultUpdate assetsMaximum blockDeposit unblockDeposit = .ok ter) :
    ter = .tesSUCCESS ∨ ter = .tecPRECISION_LOSS ∨ ter = .tecNO_PERMISSION ∨
      ter = .tecLIMIT_EXCEEDED := by
  simp only [Vault.canVaultUpdate, bind, Except.bind, pure, Except.pure] at hok
  walk_ok
  all_goals simp

/-- A lawful vault's exact total is zero exactly when it holds no cash and nothing deployed, both being
nonnegative. -/
lemma Vault.toExact_assetsTotal_eq_zero_iff (v : Vault) :
    v.toExact.assetsTotal = 0 ↔ v.assetsAvailable.toRat = 0 ∧ v.assetsDeployed.toRat = 0 := by
  have hA : 0 ≤ v.assetsAvailable.toRat := v.exact.assetsAvailable_nonneg
  have hD : 0 ≤ v.assetsDeployed.toRat := v.exact.assetsDeployed_nonneg
  show v.assetsAvailable.toRat + v.assetsDeployed.toRat = 0 ↔ _
  constructor
  · intro h; constructor <;> linarith
  · rintro ⟨h1, h2⟩; rw [h1, h2, add_zero]

/-- Proof of `Vault.isInsolvent_iff`: the total is zero exactly when the cash and the deployed assets are. -/
lemma Vault.isInsolvent_iff_proof (v : Vault) :
    v.isInsolvent = true ↔ v.toExact.assetsTotal = 0 ∧ 0 < v.toExact.sharesTotal := by
  rw [Vault.toExact_assetsTotal_eq_zero_iff]
  unfold Vault.isInsolvent
  unfold RawVault.toExact
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  rw [Number.toRat_eq_zero_iff.symm, Number.toRat_eq_zero_iff.symm,
    signum_eq_one_iff v.sharesTotal v.wf.sharesTotal_norm]
  have hcast : ((v.sharesTotal.toRat.num.toNat : ℕ) : ℚ) = v.sharesTotal.toRat :=
    RawVault.WF.toExact_sharesTotal v.toRawVault v.wf
  constructor
  · rintro ⟨ha, hs⟩
    refine ⟨ha, ?_⟩
    have : (0:ℚ) < ((v.sharesTotal.toRat.num.toNat : ℕ) : ℚ) := by rw [hcast]; exact hs
    exact_mod_cast this
  · rintro ⟨ha, hs⟩
    refine ⟨ha, ?_⟩
    have : (0:ℚ) < ((v.sharesTotal.toRat.num.toNat : ℕ) : ℚ) := by exact_mod_cast hs
    rw [hcast] at this; exact this

/-- `canVaultDelete` in closed form: once `assetsAvailable` is zero, the computed total is
`assetsDeployed`, so the check never fails and reads the three stored records. -/
private lemma Vault.canVaultDelete_eq (v : Vault) :
    v.canVaultDelete = .ok (if (v.assetsAvailable.operator_ne Number.zero ||
      v.assetsDeployed.operator_ne Number.zero || v.sharesTotal.operator_ne Number.zero) = true
      then .tecHAS_OBLIGATIONS else .tesSUCCESS) := by
  unfold Vault.canVaultDelete
  cases hAb : v.assetsAvailable.operator_ne Number.zero
  · have hA : v.assetsAvailable = Number.zero := by
      by_contra hne
      have h := (Number.operator_ne_iff_ne _ _).mpr hne
      rw [hAb] at h
      exact absurd h (by decide)
    have hat : v.assetsTotal = .ok v.assetsDeployed := by
      show v.assetsAvailable.operator_add v.assetsDeployed .downward = _
      rw [hA]; exact Number.operator_add_zero_left _ _
    cases hDb : v.assetsDeployed.operator_ne Number.zero <;>
      cases hSb : v.sharesTotal.operator_ne Number.zero <;>
      simp [bind, Except.bind, pure, Except.pure, *]
  · simp [pure, Except.pure]

/-- The closed form's condition read on the stored records. -/
private lemma Vault.canVaultDelete_cond_iff (v : Vault) :
    (v.assetsAvailable.operator_ne Number.zero || v.assetsDeployed.operator_ne Number.zero ||
      v.sharesTotal.operator_ne Number.zero) = true ↔
    (v.assetsAvailable ≠ Number.zero ∨ v.assetsDeployed ≠ Number.zero ∨
      v.sharesTotal ≠ Number.zero) := by
  rw [Bool.or_eq_true, Bool.or_eq_true, Number.operator_ne_iff_ne, Number.operator_ne_iff_ne,
    Number.operator_ne_iff_ne, or_assoc]

/-- On a lawful vault both parts of the total are nonnegative, so the total is zero exactly when
`assetsAvailable` and `assetsDeployed` are. -/
lemma Vault.canVaultDelete_lawful_iff_proof (v : Vault) :
    v.canVaultDelete = .ok .tesSUCCESS ↔
      v.toExact.assetsTotal = 0 ∧ v.toExact.sharesTotal = 0 := by
  have hA := Number.toRat_eq_zero_iff_eq_zero v.wf.assetsAvailable_norm
  have hD := Number.toRat_eq_zero_iff_eq_zero v.wf.assetsDeployed_norm
  have hS := Number.toRat_eq_zero_iff_eq_zero v.wf.sharesTotal_norm
  have hshares : v.toExact.sharesTotal = 0 ↔ v.sharesTotal.toRat = 0 := by
    rw [← RawVault.WF.toExact_sharesTotal v.toRawVault v.wf, Nat.cast_eq_zero]
  rw [Vault.canVaultDelete_eq, Vault.toExact_assetsTotal_eq_zero_iff, hshares, hA, hD, hS]
  split_ifs with h
  · refine iff_of_false (by simp) ?_
    rintro ⟨⟨h1, h2⟩, h3⟩
    rcases (Vault.canVaultDelete_cond_iff v).mp h with h | h | h <;> contradiction
  · refine iff_of_true rfl ?_
    rw [Vault.canVaultDelete_cond_iff, not_or, not_or, not_not, not_not, not_not] at h
    exact ⟨⟨h.1, h.2.1⟩, h.2.2⟩

/-- The closed form returns one of the two codes. -/
lemma Vault.canVaultDelete_error_codes_proof (v : Vault) :
    v.canVaultDelete = .ok .tesSUCCESS ∨
    v.canVaultDelete = .ok .tecHAS_OBLIGATIONS := by
  rw [Vault.canVaultDelete_eq]
  split_ifs <;> simp

/-- The closed form fails exactly when one of the three stored records is nonzero. -/
lemma Vault.canVaultDelete_has_obligations_iff_proof (v : Vault) :
    v.canVaultDelete = .ok .tecHAS_OBLIGATIONS ↔
      (v.assetsAvailable ≠ Number.zero ∨ v.assetsDeployed ≠ Number.zero ∨
        v.sharesTotal ≠ Number.zero) := by
  rw [Vault.canVaultDelete_eq, ← Vault.canVaultDelete_cond_iff]
  split_ifs with h
  · exact iff_of_true rfl h
  · exact iff_of_false (by simp) h

/-- An update the checks accept sets only a maximum on the vault's base grid. -/
lemma Vault.canVaultUpdate_assetsMaximum (v : Vault) (m : Number) (blockDeposit unblockDeposit : Bool)
    (h : v.canVaultUpdate (some m) blockDeposit unblockDeposit = .ok .tesSUCCESS) :
    m.isOnExponentGrid v.baseExponent v.numericType = .ok true := by
  simp only [Vault.canVaultUpdate, bind, Except.bind, pure, Except.pure] at h
  walk_ok
  all_goals simp_all

/-- An update keeps the maximum, clears it, or sets the one the transaction names. -/
lemma Vault.update_assetsMaximum_mem (v : Vault) (assetsMaximum : Option Number) (blockDeposit unblockDeposit : Bool)
    (v' : Vault) (hok : v.update assetsMaximum blockDeposit unblockDeposit = .ok v') :
    ∀ m ∈ v'.assetsMaximum, m ∈ v.assetsMaximum ∨ assetsMaximum = some m := by
  intro m hm
  unfold Vault.update at hok
  have hv := congrArg RawVault.assetsMaximum (RawVault.to_lawful_ok hok).1
  change v'.assetsMaximum = _ at hv
  rw [hv] at hm
  cases assetsMaximum with
  | none => exact Or.inl hm
  | some m' =>
    simp only at hm
    split at hm
    · simp at hm
    · simp only [Option.mem_def, Option.some.injEq] at hm
      exact Or.inr (by rw [hm])

end XRPL.Model.SingleAssetVault
