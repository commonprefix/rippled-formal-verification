import XRPL.Properties.Vault.Common.GuardProofs
import XRPL.Properties.Vault.Proofs.Support.DepositExchange
import XRPL.Properties.Vault.Proofs.Reachable

/-! # The maximum check of `Vault.canVaultUpdate`

The check compares the new maximum with the total it computes, the cash plus the deployed assets
rounded down to 19 digits. -/

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol

/-- With the maximum on the grid and permitted flags, the update passes exactly when the maximum is zero or at least the
computed total. -/
private lemma canVaultUpdate_on_grid_iff (v : Vault) (m assetsTotal : Number) (blockDeposit unblockDeposit : Bool)
    (hnorm : m.isNormalized)
    (hgrid : m.isOnExponentGrid v.baseExponent v.numericType = .ok true)
    (hperm : (!v.ownerCanBlockDeposit && (blockDeposit || unblockDeposit)) = false)
    (hat : v.assetsTotal = .ok assetsTotal) :
    v.canVaultUpdate (some m) blockDeposit unblockDeposit = .ok .tesSUCCESS ↔
      m.toRat = 0 ∨ assetsTotal.toRat ≤ m.toRat := by
  have hatn := (Vault.assetsTotal_ge_deployed v assetsTotal hat).1
  -- the nonzero guard vanishes exactly at zero
  have hb1 : m.operator_ne Number.zero = false ↔ m.toRat = 0 := Number.operator_ne_zero_eq_false_iff m hnorm
  -- the below-total guard vanishes exactly when the maximum is at least the total
  have hb2 : m.operator_lt assetsTotal = false ↔ assetsTotal.toRat ≤ m.toRat := by
    rw [Bool.eq_false_iff, ne_eq, operator_lt_iff m assetsTotal hnorm hatn, not_lt]
  by_cases hc : (m.operator_ne Number.zero && m.operator_lt assetsTotal) = true
  · have hrej := Vault.canVaultUpdate_below_total_proof v m assetsTotal blockDeposit unblockDeposit hgrid hperm hat
      (Bool.and_eq_true _ _ ▸ hc).1 (Bool.and_eq_true _ _ ▸ hc).2
    rw [hrej]
    rw [Bool.and_eq_true] at hc
    refine iff_of_false (by simp) ?_
    rintro (h0 | hle)
    · rw [hb1.mpr h0] at hc; exact absurd hc.1 (by decide)
    · rw [hb2.mpr hle] at hc; exact absurd hc.2 (by decide)
  · rw [Bool.not_eq_true, Bool.and_eq_false_iff] at hc
    have hpass : v.canVaultUpdate (some m) blockDeposit unblockDeposit = .ok .tesSUCCESS := by
      rcases hc with h1 | h2
      · simp [Vault.canVaultUpdate, hgrid, hperm, hat, h1, bind, Except.bind, pure, Except.pure]
      · simp [Vault.canVaultUpdate, hgrid, hperm, hat, h2, bind, Except.bind, pure, Except.pure]
    refine iff_of_true hpass ?_
    rcases hc with h1 | h2
    · exact Or.inl (hb1.mp h1)
    · exact Or.inr (hb2.mp h2)

/-- Proof of `Vault.canVaultUpdate_lawful_iff`. -/
lemma Vault.canVaultUpdate_lawful_iff_proof (v : Vault) (m assetsTotal : Number) (blockDeposit unblockDeposit : Bool)
    (hnorm : m.isNormalized) (hat : v.assetsTotal = .ok assetsTotal) :
    v.canVaultUpdate (some m) blockDeposit unblockDeposit = .ok .tesSUCCESS ↔
      m.isOnExponentGrid v.baseExponent v.numericType = .ok true ∧
      (!v.ownerCanBlockDeposit && (blockDeposit || unblockDeposit)) = false ∧
      (m.toRat = 0 ∨ assetsTotal.toRat ≤ m.toRat) := by
  constructor
  · intro hok
    have hgrid : m.isOnExponentGrid v.baseExponent v.numericType = .ok true := by
      cases hg : m.isOnExponentGrid v.baseExponent v.numericType with
      | error e => simp [Vault.canVaultUpdate, hg, bind, Except.bind] at hok
      | ok b =>
        cases b with
        | true => rfl
        | false =>
          rw [Vault.canVaultUpdate_off_grid_proof v m blockDeposit unblockDeposit hg] at hok
          simp at hok
    have hperm : (!v.ownerCanBlockDeposit && (blockDeposit || unblockDeposit)) = false := by
      cases hb : (!v.ownerCanBlockDeposit && (blockDeposit || unblockDeposit)) with
      | false => rfl
      | true =>
        rw [Bool.and_eq_true, Bool.not_eq_true'] at hb
        rw [Vault.canVaultUpdate_no_permission_proof v (some m) blockDeposit unblockDeposit
          (fun m' hm' => by cases hm'; exact hgrid) hb.1 hb.2] at hok
        simp at hok
    exact ⟨hgrid, hperm, (canVaultUpdate_on_grid_iff v m assetsTotal blockDeposit unblockDeposit hnorm hgrid hperm
      hat).mp hok⟩
  · rintro ⟨hgrid, hperm, h⟩
    exact (canVaultUpdate_on_grid_iff v m assetsTotal blockDeposit unblockDeposit hnorm hgrid hperm hat).mpr h

end XRPL.Model.SingleAssetVault
