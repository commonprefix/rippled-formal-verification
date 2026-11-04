import XRPL.Properties.Vault.Common.GuardProofs
import XRPL.Properties.Vault.Proofs.Support.DepositExchange
import XRPL.Properties.Vault.Proofs.Reachable

/-! # The maximum check of `Vault.canVaultUpdate`

The check compares the new maximum with the total it computes, the cash plus the deployed assets
rounded down to 19 digits. On a reachable vault nothing is deployed, so that total is exact. -/

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol

/-- Proof of `Vault.canVaultUpdate_lawful_iff`. -/
lemma Vault.canVaultUpdate_lawful_iff_proof (v : Vault) (m assetsTotal : Number) (blockDeposit unblockDeposit : Bool)
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

/-- Proof of `Vault.Reachable.canVaultUpdate_iff`. -/
lemma Vault.Reachable.canVaultUpdate_iff_proof (v : Vault) (t : UInt32) (hr : Vault.Reachable v t) (m : Number)
    (blockDeposit unblockDeposit : Bool) (hnorm : m.isNormalized)
    (hgrid : m.isOnExponentGrid v.baseExponent v.numericType = .ok true)
    (hperm : (!v.ownerCanBlockDeposit && (blockDeposit || unblockDeposit)) = false) :
    v.canVaultUpdate (some m) blockDeposit unblockDeposit = .ok .tesSUCCESS ↔
      m.toRat = 0 ∨ v.toExact.assetsTotal ≤ m.toRat := by
  obtain ⟨n, hat, hn⟩ := Vault.Reachable.depositNavExact_proof v t hr
  rw [show v.toExact.assetsTotal = n.toRat from hn.symm]
  exact Vault.canVaultUpdate_lawful_iff_proof v m n blockDeposit unblockDeposit hnorm hgrid hperm hat

end XRPL.Model.SingleAssetVault
