import XRPL.Properties.Lending.Ledger.Common.Scope
import XRPL.Properties.Protocol.STAmount.Common.OfNumberRounding
import XRPL.Properties.Protocol.Number.Sub.ZeroShape

/-! # Holder shares on a reachable ledger

Every holder's shares are a normalized Number. A vault transaction writes the holder's new shares as a
sum, a difference or zero, every other transaction leaves the shares as they are. -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault (Vault)

/-- Every holder's shares are a normalized Number. -/
def LendingLedger.SharesNormalized (l : LendingLedger) : Prop :=
  ∀ x ∈ l.shares, x.isNormalized

/-- The shares of any holder are a normalized Number, zero for a holder the ledger doesn't list. -/
lemma LendingLedger.SharesNormalized.sharesOf {l : LendingLedger} (hl : l.SharesNormalized) (h : Nat) :
    (l.sharesOf h).isNormalized := by
  unfold LendingLedger.sharesOf
  rw [List.getD_eq_getElem?_getD]
  cases hx : l.shares[h]? with
  | none => exact Number.zero_isNormalized
  | some x => exact hl x (List.mem_of_getElem? hx)

/-- Setting one holder to a normalized Number keeps every holder normalized. -/
private lemma LendingLedger.SharesNormalized.setShares {l : LendingLedger} (hl : l.SharesNormalized) (h : Nat)
    (n : Number) (hn : n.isNormalized) : (l.setShares h n).SharesNormalized := by
  intro x hx
  unfold LendingLedger.setShares at hx
  rcases List.mem_or_eq_of_mem_set hx with hx | rfl
  · rcases List.mem_append.mp hx with hx | hx
    · exact hl x hx
    · rw [List.eq_of_mem_replicate hx]; exact Number.zero_isNormalized
  · exact hn

/-- A vault transaction writes a normalized share count for the holder it names. -/
private lemma LendingLedger.applyVault_holder (l : LendingLedger) (hl : l.SharesNormalized) (tx : LendingTx)
    (u : VaultEffect) (hu : (l.applyVault tx).run = .ok (.ok u)) : ∀ p ∈ u.holderShares, p.2.isNormalized := by
  intro p hp
  cases tx with
  | vaultDeposit h amount isDonation =>
    simp only [LendingLedger.applyVault] at hu
    split at hu
    · unfold_ter at hu
      walk_ok'
      simp only [Option.mem_def, Option.some.injEq] at hp
      subst hp
      exact operator_add_isNormalized_to_nearest_sz _ _ _ (hl.sharesOf h)
        (STAmount.toNumber_isNormalized _ _ _ ‹_›) ‹_›
    · cases hu
  | vaultWithdraw h amount =>
    simp only [LendingLedger.applyVault] at hu
    split at hu
    · unfold_ter at hu
      walk_ok'
      simp only [Option.mem_def, Option.some.injEq] at hp
      subst hp
      exact operator_sub_isNormalized_to_nearest_sz _ _ _ (hl.sharesOf h)
        (STAmount.toNumber_isNormalized _ _ _ ‹_›) ‹_›
    · cases hu
  | vaultClawback h assets =>
    simp only [LendingLedger.applyVault] at hu
    split at hu
    · unfold_ter at hu
      walk_ok'
      simp only [Option.mem_def, Option.some.injEq] at hp
      subst hp
      exact operator_sub_isNormalized_to_nearest_sz _ _ _ (hl.sharesOf h)
        (STAmount.toNumber_isNormalized _ _ _ ‹_›) ‹_›
    · cases hu
  | vaultBurnShares h amount =>
    simp only [LendingLedger.applyVault] at hu
    unfold_ter at hu
    walk_ok'
    simp only [Option.mem_def, Option.some.injEq] at hp
    subst hp
    exact Number.zero_isNormalized
  | vaultSet assetsMaximum blockDeposit =>
    simp only [LendingLedger.applyVault] at hu
    unfold_ter at hu
    walk_ok'
    cases hp
  | _ => simp only [LendingLedger.applyVault] at hu; cases hu

/-- Every transaction keeps every holder's shares normalized. -/
private lemma LendingLedger.SharesNormalized.step {l l' : LendingLedger} {tx : LendingTx} (hl : l.SharesNormalized)
    (h : (l.apply tx).run = .ok (.ok l')) : l'.SharesNormalized := by
  by_cases hv : tx.isVault = true
  · obtain ⟨u, hu, rfl⟩ := LendingLedger.apply_vault hv h
    unfold LendingLedger.commitVault
    cases hs : u.holderShares with
    | none => exact hl
    | some p =>
      obtain ⟨i, n⟩ := p
      exact LendingLedger.SharesNormalized.setShares (l := { l with vault := u.vault }) hl i n
        (l.applyVault_holder hl tx u hu (i, n) hs)
  by_cases hb : tx.isBroker = true
  · unfold LendingLedger.SharesNormalized; rw [(LendingLedger.broker_ops_scope_proof l l' tx hb h).2.1]; exact hl
  by_cases hlo : tx.isLoan = true
  · unfold LendingLedger.SharesNormalized; rw [(LendingLedger.loan_ops_scope_proof l l' tx hlo h).2.2.1]; exact hl
  have h' := (LendingLedger.apply_checked h).2
  cases tx <;> simp only [LendingTx.isVault, LendingTx.isBroker, LendingTx.isLoan, not_true_eq_false] at hv hb hlo
  · simp only [LendingLedger.applyChecked, LendingLedger.applyVaultDelete] at h'
    unfold_ter at h'
    walk_ok'
    exact hl
  · simp only [LendingLedger.applyChecked] at h'
    unfold_ter at h'
    walk_ok'
    exact hl

/-- On a reachable ledger every holder's shares are a normalized Number. -/
lemma LendingLedger.Reachable.sharesNormalized {l : LendingLedger} (hr : l.Reachable) : l.SharesNormalized :=
  LendingLedger.Reachable.invariant (Inv := LendingLedger.SharesNormalized)
    (fun g hg => by intro x hx; rw [hg.no_holders] at hx; cases hx)
    (fun _ _ _ hi ha => hi.step ha) hr

end XRPL.Model.Lending
