import XRPL.Properties.Lending.Ledger.Common.Scope
import XRPL.Properties.Lending.Ledger.Common.OpenZoneSteps
import XRPL.Properties.Vault.Proofs.DepositRounding.Charge
import XRPL.Properties.Lending.Ledger.Common.WithdrawHolder

/-! # Holder shares are never negative

A deposit adds the shares it mints, a withdrawal and a clawback take off at most what the holder has, a burn
zeroes the holding, and every other transaction leaves the shares as they are. -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault (Vault VaultWithAmounts)

/-- Every holder's shares are a normalized Number of at least zero. -/
def LendingLedger.SharesNonneg (l : LendingLedger) : Prop :=
  ∀ x ∈ l.shares, x.isNormalized ∧ 0 ≤ x.toRat

/-- The shares of any holder are a normalized Number of at least zero, zero for a holder the ledger doesn't list. -/
lemma LendingLedger.SharesNonneg.sharesOf {l : LendingLedger} (hl : l.SharesNonneg) (h : Nat) :
    (l.sharesOf h).isNormalized ∧ 0 ≤ (l.sharesOf h).toRat := by
  unfold LendingLedger.sharesOf
  rw [List.getD_eq_getElem?_getD]
  cases hx : l.shares[h]? with
  | none => exact ⟨Number.zero_isNormalized, by rw [Option.getD_none, Number.toRat_zero]⟩
  | some x => exact hl x (List.mem_of_getElem? hx)

private lemma LendingLedger.SharesNonneg.setShares {l : LendingLedger} (hl : l.SharesNonneg) (h : Nat)
    (n : Number) (hn : n.isNormalized ∧ 0 ≤ n.toRat) : (l.setShares h n).SharesNonneg := by
  intro x hx
  unfold LendingLedger.setShares at hx
  rcases List.mem_or_eq_of_mem_set hx with hx | rfl
  · rcases List.mem_append.mp hx with hx | hx
    · exact hl x hx
    · rw [List.eq_of_mem_replicate hx]; exact ⟨Number.zero_isNormalized, by rw [Number.toRat_zero]⟩
  · exact hn

/-- A holding less an amount it covers is a normalized Number of at least zero. -/
private lemma Number.sub_covered (held burned shares' : Number) (hh : held.isNormalized)
    (hb : burned.isNormalized) (hlt : ¬ held.operator_lt burned = true)
    (hok : held.operator_sub burned .to_nearest = .ok shares') : shares'.isNormalized ∧ 0 ≤ shares'.toRat := by
  have hle : burned.toRat ≤ held.toRat := by
    by_contra hc
    push Not at hc
    exact hlt ((operator_lt_iff _ _ hh hb).mpr hc)
  exact ⟨operator_sub_isNormalized_to_nearest_sz _ _ _ hh hb hok,
    Number.RoundsToRepresentable.nonneg_of_nonneg _ _ (operator_sub_rounded_to_nearest _ _ _ hh hb hok)
      (by linarith)⟩

open XRPL.Model.SingleAssetVault in
/-- A deposit mints shares of at least zero. -/
private lemma Vault.deposit_shares_nonneg (v : Vault) (amount : STAmount) (isDonation : Bool) (t : UInt32)
    (hpos : 0 < amount.toRat) (hc : amount.Canonical) (r : VaultWithAmounts)
    (h : (v.deposit amount isDonation t hpos).run = .ok (.ok r)) :
    r.shares.CanonicalOrZero ∧ 0 ≤ r.shares.toRat := by
  obtain ⟨ra, amounts, -, hra, hcomp, -, -, -, -, hrs⟩ := Vault.deposit_ok_reduces v amount isDonation t hpos r h
  obtain ⟨hrc, hrp⟩ := DepRnd.Vault.roundedDepositAmount_canonical_pos v amount ra hc hra
  rw [hrs]
  obtain ⟨hic, hty, h0⟩ := computeDeposit_shares_form v ra isDonation amounts hrc hrp hcomp
  exact ⟨Or.inl (hic.canonical (by rw [hty]; decide)), h0⟩

/-- A vault transaction writes a holding of at least zero for the holder it names. -/
private lemma LendingLedger.applyVault_holder_nonneg (l : LendingLedger) (hl : l.SharesNonneg)
    (hasset : Vault.HoldsAsset l.vault) (tx : LendingTx) (hpre : (tx.preflight l).isTesSuccess = true)
    (u : VaultEffect) (hu : (l.applyVault tx).run = .ok (.ok u)) :
    ∀ p ∈ u.holderShares, p.2.isNormalized ∧ 0 ≤ p.2.toRat := by
  intro p hp
  cases tx with
  | vaultDeposit h amount isDonation =>
    obtain ⟨hc, -⟩ := LendingTx.preflight_vaultDeposit' l h amount isDonation hasset hpre
    simp only [LendingLedger.applyVault] at hu
    split at hu
    · unfold_ter at hu
      walk_ok
      simp only [Option.mem_def, Option.some.injEq] at hp
      subst hp
      have hdep : (l.vault.deposit amount isDonation l.now _).run = .ok (.ok _) := ‹_›
      obtain ⟨hsc, hs0⟩ := Vault.deposit_shares_nonneg _ _ _ _ _ hc _ hdep
      have hmn : (_ : STAmount).toNumber .to_nearest = .ok _ := ‹_›
      obtain ⟨hmv, hmn'⟩ := hsc.toNumber_exact _ hmn
      obtain ⟨hhn, hh0⟩ := hl.sharesOf h
      exact ⟨operator_add_isNormalized_to_nearest_sz _ _ _ hhn hmn' ‹_›,
        operator_add_nonneg _ _ _ hhn hmn' ‹_› (by rw [hmv]; linarith)⟩
    · cases hu
  | vaultWithdraw h amount =>
    simp only [LendingLedger.applyVault] at hu
    split at hu
    · unfold_ter at hu
      walk_ok
      simp only [Option.mem_def, Option.some.injEq] at hp
      subst hp
      -- the withdrawal checked that the holder owns the shares it burns
      have hburn : (_ : STAmount).toNumber .to_nearest = .ok _ := ‹_›
      have hheld := (Vault.withdraw_holder_ok _ _ _ _ _ _ _ ‹_›).2 _ hburn
      exact Number.sub_covered _ _ _ (hl.sharesOf h).1 (STAmount.toNumber_isNormalized _ _ _ hburn)
        (by rw [hheld]; decide) ‹_›
    · cases hu
  | vaultClawback h assets =>
    simp only [LendingLedger.applyVault] at hu
    split at hu
    · unfold_ter at hu
      walk_ok
      simp only [Option.mem_def, Option.some.injEq] at hp
      subst hp
      exact Number.sub_covered _ _ _ (hl.sharesOf h).1 (STAmount.toNumber_isNormalized _ _ _ ‹_›) ‹_› ‹_›
    · cases hu
  | vaultBurnShares h amount =>
    simp only [LendingLedger.applyVault] at hu
    unfold_ter at hu
    walk_ok
    simp only [Option.mem_def, Option.some.injEq] at hp
    subst hp
    exact ⟨Number.zero_isNormalized, by rw [Number.toRat_zero]⟩
  | vaultSet assetsMaximum blockDeposit =>
    simp only [LendingLedger.applyVault] at hu
    unfold_ter at hu
    walk_ok
    cases hp
  | _ => simp only [LendingLedger.applyVault] at hu; cases hu

/-- Every transaction keeps every holder's shares at least zero. -/
private lemma LendingLedger.SharesNonneg.step {l l' : LendingLedger} {tx : LendingTx} (hl : l.SharesNonneg)
    (hasset : Vault.HoldsAsset l.vault) (h : (l.apply tx).run = .ok (.ok l')) : l'.SharesNonneg := by
  by_cases hv : tx.isVault = true
  · have hpre := (LendingLedger.apply_checked h).1
    obtain ⟨u, hu, rfl⟩ := LendingLedger.apply_vault hv h
    unfold LendingLedger.commitVault
    cases hs : u.holderShares with
    | none => exact hl
    | some p =>
      obtain ⟨i, n⟩ := p
      exact LendingLedger.SharesNonneg.setShares (l := { l with vault := u.vault }) hl i n
        (l.applyVault_holder_nonneg hl hasset tx hpre u hu (i, n) hs)
  by_cases hb : tx.isBroker = true
  · unfold LendingLedger.SharesNonneg; rw [(LendingLedger.broker_ops_scope_proof l l' tx hb h).2.1]; exact hl
  by_cases hlo : tx.isLoan = true
  · unfold LendingLedger.SharesNonneg; rw [(LendingLedger.loan_ops_scope_proof l l' tx hlo h).2.2.1]; exact hl
  have h' := (LendingLedger.apply_checked h).2
  cases tx <;> simp only [LendingTx.isVault, LendingTx.isBroker, LendingTx.isLoan, not_true_eq_false] at hv hb hlo
  · simp only [LendingLedger.applyChecked, LendingLedger.applyVaultDelete] at h'
    unfold_ter at h'
    walk_ok
    exact hl
  · simp only [LendingLedger.applyChecked] at h'
    unfold_ter at h'
    walk_ok
    exact hl

/-- On a reachable ledger every holder's shares are a normalized Number of at least zero. -/
lemma LendingLedger.Reachable.sharesNonneg {l : LendingLedger} (hr : l.Reachable) : l.SharesNonneg := by
  have := LendingLedger.Reachable.invariant (Inv := fun l => l.SharesNonneg ∧ Vault.HoldsAsset l.vault)
    (fun g hg => ⟨(by intro x hx; rw [hg.no_holders] at hx; cases hx), hg.holds_asset⟩)
    (fun _ l' _ hi ha => ⟨hi.1.step hi.2 ha, show Vault.HoldsAsset l'.vault by
      have h2 := hi.2
      unfold Vault.HoldsAsset at h2 ⊢; rw [LendingLedger.apply_numericType ha]; exact h2⟩) hr
  exact this.1

end XRPL.Model.Lending
