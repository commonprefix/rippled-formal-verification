import XRPL.Properties.Lending.Ledger.Common.Scope
import XRPL.Properties.Lending.Ledger.Common.OpenZoneSteps
import XRPL.Properties.Vault.Proofs.DepositRounding.Charge
import XRPL.Properties.Lending.Ledger.Common.WithdrawHolder
import XRPL.Properties.Lending.Ledger.Common.RecheckVault

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
    exact hlt ((Number.operator_lt_iff _ _ hh hb).mpr hc)
  exact ⟨Number.operator_sub_isNormalized_to_nearest_sz _ _ _ hh hb hok,
    Number.RoundsToRepresentable.nonneg_of_nonneg _ _ (Number.operator_sub_rounded_to_nearest _ _ _ hh hb hok)
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

open XRPL.Model.SingleAssetVault in
/-- A vault transaction writes a holding of at least zero for the holder it names, when every holder owns a whole
number of shares. -/
private lemma LendingLedger.applyVault_holder_nonneg (l : LendingLedger) (hl : l.SharesNonneg)
    (hwhole : ∀ h, (l.sharesOf h).toRat.den = 1)
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
      exact ⟨Number.operator_add_isNormalized_to_nearest_sz _ _ _ hhn hmn' ‹_›,
        Number.operator_add_nonneg _ _ _ hhn hmn' ‹_› (by rw [hmv]; linarith)⟩
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
    have hc := LendingTx.preflight_vaultClawback_canonical l hasset h assets ((TER.isTesSuccess_iff _).mp hpre)
    have hmax := hasset.maxValue_le
    simp only [LendingLedger.applyVault] at hu
    split at hu
    · rename_i hnn
      unfold_ter at hu
      walk_ok
      simp only [Option.mem_def, Option.some.injEq] at hp
      subst hp
      have hof : STAmount.ofNumber .int64 (l.sharesOf h) .to_nearest = .ok _ := ‹_›
      have hcl : (l.vault.clawback assets _ (l.isSoleShareholder h) hnn).run = .ok (.ok _) := ‹_›
      have hdes : (_ : STAmount).toNumber .to_nearest = .ok _ := ‹_›
      obtain ⟨hheldn, hheld0⟩ := hl.sharesOf h
      -- the holding as a share amount of the same value
      obtain ⟨hic, hty⟩ := STAmount.ofNumber_integral_canonical .int64 _ _ _ (by decide) hof
      have hval := STAmount.ofNumber_integral_exact .int64 _ _ _ (by decide) hheldn (hwhole h) hof
      have hfit : (l.sharesOf h).toRat ≤ 2 ^ 63 - 1 := by
        rw [← hval]; exact le_trans (le_abs_self _) (hic.abs_le_int64 hty)
      obtain ⟨-, -, hneg, -, -⟩ := STAmount.ofNumber_int64_shape _ _ _ hheldn hheld0 (hwhole h) hfit hof
      have hhs : STAmount.ShareBalance _ := ⟨hty, hic.canonical (by rw [hty]; decide), hneg⟩
      -- the clawback checked that the holder owns the shares it destroys
      obtain ⟨hz, hlt⟩ := Vault.clawback_ok_holder _ _ _ _ hnn _ hcl
      obtain ⟨amounts, raw, hcomp, -, -, -, hrsh⟩ := Vault.clawback_ok_reduces _ _ _ _ hnn _ hcl
      obtain ⟨hsic, hs64, -, -, -⟩ := computeClawback_amounts_form _ _ _ _ _ hc hnn hhs hmax hcomp
      rw [← hrsh] at hsic hs64
      have hcmp := STAmount.CmpFaithful.ofIntegral _ _ hic hsic
        (by simp [STAmount.areComparable, hty, hs64]) (fun _ => hneg)
        (fun h0 => absurd h0 (by simpa [STAmount.isZero] using hz))
      rw [STAmount.operator_lt_eq _ _ hcmp] at hlt
      obtain ⟨hdv, hdn⟩ := STAmount.CanonicalOrZero.toNumber_exact
        (Or.inl (hsic.canonical (by rw [hs64]; decide))) _ hdes
      refine Number.sub_covered _ _ _ hheldn hdn (fun hlt' => ?_) ‹_›
      have hlt'' := (Number.operator_lt_iff _ _ hheldn hdn).mp hlt'
      rw [← hval, hdv] at hlt''
      simp [hlt''] at hlt
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

/-- Every transaction keeps every holder's shares at least zero, when every holder owns a whole number of
shares. -/
lemma LendingLedger.SharesNonneg.step {l l' : LendingLedger} {tx : LendingTx} (hl : l.SharesNonneg)
    (hwhole : ∀ h, (l.sharesOf h).toRat.den = 1)
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
        (l.applyVault_holder_nonneg hl hwhole hasset tx hpre u hu (i, n) hs)
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

end XRPL.Model.Lending
