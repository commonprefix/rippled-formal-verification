import XRPL.Properties.Lending.Ledger.Common.CashPrecision
import XRPL.Properties.Lending.Ledger.Common.DebtInv
import XRPL.Properties.Lending.Ledger.Common.LossInv
import XRPL.Properties.Lending.Ledger.Common.WithdrawHolder

/-! # The lending ledger stores the vault's amounts exactly

AssetsReserved and LossUnrealized are whole base units within `10^16` base units and AssetsDeployed. VaultCreate
and VaultSet put AssetsMaximum on the base grid, and no other transaction writes it. -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault (Vault RawVault)

/-- The asset stores the vault's AssetsMaximum exactly. -/
private def Vault.StoresMaximum (v : Vault) : Prop := ∀ m ∈ v.assetsMaximum, STAmount.isRounded v.numericType m = false

/-- A vault that keeps AssetsMaximum and its asset keeps AssetsMaximum stored exactly. -/
private lemma Vault.StoresMaximum.of_raw {v v' : Vault} (hst : Vault.StoresMaximum v)
    (hm : v'.assetsMaximum = v.assetsMaximum) (hnt : v'.numericType = v.numericType) : Vault.StoresMaximum v' := by
  unfold Vault.StoresMaximum; rw [hm, hnt]; exact hst

/-- A VaultSet check that passed returned tesSUCCESS. -/
private lemma Vault.canVaultUpdate_success {v : Vault} {m : Option Number} {b : Option Bool} {ter : TER}
    (h : v.canVaultUpdate m b = .ok ter) (hs : ¬(!ter.isTesSuccess) = true) :
    v.canVaultUpdate m b = .ok .tesSUCCESS := by
  rw [h, (TER.isTesSuccess_iff ter).mp (by simpa using hs)]

open XRPL.Model.SingleAssetVault in
/-- A vault transaction keeps AssetsMaximum stored exactly. -/
private lemma LendingLedger.applyVault_storesMaximum (l : LendingLedger) (tx : LendingTx) (u : VaultEffect)
    (h : (l.applyVault tx).run = .ok (.ok u)) (hst : Vault.StoresMaximum l.vault) : Vault.StoresMaximum u.vault := by
  cases tx with
  | vaultDeposit hd amount isDonation =>
    simp only [LendingLedger.applyVault] at h
    split at h
    · unfold_ter at h
      walk_ok
      obtain ⟨_, _, hf⟩ := Vault.deposit_frame _ _ _ _ _ _ ‹_›
      exact hst.of_raw (congrArg RawVault.assetsMaximum hf :) (congrArg RawVault.numericType hf :)
    · cases h
  | vaultWithdraw hd amount =>
    simp only [LendingLedger.applyVault] at h
    split at h
    · unfold_ter at h
      walk_ok
      all_goals
        obtain ⟨_, _, hf⟩ := Vault.withdraw_frame _ _ _ _ _ _ (Vault.withdraw_holder_ok _ _ _ _ _ _ _ ‹_›).1
        exact hst.of_raw (congrArg RawVault.assetsMaximum hf :) (congrArg RawVault.numericType hf :)
    · cases h
  | vaultClawback hd assets =>
    simp only [LendingLedger.applyVault] at h
    split at h
    · unfold_ter at h
      walk_ok
      all_goals
        obtain ⟨_, _, hf⟩ := Vault.clawback_frame _ _ _ _ _ _ ‹_›
        exact hst.of_raw (congrArg RawVault.assetsMaximum hf :) (congrArg RawVault.numericType hf :)
    · cases h
  | vaultBurnShares hd amount =>
    simp only [LendingLedger.applyVault] at h
    unfold_ter at h
    walk_ok
    obtain ⟨_, hf⟩ := Vault.burnShares_frame _ _ _ ‹_›
    exact hst.of_raw (congrArg RawVault.assetsMaximum hf :) (congrArg RawVault.numericType hf :)
  | vaultSet m b =>
    simp only [LendingLedger.applyVault] at h
    unfold_ter at h
    walk_ok
    have hcan := Vault.canVaultUpdate_success ‹_› ‹_›
    obtain ⟨_, _, hf⟩ := Vault.update_frame _ _ _ _ _ ‹_›
    intro m' hm'
    rw [(congrArg RawVault.numericType hf :)]
    rcases Vault.update_assetsMaximum_mem _ _ _ _ _ ‹_› m' hm' with h' | h'
    · exact hst m' h'
    · subst h'
      exact Number.isRounded_eq_false_of_isOnExponentGrid _ _ _ (Vault.canVaultUpdate_assetsMaximum _ m' _ _ hcan)
  | _ => simp only [LendingLedger.applyVault] at h; cases h

/-- Every transaction keeps AssetsMaximum stored exactly. -/
private lemma LendingLedger.apply_storesMaximum {l l' : LendingLedger} {tx : LendingTx}
    (h : (l.apply tx).run = .ok (.ok l')) (hst : Vault.StoresMaximum l.vault) : Vault.StoresMaximum l'.vault := by
  by_cases hv : tx.isVault = true
  · obtain ⟨u, hu, rfl⟩ := LendingLedger.apply_vault hv h
    have hvault : (l.commitVault u).vault = u.vault := by
      unfold LendingLedger.commitVault; split <;> simp [LendingLedger.setShares]
    rw [hvault]
    exact l.applyVault_storesMaximum tx u hu hst
  by_cases hb : tx.isBroker = true
  · obtain ⟨u, -, rfl⟩ := LendingLedger.apply_broker hb h
    exact hst
  by_cases hl : tx.isLoan = true
  · obtain ⟨u, hu, rfl⟩ := LendingLedger.apply_loan hl h
    have hs := l.applyLoan_keepsSettings tx u hu
    exact hst.of_raw hs.assetsMaximum hs.numericType
  have hc := (LendingLedger.apply_checked h).2
  cases tx <;> simp only [LendingTx.isVault, LendingTx.isBroker, LendingTx.isLoan, Bool.false_eq_true,
    not_false_eq_true, not_true_eq_false] at hv hb hl
  · -- vaultDelete only sets the deleted flag
    simp only [LendingLedger.applyChecked, LendingLedger.applyVaultDelete] at hc
    unfold_ter at hc
    walk_ok
    exact hst
  · -- close moves the close time forward
    simp only [LendingLedger.applyChecked] at hc
    cases hc
    exact hst

/-- VaultCreate puts AssetsMaximum on the base grid. -/
private lemma LendingLedger.Genesis.storesMaximum {g : LendingLedger} (hg : g.Genesis) :
    Vault.StoresMaximum g.vault := by
  obtain ⟨scale, amax, s, eer, ocb, nt, hcan, hcreate⟩ := hg.created
  unfold XRPL.Model.SingleAssetVault.Vault.create at hcreate
  have hraw := (XRPL.Model.SingleAssetVault.RawVault.to_lawful_ok hcreate).1
  have hmax : g.vault.assetsMaximum = _ := (congrArg RawVault.assetsMaximum hraw :)
  have hnt : g.vault.numericType = nt := (congrArg RawVault.numericType hraw :)
  intro m hm
  rw [hmax] at hm
  have hm' : m ∈ amax := by
    clear hcan hcreate hraw hmax
    cases amax with
    | none => simp at hm
    | some b =>
      simp only [Option.filter, Option.mem_def] at hm ⊢
      split at hm <;> simp_all
  rw [hnt]
  exact Number.isRounded_eq_false_of_isOnExponentGrid _ _ _ (Vault.canCreate_assetsMaximum _ _ _ _ _ hcan m hm')

/-- On a reachable ledger the asset stores AssetsMaximum exactly. -/
private lemma LendingLedger.Reachable.storesMaximum {l : LendingLedger} (hr : l.Reachable) :
    Vault.StoresMaximum l.vault :=
  LendingLedger.Reachable.invariant (Inv := fun l => Vault.StoresMaximum l.vault) (fun _ hg => hg.storesMaximum)
    (fun _ _ _ hi ha => LendingLedger.apply_storesMaximum ha hi) hr

/-- A whole number of base units, at most `10^16` of them and at most AssetsDeployed, is a value the asset
stores exactly. -/
private lemma Vault.isRounded_false_of_units (v : Vault) (x : Number) (hn : x.isNormalized) (hnn : 0 ≤ x.toRat)
    (hgrid : ∃ n : ℕ, x.toRat = (n : ℚ) * 10 ^ v.baseExponent)
    (hbound : x.toRat ≤ 10 ^ 16 * (10 : ℚ) ^ v.baseExponent) (hle : x.toRat ≤ v.assetsDeployed.toRat) :
    STAmount.isRounded v.numericType x = false := by
  rw [STAmount.isRounded_eq_false_iff _ _ hn hnn]
  obtain ⟨n, hx⟩ := hgrid
  have hAD : STAmount.Representable v.numericType v.assetsDeployed.toRat := v.exact.assetsDeployed_representable
  have hscale := v.wf.scale_le
  unfold XRPL.Model.SingleAssetVault.Vault.baseExponent NumericType.baseExponent at hx hbound
  cases hnt : v.numericType with
  | integral mv mo ms msh =>
    rw [hnt] at hx hbound hAD
    simp only [NumericType.isIntegral, if_true, zpow_zero, mul_one] at hx hbound
    rcases hAD with h0 | ⟨hmo, k, hk, hk63, hk'⟩
    · exact Or.inl (le_antisymm (h0 ▸ hle) hnn)
    · have hnk : n ≤ k := by exact_mod_cast (show (n : ℚ) ≤ k by rw [← hx, ← hk']; exact hle)
      exact Or.inr ⟨hmo, n, le_trans hnk hk, le_trans hnk hk63, hx⟩
  | fractional =>
    rw [hnt] at hx hbound
    simp only [NumericType.isIntegral, Bool.false_eq_true, if_false] at hx hbound
    have hpos : (0 : ℚ) < 10 ^ (-(v.scale.toNat : ℤ)) := by positivity
    have hn16 : n ≤ 10 ^ 16 := by
      have : (n : ℚ) ≤ 10 ^ 16 := le_of_mul_le_mul_right (by rw [← hx]; exact hbound) hpos
      exact_mod_cast this
    have hs : v.scale.toNat ≤ 10 := UInt8.le_iff_toNat_le.mp hscale
    rcases lt_or_eq_of_le hn16 with hlt | heq
    · rw [hx]; exact STAmount.representable_fractional_of_units n _ hlt (by omega) (by omega)
    · refine Or.inr ⟨10 ^ 15, -(v.scale.toNat : ℤ) + 1, by norm_num, by norm_num, by omega, by omega, ?_⟩
      rw [hx, heq, zpow_add₀ (by norm_num)]
      push_cast
      ring

/-- On a reachable ledger the asset stores AssetsAvailable, AssetsDeployed, AssetsReserved, LossUnrealized,
AssetsMaximum and every broker's DebtTotal exactly, when an XRP or MPT asset's maximum fits an int64. -/
lemma LendingLedger.associateAsset_noop_proof (l : LendingLedger) (hr : l.Reachable)
    (hmax : l.vault.numericType.isIntegral = true → l.vault.numericType.maxValue.toNat ≤ maxRep.toNat) :
    STAmount.isRounded l.vault.numericType l.vault.assetsAvailable = false ∧
      STAmount.isRounded l.vault.numericType l.vault.assetsDeployed = false ∧
      STAmount.isRounded l.vault.numericType l.vault.assetsReserved = false ∧
      STAmount.isRounded l.vault.numericType l.vault.lossUnrealized = false ∧
      (∀ (j : Nat) (b : LoanBroker), l.broker? j = some b →
        STAmount.isRounded l.vault.numericType b.debtTotal = false) ∧
      ∀ m ∈ l.vault.assetsMaximum, STAmount.isRounded l.vault.numericType m = false := by
  have hloss := hr.lossInv
  refine ⟨hr.storesAvailable hmax, l.vault.valid.assetsDeployed_representable, ?_, ?_, ?_, hr.storesMaximum⟩
  · exact Vault.isRounded_false_of_units l.vault _ l.vault.wf.assetsReserved_norm
      l.vault.exact.assetsReserved_nonneg hloss.reserved.grid hloss.reserved.bound l.vault.exact.assetsReserved_le
  · exact Vault.isRounded_false_of_units l.vault _ l.vault.wf.lossUnrealized_norm
      l.vault.exact.lossUnrealized_nonneg hloss.grid hloss.bound l.vault.exact.lossUnrealized_le
  · -- DebtTotal is the sum of its loans' principal, whole base units within AssetsDeployed
    intro j b hb
    have hd := hr.debtInv
    have hdt := hd.debt j b hb
    have hle : b.debtTotal.toRat ≤ l.vault.assetsDeployed.toRat := by
      rw [hdt, hd.deployed]; exact l.brokerPrincipal_le j
    obtain ⟨n, hn⟩ := hr.scaleInv.brokerPrincipal_grid j
    have h0 : 0 ≤ b.debtTotal.toRat := by rw [hdt, hn]; positivity
    exact Vault.isRounded_false_of_units l.vault _ b.wf.debtTotal_norm h0 ⟨n, by rw [hdt, hn]⟩
      (le_trans hle hloss.deployed) hle

end XRPL.Model.Lending
