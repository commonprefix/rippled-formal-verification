import XRPL.Properties.Lending.Ledger.Common.Scope
import XRPL.Properties.Vault.Proofs.Frame
import XRPL.Properties.Lending.Ledger.Common.WithdrawHolder

/-! # What a vault transaction leaves to the lending side

Deposits, withdrawals, clawbacks and burns write only AssetsAvailable and SharesTotal, and VaultSet only
AssetsMaximum and the deposit block, so the lent-out balances and the schedule stay as they were. -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault (Vault RawVault)

/-- The vault fields only loan transactions write: the lent-out balances, and the settings that never change. -/
structure Vault.KeepsLending (v v' : Vault) : Prop where
  assetsDeployed : v'.assetsDeployed = v.assetsDeployed
  assetsReserved : v'.assetsReserved = v.assetsReserved
  lossUnrealized : v'.lossUnrealized = v.lossUnrealized
  yieldUnrealized : v'.yieldUnrealized = v.yieldUnrealized
  schedule : v'.schedule = v.schedule
  numericType : v'.numericType = v.numericType
  scale : v'.scale = v.scale

/-- A vault that only took new cash and shares keeps the lent-out balances and settings. -/
lemma Vault.KeepsLending.of_raw {v v' : Vault} {aa st : Number}
    (h : v'.toRawVault = { v.toRawVault with assetsAvailable := aa, sharesTotal := st }) : Vault.KeepsLending v v' :=
  ⟨(congrArg RawVault.assetsDeployed h :), (congrArg RawVault.assetsReserved h :),
    (congrArg RawVault.lossUnrealized h :), (congrArg RawVault.yieldUnrealized h :),
    (congrArg RawVault.schedule h :), (congrArg RawVault.numericType h :), (congrArg RawVault.scale h :)⟩

open XRPL.Model.SingleAssetVault in
/-- A vault transaction keeps the lent-out balances and the vault settings it does not set. -/
lemma LendingLedger.applyVault_keepsLending (l : LendingLedger) (tx : LendingTx) (u : VaultEffect)
    (h : (l.applyVault tx).run = .ok (.ok u)) : Vault.KeepsLending l.vault u.vault := by
  cases tx with
  | vaultDeposit hd amount isDonation =>
    simp only [LendingLedger.applyVault] at h
    split at h
    · unfold_ter at h
      walk_ok
      obtain ⟨_, _, hf⟩ := Vault.deposit_frame _ _ _ _ _ _ ‹_›
      exact Vault.KeepsLending.of_raw hf
    · cases h
  | vaultWithdraw hd amount =>
    simp only [LendingLedger.applyVault] at h
    split at h
    · unfold_ter at h
      walk_ok
      all_goals
        obtain ⟨_, _, hf⟩ := Vault.withdraw_frame _ _ _ _ _ _ (Vault.withdraw_holder_ok _ _ _ _ _ _ _ ‹_›).1
        exact Vault.KeepsLending.of_raw hf
    · cases h
  | vaultClawback hd assets =>
    simp only [LendingLedger.applyVault] at h
    split at h
    · unfold_ter at h
      walk_ok
      all_goals
        obtain ⟨_, _, hf⟩ := Vault.clawback_frame _ _ _ _ _ _ ‹_›
        exact Vault.KeepsLending.of_raw hf
    · cases h
  | vaultBurnShares hd amount =>
    simp only [LendingLedger.applyVault] at h
    unfold_ter at h
    walk_ok
    obtain ⟨_, hf⟩ := Vault.burnShares_frame _ _ _ ‹_›
    exact ⟨(congrArg RawVault.assetsDeployed hf :), (congrArg RawVault.assetsReserved hf :),
      (congrArg RawVault.lossUnrealized hf :), (congrArg RawVault.yieldUnrealized hf :),
      (congrArg RawVault.schedule hf :), (congrArg RawVault.numericType hf :), (congrArg RawVault.scale hf :)⟩
  | vaultSet m b =>
    simp only [LendingLedger.applyVault] at h
    unfold_ter at h
    walk_ok
    obtain ⟨_, _, hf⟩ := Vault.update_frame _ _ _ _ _ ‹_›
    exact ⟨(congrArg RawVault.assetsDeployed hf :), (congrArg RawVault.assetsReserved hf :),
      (congrArg RawVault.lossUnrealized hf :), (congrArg RawVault.yieldUnrealized hf :),
      (congrArg RawVault.schedule hf :), (congrArg RawVault.numericType hf :), (congrArg RawVault.scale hf :)⟩
  | _ => simp only [LendingLedger.applyVault] at h; cases h

/-- Every transaction keeps the vault's asset. -/
lemma LendingLedger.apply_numericType {l l' : LendingLedger} {tx : LendingTx}
    (h : (l.apply tx).run = .ok (.ok l')) : l'.vault.numericType = l.vault.numericType := by
  by_cases hv : tx.isVault = true
  · obtain ⟨u, hu, rfl⟩ := LendingLedger.apply_vault hv h
    have hvault : (l.commitVault u).vault = u.vault := by
      unfold LendingLedger.commitVault; split <;> simp [LendingLedger.setShares]
    rw [hvault]; exact (l.applyVault_keepsLending tx u hu).numericType
  by_cases hb : tx.isBroker = true
  · obtain ⟨u, -, rfl⟩ := LendingLedger.apply_broker hb h
    rfl
  by_cases hl : tx.isLoan = true
  · obtain ⟨u, hu, rfl⟩ := LendingLedger.apply_loan hl h
    exact (l.applyLoan_keepsSettings tx u hu).numericType
  have hc := (LendingLedger.apply_checked h).2
  cases tx <;> simp only [LendingTx.isVault, LendingTx.isBroker, LendingTx.isLoan, Bool.false_eq_true,
    not_false_eq_true, not_true_eq_false] at hv hb hl
  · simp only [LendingLedger.applyChecked, LendingLedger.applyVaultDelete] at hc
    unfold_ter at hc
    walk_ok
    rfl
  · simp only [LendingLedger.applyChecked] at hc
    cases hc
    rfl

/-- A nonzero amount that passes the preflight's `isCanonicalAmount` check for `nt` is canonical and of type `nt`,
when an integral `nt` has a maximum that fits an int64. -/
lemma isCanonicalAmount_canonical (s : STAmount) (nt : NumericType)
    (hmax : nt.isIntegral = true → nt.maxValue.toNat ≤ maxRep.toNat)
    (h : isCanonicalAmount s nt = true) (hnz : s.mValue ≠ 0) : s.Canonical ∧ s.mNumericType = nt := by
  unfold isCanonicalAmount at h
  rw [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨hty, h⟩ := h
  refine ⟨⟨fun hi => ?_, fun hf => ?_⟩, hty⟩
  · unfold STAmount.integral at hi
    rw [hty] at hi
    rw [if_pos hi] at h
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
    exact ⟨⟨by rw [hty]; exact hi, h.1, by rw [hty]; exact h.2⟩, by rw [hty]; exact hmax hi⟩
  · unfold STAmount.integral at hf
    rw [hty] at hf
    rw [if_neg (by simp [hf])] at h
    simp only [Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true, decide_eq_true_eq] at h
    rcases h with h0 | ⟨⟨⟨hlo, hhi⟩, helo⟩, hehi⟩
    · exact absurd h0 hnz
    · exact ⟨by rw [hty]; exact NumericType.eq_fractional_of_not_integral hf, hlo, hhi, helo, hehi⟩

/-- Every reachable ledger's vault holds an IOU, XRP or an MPT. -/
lemma LendingLedger.Reachable.holdsAsset {l : LendingLedger} (hr : l.Reachable) : Vault.HoldsAsset l.vault :=
  LendingLedger.Reachable.invariant (Inv := fun l => Vault.HoldsAsset l.vault) (fun _ hg => hg.holds_asset)
    (fun _ l' _ hi ha => show Vault.HoldsAsset l'.vault by
      unfold Vault.HoldsAsset at hi ⊢; rw [LendingLedger.apply_numericType ha]; exact hi) hr

end XRPL.Model.Lending
