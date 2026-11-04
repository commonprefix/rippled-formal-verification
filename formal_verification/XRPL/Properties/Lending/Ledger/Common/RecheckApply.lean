import XRPL.Properties.Lending.Common.Walk
import XRPL.Properties.Lending.Ledger.Common.ReachableProofs
import XRPL.Properties.Protocol.Common.Errors
import XRPL.Properties.Vault.Proofs.Support.Errors

/-! # Where a transaction can fail its lawfulness re-check

A transaction fails the model with `notLawful` only through the vault, broker or loan operation it runs.
The preflight, the ledger lookups and the commit never raise it, and neither do `close` and VaultDelete. -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault (Vault RawVault)

/-- A step that maps the result of `x` fails only as `x` does. -/
lemma TerExcept.map_error {ε β : Type} {x : TerExcept ε} {f : ε → β} {e : Error}
    (h : (f <$> x).run = .error e) : x.run = .error e := by
  simp only [ExceptT.run, Functor.map, ExceptT.map, ExceptT.mk, bind, Except.bind] at h ⊢
  cases hx : x with
  | error e' => rw [hx] at h; simpa using h
  | ok r => rw [hx] at h; cases r <;> cases h

/-- A transaction that fails the model passed its preflight, and its checks and operation failed. -/
lemma LendingLedger.apply_error {l : LendingLedger} {tx : LendingTx} {e : Error}
    (h : (l.apply tx).run = .error e) : tx.preflight l = .tesSUCCESS ∧ (l.applyChecked tx).run = .error e := by
  unfold LendingLedger.apply at h
  generalize hp : tx.preflight l = p at h
  dsimp only at h
  cases hs : p.isTesSuccess
  · rw [hs, if_pos (by decide)] at h; cases h
  · rw [hs, if_neg (by decide)] at h; exact ⟨(TER.isTesSuccess_iff p).mp hs, h⟩

/-- A vault transaction fails the model only through its vault operation. -/
lemma LendingLedger.apply_ne_notLawful_of_vault {l : LendingLedger} {tx : LendingTx} (hv : tx.isVault = true)
    (h : tx.preflight l = .tesSUCCESS → l.vaultDeleted = false → (l.applyVault tx).run ≠ .error .notLawful) :
    (l.apply tx).run ≠ .error .notLawful := by
  intro ha
  obtain ⟨hpre, ha⟩ := LendingLedger.apply_error ha
  cases tx <;> simp only [LendingTx.isVault, Bool.false_eq_true] at hv <;>
  · simp only [LendingLedger.applyChecked, LendingTx.isVault, ↓reduceIte] at ha
    split at ha
    · cases ha
    · exact h hpre (by simpa using ‹¬ l.vaultDeleted = true›) (TerExcept.map_error ha)

/-- A broker transaction fails the model only through its broker operation. -/
lemma LendingLedger.apply_ne_notLawful_of_broker {l : LendingLedger} {tx : LendingTx} (hb : tx.isBroker = true)
    (h : tx.preflight l = .tesSUCCESS → l.vaultDeleted = false → (l.applyBroker tx).run ≠ .error .notLawful) :
    (l.apply tx).run ≠ .error .notLawful := by
  intro ha
  obtain ⟨hpre, ha⟩ := LendingLedger.apply_error ha
  cases tx <;> simp only [LendingTx.isBroker, Bool.false_eq_true] at hb <;>
  · simp only [LendingLedger.applyChecked, LendingTx.isVault, LendingTx.isBroker, Bool.false_eq_true,
      ↓reduceIte] at ha
    split at ha
    · cases ha
    · exact h hpre (by simpa using ‹¬ l.vaultDeleted = true›) (TerExcept.map_error ha)

/-- A loan transaction fails the model only through its loan operation. -/
lemma LendingLedger.apply_ne_notLawful_of_loan {l : LendingLedger} {tx : LendingTx} (hl : tx.isLoan = true)
    (h : tx.preflight l = .tesSUCCESS → l.vaultDeleted = false → (l.applyLoan tx).run ≠ .error .notLawful) :
    (l.apply tx).run ≠ .error .notLawful := by
  intro ha
  obtain ⟨hpre, ha⟩ := LendingLedger.apply_error ha
  cases tx <;> simp only [LendingTx.isLoan, Bool.false_eq_true] at hl <;>
  · simp only [LendingLedger.applyChecked, LendingTx.isVault, LendingTx.isBroker, Bool.false_eq_true,
      ↓reduceIte] at ha
    split at ha
    · cases ha
    · exact h hpre (by simpa using ‹¬ l.vaultDeleted = true›) (TerExcept.map_error ha)

/-- A `close` never fails the model. -/
lemma LendingLedger.close_ne_notLawful (l : LendingLedger) (time : UInt32) :
    (l.apply (.close time)).run ≠ .error .notLawful := by
  intro ha
  obtain ⟨-, ha⟩ := LendingLedger.apply_error ha
  simp only [LendingLedger.applyChecked] at ha
  cases ha

/-- The VaultDelete checks read the vault through Number comparisons only. -/
lemma Vault.canVaultDelete_ne_notLawful (v : Vault) : v.canVaultDelete ≠ .error .notLawful := by
  unfold XRPL.Model.SingleAssetVault.Vault.canVaultDelete
  simp only [bind, Except.bind, pure, Except.pure]
  split_ne_notLawful [RawVault.assetsTotal_ne_notLawful]

/-- The Open-limit check reads the vault through Number sums and comparisons only. -/
lemma Vault.exceedsOpenLimit_ne_notLawful (v : Vault) (x : Number) : v.exceedsOpenLimit x ≠ .error .notLawful := by
  unfold XRPL.Model.SingleAssetVault.Vault.exceedsOpenLimit XRPL.Model.SingleAssetVault.Vault.openLimit
  simp only [bind, Except.bind, pure, Except.pure]
  split_ne_notLawful [RawVault.assetsTotal_ne_notLawful, Number.operator_add_ne_notLawful,
    Number.from_rep_ne_notLawful]

/-- A VaultDelete never fails its lawfulness re-check. It re-checks no ledger object. -/
lemma LendingLedger.vaultDelete_ne_notLawful (l : LendingLedger) :
    (l.apply .vaultDelete).run ≠ .error .notLawful := by
  intro ha
  obtain ⟨-, ha⟩ := LendingLedger.apply_error ha
  simp only [LendingLedger.applyChecked, LendingLedger.applyVaultDelete] at ha
  unfold_ter at ha
  walk_ok'
  all_goals exact Vault.canVaultDelete_ne_notLawful _ ‹_›

end XRPL.Model.Lending
