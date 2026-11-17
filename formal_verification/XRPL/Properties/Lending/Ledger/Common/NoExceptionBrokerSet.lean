import XRPL.Properties.Lending.Ledger.Common.RecheckBroker
import XRPL.Properties.Lending.Ledger.Common.BrokerProofs
import XRPL.Properties.Lending.Loan.Common.OverpaymentSkip

/-! # LoanBrokerSet and LoanBrokerDelete never end in an exception

A LoanBrokerSet reads the new DebtMaximum, which its preflight keeps within `2^63 - 1`, so every conversion to the
asset succeeds. A LoanBrokerDelete converts CoverAvailable to an amount of the asset, which succeeds while the cover
is within the asset's maximum. -/

namespace XRPL.Model.Protocol

open private STAmount.roundToNumericType_towards_zero_ok from XRPL.Properties.Lending.Loan.Common.OverpaymentSkip

/-- The grid check of a DebtMaximum never throws: a value the asset does not store is off the grid, and a value it
stores rounds to the scale. -/
lemma Number.isOnExponentGrid_ok_of_asset (value : Number) (s : Int) (nt : NumericType) (hn : value.isNormalized)
    (h0 : 0 ≤ value.toRat) (hasset : nt = .fractional ∨ nt = .native ∨ nt = .int64) (hs : -81 ≤ s ∧ s ≤ 0) :
    ∃ b, value.isOnExponentGrid s nt = .ok b := by
  unfold Number.isOnExponentGrid
  cases hr : STAmount.isRounded nt value
  · obtain ⟨c, hc⟩ := STAmount.roundToNumericType_towards_zero_ok nt value s hn h0 hr hasset hs
    exact ⟨c.operator_eq value, by simp [hc, bind, Except.bind, pure, Except.pure]⟩
  · exact ⟨false, by simp [pure, Except.pure]⟩

end XRPL.Model.Protocol

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault (Vault)

/-- A broker transaction that fails the model passed its preflight on a vault that exists, and its broker
operation failed. -/
lemma LendingLedger.applyBroker_of_error {l : LendingLedger} {tx : LendingTx} {e : Error} (hb : tx.isBroker = true)
    (h : (l.apply tx).run = .error e) :
    tx.preflight l = .tesSUCCESS ∧ l.vaultDeleted = false ∧ (l.applyBroker tx).run = .error e := by
  obtain ⟨hpre, ha⟩ := LendingLedger.apply_error h
  cases tx <;> simp only [LendingTx.isBroker, Bool.false_eq_true] at hb <;>
  · simp only [LendingLedger.applyChecked, LendingTx.isVault, LendingTx.isBroker, Bool.false_eq_true,
      ↓reduceIte] at ha
    split at ha
    · cases ha
    · exact ⟨hpre, by simpa using ‹¬ l.vaultDeleted = true›, TerExcept.map_error ha⟩

/-- The LoanBrokerSet checks of a new broker never throw. -/
lemma LoanBroker.canCreate_ok_of_asset (v : Vault) (dm : Option Number) (hasset : Vault.HoldsAsset v)
    (hdm : ∀ d ∈ dm, d.isNormalized ∧ 0 ≤ d.toRat) :
    ∃ ter, LoanBroker.canCreate v dm v.numericType = .ok ter := by
  have hbase := v.baseExponent_bounds
  unfold LoanBroker.canCreate
  simp only [bind, Except.bind, pure, Except.pure]
  split
  · exact ⟨_, rfl⟩
  cases dm with
  | none => exact ⟨_, rfl⟩
  | some d =>
    obtain ⟨hdn, hd0⟩ := hdm d rfl
    obtain ⟨b, hb⟩ := Number.isOnExponentGrid_ok_of_asset d v.baseExponent v.numericType hdn hd0 hasset
      ⟨by omega, hbase.2.1⟩
    simp only [show AssetPool.baseExponent v = v.baseExponent from rfl, hb]
    split_ifs <;> exact ⟨_, rfl⟩

/-- The LoanBrokerSet checks of an update never throw. -/
lemma LoanBroker.canUpdate_ok_of_asset (lb : LoanBroker) (v : Vault) (dm : Option Number)
    (hasset : Vault.HoldsAsset v) (hnt : lb.numericType = v.numericType)
    (hdm : ∀ d ∈ dm, d.isNormalized ∧ 0 ≤ d.toRat) : ∃ ter, lb.canUpdate v dm = .ok ter := by
  have hbase := v.baseExponent_bounds
  unfold LoanBroker.canUpdate
  simp only [bind, Except.bind, pure, Except.pure]
  cases dm with
  | none => exact ⟨_, rfl⟩
  | some d =>
    obtain ⟨hdn, hd0⟩ := hdm d rfl
    obtain ⟨b, hb⟩ := Number.isOnExponentGrid_ok_of_asset d v.baseExponent lb.numericType hdn hd0
      (by rw [hnt]; exact hasset) ⟨by omega, hbase.2.1⟩
    simp only [show AssetPool.baseExponent v = v.baseExponent from rfl, hb]
    split_ifs <;> exact ⟨_, rfl⟩

/-- A new DebtMaximum that passed the preflight is normalized and at least zero. -/
private lemma isNonnegativeInput_facts {d : Number} (h : isNonnegativeInput d = true) :
    d.isNormalized ∧ 0 ≤ d.toRat := by
  unfold isNonnegativeInput at h
  rw [Bool.and_eq_true, decide_eq_true_eq] at h
  refine ⟨h.1, ?_⟩
  have := (Number.operator_le_iff _ _ Number.zero_isNormalized h.1).mp h.2
  rwa [Number.toRat_zero] at this

/-- Proof body of the LoanBrokerSet create line: on a reachable ledger it returns a result code. -/
lemma LendingLedger.loanBrokerCreate_no_exception_proof (l : LendingLedger) (hr : l.Reachable)
    (tx : LoanBrokerSetCreate) : ∃ r, (l.apply (.loanBrokerCreate tx)).run = .ok r := by
  cases hrun : (l.apply (.loanBrokerCreate tx)).run with
  | ok r => exact ⟨r, rfl⟩
  | error e =>
    exfalso
    obtain ⟨hpre, -, hb⟩ := LendingLedger.applyBroker_of_error rfl hrun
    have hdm : ∀ d ∈ tx.debtMaximum, d.isNormalized ∧ 0 ≤ d.toRat := by
      intro d hd
      rw [Option.mem_def] at hd
      have hok : (isNonnegativeInput d && d.operator_le debtMaximumCap) = true := by
        by_contra hne
        simp only [Bool.not_eq_true] at hne
        simp [LendingTx.preflight, hd, hne] at hpre
      rw [Bool.and_eq_true] at hok
      exact isNonnegativeInput_facts hok.1
    simp only [LendingLedger.applyBroker] at hb
    unfold_ter at hb
    walk_ok'
    · obtain ⟨ter, hter⟩ := LoanBroker.canCreate_ok_of_asset l.vault tx.debtMaximum hr.holdsAsset hdm
      have hc := ‹LoanBroker.canCreate l.vault tx.debtMaximum l.vault.numericType = .error e›
      rw [hter] at hc
      cases hc
    · obtain ⟨b, hb'⟩ := LoanBroker.create_ok_of_preflight l tx l.vault.numericType hpre
      have hc := ‹LoanBroker.create tx l.vault.numericType = .error e›
      rw [hb'] at hc
      cases hc

/-- Proof body of the LoanBrokerSet update line: on a reachable ledger it returns a result code. -/
lemma LendingLedger.loanBrokerUpdate_no_exception_proof (l : LendingLedger) (hr : l.Reachable) (i : Nat)
    (debtMaximum : Option Number) : ∃ r, (l.apply (.loanBrokerUpdate i debtMaximum)).run = .ok r := by
  cases hrun : (l.apply (.loanBrokerUpdate i debtMaximum)).run with
  | ok r => exact ⟨r, rfl⟩
  | error e =>
    exfalso
    obtain ⟨hpre, -, hb⟩ := LendingLedger.applyBroker_of_error rfl hrun
    have hdm : ∀ d ∈ debtMaximum, d.isNormalized ∧ 0 ≤ d.toRat := by
      intro d hd
      rw [Option.mem_def] at hd
      subst hd
      have hok : (isNonnegativeInput d && d.operator_le debtMaximumCap) = true := by
        by_contra hne
        simp only [Bool.not_eq_true] at hne
        simp [LendingTx.preflight, hne] at hpre
      rw [Bool.and_eq_true] at hok
      exact isNonnegativeInput_facts hok.1
    simp only [LendingLedger.applyBroker] at hb
    unfold_ter at hb
    walk_ok'
    · have hc := ‹LoanBroker.canUpdate _ l.vault debtMaximum = .error e›
      have hbr := ‹l.broker? i = some _›
      obtain ⟨ter, hter⟩ := LoanBroker.canUpdate_ok_of_asset _ l.vault debtMaximum hr.holdsAsset
        (hr.scaleInv.brokers i _ hbr) hdm
      rw [hter] at hc
      cases hc
    · have hcan := ‹LoanBroker.canUpdate _ l.vault debtMaximum = .ok _›
      have hter := ‹¬ (!(_ : TER).isTesSuccess) = true›
      have hup := ‹LoanBroker.update _ debtMaximum = .error e›
      simp only [Bool.not_eq_true', Bool.not_eq_false] at hter
      rw [(TER.isTesSuccess_iff _).mp hter] at hcan
      obtain ⟨b', hb'⟩ := LoanBroker.update_ok_of_checks l i _ l.vault debtMaximum hpre hcan
      rw [hb'] at hup
      cases hup

/-- A broker with loans or debt left is rejected, and one without either passes: the delete checks never throw. -/
lemma LoanBroker.canDelete_ok (lb : LoanBroker) (v : Vault) : ∃ ter, lb.canDelete v = .ok ter := by
  unfold LoanBroker.canDelete
  simp only [bind, Except.bind, pure, Except.pure]
  by_cases h0 : lb.loanCount = 0
  · have hd := lb.valid.empty_broker h0
    rw [h0, show lb.debtTotal = Number.zero from hd]
    exact ⟨_, rfl⟩
  · rw [if_pos (by simpa using h0)]
    exact ⟨_, rfl⟩

/-- Proof body of the LoanBrokerDelete line: on a reachable ledger it returns a result code while CoverAvailable is
within the asset's maximum. -/
lemma LendingLedger.loanBrokerDelete_no_exception_proof (l : LendingLedger) (hr : l.Reachable) (i : Nat)
    (hcover : ∀ b, l.broker? i = some b → b.coverAvailable.toRat ≤ l.vault.numericType.maxAmount) :
    ∃ r, (l.apply (.loanBrokerDelete i)).run = .ok r := by
  cases hrun : (l.apply (.loanBrokerDelete i)).run with
  | ok r => exact ⟨r, rfl⟩
  | error e =>
    exfalso
    obtain ⟨-, -, hb⟩ := LendingLedger.applyBroker_of_error rfl hrun
    simp only [LendingLedger.applyBroker] at hb
    unfold_ter at hb
    walk_ok'
    · have hc := ‹LoanBroker.canDelete _ l.vault = .error e›
      obtain ⟨ter, hter⟩ := LoanBroker.canDelete_ok _ l.vault
      rw [hter] at hc
      cases hc
    · have hc' := ‹LoanBroker.roundedCoverAvailable _ = .error e›
      have hbr := ‹l.broker? i = some _›
      obtain ⟨c, hc⟩ := hr.roundedCoverAvailable_ok hbr (hcover _ hbr)
      rw [hc] at hc'
      cases hc'

end XRPL.Model.Lending
