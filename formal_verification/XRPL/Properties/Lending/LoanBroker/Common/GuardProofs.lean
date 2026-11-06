import XRPL.Model.Lending.LoanBroker.LoanBrokerSet
import XRPL.Model.Lending.LoanBroker.LoanBrokerDelete
import XRPL.Properties.Lending.Common.Reduction
import XRPL.Properties.Lending.LoanBroker.LoanBrokerValid
import XRPL.Properties.Protocol.Number.Signum.Signum
import XRPL.Properties.Protocol.Number.Compare.Compare
import XRPL.Properties.Protocol.STAmount.Common.Representable

/-! # Proof bodies for the LoanBroker guard theorems

Proofs for the `canCreate`, `canUpdate` and `canDelete` exits. -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol

variable {α : Type} [AssetPool α]

/-- The nonzero-and-below-debt guard of `canUpdate`, read in exact rationals. -/
private lemma canUpdate_guard_true_iff (lb : LoanBroker) (dm : Number) (hnorm : dm.isNormalized) :
    (dm.signum ≠ 0 ∧ dm.operator_lt lb.debtTotal = true) ↔
      dm.toRat ≠ 0 ∧ dm.toRat < lb.toExact.debtTotal := by
  rw [ne_eq, signum_eq_zero_iff dm hnorm,
    operator_lt_iff dm lb.debtTotal hnorm lb.wf.debtTotal_norm]
  rfl

/-- The same guard reads `false` exactly when `dm` is zero or not below the debt. -/
private lemma canUpdate_guard_false_iff (lb : LoanBroker) (dm : Number) (hnorm : dm.isNormalized) :
    (dm.signum != 0 && dm.operator_lt lb.debtTotal) = false ↔
      dm.toRat = 0 ∨ lb.toExact.debtTotal ≤ dm.toRat := by
  have h := canUpdate_guard_true_iff lb dm hnorm
  constructor
  · intro hf
    by_contra hc
    push Not at hc
    obtain ⟨hs, hl⟩ := h.mpr hc
    simp [hs, hl] at hf
  · intro hg
    cases hb : (dm.signum != 0 && dm.operator_lt lb.debtTotal)
    · rfl
    · rw [Bool.and_eq_true, bne_iff_ne] at hb
      obtain ⟨hne, hlt⟩ := h.mp hb
      rcases hg with h0 | hle
      · exact absurd h0 hne
      · exact absurd hle (not_le.mpr hlt)

/-- When that guard does not fire, `canUpdate` is the base-grid check. -/
private lemma canUpdate_guard_false (lb : LoanBroker) (pool : α) (dm : Number)
    (hguard : (dm.signum != 0 && dm.operator_lt lb.debtTotal) = false) :
    lb.canUpdate pool (some dm) = (do
      if !(← dm.isOnExponentGrid (AssetPool.baseExponent pool) lb.numericType) then
        return .tecPRECISION_LOSS
      return .tesSUCCESS) := by
  simp only [LoanBroker.canUpdate]
  rw [if_neg (by rw [hguard]; decide)]
  rfl

/-- On a closed-ended pool, `canCreate` is the base-grid check. -/
private lemma canCreate_closed (pool : α) (debtMaximum : Option Number) (nt : NumericType)
    (hclosed : AssetPool.redemptionDate pool ≠ none) :
    LoanBroker.canCreate pool debtMaximum nt = (match debtMaximum with
      | none => .ok .tesSUCCESS
      | some dm => do
        if !(← dm.isOnExponentGrid (AssetPool.baseExponent pool) nt) then
          return .tecPRECISION_LOSS
        return .tesSUCCESS) := by
  cases hr : AssetPool.redemptionDate pool with
  | none => exact absurd hr hclosed
  | some r => cases debtMaximum <;> simp [LoanBroker.canCreate, hr]

/-- Proof body of the no-permission exit of `LoanBroker.canCreate_exits`. -/
lemma LoanBroker.canCreate_no_permission_proof (pool : α) (debtMaximum : Option Number)
    (nt : NumericType) (hopen : AssetPool.redemptionDate pool = none) :
    LoanBroker.canCreate pool debtMaximum nt = .ok .tecNO_PERMISSION := by
  simp [LoanBroker.canCreate, hopen]

/-- Proof body of the precision-loss exit of `LoanBroker.canCreate_exits`. -/
lemma LoanBroker.canCreate_precision_loss_proof (pool : α) (dm : Number) (nt : NumericType)
    (hclosed : AssetPool.redemptionDate pool ≠ none)
    (hround : dm.isOnExponentGrid (AssetPool.baseExponent pool) nt = .ok false) :
    LoanBroker.canCreate pool (some dm) nt = .ok .tecPRECISION_LOSS := by
  rw [canCreate_closed pool _ nt hclosed]
  simp [hround]

/-- Proof body of the success exit of `LoanBroker.canCreate_exits`. -/
lemma LoanBroker.canCreate_success_proof (pool : α) (debtMaximum : Option Number) (nt : NumericType)
    (hclosed : AssetPool.redemptionDate pool ≠ none)
    (hgrid : ∀ dm ∈ debtMaximum, dm.isOnExponentGrid (AssetPool.baseExponent pool) nt = .ok true) :
    LoanBroker.canCreate pool debtMaximum nt = .ok .tesSUCCESS := by
  rw [canCreate_closed pool _ nt hclosed]
  cases debtMaximum with
  | none => rfl
  | some dm => simp [hgrid dm rfl]

/-- Proof body of `canCreate_error_codes`. -/
lemma LoanBroker.canCreate_error_codes_proof (pool : α) (debtMaximum : Option Number)
    (nt : NumericType) (ter : TER) (hok : LoanBroker.canCreate pool debtMaximum nt = .ok ter) :
    ter = .tesSUCCESS ∨ ter = .tecNO_PERMISSION ∨ ter = .tecPRECISION_LOSS := by
  cases hr : AssetPool.redemptionDate pool with
  | none =>
    rw [LoanBroker.canCreate_no_permission_proof pool debtMaximum nt hr] at hok
    exact Or.inr (Or.inl (by simpa using hok.symm))
  | some r =>
    rw [canCreate_closed pool _ nt (by simp [hr])] at hok
    cases debtMaximum with
    | none => exact Or.inl (by simpa using hok.symm)
    | some dm =>
      cases h : dm.isOnExponentGrid (AssetPool.baseExponent pool) nt with
      | error e => simp [h] at hok
      | ok b =>
        cases b
        · exact Or.inr (Or.inr (by simpa [h] using hok.symm))
        · exact Or.inl (by simpa [h] using hok.symm)

/-- A DebtMaximum that passed `canCreate` is on the pool's base grid. -/
lemma LoanBroker.canCreate_grid (pool : α) (dm : Number) (nt : NumericType)
    (hcan : LoanBroker.canCreate pool (some dm) nt = .ok .tesSUCCESS) :
    dm.isOnExponentGrid (AssetPool.baseExponent pool) nt = .ok true := by
  cases hr : AssetPool.redemptionDate pool with
  | none => rw [LoanBroker.canCreate_no_permission_proof pool _ nt hr] at hcan; simp at hcan
  | some r =>
    rw [canCreate_closed pool _ nt (by simp [hr])] at hcan
    cases h : dm.isOnExponentGrid (AssetPool.baseExponent pool) nt with
    | error e => simp [h] at hcan
    | ok b => cases b <;> simp_all

/-- Proof body of the rounding line of `LoanBroker.create_success`. -/
lemma LoanBroker.canCreate_debtMaximum_not_rounded_proof (pool : α) (dm : Number) (nt : NumericType)
    (hcan : LoanBroker.canCreate pool (some dm) nt = .ok .tesSUCCESS) :
    STAmount.isRounded nt dm = false :=
  Number.isRounded_eq_false_of_isOnExponentGrid dm _ nt (LoanBroker.canCreate_grid pool dm nt hcan)

/-- Proof body of the limit exit of `LoanBroker.canUpdate_exits`. -/
lemma LoanBroker.canUpdate_limit_exceeded_proof (lb : LoanBroker) (pool : α) (dm : Number)
    (hne : dm.signum ≠ 0) (hlt : dm.operator_lt lb.debtTotal = true) :
    lb.canUpdate pool (some dm) = .ok .tecLIMIT_EXCEEDED := by
  simp [LoanBroker.canUpdate, hne, hlt]

/-- Proof body of the precision-loss exit of `LoanBroker.canUpdate_exits`. -/
lemma LoanBroker.canUpdate_precision_loss_proof (lb : LoanBroker) (pool : α) (dm : Number)
    (hguard : (dm.signum != 0 && dm.operator_lt lb.debtTotal) = false)
    (hround : dm.isOnExponentGrid (AssetPool.baseExponent pool) lb.numericType = .ok false) :
    lb.canUpdate pool (some dm) = .ok .tecPRECISION_LOSS := by
  rw [canUpdate_guard_false lb pool dm hguard, hround, ok_bind]
  rfl

/-- Proof body of the success exit of `LoanBroker.canUpdate_exits`. -/
lemma LoanBroker.canUpdate_success_proof (lb : LoanBroker) (pool : α) (debtMaximum : Option Number)
    (hok : ∀ dm ∈ debtMaximum, (dm.signum != 0 && dm.operator_lt lb.debtTotal) = false ∧
      dm.isOnExponentGrid (AssetPool.baseExponent pool) lb.numericType = .ok true) :
    lb.canUpdate pool debtMaximum = .ok .tesSUCCESS := by
  cases debtMaximum with
  | none => rfl
  | some dm =>
    obtain ⟨hguard, hgrid⟩ := hok dm rfl
    rw [canUpdate_guard_false lb pool dm hguard, hgrid, ok_bind]
    rfl

/-- Proof body of `canUpdate_error_codes`. -/
lemma LoanBroker.canUpdate_error_codes_proof (lb : LoanBroker) (pool : α) (debtMaximum : Option Number)
    (ter : TER) (hok : lb.canUpdate pool debtMaximum = .ok ter) :
    ter = .tesSUCCESS ∨ ter = .tecLIMIT_EXCEEDED ∨ ter = .tecPRECISION_LOSS := by
  cases debtMaximum with
  | none => simp [LoanBroker.canUpdate] at hok; exact Or.inl hok.symm
  | some dm =>
    simp only [LoanBroker.canUpdate] at hok
    split_ifs at hok
    · simp at hok; exact Or.inr (Or.inl hok.symm)
    · cases h : dm.isOnExponentGrid (AssetPool.baseExponent pool) lb.numericType with
      | error e => rw [h, err_bind] at hok; exact absurd hok (by simp)
      | ok b =>
        rw [h, ok_bind] at hok
        cases b
        · exact Or.inr (Or.inr (by simpa using hok.symm))
        · exact Or.inl (by simpa using hok.symm)

/-- A DebtMaximum that passed `canUpdate` is on the pool's base grid. -/
lemma LoanBroker.canUpdate_grid (lb : LoanBroker) (pool : α) (dm : Number)
    (hcan : lb.canUpdate pool (some dm) = .ok .tesSUCCESS) :
    dm.isOnExponentGrid (AssetPool.baseExponent pool) lb.numericType = .ok true := by
  simp only [LoanBroker.canUpdate] at hcan
  split_ifs at hcan
  · simp at hcan
  · cases h : dm.isOnExponentGrid (AssetPool.baseExponent pool) lb.numericType with
    | error e => rw [h, err_bind] at hcan; exact absurd hcan (by simp)
    | ok b =>
      rw [h, ok_bind] at hcan
      cases b
      · simp at hcan
      · rfl

/-- Proof body of the rounding line of `LoanBroker.update_success`. -/
lemma LoanBroker.canUpdate_debtMaximum_not_rounded_proof (lb : LoanBroker) (pool : α) (dm : Number)
    (hcan : lb.canUpdate pool (some dm) = .ok .tesSUCCESS) :
    STAmount.isRounded lb.numericType dm = false :=
  Number.isRounded_eq_false_of_isOnExponentGrid dm _ _ (LoanBroker.canUpdate_grid lb pool dm hcan)

/-- Proof body of `canUpdate_lawful_iff`. -/
lemma LoanBroker.canUpdate_lawful_iff_proof (lb : LoanBroker) (pool : α) (dm : Number)
    (hnorm : dm.isNormalized) :
    lb.canUpdate pool (some dm) = .ok .tesSUCCESS ↔
      (dm.toRat = 0 ∨ lb.toExact.debtTotal ≤ dm.toRat) ∧
        dm.isOnExponentGrid (AssetPool.baseExponent pool) lb.numericType = .ok true := by
  constructor
  · intro hok
    have hguard : (dm.signum != 0 && dm.operator_lt lb.debtTotal) = false := by
      cases hb : (dm.signum != 0 && dm.operator_lt lb.debtTotal)
      · rfl
      · rw [Bool.and_eq_true, bne_iff_ne] at hb
        rw [LoanBroker.canUpdate_limit_exceeded_proof lb pool dm hb.1 hb.2] at hok
        simp at hok
    exact ⟨(canUpdate_guard_false_iff lb dm hnorm).mp hguard, LoanBroker.canUpdate_grid lb pool dm hok⟩
  · rintro ⟨hg, hgrid⟩
    exact LoanBroker.canUpdate_success_proof lb pool (some dm)
      (fun d hd => by cases hd; exact ⟨(canUpdate_guard_false_iff lb dm hnorm).mpr hg, hgrid⟩)

/-- Proof body of the has-loans exit of `LoanBroker.canDelete_exits`. -/
lemma LoanBroker.canDelete_has_loans_proof (lb : LoanBroker) (pool : α)
    (hloans : lb.loanCount ≠ 0) : lb.canDelete pool = .ok .tecHAS_OBLIGATIONS := by
  simp [LoanBroker.canDelete, hloans]

/-- Proof body of the has-debt exit of `LoanBroker.canDelete_exits`. -/
lemma LoanBroker.canDelete_has_debt_proof (lb : LoanBroker) (pool : α)
    (hdebt : lb.debtTotal.signum ≠ 0) : lb.canDelete pool = .ok .tecHAS_OBLIGATIONS := by
  -- on a lawful broker no loans means no debt
  refine LoanBroker.canDelete_has_loans_proof lb pool fun hloans => hdebt ?_
  rw [lb.valid.empty_broker hloans]
  decide

/-- Proof body of the success exit of `LoanBroker.canDelete_exits`. -/
lemma LoanBroker.canDelete_success_proof (lb : LoanBroker) (pool : α)
    (hloans : lb.loanCount = 0) : lb.canDelete pool = .ok .tesSUCCESS := by
  have hd : lb.debtTotal = Number.zero := lb.valid.empty_broker hloans
  simp [LoanBroker.canDelete, hloans, hd, Number.signum, Number.zero]

/-- Proof body of `canDelete_error_codes`. -/
lemma LoanBroker.canDelete_error_codes_proof (lb : LoanBroker) (pool : α) (ter : TER)
    (hok : lb.canDelete pool = .ok ter) : ter = .tesSUCCESS ∨ ter = .tecHAS_OBLIGATIONS := by
  unfold LoanBroker.canDelete at hok
  simp only [pure_eq, ok_bind] at hok
  split_ifs at hok
  · exact Or.inr (by simpa using hok.symm)
  · cases hexp : AssetPool.exponent pool lb.numericType with
    | error e => rw [hexp, err_bind] at hok; exact absurd hok (by simp)
    | ok e =>
      rw [hexp, ok_bind] at hok
      cases hr : STAmount.roundToNumericType lb.numericType lb.debtTotal .towards_zero (some e) with
      | error e => rw [hr, err_bind] at hok; exact absurd hok (by simp)
      | ok r =>
        rw [hr, ok_bind] at hok
        by_cases hz : (r.signum != 0) = true
        · exact Or.inr (by simpa [hz] using hok.symm)
        · exact Or.inl (by simpa [hz] using hok.symm)
  · exact Or.inl (by simpa using hok.symm)

/-- Proof body of `canDelete_lawful_iff`. -/
lemma LoanBroker.canDelete_lawful_iff_proof (lb : LoanBroker) (pool : α) :
    lb.canDelete pool = .ok .tesSUCCESS ↔ lb.loanCount = 0 := by
  constructor
  · intro h
    by_contra hloans
    rw [LoanBroker.canDelete_has_loans_proof lb pool hloans] at h
    exact absurd h (by simp)
  · exact LoanBroker.canDelete_success_proof lb pool

end XRPL.Model.Lending
