import XRPL.Model.Lending.LoanBroker.LoanBrokerSet
import XRPL.Model.Lending.LoanBroker.LoanBrokerDelete
import XRPL.Properties.Lending.Common.Reduction
import XRPL.Properties.Lending.LoanBroker.LoanBrokerValid
import XRPL.Properties.Protocol.Number.Signum.Signum
import XRPL.Properties.Protocol.Number.Compare.Compare

/-! # Proof bodies for the LoanBroker guard theorems

The `canCreate`, `canUpdate` and `canDelete` exits. `LoanBrokerSetReturn.lean`
and `LoanBrokerDeleteReturn.lean` state them and delegate here. -/

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

/-- When that guard does not fire, `canUpdate` is the precision check. -/
private lemma canUpdate_guard_false (lb : LoanBroker) (dm : Number)
    (hguard : (dm.signum != 0 && dm.operator_lt lb.debtTotal) = false) :
    lb.canUpdate (some dm) = (do
      if !(← STAmount.equalAfterNumberConvert lb.numericType dm) then
        return .tecPRECISION_LOSS
      return .tesSUCCESS) := by
  simp only [LoanBroker.canUpdate]
  rw [if_neg (by rw [hguard]; decide)]
  rfl

/-- **Proof body of `canCreate_precision_loss`.** -/
lemma LoanBroker.canCreate_precision_loss_proof (dm : Number) (nt : NumericType)
    (hround : STAmount.equalAfterNumberConvert nt dm = .ok false) :
    LoanBroker.canCreate (some dm) nt = .ok .tecPRECISION_LOSS := by
  simp [LoanBroker.canCreate, hround]

/-- **Proof body of `canCreate_success`.** -/
lemma LoanBroker.canCreate_success_proof (debtMaximum : Option Number) (nt : NumericType)
    (hexact : ∀ dm ∈ debtMaximum, STAmount.equalAfterNumberConvert nt dm = .ok true) :
    LoanBroker.canCreate debtMaximum nt = .ok .tesSUCCESS := by
  cases debtMaximum with
  | none => rfl
  | some dm => simp [LoanBroker.canCreate, hexact dm rfl]

/-- **Proof body of `canCreate_error_codes`.** -/
lemma LoanBroker.canCreate_error_codes_proof (debtMaximum : Option Number) (nt : NumericType)
    (ter : TER) (hok : LoanBroker.canCreate debtMaximum nt = .ok ter) :
    ter = .tesSUCCESS ∨ ter = .tecPRECISION_LOSS := by
  cases debtMaximum with
  | none => simp [LoanBroker.canCreate] at hok; exact Or.inl hok.symm
  | some dm =>
    simp only [LoanBroker.canCreate] at hok
    cases h : STAmount.equalAfterNumberConvert nt dm with
    | error e => rw [h, err_bind] at hok; exact absurd hok (by simp)
    | ok b =>
      rw [h, ok_bind] at hok
      cases b
      · exact Or.inr (by simpa using hok.symm)
      · exact Or.inl (by simpa using hok.symm)

/-- **Proof body of `canCreate_debtMaximum_not_rounded`.** -/
lemma LoanBroker.canCreate_debtMaximum_not_rounded_proof (dm : Number) (nt : NumericType)
    (hcan : LoanBroker.canCreate (some dm) nt = .ok .tesSUCCESS) :
    STAmount.isRounded nt dm = false := by
  simp only [LoanBroker.canCreate] at hcan
  unfold STAmount.isRounded
  cases h : STAmount.equalAfterNumberConvert nt dm with
  | error e => rw [h, err_bind] at hcan; exact absurd hcan (by simp)
  | ok b =>
    rw [h, ok_bind] at hcan
    cases b
    · simp at hcan
    · simp

/-- **Proof body of `canUpdate_limit_exceeded`.** -/
lemma LoanBroker.canUpdate_limit_exceeded_proof (lb : LoanBroker) (dm : Number)
    (hne : dm.signum ≠ 0) (hlt : dm.operator_lt lb.debtTotal = true) :
    lb.canUpdate (some dm) = .ok .tecLIMIT_EXCEEDED := by
  simp [LoanBroker.canUpdate, hne, hlt]

/-- **Proof body of `canUpdate_precision_loss`.** -/
lemma LoanBroker.canUpdate_precision_loss_proof (lb : LoanBroker) (dm : Number)
    (hguard : (dm.signum != 0 && dm.operator_lt lb.debtTotal) = false)
    (hround : STAmount.equalAfterNumberConvert lb.numericType dm = .ok false) :
    lb.canUpdate (some dm) = .ok .tecPRECISION_LOSS := by
  rw [canUpdate_guard_false lb dm hguard, hround, ok_bind]
  rfl

/-- **Proof body of `canUpdate_success`.** -/
lemma LoanBroker.canUpdate_success_proof (lb : LoanBroker) (debtMaximum : Option Number)
    (hok : ∀ dm ∈ debtMaximum, (dm.signum != 0 && dm.operator_lt lb.debtTotal) = false ∧
      STAmount.equalAfterNumberConvert lb.numericType dm = .ok true) :
    lb.canUpdate debtMaximum = .ok .tesSUCCESS := by
  cases debtMaximum with
  | none => rfl
  | some dm =>
    obtain ⟨hguard, hexact⟩ := hok dm rfl
    rw [canUpdate_guard_false lb dm hguard, hexact, ok_bind]
    rfl

/-- **Proof body of `canUpdate_error_codes`.** -/
lemma LoanBroker.canUpdate_error_codes_proof (lb : LoanBroker) (debtMaximum : Option Number)
    (ter : TER) (hok : lb.canUpdate debtMaximum = .ok ter) :
    ter = .tesSUCCESS ∨ ter = .tecLIMIT_EXCEEDED ∨ ter = .tecPRECISION_LOSS := by
  cases debtMaximum with
  | none => simp [LoanBroker.canUpdate] at hok; exact Or.inl hok.symm
  | some dm =>
    simp only [LoanBroker.canUpdate] at hok
    split_ifs at hok
    · simp at hok; exact Or.inr (Or.inl hok.symm)
    · cases h : STAmount.equalAfterNumberConvert lb.numericType dm with
      | error e => rw [h, err_bind] at hok; exact absurd hok (by simp)
      | ok b =>
        rw [h, ok_bind] at hok
        cases b
        · exact Or.inr (Or.inr (by simpa using hok.symm))
        · exact Or.inl (by simpa using hok.symm)

/-- **Proof body of `canUpdate_debtMaximum_not_rounded`.** -/
lemma LoanBroker.canUpdate_debtMaximum_not_rounded_proof (lb : LoanBroker) (dm : Number)
    (hcan : lb.canUpdate (some dm) = .ok .tesSUCCESS) :
    STAmount.isRounded lb.numericType dm = false := by
  simp only [LoanBroker.canUpdate] at hcan
  split_ifs at hcan
  · simp at hcan
  · unfold STAmount.isRounded
    cases h : STAmount.equalAfterNumberConvert lb.numericType dm with
    | error e => rw [h, err_bind] at hcan; exact absurd hcan (by simp)
    | ok b =>
      rw [h, ok_bind] at hcan
      cases b
      · simp at hcan
      · simp

/-- **Proof body of `lawful_canUpdate_iff`.** -/
lemma LoanBroker.lawful_canUpdate_iff_proof (lb : LoanBroker) (dm : Number)
    (hnorm : dm.isNormalized) :
    lb.canUpdate (some dm) = .ok .tesSUCCESS ↔
      (dm.toRat = 0 ∨ lb.toExact.debtTotal ≤ dm.toRat) ∧
        STAmount.equalAfterNumberConvert lb.numericType dm = .ok true := by
  constructor
  · intro hok
    have hguard : (dm.signum != 0 && dm.operator_lt lb.debtTotal) = false := by
      cases hb : (dm.signum != 0 && dm.operator_lt lb.debtTotal)
      · rfl
      · rw [Bool.and_eq_true, bne_iff_ne] at hb
        rw [LoanBroker.canUpdate_limit_exceeded_proof lb dm hb.1 hb.2] at hok
        simp at hok
    refine ⟨(canUpdate_guard_false_iff lb dm hnorm).mp hguard, ?_⟩
    cases hc : STAmount.equalAfterNumberConvert lb.numericType dm with
    | error e =>
      rw [canUpdate_guard_false lb dm hguard, hc, err_bind] at hok
      simp at hok
    | ok b =>
      cases b
      · rw [LoanBroker.canUpdate_precision_loss_proof lb dm hguard hc] at hok
        simp at hok
      · rfl
  · rintro ⟨hg, hexact⟩
    exact LoanBroker.canUpdate_success_proof lb (some dm)
      (fun d hd => by cases hd; exact ⟨(canUpdate_guard_false_iff lb dm hnorm).mpr hg, hexact⟩)

/-- **Proof body of `canDelete_has_loans`.** -/
lemma LoanBroker.canDelete_has_loans_proof (lb : LoanBroker) (pool : α)
    (hloans : lb.loanCount ≠ 0) : lb.canDelete pool = .ok .tecHAS_OBLIGATIONS := by
  simp [LoanBroker.canDelete, hloans]

/-- **Proof body of `canDelete_has_debt`.** -/
lemma LoanBroker.canDelete_has_debt_proof (lb : LoanBroker) (pool : α)
    (hdebt : lb.debtTotal.signum ≠ 0) : lb.canDelete pool = .ok .tecHAS_OBLIGATIONS := by
  -- on a lawful broker no loans means no debt
  refine LoanBroker.canDelete_has_loans_proof lb pool fun hloans => hdebt ?_
  rw [lb.valid.empty_broker hloans]
  decide

/-- **Proof body of `canDelete_success`.** -/
lemma LoanBroker.canDelete_success_proof (lb : LoanBroker) (pool : α)
    (hloans : lb.loanCount = 0) : lb.canDelete pool = .ok .tesSUCCESS := by
  have hd : lb.debtTotal = Number.zero := lb.valid.empty_broker hloans
  simp [LoanBroker.canDelete, hloans, hd, Number.signum, Number.zero]

/-- **Proof body of `canDelete_error_codes`.** -/
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

/-- **Proof body of `lawful_canDelete_iff`.** -/
lemma LoanBroker.lawful_canDelete_iff_proof (lb : LoanBroker) (pool : α) :
    lb.canDelete pool = .ok .tesSUCCESS ↔ lb.loanCount = 0 := by
  constructor
  · intro h
    by_contra hloans
    rw [LoanBroker.canDelete_has_loans_proof lb pool hloans] at h
    exact absurd h (by simp)
  · exact LoanBroker.canDelete_success_proof lb pool

end XRPL.Model.Lending
