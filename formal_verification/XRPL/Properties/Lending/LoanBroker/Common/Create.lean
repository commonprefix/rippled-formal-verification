import XRPL.Properties.Lending.LoanBroker.Common.GuardProofs

/-! # Proof bodies for `LoanBroker.create` and `LoanBroker.update`

Both build a raw broker and re-check it with `to_lawful`. `update_eq` exposes the
raw broker `update` checks. `LoanBrokerSet.lean` and `LoanBrokerSetReturn.lean`
state the theorems and delegate here. -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol

/-- **Proof body of `create_debtMaximum_out_of_range`.** -/
lemma LoanBroker.create_debtMaximum_out_of_range_proof (tx : LoanBrokerSetCreate)
    (nt : NumericType) (dm : Number) (hdm : tx.debtMaximum = some dm)
    (hbad : ¬ dm.isNormalized ∨ Number.zero.operator_le dm = false ∨
      dm.operator_le debtMaximumCap = false) :
    LoanBroker.create tx nt = .error .notLawful := by
  unfold LoanBroker.create
  apply RawLoanBroker.to_lawful_not_lawful
  rintro ⟨hwf, hv⟩
  have hraw : (LoanBroker.createRaw tx nt).debtMaximum = dm := by
    simp [LoanBroker.createRaw, hdm]
  rcases hbad with hn | hneg | hcap
  · exact hn (hraw ▸ hwf.debtMaximum_norm)
  · have h1 : Number.zero.operator_le dm = true := hraw ▸ hv.debtMaximum_nonneg
    simp [h1] at hneg
  · have h1 : dm.operator_le debtMaximumCap = true := hraw ▸ hv.debtMaximum_cap
    simp [h1] at hcap

/-- **Proof body of `create_rate_above_maximum`.** -/
lemma LoanBroker.create_rate_above_maximum_proof (tx : LoanBrokerSetCreate) (nt : NumericType)
    (hbad : maxManagementFeeRate < tx.managementFeeRate.getD 0 ∨
      maxCoverRate < tx.coverRateMinimum.getD 0 ∨ maxCoverRate < tx.coverRateLiquidation.getD 0) :
    LoanBroker.create tx nt = .error .notLawful := by
  unfold LoanBroker.create
  apply RawLoanBroker.to_lawful_not_lawful
  rintro ⟨_, hv⟩
  rcases hbad with h | h | h
  · exact UInt16.not_le.mpr h hv.managementFeeRate_cap
  · exact UInt32.not_le.mpr h hv.coverRateMinimum_cap
  · exact UInt32.not_le.mpr h hv.coverRateLiquidation_cap

/-- **Proof body of `create_cover_rates_uncoupled`.** -/
lemma LoanBroker.create_cover_rates_uncoupled_proof (tx : LoanBrokerSetCreate)
    (nt : NumericType)
    (hbad : ¬ (tx.coverRateMinimum.getD 0 = 0 ↔ tx.coverRateLiquidation.getD 0 = 0)) :
    LoanBroker.create tx nt = .error .notLawful := by
  unfold LoanBroker.create
  apply RawLoanBroker.to_lawful_not_lawful
  rintro ⟨_, hv⟩
  exact hbad hv.coverRates_coupled

/-- **Proof body of `create_success`.** -/
lemma LoanBroker.create_success_proof (tx : LoanBrokerSetCreate) (nt : NumericType)
    (hdm : ∀ dm ∈ tx.debtMaximum, dm.isNormalized ∧ 0 ≤ dm.toRat ∧ dm.toRat ≤ (2 : ℚ) ^ 63 - 1)
    (hfee : tx.managementFeeRate.getD 0 ≤ maxManagementFeeRate)
    (hmin : tx.coverRateMinimum.getD 0 ≤ maxCoverRate)
    (hliq : tx.coverRateLiquidation.getD 0 ≤ maxCoverRate)
    (hcoupled : tx.coverRateMinimum.getD 0 = 0 ↔ tx.coverRateLiquidation.getD 0 = 0) :
    ∃ lb, LoanBroker.create tx nt = .ok lb ∧
      lb.toRawLoanBroker = LoanBroker.createRaw tx nt := by
  -- the stored maximum is the requested one, or zero when none was requested
  have hdm' : (tx.debtMaximum.getD Number.zero).isNormalized ∧
      0 ≤ (tx.debtMaximum.getD Number.zero).toRat ∧
      (tx.debtMaximum.getD Number.zero).toRat ≤ (2 : ℚ) ^ 63 - 1 := by
    cases h : tx.debtMaximum with
    | none =>
      simp only [Option.getD_none, Number.toRat_zero]
      exact ⟨Number.zero_isNormalized, le_refl _, by norm_num⟩
    | some dm => simpa using hdm dm h
  have hwf : (LoanBroker.createRaw tx nt).WF :=
    ⟨Number.zero_isNormalized, hdm'.1, Number.zero_isNormalized⟩
  have he : (LoanBroker.createRaw tx nt).toExact.Valid := by
    refine
      { debtTotal_nonneg := ?_
        coverAvailable_nonneg := ?_
        debt_within_cap := ?_
        empty_broker := ?_
        debtMaximum_nonneg := hdm'.2.1
        debtMaximum_cap := hdm'.2.2
        managementFeeRate_cap := UInt16.le_iff_toNat_le.mp hfee
        coverRateMinimum_cap := UInt32.le_iff_toNat_le.mp hmin
        coverRateLiquidation_cap := UInt32.le_iff_toNat_le.mp hliq
        coverRates_coupled := ?_ }
    · show (0 : ℚ) ≤ Number.zero.toRat; rw [Number.toRat_zero]
    · show (0 : ℚ) ≤ Number.zero.toRat; rw [Number.toRat_zero]
    · intro _
      show Number.zero.toRat ≤ (tx.debtMaximum.getD Number.zero).toRat
      rw [Number.toRat_zero]; exact hdm'.2.1
    · intro _; show Number.zero.toRat = 0; exact Number.toRat_zero
    · show (tx.coverRateMinimum.getD 0).toNat = 0 ↔ (tx.coverRateLiquidation.getD 0).toNat = 0
      rw [UInt32.toNat_eq_zero_iff, UInt32.toNat_eq_zero_iff]; exact hcoupled
  have hv := (RawLoanBroker.valid_iff_exact _ hwf).mpr he
  unfold LoanBroker.create
  exact RawLoanBroker.to_lawful_ok_of hwf hv

/-- **Proof body of `create_no_exposure`.** -/
lemma LoanBroker.create_no_exposure_proof (tx : LoanBrokerSetCreate) (nt : NumericType)
    (lb : LoanBroker) (hok : LoanBroker.create tx nt = .ok lb) :
    lb.debtTotal = Number.zero ∧ lb.coverAvailable = Number.zero ∧ lb.loanCount = 0 := by
  unfold LoanBroker.create at hok
  have h := (RawLoanBroker.to_lawful_ok hok).1
  refine ⟨?_, ?_, ?_⟩
  · show lb.toRawLoanBroker.debtTotal = _; rw [h]; rfl
  · show lb.toRawLoanBroker.coverAvailable = _; rw [h]; rfl
  · show lb.toRawLoanBroker.loanCount = _; rw [h]; rfl

/-- `update` re-checks the broker with only `debtMaximum` replaced. -/
lemma LoanBroker.update_eq (lb : LoanBroker) (debtMaximum : Option Number) :
    lb.update debtMaximum =
      ({ lb.toRawLoanBroker with debtMaximum := debtMaximum.getD lb.debtMaximum } :
        RawLoanBroker).to_lawful := rfl

/-- **Proof body of `update_not_lawful`.** -/
lemma LoanBroker.update_not_lawful_proof (lb : LoanBroker) (dm : Number)
    (hbad : ¬ dm.isNormalized ∨ Number.zero.operator_le dm = false ∨
      dm.operator_le debtMaximumCap = false ∨
      (dm ≠ Number.zero ∧ lb.debtTotal.operator_le dm = false)) :
    lb.update (some dm) = .error .notLawful := by
  rw [LoanBroker.update_eq]
  apply RawLoanBroker.to_lawful_not_lawful
  rintro ⟨hwf, hv⟩
  rcases hbad with hn | hneg | hcap | ⟨hne, hlt⟩
  · exact hn hwf.debtMaximum_norm
  · have h1 : Number.zero.operator_le dm = true := hv.debtMaximum_nonneg
    simp [h1] at hneg
  · have h1 : dm.operator_le debtMaximumCap = true := hv.debtMaximum_cap
    simp [h1] at hcap
  · have h1 : lb.debtTotal.operator_le dm = true := hv.debt_within_cap hne
    simp [h1] at hlt

/-- **Proof body of `update_success`.** -/
lemma LoanBroker.update_success_proof (lb : LoanBroker) (dm : Number)
    (hnorm : dm.isNormalized) (hnn : 0 ≤ dm.toRat) (hcap : dm.toRat ≤ (2 : ℚ) ^ 63 - 1)
    (hdebt : dm.toRat = 0 ∨ lb.toExact.debtTotal ≤ dm.toRat) :
    ∃ lb', lb.update (some dm) = .ok lb' ∧
      lb'.toRawLoanBroker = { lb.toRawLoanBroker with debtMaximum := dm } := by
  have hwf : ({ lb.toRawLoanBroker with debtMaximum := dm } : RawLoanBroker).WF :=
    ⟨lb.wf.debtTotal_norm, hnorm, lb.wf.coverAvailable_norm⟩
  have hlb := lb.exact
  have he : ({ lb.toRawLoanBroker with debtMaximum := dm } : RawLoanBroker).toExact.Valid :=
    { debtTotal_nonneg := hlb.debtTotal_nonneg
      coverAvailable_nonneg := hlb.coverAvailable_nonneg
      debt_within_cap := fun hne => hdebt.resolve_left hne
      empty_broker := hlb.empty_broker
      debtMaximum_nonneg := hnn
      debtMaximum_cap := hcap
      managementFeeRate_cap := hlb.managementFeeRate_cap
      coverRateMinimum_cap := hlb.coverRateMinimum_cap
      coverRateLiquidation_cap := hlb.coverRateLiquidation_cap
      coverRates_coupled := hlb.coverRates_coupled }
  have hv := (RawLoanBroker.valid_iff_exact _ hwf).mpr he
  rw [LoanBroker.update_eq]
  exact RawLoanBroker.to_lawful_ok_of hwf hv

/-- **Proof body of `update_none`.** -/
lemma LoanBroker.update_none_proof (lb : LoanBroker) : lb.update none = .ok lb := by
  rw [LoanBroker.update_eq]
  unfold RawLoanBroker.to_lawful
  rw [dif_pos ⟨lb.wf, lb.valid⟩]
  rfl

end XRPL.Model.Lending
