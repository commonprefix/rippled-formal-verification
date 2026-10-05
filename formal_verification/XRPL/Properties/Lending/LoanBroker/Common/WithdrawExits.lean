import XRPL.Properties.Lending.LoanBroker.Common.CoverReduction

/-! # Proof bodies for the `LoanBrokerCoverWithdraw` exits

`LoanBrokerCoverWithdrawReturn.lean` states the exits and delegates here. -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.Result

variable {α : Type} [AssetPool α]

/-- **Proof body of `canCoverWithdraw_precision_loss`.** -/
lemma LoanBroker.canCoverWithdraw_precision_loss_proof (lb : LoanBroker) (pool : α)
    (amount rn : STAmount)
    (hz : amount.isZero = true ∨
      (roundToCoverScale lb.numericType lb.coverAvailable amount .to_nearest = .ok rn ∧
        rn.signum = 0)) :
    lb.canCoverWithdraw pool amount = .ok .tecPRECISION_LOSS := by
  by_cases hza : amount.isZero = true
  · simp [LoanBroker.canCoverWithdraw, canApplyToBrokerCover_zero _ _ _ hza, TER.operator_bool]
  · have hza' : amount.isZero = false := by simpa using hza
    obtain ⟨hnear, hrn⟩ := hz.resolve_left hza
    simp [LoanBroker.canCoverWithdraw, canApplyToBrokerCover_rounds_zero _ _ _ _ hza' hnear hrn,
      TER.operator_bool]

/-- **Proof body of `canCoverWithdraw_insufficient_cover`.** -/
lemma LoanBroker.canCoverWithdraw_insufficient_cover_proof (lb : LoanBroker) (pool : α)
    (amount : STAmount) (e : Int) (aN : Number)
    (hcheck : canApplyToBrokerCover lb.numericType lb.coverAvailable amount = .ok .tesSUCCESS)
    (hexp : AssetPool.exponent pool lb.numericType = .ok e)
    (hnum : amount.toNumber .to_nearest = .ok aN)
    (hlt : lb.coverAvailable.operator_lt aN = true) :
    lb.canCoverWithdraw pool amount = .ok .tecINSUFFICIENT_FUNDS := by
  simp [LoanBroker.canCoverWithdraw, hcheck, hexp, hnum, hlt, TER.operator_bool]

/-- **Proof body of `canCoverWithdraw_below_minimum`.** -/
lemma LoanBroker.canCoverWithdraw_below_minimum_proof (lb : LoanBroker) (pool : α)
    (amount : STAmount) (e : Int) (aN c' : Number)
    (hcheck : canApplyToBrokerCover lb.numericType lb.coverAvailable amount = .ok .tesSUCCESS)
    (hexp : AssetPool.exponent pool lb.numericType = .ok e)
    (hnum : amount.toNumber .to_nearest = .ok aN)
    (hge : lb.coverAvailable.operator_lt aN = false)
    (hsub : lb.coverAvailable.operator_sub aN .to_nearest = .ok c')
    (hmin : ({ lb.toRawLoanBroker with coverAvailable := c' } : RawLoanBroker).hasMinimumCover e =
      .ok false) :
    lb.canCoverWithdraw pool amount = .ok .tecINSUFFICIENT_FUNDS := by
  simp [LoanBroker.canCoverWithdraw, hcheck, hexp, hnum, hge, hsub, hmin, TER.operator_bool]

/-- **Proof body of `canCoverWithdraw_success`.** -/
lemma LoanBroker.canCoverWithdraw_success_proof (lb : LoanBroker) (pool : α)
    (amount : STAmount) (e : Int) (aN c' : Number)
    (hcheck : canApplyToBrokerCover lb.numericType lb.coverAvailable amount = .ok .tesSUCCESS)
    (hexp : AssetPool.exponent pool lb.numericType = .ok e)
    (hnum : amount.toNumber .to_nearest = .ok aN)
    (hge : lb.coverAvailable.operator_lt aN = false)
    (hsub : lb.coverAvailable.operator_sub aN .to_nearest = .ok c')
    (hmin : ({ lb.toRawLoanBroker with coverAvailable := c' } : RawLoanBroker).hasMinimumCover e =
      .ok true) :
    lb.canCoverWithdraw pool amount = .ok .tesSUCCESS := by
  simp [LoanBroker.canCoverWithdraw, hcheck, hexp, hnum, hge, hsub, hmin, TER.operator_bool]

/-- **Proof body of `canCoverWithdraw_error_codes`.** -/
lemma LoanBroker.canCoverWithdraw_error_codes_proof (lb : LoanBroker) (pool : α)
    (amount : STAmount) (ter : TER) (hok : lb.canCoverWithdraw pool amount = .ok ter) :
    ter = .tesSUCCESS ∨ ter = .tecPRECISION_LOSS ∨ ter = .tecINSUFFICIENT_FUNDS := by
  unfold LoanBroker.canCoverWithdraw at hok
  dsimp only at hok
  cases hc : canApplyToBrokerCover lb.numericType lb.coverAvailable amount with
  | error e => rw [hc, err_bind] at hok; exact absurd hok (by simp)
  | ok t =>
    rw [hc, ok_bind] at hok
    rcases canApplyToBrokerCover_error_codes _ _ _ t hc with rfl | rfl
    swap
    · simp only [TER.operator_bool, if_true, pure_eq, Except.ok.injEq] at hok
      exact Or.inr (Or.inl hok.symm)
    simp only [TER.operator_bool, Bool.false_eq_true, if_false] at hok
    cases he : AssetPool.exponent pool lb.numericType with
    | error e => rw [he, err_bind] at hok; exact absurd hok (by simp)
    | ok e =>
      rw [he, ok_bind] at hok
      cases hn : amount.toNumber .to_nearest with
      | error e => rw [hn, err_bind] at hok; exact absurd hok (by simp)
      | ok aN =>
        rw [hn, ok_bind] at hok
        by_cases hlt : lb.coverAvailable.operator_lt aN = true
        · exact Or.inr (Or.inr (by simpa [hlt] using hok.symm))
        · simp only [hlt, Bool.false_eq_true, if_false] at hok
          cases hs : lb.coverAvailable.operator_sub aN .to_nearest with
          | error e => rw [hs, err_bind] at hok; exact absurd hok (by simp)
          | ok c' =>
            rw [hs, ok_bind] at hok
            cases hm : ({ lb.toRawLoanBroker with coverAvailable := c' } :
                RawLoanBroker).hasMinimumCover e with
            | error e => rw [hm, err_bind] at hok; exact absurd hok (by simp)
            | ok b =>
              rw [hm, ok_bind] at hok
              cases b
              · exact Or.inr (Or.inr (by simpa using hok.symm))
              · exact Or.inl (by simpa using hok.symm)

/-- A withdrawal check that passed ran every step: the scale check, the cover
check and the minimum-cover check. -/
lemma LoanBroker.canCoverWithdraw_success_inv (lb : LoanBroker) (pool : α) (amount : STAmount)
    (hok : lb.canCoverWithdraw pool amount = .ok .tesSUCCESS) :
    ∃ e aN c', canApplyToBrokerCover lb.numericType lb.coverAvailable amount = .ok .tesSUCCESS ∧
      AssetPool.exponent pool lb.numericType = .ok e ∧ amount.toNumber .to_nearest = .ok aN ∧
      lb.coverAvailable.operator_lt aN = false ∧
      lb.coverAvailable.operator_sub aN .to_nearest = .ok c' ∧
      ({ lb.toRawLoanBroker with coverAvailable := c' } : RawLoanBroker).hasMinimumCover e =
        .ok true := by
  unfold LoanBroker.canCoverWithdraw at hok
  dsimp only at hok
  obtain ⟨t, hc, hok⟩ := bind_ok_peel _ _ _ hok
  rcases canApplyToBrokerCover_error_codes _ _ _ t hc with rfl | rfl
  swap
  · simp [TER.operator_bool] at hok
  simp only [TER.operator_bool, Bool.false_eq_true, if_false, pure_eq, ok_bind] at hok
  obtain ⟨e, he, hok⟩ := bind_ok_peel _ _ _ hok
  obtain ⟨aN, hn, hok⟩ := bind_ok_peel _ _ _ hok
  by_cases hlt : lb.coverAvailable.operator_lt aN = true
  · simp [hlt] at hok
  have hlt' : lb.coverAvailable.operator_lt aN = false := by simpa using hlt
  simp only [hlt', Bool.false_eq_true, if_false] at hok
  obtain ⟨c', hs, hok⟩ := bind_ok_peel _ _ _ hok
  obtain ⟨b, hm, hok⟩ := bind_ok_peel _ _ _ hok
  cases b
  · simp at hok
  · exact ⟨e, aN, c', hc, he, hn, hlt', hs, hm⟩

/-- **Proof body of `coverWithdraw_negative_cover`.** -/
lemma LoanBroker.coverWithdraw_negative_cover_proof (lb : LoanBroker) (amount : STAmount)
    (aN c' : Number)
    (hnum : amount.toNumber .to_nearest = .ok aN)
    (hsub : lb.coverAvailable.operator_sub aN .to_nearest = .ok c')
    (hneg : Number.zero.operator_le c' = false) :
    lb.coverWithdraw amount = .error .notLawful := by
  simp [LoanBroker.coverWithdraw, LoanBroker.applyCoverTransaction, hnum, hsub,
    RawLoanBroker.to_lawful_negative_cover lb c' hneg]

/-- **Proof body of `coverWithdraw_success`.** -/
lemma LoanBroker.coverWithdraw_success_proof (lb : LoanBroker) (amount : STAmount)
    (aN c' : Number) (hc : amount.ExactCanonical) (hnum : amount.toNumber .to_nearest = .ok aN)
    (hge : lb.coverAvailable.operator_lt aN = false)
    (hsub : lb.coverAvailable.operator_sub aN .to_nearest = .ok c') :
    ∃ lb' : LoanBroker, lb.coverWithdraw amount = .ok (.ok ⟨amount, lb'⟩) ∧
      lb'.toRawLoanBroker = { lb.toRawLoanBroker with coverAvailable := c' } := by
  obtain ⟨_, han⟩ := STAmount.toNumber_exact_of amount aN hc hnum
  obtain ⟨lb', htl, hraw⟩ := LoanBroker.debit_lawful lb aN c' han hge hsub
  refine ⟨lb', ?_, hraw⟩
  simp [LoanBroker.coverWithdraw, LoanBroker.applyCoverTransaction, hnum, hsub, htl]

/-- **Proof body of `coverWithdraw_never_rejects`.** -/
lemma LoanBroker.coverWithdraw_never_rejects_proof (lb : LoanBroker) (amount : STAmount)
    (ter : TER) : lb.coverWithdraw amount ≠ .ok (.error ter) := by
  intro hok
  unfold LoanBroker.coverWithdraw at hok
  obtain ⟨res, _, hok⟩ := bind_ok_peel _ _ _ hok
  simp at hok

end XRPL.Model.Lending
