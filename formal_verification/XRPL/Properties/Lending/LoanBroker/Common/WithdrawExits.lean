import XRPL.Properties.Lending.LoanBroker.Common.CoverDebit

/-! # Proof bodies for the `LoanBrokerCoverWithdraw` exits

Proofs for the withdrawal exits. The check and the withdrawal both clamp the amount onto the grid
of `coverAvailable` minus the amount, so every exit reads the clamped amount. -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol

variable {α : Type} [AssetPool α]

/-- Proof body of the precision-loss exit of `LoanBroker.canCoverWithdraw_exits`. -/
lemma LoanBroker.canCoverWithdraw_precision_loss_proof (lb : LoanBroker) (pool : α) (amount a : STAmount)
    (hcl : clampToSumExponent lb.coverAvailable amount.operator_neg (AssetPool.baseExponent pool) = .ok a)
    (hz : a.isZero = true) :
    lb.canCoverWithdraw pool amount = .ok .tecPRECISION_LOSS := by
  simp [LoanBroker.canCoverWithdraw, hcl, hz]

/-- Proof body of the insufficient-cover exit of `LoanBroker.canCoverWithdraw_exits`. -/
lemma LoanBroker.canCoverWithdraw_insufficient_cover_proof (lb : LoanBroker) (pool : α) (amount a : STAmount)
    (aN : Number)
    (hcl : clampToSumExponent lb.coverAvailable amount.operator_neg (AssetPool.baseExponent pool) = .ok a)
    (hnz : a.isZero = false) (hnum : a.toNumber .to_nearest = .ok aN)
    (hlt : lb.coverAvailable.operator_lt aN = true) :
    lb.canCoverWithdraw pool amount = .ok .tecINSUFFICIENT_FUNDS := by
  simp [LoanBroker.canCoverWithdraw, hcl, hnz, hnum, hlt]

/-- Proof body of the below-minimum exit of `LoanBroker.canCoverWithdraw_exits`. -/
lemma LoanBroker.canCoverWithdraw_below_minimum_proof (lb : LoanBroker) (pool : α) (amount a : STAmount)
    (aN c' : Number)
    (hcl : clampToSumExponent lb.coverAvailable amount.operator_neg (AssetPool.baseExponent pool) = .ok a)
    (hnz : a.isZero = false) (hnum : a.toNumber .to_nearest = .ok aN)
    (hge : lb.coverAvailable.operator_lt aN = false)
    (hsub : lb.coverAvailable.operator_sub aN .to_nearest = .ok c')
    (hmin : ({ lb.toRawLoanBroker with coverAvailable := c' } : RawLoanBroker).hasMinimumCover
      (AssetPool.baseExponent pool) = .ok false) :
    lb.canCoverWithdraw pool amount = .ok .tecINSUFFICIENT_FUNDS := by
  simp [LoanBroker.canCoverWithdraw, hcl, hnz, hnum, hge, hsub, hmin]

/-- Proof body of the success exit of `LoanBroker.canCoverWithdraw_exits`. -/
lemma LoanBroker.canCoverWithdraw_success_proof (lb : LoanBroker) (pool : α) (amount a : STAmount)
    (aN c' : Number)
    (hcl : clampToSumExponent lb.coverAvailable amount.operator_neg (AssetPool.baseExponent pool) = .ok a)
    (hnz : a.isZero = false) (hnum : a.toNumber .to_nearest = .ok aN)
    (hge : lb.coverAvailable.operator_lt aN = false)
    (hsub : lb.coverAvailable.operator_sub aN .to_nearest = .ok c')
    (hmin : ({ lb.toRawLoanBroker with coverAvailable := c' } : RawLoanBroker).hasMinimumCover
      (AssetPool.baseExponent pool) = .ok true) :
    lb.canCoverWithdraw pool amount = .ok .tesSUCCESS := by
  simp [LoanBroker.canCoverWithdraw, hcl, hnz, hnum, hge, hsub, hmin]

/-- Proof body of `canCoverWithdraw_error_codes`. -/
lemma LoanBroker.canCoverWithdraw_error_codes_proof (lb : LoanBroker) (pool : α) (amount : STAmount)
    (ter : TER) (hok : lb.canCoverWithdraw pool amount = .ok ter) :
    ter = .tesSUCCESS ∨ ter = .tecPRECISION_LOSS ∨ ter = .tecINSUFFICIENT_FUNDS := by
  unfold LoanBroker.canCoverWithdraw at hok
  unfold_ter at hok
  walk_ok
  all_goals first | exact Or.inl rfl | exact Or.inr (Or.inl rfl) | exact Or.inr (Or.inr rfl)

/-- Proof body of the negative-cover exit of `LoanBroker.coverWithdraw_exits`. -/
lemma LoanBroker.coverWithdraw_negative_cover_proof (lb : LoanBroker) (pool : α) (amount a : STAmount)
    (aN c' : Number)
    (hcl : clampToSumExponent lb.coverAvailable amount.operator_neg (AssetPool.baseExponent pool) = .ok a)
    (hnum : a.toNumber .to_nearest = .ok aN)
    (hsub : lb.coverAvailable.operator_sub aN .to_nearest = .ok c')
    (hneg : Number.zero.operator_le c' = false) :
    (lb.coverWithdraw pool amount).run = .error .notLawful := by
  unfold LoanBroker.coverWithdraw LoanBroker.applyCoverTransaction
  unfold_ter
  simp [hcl, hnum, hsub, RawLoanBroker.to_lawful_negative_cover lb c' hneg]

/-- Proof body of the success exit of `LoanBroker.coverWithdraw_exits`. -/
lemma LoanBroker.coverWithdraw_success_proof (lb : LoanBroker) (pool : α) (amount a : STAmount)
    (aN c' : Number)
    (hcl : clampToSumExponent lb.coverAvailable amount.operator_neg (AssetPool.baseExponent pool) = .ok a)
    (hnum : a.toNumber .to_nearest = .ok aN)
    (hge : lb.coverAvailable.operator_lt aN = false)
    (hsub : lb.coverAvailable.operator_sub aN .to_nearest = .ok c') :
    ∃ lb' : LoanBroker, (lb.coverWithdraw pool amount).run = .ok (.ok ⟨a, lb'⟩) ∧
      lb'.toRawLoanBroker = { lb.toRawLoanBroker with coverAvailable := c' } := by
  obtain ⟨lb', htl, hraw⟩ :=
    LoanBroker.debit_lawful lb aN c' (STAmount.toNumber_isNormalized a _ aN hnum) hge hsub
  refine ⟨lb', ?_, hraw⟩
  unfold LoanBroker.coverWithdraw LoanBroker.applyCoverTransaction
  unfold_ter
  simp [hcl, hnum, hsub, htl]

/-- Proof body of `coverWithdraw_error_codes`. -/
lemma LoanBroker.coverWithdraw_error_codes_proof (lb : LoanBroker) (pool : α) (amount : STAmount)
    (ter : TER) : (lb.coverWithdraw pool amount).run ≠ .ok (.error ter) := by
  intro hok
  unfold LoanBroker.coverWithdraw at hok
  unfold_ter at hok
  walk_ok

end XRPL.Model.Lending
