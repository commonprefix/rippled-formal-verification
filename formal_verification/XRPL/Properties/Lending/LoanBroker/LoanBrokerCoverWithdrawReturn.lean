import XRPL.Properties.Lending.LoanBroker.Common.WithdrawExits

/-! # `LoanBrokerCoverWithdraw` exits

The exits of the withdrawal check and the withdrawal. Both clamp the amount toward zero onto the grid of
CoverAvailable minus the amount, never finer than the base exponent. The withdrawal pays out the clamped amount. -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol

variable {α : Type} [AssetPool α]

variable (lb : LoanBroker)

/-- The exits of `canCoverWithdraw`, in the order it runs its checks. Each line assumes the checks before it passed. -/
theorem LoanBroker.canCoverWithdraw_exits (pool : α) (amount : STAmount) :
    (∀ a : STAmount,
      clampToSumExponent lb.coverAvailable amount.operator_neg (AssetPool.baseExponent pool) = .ok a →
      a.isZero = true → lb.canCoverWithdraw pool amount = .ok .tecPRECISION_LOSS) ∧
    (∀ (a : STAmount) (aN : Number),
      clampToSumExponent lb.coverAvailable amount.operator_neg (AssetPool.baseExponent pool) = .ok a →
      a.isZero = false → a.toNumber .to_nearest = .ok aN → lb.coverAvailable.operator_lt aN = true →
      lb.canCoverWithdraw pool amount = .ok .tecINSUFFICIENT_FUNDS) ∧
    (∀ (a : STAmount) (aN c' : Number),
      clampToSumExponent lb.coverAvailable amount.operator_neg (AssetPool.baseExponent pool) = .ok a →
      a.isZero = false → a.toNumber .to_nearest = .ok aN → lb.coverAvailable.operator_lt aN = false →
      lb.coverAvailable.operator_sub aN .to_nearest = .ok c' →
      ({ lb.toRawLoanBroker with coverAvailable := c' } : RawLoanBroker).hasMinimumCover
        (AssetPool.baseExponent pool) = .ok false →
      lb.canCoverWithdraw pool amount = .ok .tecINSUFFICIENT_FUNDS) ∧
    (∀ (a : STAmount) (aN c' : Number),
      clampToSumExponent lb.coverAvailable amount.operator_neg (AssetPool.baseExponent pool) = .ok a →
      a.isZero = false → a.toNumber .to_nearest = .ok aN → lb.coverAvailable.operator_lt aN = false →
      lb.coverAvailable.operator_sub aN .to_nearest = .ok c' →
      ({ lb.toRawLoanBroker with coverAvailable := c' } : RawLoanBroker).hasMinimumCover
        (AssetPool.baseExponent pool) = .ok true →
      lb.canCoverWithdraw pool amount = .ok .tesSUCCESS) :=
  ⟨LoanBroker.canCoverWithdraw_precision_loss_proof lb pool amount,
    LoanBroker.canCoverWithdraw_insufficient_cover_proof lb pool amount,
    LoanBroker.canCoverWithdraw_below_minimum_proof lb pool amount,
    LoanBroker.canCoverWithdraw_success_proof lb pool amount⟩

/-- Error codes: success, tecPRECISION_LOSS or tecINSUFFICIENT_FUNDS. -/
theorem LoanBroker.canCoverWithdraw_error_codes (pool : α) (amount : STAmount)
    (ter : TER) (hok : lb.canCoverWithdraw pool amount = .ok ter) :
    ter = .tesSUCCESS ∨ ter = .tecPRECISION_LOSS ∨ ter = .tecINSUFFICIENT_FUNDS :=
  LoanBroker.canCoverWithdraw_error_codes_proof lb pool amount ter hok

/-- The exits of `coverWithdraw`, in the order it runs its checks. Each line assumes the checks before it passed. -/
theorem LoanBroker.coverWithdraw_exits (pool : α) (amount : STAmount) :
    (∀ (a : STAmount) (aN c' : Number),
      clampToSumExponent lb.coverAvailable amount.operator_neg (AssetPool.baseExponent pool) = .ok a →
      a.toNumber .to_nearest = .ok aN → lb.coverAvailable.operator_sub aN .to_nearest = .ok c' →
      Number.zero.operator_le c' = false → (lb.coverWithdraw pool amount).run = .error .notLawful) ∧
    -- `c'` - the new CoverAvailable, the difference rounded to nearest
    (∀ (a : STAmount) (aN c' : Number),
      clampToSumExponent lb.coverAvailable amount.operator_neg (AssetPool.baseExponent pool) = .ok a →
      a.toNumber .to_nearest = .ok aN → lb.coverAvailable.operator_lt aN = false →
      lb.coverAvailable.operator_sub aN .to_nearest = .ok c' →
      ∃ lb' : LoanBroker, (lb.coverWithdraw pool amount).run = .ok (.ok ⟨a, lb'⟩) ∧
        lb'.toRawLoanBroker = { lb.toRawLoanBroker with coverAvailable := c' }) :=
  ⟨LoanBroker.coverWithdraw_negative_cover_proof lb pool amount, LoanBroker.coverWithdraw_success_proof lb pool amount⟩

/-- A withdrawal never returns a transaction error code. -/
theorem LoanBroker.coverWithdraw_error_codes (pool : α) (amount : STAmount) (ter : TER) :
    (lb.coverWithdraw pool amount).run ≠ .ok (.error ter) :=
  LoanBroker.coverWithdraw_error_codes_proof lb pool amount ter

end XRPL.Model.Lending
