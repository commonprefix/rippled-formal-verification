import XRPL.Properties.Lending.LoanBroker.Common.WithdrawExits

/-! # `LoanBrokerCoverWithdraw` exits

The exits of the withdrawal checks. The amount itself is never rounded. -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.Result

variable {α : Type} [AssetPool α]

variable (lb : LoanBroker)

/-- When the amount is zero or rounds to zero at CoverAvailable's scale -> tecPRECISION_LOSS. -/
theorem LoanBroker.canCoverWithdraw_precision_loss (pool : α) (amount rn : STAmount)
    (hz : amount.isZero = true ∨
      (roundToCoverScale lb.numericType lb.coverAvailable amount .to_nearest = .ok rn ∧
        rn.signum = 0)) :
    lb.canCoverWithdraw pool amount = .ok .tecPRECISION_LOSS :=
  LoanBroker.canCoverWithdraw_precision_loss_proof lb pool amount rn hz

/-- When CoverAvailable < amount -> tecINSUFFICIENT_FUNDS. -/
theorem LoanBroker.canCoverWithdraw_insufficient_cover (pool : α) (amount : STAmount) (e : Int)
    (aN : Number)
    (hcheck : canApplyToBrokerCover lb.numericType lb.coverAvailable amount = .ok .tesSUCCESS)
    (hexp : AssetPool.exponent pool lb.numericType = .ok e)
    (hnum : amount.toNumber .to_nearest = .ok aN)
    (hlt : lb.coverAvailable.operator_lt aN = true) :
    lb.canCoverWithdraw pool amount = .ok .tecINSUFFICIENT_FUNDS :=
  LoanBroker.canCoverWithdraw_insufficient_cover_proof lb pool amount e aN hcheck hexp hnum hlt

/-- When CoverAvailable − amount < minCover -> tecINSUFFICIENT_FUNDS. -/
theorem LoanBroker.canCoverWithdraw_below_minimum (pool : α) (amount : STAmount) (e : Int)
    (aN c' : Number)
    (hcheck : canApplyToBrokerCover lb.numericType lb.coverAvailable amount = .ok .tesSUCCESS)
    (hexp : AssetPool.exponent pool lb.numericType = .ok e)
    (hnum : amount.toNumber .to_nearest = .ok aN)
    (hge : lb.coverAvailable.operator_lt aN = false)
    (hsub : lb.coverAvailable.operator_sub aN .to_nearest = .ok c')
    (hmin : ({ lb.toRawLoanBroker with coverAvailable := c' } : RawLoanBroker).hasMinimumCover e =
      .ok false) :
    lb.canCoverWithdraw pool amount = .ok .tecINSUFFICIENT_FUNDS :=
  LoanBroker.canCoverWithdraw_below_minimum_proof lb pool amount e aN c' hcheck hexp hnum hge hsub
    hmin

/-- Otherwise -> success. -/
theorem LoanBroker.canCoverWithdraw_success (pool : α) (amount : STAmount) (e : Int)
    (aN c' : Number)
    (hcheck : canApplyToBrokerCover lb.numericType lb.coverAvailable amount = .ok .tesSUCCESS)
    (hexp : AssetPool.exponent pool lb.numericType = .ok e)
    (hnum : amount.toNumber .to_nearest = .ok aN)
    (hge : lb.coverAvailable.operator_lt aN = false)
    (hsub : lb.coverAvailable.operator_sub aN .to_nearest = .ok c')
    (hmin : ({ lb.toRawLoanBroker with coverAvailable := c' } : RawLoanBroker).hasMinimumCover e =
      .ok true) :
    lb.canCoverWithdraw pool amount = .ok .tesSUCCESS :=
  LoanBroker.canCoverWithdraw_success_proof lb pool amount e aN c' hcheck hexp hnum hge hsub hmin

/-- Error codes: success, tecPRECISION_LOSS or tecINSUFFICIENT_FUNDS. -/
theorem LoanBroker.canCoverWithdraw_error_codes (pool : α) (amount : STAmount)
    (ter : TER) (hok : lb.canCoverWithdraw pool amount = .ok ter) :
    ter = .tesSUCCESS ∨ ter = .tecPRECISION_LOSS ∨ ter = .tecINSUFFICIENT_FUNDS :=
  LoanBroker.canCoverWithdraw_error_codes_proof lb pool amount ter hok

/-- When amount > CoverAvailable -> notLawful. -/
theorem LoanBroker.coverWithdraw_negative_cover (amount : STAmount) (aN c' : Number)
    (hnum : amount.toNumber .to_nearest = .ok aN)
    (hsub : lb.coverAvailable.operator_sub aN .to_nearest = .ok c')
    (hneg : Number.zero.operator_le c' = false) :
    lb.coverWithdraw amount = .error .notLawful :=
  LoanBroker.coverWithdraw_negative_cover_proof lb amount aN c' hnum hsub hneg

/-- All checks pass -> updated loan broker and amount.
`c'` - the new CoverAvailable, the rounded difference -/
theorem LoanBroker.coverWithdraw_success (amount : STAmount) (aN c' : Number)
    (hc : amount.ExactCanonical)
    (hnum : amount.toNumber .to_nearest = .ok aN)
    (hge : lb.coverAvailable.operator_lt aN = false)
    (hsub : lb.coverAvailable.operator_sub aN .to_nearest = .ok c') :
    ∃ lb' : LoanBroker, lb.coverWithdraw amount = .ok (.ok ⟨amount, lb'⟩) ∧
      lb'.toRawLoanBroker = { lb.toRawLoanBroker with coverAvailable := c' } :=
  LoanBroker.coverWithdraw_success_proof lb amount aN c' hc hnum hge hsub

/-- `coverWithdraw` never returns a rejection. -/
theorem LoanBroker.coverWithdraw_never_rejects (amount : STAmount) (ter : TER) :
    lb.coverWithdraw amount ≠ .ok (.error ter) :=
  LoanBroker.coverWithdraw_never_rejects_proof lb amount ter

end XRPL.Model.Lending
