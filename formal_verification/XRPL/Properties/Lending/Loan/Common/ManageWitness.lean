import XRPL.Properties.Lending.Loan.Common.ManageDefs

/-! # Witnesses for the LoanManage theorems

Concrete defaults on IOU vaults, checked by `native_decide`. -/

set_option linter.style.nativeDecide false

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault (Vault RawVault)

/-- A closed-ended IOU vault holding 1000 shares, with the given scale and balances. -/
private def mwVault (scale : UInt8) (assetsAvailable assetsDeployed lossUnrealized : Number) : RawVault :=
  { assetsAvailable := assetsAvailable, assetsDeployed := assetsDeployed, assetsReserved := Number.zero
  , assetsMaximum := none, numericType := .fractional, scale := scale
  , sharesTotal := ⟨false, 1000000000000000000, -15⟩, lossUnrealized := lossUnrealized
  , yieldUnrealized := Number.zero, schedule := some ⟨0, 900000000⟩, earlyExitFeeRate := none
  , ownerCanBlockDeposit := false, depositBlocked := false }

/-- An IOU broker with one loan and both cover rates at 100%, so the liquidation amount is DebtTotal. -/
def mwBroker (debtTotal coverAvailable : Number) : RawLoanBroker :=
  { numericType := .fractional, managementFeeRate := 0, coverRateMinimum := 100000
  , coverRateLiquidation := 100000, debtTotal := debtTotal, debtMaximum := Number.zero
  , coverAvailable := coverAvailable, loanCount := 1 }

/-- An active loan without interest or fees: one payment of PrincipalOutstanding due at 60 seconds. -/
def mwLoan (broker : LoanBroker) (principal : Number) (loanScale : Int) : RawLoan :=
  { broker := broker
    rates := { interestRate := 0, lateInterestRate := 0, closeInterestRate := 0, overpaymentInterestRate := 0
               overpaymentFee := 0 }
    fees := { originationFee := Number.zero, serviceFee := Number.zero, latePaymentFee := Number.zero
              closePaymentFee := Number.zero }
    schedule := { paymentInterval := 60, paymentTotal := 1, gracePeriod := 60, startDate := 0 }
    paymentRemaining := 1, periodicPayment := principal, principalOutstanding := principal
    totalValueOutstanding := principal, managementFeeOutstanding := Number.zero, loanScale := loanScale
    previousPaymentDueDate := 0, nextPaymentDueDate := 60
    isPending := false, isImpaired := false, isDefault := false, allowsOverpayment := false }

/-- `100`. -/
private def mwHundred : Number := ⟨false, 1000000000000000000, -16⟩

/-- `1000`. -/
private def mwThousand : Number := ⟨false, 1000000000000000000, -15⟩

/-- `5000`. -/
private def mwFiveThousand : Number := ⟨false, 5000000000000000000, -15⟩

/-! ### A default the cover pays in full, at scale `10^-6` -/

private def mwExactVault : Vault := ⟨mwVault 6 mwThousand mwThousand Number.zero, by native_decide, by native_decide⟩

private def mwExactBroker : LoanBroker := ⟨mwBroker mwThousand mwFiveThousand, by native_decide, by native_decide⟩

private def mwExactLoan : Loan := ⟨mwLoan mwExactBroker mwHundred (-6), by native_decide, by native_decide⟩

/-- The cover of the exact default, with the liquidation amount it caps. -/
private def exactCoverCheck : Bool :=
  match (mwExactLoan.manageDefault mwExactVault).run,
      tenthBipsOfValue mwExactLoan.broker.debtTotal mwExactLoan.broker.coverRateMinimum .upward with
  | .ok (.ok r), .ok minimumCover =>
    match tenthBipsOfValue minimumCover mwExactLoan.broker.coverRateLiquidation .upward with
    | .ok liquidationAmount =>
      decide (r.amountToPool.toRat = min (min liquidationAmount.toRat mwExactLoan.principalOutstanding.toRat)
        mwExactLoan.broker.coverAvailable.toRat) &&
      decide (r.amountToPool.toRat = min mwExactLoan.broker.coverAvailable.toRat
        mwExactLoan.principalOutstanding.toRat)
    | .error _ => false
  | _, _ => false

private lemma exactCoverCheck_true : exactCoverCheck = true := by native_decide

/-- A default whose cover equals the capped liquidation amount: 100 of PrincipalOutstanding, with a
liquidation amount of 1000 and 5000 of cover. -/
lemma Loan.manageDefault_cover_upper_bound_witness :
    ∃ (loan : Loan) (v : Vault) (minimumCover liquidationAmount : Number) (r : LoanWithAmounts Vault),
      (loan.manageDefault v).run = .ok (.ok r) ∧
      tenthBipsOfValue loan.broker.debtTotal loan.broker.coverRateMinimum .upward = .ok minimumCover ∧
      tenthBipsOfValue minimumCover loan.broker.coverRateLiquidation .upward = .ok liquidationAmount ∧
      r.amountToPool.toRat -
        min (min liquidationAmount.toRat loan.principalOutstanding.toRat) loan.broker.coverAvailable.toRat = 0 := by
  have h := exactCoverCheck_true
  unfold exactCoverCheck at h
  split at h
  · rename_i r minimumCover hr hmin
    split at h
    · rename_i liquidationAmount hliq
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h
      exact ⟨_, _, minimumCover, liquidationAmount, r, hr, hmin, hliq, by rw [h.1]; ring⟩
    · exact absurd h (by decide)
  · exact absurd h (by decide)

/-- A default whose cover equals the smaller of CoverAvailable and PrincipalOutstanding. -/
lemma Loan.manageDefault_cover_cap_witness :
    ∃ (loan : Loan) (v : Vault) (r : LoanWithAmounts Vault),
      (loan.manageDefault v).run = .ok (.ok r) ∧
      r.amountToPool.toRat - min loan.broker.coverAvailable.toRat loan.principalOutstanding.toRat = 0 := by
  have h := exactCoverCheck_true
  unfold exactCoverCheck at h
  split at h
  · rename_i r minimumCover hr hmin
    split at h
    · simp only [Bool.and_eq_true, decide_eq_true_eq] at h
      exact ⟨_, _, r, hr, by rw [h.2]; ring⟩
    · exact absurd h (by decide)
  · exact absurd h (by decide)

end XRPL.Model.Lending
