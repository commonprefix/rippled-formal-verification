import XRPL.Model.Lending.Loan.LoanSet
import XRPL.Model.Lending1_1.AssetPool
import XRPL.Properties.Lending.Loan.Defs

/-! # Witness for the management fee of a new loan, from above

A one-payment create on a closed-ended IOU vault, checked by `native_decide`. Its fee product ends in a tie
that rounds up by half of its last digit. -/

set_option linter.style.nativeDecide false

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault (Vault RawVault)

/-- A closed-ended IOU vault at scale `10^-6` holding `620000000`, with nothing lent out. -/
private def feeTieVaultRaw : RawVault :=
  { assetsAvailable := ⟨false, 6200000000000000000, -10⟩, assetsDeployed := Number.zero
  , assetsReserved := Number.zero, assetsMaximum := none, numericType := .fractional, scale := 6
  , sharesTotal := ⟨false, 6200000000000000000, -10⟩, lossUnrealized := Number.zero
  , yieldUnrealized := Number.zero, schedule := some ⟨0, 900000000⟩, earlyExitFeeRate := none
  , ownerCanBlockDeposit := false, depositBlocked := false }

private def feeTieVault : Vault := ⟨feeTieVaultRaw, by native_decide, by native_decide⟩

/-- An IOU broker with no loans, no cover requirement and a 9.999% management fee. -/
private def feeTieBrokerRaw : RawLoanBroker :=
  { numericType := .fractional, managementFeeRate := 9999, coverRateMinimum := 0
  , coverRateLiquidation := 0, debtTotal := Number.zero, debtMaximum := Number.zero
  , coverAvailable := Number.zero, loanCount := 0 }

private def feeTieBroker : LoanBroker := ⟨feeTieBrokerRaw, by native_decide, by native_decide⟩

/-- `615000000.00667`. -/
private def feeTiePrincipal : Number := ⟨false, 6150000000066700000, -10⟩

/-- InterestRate 100% and no other rate. -/
private def feeTieRates : LoanRates :=
  { interestRate := 100000, lateInterestRate := 0, closeInterestRate := 0, overpaymentInterestRate := 0
  , overpaymentFee := 0 }

/-- No fees. -/
private def feeTieFees : LoanFees :=
  { originationFee := Number.zero, serviceFee := Number.zero, latePaymentFee := Number.zero
  , closePaymentFee := Number.zero }

/-- One payment fifteen years of 365 days after the start. -/
private def feeTieSchedule : LoanSchedule :=
  { paymentInterval := 473040000, paymentTotal := 1, gracePeriod := 60, startDate := 1000 }

/-- PrincipalRequested fits an IOU amount. -/
private lemma feeTiePrincipal_exact : STAmount.isRounded feeTieBroker.numericType feeTiePrincipal = false := by
  native_decide

/-- The interest is `9225000000.10005` and its 9.999% share `922407750.0090039995`. The product
`92240775000900.39995` keeps 18 digits at that size, so the tie rounds up to `92240775000900.4`. -/
private def feeTieCheck : Bool :=
  match (Loan.create feeTieBroker feeTieVault feeTiePrincipal feeTieRates feeTieFees feeTieSchedule false
      false).run with
  | .ok (.ok r) =>
    decide (r.loan'.toExact.managementFeeOutstanding - (r.loan'.broker.managementFeeRate.toNat : ℚ) / 100000 *
      (r.loan'.toExact.totalValueOutstanding - r.loan'.toExact.principalOutstanding) =
        50 / 100000 * 10 ^ r.loan'.toExact.loanScale)
  | _ => false

private lemma feeTieCheck_true : feeTieCheck = true := by native_decide

/-- ManagementFeeOutstanding − ManagementFeeRate × (TotalValueOutstanding − PrincipalOutstanding) can be
`0.0005` ULP. -/
lemma Loan.create_managementFee_upper_bound_tie_witness :
    ∃ (broker : LoanBroker) (v : Vault) (principal : Number) (rates : LoanRates) (fees : LoanFees)
      (schedule : LoanSchedule) (r : LoanWithPool Vault),
      STAmount.isRounded broker.numericType principal = false ∧
      (Loan.create broker v principal rates fees schedule false false).run = .ok (.ok r) ∧
      r.loan'.toExact.managementFeeOutstanding - (r.loan'.broker.managementFeeRate.toNat : ℚ) / 100000 *
        (r.loan'.toExact.totalValueOutstanding - r.loan'.toExact.principalOutstanding) =
        50 / 100000 * 10 ^ r.loan'.toExact.loanScale := by
  have h := feeTieCheck_true
  unfold feeTieCheck at h
  split at h
  · rename_i r hr
    exact ⟨_, _, _, _, _, _, r, feeTiePrincipal_exact, hr, of_decide_eq_true h⟩
  · exact absurd h (by decide)

end XRPL.Model.Lending
