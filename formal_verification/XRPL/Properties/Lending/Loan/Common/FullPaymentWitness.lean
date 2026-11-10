import XRPL.Properties.Lending.Loan.Common.FullPaymentSize
import XRPL.Properties.Lending.Loan.Common.SetWitness

/-! # A full payment whose fee loses its last digits

An IOU loan with a ClosePaymentFee of `10^25` and a 10% management fee. The early payoff adds the management fee
of `100` to the close fee, a sum of 26 digits, and the `Number` keeps 19 of them: feePaid is `10^25`. -/

set_option linter.style.nativeDecide false

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault (Vault RawVault)

/-- The witness vault: an IOU vault at scale `10^-6` holding `3·10^9`. -/
private def fpVault : Vault := ⟨lwVault, by native_decide, by native_decide⟩

/-- An IOU broker with a 10% management fee and no cover requirement. -/
private def fpBroker : LoanBroker :=
  ⟨{ numericType := .fractional, managementFeeRate := 10000, coverRateMinimum := 0, coverRateLiquidation := 0,
     debtTotal := Number.zero, debtMaximum := Number.zero, coverAvailable := Number.zero, loanCount := 0 },
    by native_decide, by native_decide⟩

/-- `1000`. -/
private def fpPrincipal : Number := ⟨false, 1000000000000000000, -15⟩

/-- A ClosePaymentFee of `10^25`. -/
private def fpFees : LoanFees := { lwFees with closePaymentFee := ⟨false, 1000000000000000000, 7⟩ }

/-- A 10% InterestRate and a 100% CloseInterestRate. -/
private def fpRates : LoanRates := { lwRates 10000 with closeInterestRate := 100000 }

/-- `2·10^25`, enough for the payoff. -/
private def fpAmount : Number := ⟨false, 2000000000000000000, 7⟩

/-- Thirty payments 60 seconds apart, starting at the LoanSet close time `1000`. -/
private def fpSchedule : LoanSchedule := LoanSchedule.build (some 60) (some 30) (some 60) 1000 1000 false

/-- The LoanSet at close time `1000`, then a full payment at `1010`. Its feePaid is not ClosePaymentFee plus the
management fee. -/
private def fpCheck : Bool :=
  match Loan.canCreate fpBroker fpVault fpPrincipal fpFees fpSchedule 1000 false with
  | .ok .tesSUCCESS =>
    match (Loan.create fpBroker fpVault fpPrincipal fpRates fpFees fpSchedule false false).run with
    | .ok (.ok r0) =>
      let loan := r0.loan'
      match (loan.payInstalments r0.pool' .full fpAmount 1010).run, loan.periodicRate with
      | .ok (.ok payment), .ok rate =>
        match loanPrincipalFromPeriodicPayment loan.periodicPayment rate loan.paymentRemaining with
        | .ok tpo =>
          match computeFullPaymentInterest tpo rate 1010 loan.schedule.paymentInterval loan.previousPaymentDueDate
              loan.schedule.startDate loan.rates.closeInterestRate with
          | .ok fi =>
            match STAmount.roundToNumericType loan.broker.numericType fi .downward (some loan.loanScale) with
            | .ok fi' =>
              match computeManagementFee loan.broker.numericType fi' loan.broker.managementFeeRate loan.loanScale with
              | .ok mf => decide (payment.amounts.feePaid.toRat ≠ loan.fees.closePaymentFee.toRat + mf.toRat)
              | .error _ => false
            | .error _ => false
          | .error _ => false
        | .error _ => false
      | _, _ => false
    | _ => false
  | _ => false

private lemma fpCheck_true : fpCheck = true := by native_decide

/-- **A reachable IOU loan whose full payment has feePaid ≠ ClosePaymentFee + managementFee.** The fee sum has 26
digits, the payoff keeps 19. -/
lemma Loan.fullPayment_broker_witness :
    ∃ (loan : Loan) (v : Vault) (amount : Number) (now t : UInt32) (payment : UnsettledPayment Vault)
      (rate tpo fullInterest fullInterest' managementFee : Number),
      loan.Reachable t ∧ (loan.payInstalments v .full amount now).run = .ok (.ok payment) ∧
      loan.periodicRate = .ok rate ∧
      loanPrincipalFromPeriodicPayment loan.periodicPayment rate loan.paymentRemaining = .ok tpo ∧
      computeFullPaymentInterest tpo rate now loan.schedule.paymentInterval loan.previousPaymentDueDate
        loan.schedule.startDate loan.rates.closeInterestRate = .ok fullInterest ∧
      STAmount.roundToNumericType loan.broker.numericType fullInterest .downward (some loan.loanScale) =
        .ok fullInterest' ∧
      computeManagementFee loan.broker.numericType fullInterest' loan.broker.managementFeeRate loan.loanScale =
        .ok managementFee ∧
      payment.amounts.feePaid.toRat ≠ loan.fees.closePaymentFee.toRat + managementFee.toRat := by
  have h := fpCheck_true
  unfold fpCheck at h
  split at h
  · rename_i hcan
    split at h
    · rename_i r0 h0
      dsimp only at h
      split at h
      · rename_i payment rate hpay hrate
        split at h
        · rename_i tpo htpo
          split at h
          · rename_i fi hfi
            split at h
            · rename_i fi' hfloor
              split at h
              · rename_i mf hmf
                have hc : Loan.Created r0.loan' 1000 :=
                  ⟨fpBroker, fpVault, fpPrincipal, fpRates, fpFees, some 60, some 30, some 60, 1000, false, false,
                    r0, hcan, h0, rfl⟩
                exact ⟨r0.loan', r0.pool', fpAmount, 1010, 1000, payment, rate, tpo, fi, fi', mf,
                  ⟨r0.loan', 1000, hc, .refl⟩, hpay, hrate, htpo, hfi, hfloor, hmf, of_decide_eq_true h⟩
              · exact absurd h (by decide)
            · exact absurd h (by decide)
          · exact absurd h (by decide)
        · exact absurd h (by decide)
      · exact absurd h (by decide)
    · exact absurd h (by decide)
  · exact absurd h (by decide)

end XRPL.Model.Lending
