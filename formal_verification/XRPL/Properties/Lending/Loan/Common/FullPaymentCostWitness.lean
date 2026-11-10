import XRPL.Properties.Lending.Loan.Common.PayDefs
import XRPL.Properties.Lending.Loan.Common.ReachableDefs
import XRPL.Properties.Lending.Loan.Common.SetWitness

/-! # A reachable loan whose early payoff costs more than its remaining schedule

At a periodic rate near `3·10^-11` and 860 payments, the payment factor comes from `(1 + rate)^860`. The sum
`1 + rate` keeps only 18 decimals of the rate, so the schedule books almost no interest, less than one period. -/

set_option linter.style.nativeDecide false

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault (Vault RawVault)

private def fcVaultL : Vault := ⟨lwVault, by native_decide, by native_decide⟩

/-- `10^9`. -/
private def fcPrincipal : Number := ⟨false, 1000000000000000000, -9⟩

/-- 860 payments 92 seconds apart, starting at the LoanSet close time `1000`. -/
private def fcSchedule : LoanSchedule := LoanSchedule.build (some 92) (some 860) (some 60) 1000 1000 false

/-- The LoanSet at close time `1000` with InterestRate 0.001%, then a full payment at the first due date `1092` of
exactly its totalDue, which charges more than TotalValueOutstanding. -/
private def cheaperCheck : Bool :=
  match Loan.canCreate lwBrokerNoFee fcVaultL fcPrincipal lwFees fcSchedule 1000 false with
  | .ok .tesSUCCESS =>
    match (Loan.create lwBrokerNoFee fcVaultL fcPrincipal (lwRates 1) lwFees fcSchedule true false).run with
    | .ok (.ok r0) =>
      match r0.loan'.paymentComponents .full 1092 with
      | .ok pc =>
        match pc.totalDue with
        | .ok due =>
          match (r0.loan'.payInstalments r0.pool' .full due 1092).run with
          | .ok (.ok p) => decide (r0.loan'.rates.closeInterestRate = 0 ∧
              r0.loan'.fees.closePaymentFee.toRat ≤ r0.loan'.fees.serviceFee.toRat ∧
              r0.loan'.totalValueOutstanding.toRat +
                r0.loan'.paymentRemaining.toNat * r0.loan'.fees.serviceFee.toRat < p.totalPaid.toRat)
          | _ => false
        | .error _ => false
      | .error _ => false
    | _ => false
  | _ => false

private lemma cheaperCheck_true : cheaperCheck = true := by native_decide

/-- **An early payoff can cost more than the remaining scheduled payments.** The loan books less interest than one
period accrues, and the payoff charges that accrual on the principal. -/
lemma Loan.fullPayment_cheaper_witness :
    ∃ (loan : Loan) (v : Vault) (amount : Number) (now t : UInt32) (p : UnsettledPayment Vault),
      loan.Reachable t ∧ (loan.payInstalments v .full amount now).run = .ok (.ok p) ∧
      loan.rates.closeInterestRate = 0 ∧ loan.fees.closePaymentFee.toRat ≤ loan.fees.serviceFee.toRat ∧
      loan.totalValueOutstanding.toRat + loan.paymentRemaining.toNat * loan.fees.serviceFee.toRat <
        p.totalPaid.toRat := by
  have h := cheaperCheck_true
  unfold cheaperCheck at h
  split at h
  · rename_i hcan
    split at h
    · rename_i r0 h0
      split at h
      · split at h
        · split at h
          · rename_i p hp
            have hc : Loan.Created r0.loan' 1000 :=
              ⟨lwBrokerNoFee, fcVaultL, fcPrincipal, lwRates 1, lwFees, some 92, some 860, some 60, 1000, false,
                true, r0, hcan, h0, rfl⟩
            obtain ⟨h1, h2, h3⟩ := of_decide_eq_true h
            exact ⟨r0.loan', r0.pool', _, 1092, 1000, p, ⟨r0.loan', 1000, hc, .refl⟩, hp, h1, h2, h3⟩
          · exact absurd h (by decide)
        · exact absurd h (by decide)
      · exact absurd h (by decide)
    · exact absurd h (by decide)
  · exact absurd h (by decide)

end XRPL.Model.Lending
