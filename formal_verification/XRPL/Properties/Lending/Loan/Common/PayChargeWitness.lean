import XRPL.Properties.Lending.Loan.Common.PayDefs
import XRPL.Properties.Lending.Loan.Common.ReachableDefs
import XRPL.Properties.Lending.Loan.Common.SetWitness

/-! # A reachable loan whose payment charges more than requestedAmount

A LoanServiceFee of `10^30` is exactly representable and on the LoanScale grid, so a LoanSet accepts it. totalDue
then rounds the instalment's value away, and a payment of exactly totalDue charges the value on top. -/

set_option linter.style.nativeDecide false

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault (Vault RawVault)

/-- A closed-ended IOU vault at scale `10^-2` holding `10^12`, with nothing lent out. -/
private def pcVault : RawVault :=
  { lwVault with assetsAvailable := ⟨false, 1000000000000000000, -6⟩
                 sharesTotal := ⟨false, 1000000000000000000, -6⟩
                 scale := 2 }

private def pcVaultL : Vault := ⟨pcVault, by native_decide, by native_decide⟩

/-- `5198461379.86`. -/
private def pcPrincipal : Number := ⟨false, 5198461379860000000, -9⟩

/-- LoanServiceFee and LatePaymentFee of `10^30`. -/
private def pcFees : LoanFees :=
  { lwFees with serviceFee := ⟨false, 1000000000000000000, 12⟩, latePaymentFee := ⟨false, 1000000000000000000, 12⟩ }

/-- InterestRate and LateInterestRate of 1%. -/
private def pcRates : LoanRates := { lwRates 1000 with lateInterestRate := 1000 }

/-- Thirty payments 60 seconds apart, starting at the LoanSet close time `1000`. -/
private def pcSchedule : LoanSchedule := LoanSchedule.build (some 60) (some 30) (some 60) 1000 1000 false

/-- The LoanSet at close time `1000`, then a regular payment at `1011` of exactly its first totalDue, a normalized
amount, which charges more than that amount. -/
private def chargeCheck : Bool :=
  match Loan.canCreate lwBrokerNoFee pcVaultL pcPrincipal pcFees pcSchedule 1000 false with
  | .ok .tesSUCCESS =>
    match (Loan.create lwBrokerNoFee pcVaultL pcPrincipal pcRates pcFees pcSchedule false false).run with
    | .ok (.ok r0) =>
      match r0.loan'.paymentComponents .regular 1011 with
      | .ok pc =>
        match pc.totalDue with
        | .ok due =>
          match (r0.loan'.payInstalments r0.pool' .regular due 1011).run,
              (r0.loan'.pay r0.pool' .regular due 1011).run with
          | .ok (.ok p), .ok (.ok _) => decide due.isNormalized && decide (due.toRat < p.amounts.principalPaid.toRat +
              p.amounts.interestPaid.toRat + p.amounts.feePaid.toRat)
          | _, _ => false
        | .error _ => false
      | .error _ => false
    | _ => false
  | _ => false

private lemma chargeCheck_true : chargeCheck = true := by native_decide

/-- **A payment on a reachable loan can charge more than its normalized requestedAmount.** The regular payment of
exactly its totalDue succeeds and charges the instalment's value on top of it. -/
lemma Loan.payment_charge_le_amount_fee_witness :
    ∃ (loan : Loan) (t : UInt32) (v : Vault) (amount : Number) (now : UInt32) (p : UnsettledPayment Vault)
      (r : LoanWithAmounts Vault), loan.Reachable t ∧ amount.isNormalized ∧
      (loan.payInstalments v .regular amount now).run = .ok (.ok p) ∧
      (loan.pay v .regular amount now).run = .ok (.ok r) ∧
      amount.toRat < p.amounts.principalPaid.toRat + p.amounts.interestPaid.toRat + p.amounts.feePaid.toRat := by
  have h := chargeCheck_true
  unfold chargeCheck at h
  split at h
  · rename_i hcan
    split at h
    · rename_i r0 h0
      split at h
      · split at h
        · rename_i due hdue
          split at h
          · rename_i p r hp hr
            simp only [Bool.and_eq_true, decide_eq_true_eq] at h
            have hc : Loan.Created r0.loan' 1000 :=
              ⟨lwBrokerNoFee, pcVaultL, pcPrincipal, pcRates, pcFees, some 60, some 30, some 60, 1000, false, false,
                r0, hcan, h0, rfl⟩
            exact ⟨r0.loan', 1000, r0.pool', due, 1011, p, r, ⟨r0.loan', 1000, hc, .refl⟩, h.1, hp, hr, h.2⟩
          · exact absurd h (by decide)
        · exact absurd h (by decide)
      · exact absurd h (by decide)
    · exact absurd h (by decide)
  · exact absurd h (by decide)

end XRPL.Model.Lending
