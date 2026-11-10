import XRPL.Properties.Lending.Loan.Common.PayDefs
import XRPL.Properties.Lending.Loan.Common.ReachableDefs
import XRPL.Properties.Lending.Loan.Common.SetWitness

/-! # A reachable loan whose payments charge more than their totalDue

A LoanServiceFee of `10^30` is exactly representable and on the LoanScale grid, so a LoanSet accepts it. totalDue
then rounds the instalment's value away, and paying exactly totalDue charges the value on top. -/

set_option linter.style.nativeDecide false

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault (Vault RawVault)

/-- A closed-ended IOU vault at scale `10^-2` holding `10^12`, with nothing lent out. -/
private def hfVault : RawVault :=
  { lwVault with assetsAvailable := ⟨false, 1000000000000000000, -6⟩
                 sharesTotal := ⟨false, 1000000000000000000, -6⟩
                 scale := 2 }

private def hfVaultL : Vault := ⟨hfVault, by native_decide, by native_decide⟩

/-- `5198461379.86`. -/
private def hfPrincipal : Number := ⟨false, 5198461379860000000, -9⟩

/-- LoanServiceFee and LatePaymentFee of `10^30`. -/
private def hfFees : LoanFees :=
  { lwFees with serviceFee := ⟨false, 1000000000000000000, 12⟩, latePaymentFee := ⟨false, 1000000000000000000, 12⟩ }

/-- InterestRate and LateInterestRate of 1%. -/
private def hfRates : LoanRates := { lwRates 1000 with lateInterestRate := 1000 }

/-- Thirty payments 60 seconds apart, starting at the LoanSet close time `1000`. -/
private def hfSchedule : LoanSchedule := LoanSchedule.build (some 60) (some 30) (some 60) 1000 1000 false

/-- The LoanSet at close time `1000`, then one regular instalment at `1011` of exactly its totalDue, which charges
more than that totalDue. -/
private def splitCheck : Bool :=
  match Loan.canCreate lwBrokerNoFee hfVaultL hfPrincipal hfFees hfSchedule 1000 false with
  | .ok .tesSUCCESS =>
    match (Loan.create lwBrokerNoFee hfVaultL hfPrincipal hfRates hfFees hfSchedule false false).run with
    | .ok (.ok r0) =>
      match r0.loan'.paymentComponents .regular 1011 with
      | .ok pc =>
        match pc.totalDue with
        | .ok due =>
          match (r0.loan'.payInstalment r0.pool' pc due).run with
          | .ok (.ok p) => decide (p.totalPaid.toRat < p.amounts.principalPaid.toRat + p.amounts.interestPaid.toRat +
              p.amounts.feePaid.toRat)
          | _ => false
        | .error _ => false
      | .error _ => false
    | _ => false
  | _ => false

private lemma splitCheck_true : splitCheck = true := by native_decide

/-- **A scheduled instalment can charge more than its totalDue.** A LoanServiceFee `10^19` times the instalment
makes totalDue drop the instalment's value. -/
lemma Loan.payment_split_witness :
    ∃ (loan : Loan) (t : UInt32) (v : Vault) (amount : Number) (now : UInt32) (pc : PaymentComponents)
      (p : UnsettledPayment Vault), loan.Reachable t ∧ loan.paymentComponents .regular now = .ok pc ∧
      (loan.payInstalment v pc amount).run = .ok (.ok p) ∧
      p.totalPaid.toRat < p.amounts.principalPaid.toRat + p.amounts.interestPaid.toRat + p.amounts.feePaid.toRat := by
  have h := splitCheck_true
  unfold splitCheck at h
  split at h
  · rename_i hcan
    split at h
    · rename_i r0 h0
      split at h
      · rename_i pc hpc
        split at h
        · rename_i due hdue
          split at h
          · rename_i p hp
            have hc : Loan.Created r0.loan' 1000 :=
              ⟨lwBrokerNoFee, hfVaultL, hfPrincipal, hfRates, hfFees, some 60, some 30, some 60, 1000, false, false,
                r0, hcan, h0, rfl⟩
            exact ⟨r0.loan', 1000, r0.pool', due, 1011, pc, p, ⟨r0.loan', 1000, hc, .refl⟩, hpc, hp,
              of_decide_eq_true h⟩
          · exact absurd h (by decide)
        · exact absurd h (by decide)
      · exact absurd h (by decide)
    · exact absurd h (by decide)
  · exact absurd h (by decide)

/-- The LoanSet at close time `1000`, then a late payment at `1200` of exactly its totalDue, whose totalDue misses the
value it clears plus the fees and the rounded late interest. -/
private def lateCostCheck : Bool :=
  match Loan.canCreate lwBrokerNoFee hfVaultL hfPrincipal hfFees hfSchedule 1000 false with
  | .ok .tesSUCCESS =>
    match (Loan.create lwBrokerNoFee hfVaultL hfPrincipal hfRates hfFees hfSchedule false false).run with
    | .ok (.ok r0) =>
      match r0.loan'.paymentComponents .late 1200 with
      | .ok pc =>
        match pc.totalDue with
        | .ok due =>
          match (r0.loan'.payInstalments r0.pool' .late due 1200).run,
              loanLatePaymentInterest r0.loan'.principalOutstanding r0.loan'.rates.lateInterestRate 1200
                r0.loan'.nextPaymentDueDate with
          | .ok (.ok p), .ok li =>
            match STAmount.roundToNumericType r0.loan'.broker.numericType li .to_nearest (some r0.loan'.loanScale) with
            | .ok lr => decide (p.totalPaid.toRat < r0.loan'.totalValueOutstanding.toRat -
                p.loan.totalValueOutstanding.toRat + r0.loan'.fees.serviceFee.toRat +
                r0.loan'.fees.latePaymentFee.toRat + lr.toRat)
            | .error _ => false
          | _, _ => false
        | .error _ => false
      | .error _ => false
    | _ => false
  | _ => false

private lemma lateCostCheck_true : lateCostCheck = true := by native_decide

/-- **A late payment's totalDue can miss its cost.** A LatePaymentFee `10^19` times the instalment makes totalDue
drop the instalment's value. -/
lemma Loan.latePayment_cost_witness :
    ∃ (loan : Loan) (t : UInt32) (v : Vault) (amount : Number) (now : UInt32) (p : UnsettledPayment Vault)
      (li lr : Number), loan.Reachable t ∧ (loan.payInstalments v .late amount now).run = .ok (.ok p) ∧
      loanLatePaymentInterest loan.principalOutstanding loan.rates.lateInterestRate now loan.nextPaymentDueDate =
        .ok li ∧ STAmount.roundToNumericType loan.broker.numericType li .to_nearest (some loan.loanScale) = .ok lr ∧
      p.totalPaid.toRat < loan.totalValueOutstanding.toRat - p.loan.totalValueOutstanding.toRat +
        loan.fees.serviceFee.toRat + loan.fees.latePaymentFee.toRat + lr.toRat := by
  have h := lateCostCheck_true
  unfold lateCostCheck at h
  split at h
  · rename_i hcan
    split at h
    · rename_i r0 h0
      split at h
      · split at h
        · split at h
          · rename_i p li hp hli
            split at h
            · rename_i lr hlr
              have hc : Loan.Created r0.loan' 1000 :=
                ⟨lwBrokerNoFee, hfVaultL, hfPrincipal, hfRates, hfFees, some 60, some 30, some 60, 1000, false,
                  false, r0, hcan, h0, rfl⟩
              exact ⟨r0.loan', 1000, r0.pool', _, 1200, p, li, lr, ⟨r0.loan', 1000, hc, .refl⟩, hp, hli, hlr,
                of_decide_eq_true h⟩
            · exact absurd h (by decide)
          · exact absurd h (by decide)
        · exact absurd h (by decide)
      · exact absurd h (by decide)
    · exact absurd h (by decide)
  · exact absurd h (by decide)

/-- The LoanSet at close time `1000`, then a regular payment at `1011` of exactly its first totalDue, which charges
more than that amount. -/
private def chargeCheck : Bool :=
  match Loan.canCreate lwBrokerNoFee hfVaultL hfPrincipal hfFees hfSchedule 1000 false with
  | .ok .tesSUCCESS =>
    match (Loan.create lwBrokerNoFee hfVaultL hfPrincipal hfRates hfFees hfSchedule false false).run with
    | .ok (.ok r0) =>
      match r0.loan'.paymentComponents .regular 1011 with
      | .ok pc =>
        match pc.totalDue with
        | .ok due =>
          match (r0.loan'.payInstalments r0.pool' .regular due 1011).run,
              (r0.loan'.pay r0.pool' .regular due 1011).run with
          | .ok (.ok p), .ok (.ok _) => decide (due.toRat < p.amounts.principalPaid.toRat +
              p.amounts.interestPaid.toRat + p.amounts.feePaid.toRat)
          | _, _ => false
        | .error _ => false
      | .error _ => false
    | _ => false
  | _ => false

private lemma chargeCheck_true : chargeCheck = true := by native_decide

/-- **A payment on a reachable loan can charge more than its requestedAmount.** The regular payment of exactly its
totalDue succeeds and charges the instalment's value on top of it. -/
lemma Loan.payment_charge_le_amount_witness :
    ∃ (loan : Loan) (t : UInt32) (v : Vault) (amount : Number) (now : UInt32) (p : UnsettledPayment Vault)
      (r : LoanWithAmounts Vault), loan.Reachable t ∧ (loan.payInstalments v .regular amount now).run = .ok (.ok p) ∧
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
            have hc : Loan.Created r0.loan' 1000 :=
              ⟨lwBrokerNoFee, hfVaultL, hfPrincipal, hfRates, hfFees, some 60, some 30, some 60, 1000, false, false,
                r0, hcan, h0, rfl⟩
            exact ⟨r0.loan', 1000, r0.pool', due, 1011, p, r, ⟨r0.loan', 1000, hc, .refl⟩, hp, hr,
              of_decide_eq_true h⟩
          · exact absurd h (by decide)
        · exact absurd h (by decide)
      · exact absurd h (by decide)
    · exact absurd h (by decide)
  · exact absurd h (by decide)

end XRPL.Model.Lending
