import XRPL.Properties.Lending.Loan.Common.ReachableProofs
import XRPL.Properties.Lending.Loan.Common.SetWitness

/-! # A reachable loan whose interestDue goes up

A loan at a tiny rate, paid one instalment at a time: the third instalment takes more principal off the loan than
the payment. With late or overpayment interest it passes and interestDue rises. -/

set_option linter.style.nativeDecide false

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault (Vault RawVault)

/-- `10^12`. -/
private def rwTrillion : Number := ⟨false, 1000000000000000000, -6⟩

/-- A closed-ended IOU vault at scale `10^-2` holding `10^12`, with nothing lent out. -/
private def rwVault : RawVault :=
  { lwVault with assetsAvailable := rwTrillion, sharesTotal := rwTrillion, scale := 2 }

private def rwVaultL : Vault := ⟨rwVault, by native_decide, by native_decide⟩

/-- `5198461379.86`. -/
private def rwPrincipal : Number := ⟨false, 5198461379860000000, -9⟩

/-- `173282046.55`, the first two payments. -/
private def rwPaymentLow : Number := ⟨false, 1732820465500000000, -10⟩

/-- Thirty payments 60 seconds apart, starting at the LoanSet close time `1000`. -/
private def rwSchedule : LoanSchedule := LoanSchedule.build (some 60) (some 30) (some 60) 1000 1000 false

/-- The witness loan's rates with a 100% LateInterestRate. -/
private def rwLateRates : LoanRates := { lwRates 6 with lateInterestRate := 100000 }

/-- The witness loan's rates with a 50% OverpaymentInterestRate. -/
private def rwOverRates : LoanRates := { lwRates 6 with overpaymentInterestRate := 50000 }

/-- `180000000`, a late payment covering the third instalment and its late interest. -/
private def rwLateAmount : Number := ⟨false, 1800000000000000000, -10⟩

/-- `173282056.56`, the third payment plus `10`. -/
private def rwOverAmount : Number := ⟨false, 1732820565600000000, -10⟩

/-- The LoanSet at close time `1000` with `rates`, two regular payments at `1011` and `1012`, then a payment of type
`pt` at `now`. It holds when that payment raises interestDue and the loan has `rate` zero. -/
private def raiseCheck' (rates : LoanRates) (allowsOverpayment : Bool) (rate : LoanRates → TenthBips32)
    (pt : LoanPaymentType) (amount : Number) (now : UInt32) : Bool :=
  match Loan.canCreate lwBrokerNoFee rwVaultL rwPrincipal lwFees rwSchedule 1000 false with
  | .ok .tesSUCCESS =>
    match (Loan.create lwBrokerNoFee rwVaultL rwPrincipal rates lwFees rwSchedule allowsOverpayment false).run with
    | .ok (.ok r0) =>
      if r0.loan'.canPay .regular = .tesSUCCESS then
        match (r0.loan'.regularPayment r0.pool' rwPaymentLow 1011).run with
        | .ok (.ok r1) =>
          if r1.loan'.canPay .regular = .tesSUCCESS then
            match (r1.loan'.regularPayment r1.pool' rwPaymentLow 1012).run with
            | .ok (.ok r2) =>
              if r2.loan'.canPay pt = .tesSUCCESS then
                match (r2.loan'.pay r2.pool' pt amount now).run with
                | .ok (.ok r3) => decide (rate r2.loan'.rates = 0) &&
                    decide (r2.loan'.toExact.interestDue < r3.loan'.toExact.interestDue)
                | _ => false
              else false
            | _ => false
          else false
        | _ => false
      else false
    | _ => false
  | _ => false

/-- A run that passes the check: a reachable loan with `rate` zero, and a later loan with a higher interestDue. -/
private lemma raiseCheck'_sound (rates : LoanRates) (allowsOverpayment : Bool) (rate : LoanRates → TenthBips32)
    (pt : LoanPaymentType) (amount : Number) (now : UInt32) (hnow : 1012 ≤ now)
    (h : raiseCheck' rates allowsOverpayment rate pt amount now = true) :
    ∃ (start loan : Loan) (t₀ t : UInt32), start.Reachable t₀ ∧ Loan.ReachableFrom start t₀ loan t ∧
      rate start.rates = 0 ∧ start.toExact.interestDue < loan.toExact.interestDue := by
  unfold raiseCheck' at h
  split at h
  · rename_i hcan
    split at h
    · rename_i r0 h0
      split at h
      · rename_i hp0
        split at h
        · rename_i r1 h1
          split at h
          · rename_i hp1
            split at h
            · rename_i r2 h2
              split at h
              · rename_i hp2
                split at h
                · rename_i r3 h3
                  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
                  have hc : Loan.Created r0.loan' 1000 :=
                    ⟨lwBrokerNoFee, rwVaultL, rwPrincipal, rates, lwFees, some 60, some 30, some 60, 1000, false,
                      allowsOverpayment, r0, hcan, h0, rfl⟩
                  have hr1 : Loan.ReachableFrom r0.loan' 1000 r1.loan' 1011 :=
                    .regularPayment r0.loan' 1000 1011 r0.pool' rwPaymentLow r1 .refl (by decide) hp0 h1
                  have hr2 : Loan.ReachableFrom r0.loan' 1000 r2.loan' 1012 :=
                    .regularPayment r1.loan' 1011 1012 r1.pool' rwPaymentLow r2 hr1 (by decide) hp1 h2
                  exact ⟨r2.loan', r3.loan', 1012, now, ⟨r0.loan', 1000, hc, hr2⟩,
                    Loan.ReachableFrom.pay_step .refl hnow hp2 h3, h.1, h.2⟩
                · exact absurd h (by decide)
              · exact absurd h (by decide)
            · exact absurd h (by decide)
          · exact absurd h (by decide)
        · exact absurd h (by decide)
      · exact absurd h (by decide)
    · exact absurd h (by decide)
  · exact absurd h (by decide)

private lemma lateRaise_true :
    raiseCheck' rwLateRates false (fun r => r.overpaymentInterestRate) .late rwLateAmount 1200 = true := by
  native_decide

private lemma overRaise_true :
    raiseCheck' rwOverRates true (fun r => r.lateInterestRate) .overpayment rwOverAmount 1013 = true := by
  native_decide

/-- **A late payment can raise interestDue.** Its late interest covers the negative interest part of the
instalment, so the settlement passes (C++ LoanPay.cpp:479 checks only the summed parts). -/
lemma Loan.ReachableFrom.interest_monotone_late_witness :
    ∃ (start loan : Loan) (t₀ t : UInt32), start.Reachable t₀ ∧ Loan.ReachableFrom start t₀ loan t ∧
      start.rates.overpaymentInterestRate = 0 ∧ start.toExact.interestDue < loan.toExact.interestDue :=
  raiseCheck'_sound rwLateRates false (fun r => r.overpaymentInterestRate) .late rwLateAmount 1200 (by decide)
    lateRaise_true

/-- **An overpayment can raise interestDue.** Its overpayment interest covers the negative interest part of the
instalment before it, so the settlement passes. -/
lemma Loan.ReachableFrom.interest_monotone_overpayment_witness :
    ∃ (start loan : Loan) (t₀ t : UInt32), start.Reachable t₀ ∧ Loan.ReachableFrom start t₀ loan t ∧
      start.rates.lateInterestRate = 0 ∧ start.toExact.interestDue < loan.toExact.interestDue :=
  raiseCheck'_sound rwOverRates true (fun r => r.lateInterestRate) .overpayment rwOverAmount 1013 (by decide)
    overRaise_true

end XRPL.Model.Lending
