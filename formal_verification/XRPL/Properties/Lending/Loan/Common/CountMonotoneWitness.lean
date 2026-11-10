import XRPL.Properties.Lending.Loan.Common.SetWitness

/-! # Two more payments can raise PeriodicPayment by one unit in the last digit

At InterestRate 100% and payments 60 seconds apart for nearly 30 years, the payment factor sits at the periodic
rate to about 18 digits. Its rounding moves it by one unit in the last digit while two more payments lower it less. -/

set_option linter.style.nativeDecide false

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault (Vault RawVault)

/-- The closed-ended IOU vault holding `3·10^9`, with a RedemptionDate 946700000 seconds after its start. -/
private def cmVault : RawVault := { lwVault with schedule := some ⟨0, 946700000⟩ }

private def cmVaultL : Vault := ⟨cmVault, by native_decide, by native_decide⟩

/-- `10^8`. -/
private def cmPrincipal : Number := ⟨false, 1000000000000000000, -10⟩

/-- 15396294 payments 60 seconds apart, starting at the LoanSet close time `1000`. -/
private def cmSchedule : LoanSchedule := LoanSchedule.build (some 60) (some 15396294) (some 60) 1000 1000 false

/-- The same schedule with two more payments. -/
private def cmSchedule₂ : LoanSchedule := LoanSchedule.build (some 60) (some 15396296) (some 60) 1000 1000 false

/-- Both LoanSets at InterestRate 100% pass, and the one with two more payments has the larger PeriodicPayment. -/
private def countCheck : Bool :=
  match (Loan.create lwBrokerNoFee cmVaultL cmPrincipal (lwRates 100000) lwFees cmSchedule false false).run,
      (Loan.create lwBrokerNoFee cmVaultL cmPrincipal (lwRates 100000) lwFees cmSchedule₂ false false).run with
  | .ok (.ok r₁), .ok (.ok r₂) => decide (r₁.loan'.periodicPayment.toRat < r₂.loan'.periodicPayment.toRat)
  | _, _ => false

private lemma countCheck_true : countCheck = true := by native_decide

/-- **Two more payments can raise PeriodicPayment.** The rise is one unit in the 19th digit. -/
lemma Loan.create_periodicPayment_count_antitone_witness :
    ∃ (broker : LoanBroker) (v : Vault) (rates : LoanRates) (fees : LoanFees) (schedule : LoanSchedule)
      (allowsOverpayment pending : Bool) (principal : Number) (schedule₂ : LoanSchedule)
      (r₁ r₂ : LoanWithPool Vault),
      principal.isNormalized ∧ 0 < principal.toRat ∧ STAmount.isRounded broker.numericType principal = false ∧
      schedule₂ = { schedule with paymentTotal := schedule₂.paymentTotal } ∧
      schedule.paymentTotal < schedule₂.paymentTotal ∧
      (Loan.create broker v principal rates fees schedule allowsOverpayment pending).run = .ok (.ok r₁) ∧
      (Loan.create broker v principal rates fees schedule₂ allowsOverpayment pending).run = .ok (.ok r₂) ∧
      r₁.loan'.toExact.periodicPayment < r₂.loan'.toExact.periodicPayment := by
  have h := countCheck_true
  unfold countCheck at h
  split at h
  · rename_i r₁ r₂ h₁ h₂
    exact ⟨lwBrokerNoFee, cmVaultL, lwRates 100000, lwFees, cmSchedule, false, false, cmPrincipal, cmSchedule₂, r₁, r₂,
      by native_decide, by native_decide, by native_decide, rfl, by decide, h₁, h₂, of_decide_eq_true h⟩
  · exact absurd h (by decide)

end XRPL.Model.Lending
