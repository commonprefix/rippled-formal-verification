import XRPL.Properties.Lending.Loan.Common.Frame
import XRPL.Properties.Lending.Loan.Common.PayDefs
import XRPL.Properties.Lending.Loan.Common.ReachableDefs

/-! # Proof bodies for the loan reachability theorems -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault (Vault)

/-- Every loan transaction keeps the terms, so every reachable loan has the terms it started with. -/
lemma Loan.ReachableFrom.keepsTerms {start : Loan} {t₀ : UInt32} {loan : Loan} {t : UInt32}
    (hr : Loan.ReachableFrom start t₀ loan t) : Loan.KeepsTerms start loan := by
  induction hr with
  | refl => exact Loan.KeepsTerms.refl _
  | refresh _ _ _ _ _ _ h ih => exact ih.trans (Loan.KeepsTerms.of_lawful h rfl rfl rfl rfl rfl)
  | accept _ _ _ _ _ _ _ _ h ih => exact ih.trans (Loan.accept_keepsTerms _ _ _ h)
  | regularPayment _ _ _ _ _ _ _ _ _ h ih => exact ih.trans (Loan.regularPayment_keepsTerms _ _ _ _ _ h)
  | latePayment _ _ _ _ _ _ _ _ _ h ih => exact ih.trans (Loan.latePayment_keepsTerms _ _ _ _ _ h)
  | fullPayment _ _ _ _ _ _ _ _ _ h ih => exact ih.trans (Loan.fullPayment_keepsTerms _ _ _ _ _ h)
  | overpayment _ _ _ _ _ _ _ _ _ h ih => exact ih.trans (Loan.overpayment_keepsTerms _ _ _ _ _ h)
  | impair _ _ _ _ _ _ _ _ h ih => exact ih.trans (Loan.manageImpair_keepsTerms _ _ _ _ h)
  | unimpair _ _ _ _ _ _ _ _ h ih => exact ih.trans (Loan.manageUnimpair_keepsTerms _ _ _ h)
  | default _ _ _ _ _ _ _ _ h ih => exact ih.trans (Loan.manageDefault_keepsTerms _ _ _ h)

/-- The loan part of the fixed terms line of `Lending.Reachable.loan_lifetime`. -/
lemma Loan.ReachableFrom.fixed_terms_proof (start : Loan) (t₀ : UInt32) (loan : Loan) (t : UInt32)
    (hr : Loan.ReachableFrom start t₀ loan t) :
    loan.rates = start.rates ∧ loan.fees = start.fees ∧ loan.schedule.startDate = start.schedule.startDate ∧
      loan.schedule.paymentInterval = start.schedule.paymentInterval ∧
      loan.schedule.paymentTotal = start.schedule.paymentTotal ∧
      loan.schedule.gracePeriod = start.schedule.gracePeriod ∧ loan.loanScale = start.loanScale ∧
      loan.allowsOverpayment = start.allowsOverpayment := by
  have h := hr.keepsTerms
  exact ⟨h.rates, h.fees, by rw [h.schedule], by rw [h.schedule], by rw [h.schedule], by rw [h.schedule],
    h.loanScale, h.allowsOverpayment⟩

/-- Reachability chains along two runs. -/
lemma Loan.ReachableFrom.trans {a b c : Loan} {ta tb tc : UInt32} (h1 : Loan.ReachableFrom a ta b tb)
    (h2 : Loan.ReachableFrom b tb c tc) : Loan.ReachableFrom a ta c tc := by
  induction h2 with
  | refl => exact h1
  | refresh _ _ _ _ _ hnt h ih => exact .refresh _ _ _ _ ih hnt h
  | accept _ _ _ _ _ _ hle hc h ih => exact .accept _ _ _ _ _ ih hle hc h
  | regularPayment _ _ _ _ _ _ _ hle hc h ih => exact .regularPayment _ _ _ _ _ _ ih hle hc h
  | latePayment _ _ _ _ _ _ _ hle hc h ih => exact .latePayment _ _ _ _ _ _ ih hle hc h
  | fullPayment _ _ _ _ _ _ _ hle hc h ih => exact .fullPayment _ _ _ _ _ _ ih hle hc h
  | overpayment _ _ _ _ _ _ _ hle hc h ih => exact .overpayment _ _ _ _ _ _ ih hle hc h
  | impair _ _ _ _ _ _ hle hc h ih => exact .impair _ _ _ _ _ ih hle hc h
  | unimpair _ _ _ _ _ _ hle hc h ih => exact .unimpair _ _ _ _ _ ih hle hc h
  | default _ _ _ _ _ _ hle hc h ih => exact .default _ _ _ _ _ ih hle hc h

/-- A payment that passes its checks is a step of a run. -/
lemma Loan.ReachableFrom.pay_step {start loan : Loan} {t₀ t t' : UInt32} {v : Vault}
    {pt : LoanPaymentType} {amount : Number} {r : LoanWithAmounts Vault} (hr : Loan.ReachableFrom start t₀ loan t)
    (hle : t ≤ t') (hc : loan.canPay pt = .tesSUCCESS) (h : (loan.pay v pt amount t').run = .ok (.ok r)) :
    Loan.ReachableFrom start t₀ r.loan' t' := by
  cases pt
  · exact .regularPayment _ _ _ _ _ _ hr hle hc h
  · exact .latePayment _ _ _ _ _ _ hr hle hc h
  · exact .fullPayment _ _ _ _ _ _ hr hle hc h
  · exact .overpayment _ _ _ _ _ _ hr hle hc h

end XRPL.Model.Lending
