import XRPL.Model.Lending.Loan.LoanAccept
import XRPL.Model.Lending.Loan.LoanManage
import XRPL.Model.Lending.Loan.LoanPay
import XRPL.Model.Lending.Loan.LoanSet
import XRPL.Model.Lending1_1.AssetPool

/-! # Loan reachability

A reachable loan comes from a LoanSet that passed `canCreate` and `create`, then from loan transactions that passed
their checks, on any vault, at close times that never go back. `delete` is not a step as it removes the loan. -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault (Vault)

/-- Loans reachable from `start` at close time `t₀`, with the close time of the last transaction. -/
inductive Loan.ReachableFrom (start : Loan) (t₀ : UInt32) : Loan → UInt32 → Prop where
  | refl : Loan.ReachableFrom start t₀ start t₀
  -- the loan takes the ledger's newer copy of its broker, as `LendingLedger.LoanAt` reads it. Any broker of the
  -- same asset passes, more than C++ allows, which is safe for the theorems about every reachable loan
  | refresh (loan loan' : Loan) (t : UInt32) (broker : LoanBroker) :
      Loan.ReachableFrom start t₀ loan t →
      broker.numericType = loan.broker.numericType → -- a loan's broker never changes its asset
      RawLoan.to_lawful { loan.toRawLoan with broker := broker } = .ok loan' →
      Loan.ReachableFrom start t₀ loan' t
  | accept (loan : Loan) (t t' : UInt32) (v : Vault) (r : LoanWithPool Vault) :
      Loan.ReachableFrom start t₀ loan t → t ≤ t' → loan.canAccept v t' = .ok .tesSUCCESS →
      (loan.accept v).run = .ok (.ok r) → Loan.ReachableFrom start t₀ r.loan' t'
  | regularPayment (loan : Loan) (t t' : UInt32) (v : Vault) (amount : Number) (r : LoanWithAmounts Vault) :
      Loan.ReachableFrom start t₀ loan t → t ≤ t' → loan.canPay .regular = .tesSUCCESS →
      (loan.regularPayment v amount t').run = .ok (.ok r) → Loan.ReachableFrom start t₀ r.loan' t'
  | latePayment (loan : Loan) (t t' : UInt32) (v : Vault) (amount : Number) (r : LoanWithAmounts Vault) :
      Loan.ReachableFrom start t₀ loan t → t ≤ t' → loan.canPay .late = .tesSUCCESS →
      (loan.latePayment v amount t').run = .ok (.ok r) → Loan.ReachableFrom start t₀ r.loan' t'
  | fullPayment (loan : Loan) (t t' : UInt32) (v : Vault) (amount : Number) (r : LoanWithAmounts Vault) :
      Loan.ReachableFrom start t₀ loan t → t ≤ t' → loan.canPay .full = .tesSUCCESS →
      (loan.fullPayment v amount t').run = .ok (.ok r) → Loan.ReachableFrom start t₀ r.loan' t'
  | overpayment (loan : Loan) (t t' : UInt32) (v : Vault) (amount : Number) (r : LoanWithAmounts Vault) :
      Loan.ReachableFrom start t₀ loan t → t ≤ t' → loan.canPay .overpayment = .tesSUCCESS →
      (loan.overpayment v amount t').run = .ok (.ok r) → Loan.ReachableFrom start t₀ r.loan' t'
  | impair (loan : Loan) (t t' : UInt32) (v : Vault) (r : LoanWithPool Vault) :
      Loan.ReachableFrom start t₀ loan t → t ≤ t' → loan.canManage .impair t' = .tesSUCCESS →
      (loan.manageImpair v t').run = .ok (.ok r) → Loan.ReachableFrom start t₀ r.loan' t'
  | unimpair (loan : Loan) (t t' : UInt32) (v : Vault) (r : LoanWithPool Vault) :
      Loan.ReachableFrom start t₀ loan t → t ≤ t' → loan.canManage .unimpair t' = .tesSUCCESS →
      (loan.manageUnimpair v).run = .ok (.ok r) → Loan.ReachableFrom start t₀ r.loan' t'
  | default (loan : Loan) (t t' : UInt32) (v : Vault) (r : LoanWithAmounts Vault) :
      Loan.ReachableFrom start t₀ loan t → t ≤ t' → loan.canManage .default t' = .tesSUCCESS →
      (loan.manageDefault v).run = .ok (.ok r) → Loan.ReachableFrom start t₀ r.loan' t'

/-- The loan a LoanSet at close time `t₀` creates: the schedule is built from the transaction
fields, `canCreate` passed and `create` succeeded. A two-step LoanSet creates a pending loan. -/
def Loan.Created (start : Loan) (t₀ : UInt32) : Prop :=
  ∃ (broker : LoanBroker) (v : Vault) (principal : Number) (rates : LoanRates) (fees : LoanFees)
    (paymentInterval paymentTotal gracePeriod : Option UInt32) (startDate : UInt32)
    (twoStep allowsOverpayment : Bool) (r : LoanWithPool Vault),
    let schedule := LoanSchedule.build paymentInterval paymentTotal gracePeriod startDate t₀ twoStep
    Loan.canCreate broker v principal fees schedule t₀ twoStep = .ok .tesSUCCESS ∧
      (Loan.create broker v principal rates fees schedule allowsOverpayment twoStep).run = .ok (.ok r) ∧
      r.loan' = start

/-- Loans reachable from a LoanSet, with the close time of the last transaction. -/
def Loan.Reachable (loan : Loan) (t : UInt32) : Prop :=
  ∃ (start : Loan) (t₀ : UInt32), Loan.Created start t₀ ∧ Loan.ReachableFrom start t₀ loan t

end XRPL.Model.Lending
