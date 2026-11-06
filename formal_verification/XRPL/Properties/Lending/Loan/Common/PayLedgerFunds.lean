import XRPL.Properties.Lending.Loan.Common.PayLedger
import XRPL.Properties.Lending.Loan.Common.PayProofs
import XRPL.Properties.Lending.Loan.Common.PayFit
import XRPL.Properties.Lending.Loan.Common.PayCredit
import XRPL.Properties.Lending.Loan.Common.PayYield
import XRPL.Properties.Lending.Loan.Common.SeparatePayments
import XRPL.Properties.Lending.Loan.Common.FullPaymentSize
import XRPL.Properties.Lending.Ledger.Common.YieldSum

/-! # What a LoanPay transaction moves to the vault and the broker

Proof bodies of the LoanPay headlines about the vault and the broker: the credit to AssetsAvailable, the fee to the
cover, and the vault's yield, loss and debt after a payment. -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault (Vault)

/-- Proof body of `Lending.payment_cover_unchanged`. -/
lemma LendingLedger.payment_fees_proof (l l' : LendingLedger) (i : Nat) (paymentType : LoanPaymentType)
    (amount : Number) (h : (l.apply (.loanPay i paymentType amount)).run = .ok (.ok l')) (loan loan' : Loan)
    (hat : l.LoanAt i loan) (hat' : l'.LoanAt i loan')
    (hcover : loan.broker.hasMinimumCover l.vault.baseExponent = .ok true) :
    loan'.broker.coverAvailable = loan.broker.coverAvailable := by
  obtain ⟨r, hok, rfl, -⟩ := LendingLedger.loanPay_loans h hat hat'
  exact Loan.payment_fees_proof loan l.vault amount l.now paymentType r hcover hok

/-- Proof body of the upper line of `Lending.payment_fees`. -/
lemma LendingLedger.payment_fees_upper_bound_proof (l : LendingLedger) (hr : l.Reachable) (l' : LendingLedger)
    (i : Nat) (paymentType : LoanPaymentType) (amount : Number)
    (h : (l.apply (.loanPay i paymentType amount)).run = .ok (.ok l')) (loan loan' : Loan) (hat : l.LoanAt i loan)
    (hat' : l'.LoanAt i loan') (payment : UnsettledPayment Vault)
    (hcover : loan.broker.hasMinimumCover l.vault.baseExponent = .ok false)
    (hpay : (loan.payInstalments l.vault paymentType amount l.now).run = .ok (.ok payment))
    (hfit : loan.broker.numericType.isIntegral = true → loan.broker.coverAvailable.toRat +
      payment.amounts.feePaid.toRat < 2 ^ 63 * (10 : ℚ) ^ l.vault.baseExponent) :
    (loan'.broker.coverAvailable.toRat - loan.broker.coverAvailable.toRat) - payment.amounts.feePaid.toRat ≤ 0 := by
  obtain ⟨r, hok, rfl, -⟩ := LendingLedger.loanPay_loans h hat hat'
  exact Loan.payment_fees_upper_bound_proof loan amount paymentType r l hr i hat payment hcover hpay hok hfit

/-- Proof body of the lower line of `Lending.payment_fees`. -/
lemma LendingLedger.payment_fees_lower_bound_proof (l : LendingLedger) (hr : l.Reachable) (l' : LendingLedger)
    (i : Nat) (paymentType : LoanPaymentType) (amount : Number)
    (h : (l.apply (.loanPay i paymentType amount)).run = .ok (.ok l')) (loan loan' : Loan) (hat : l.LoanAt i loan)
    (hat' : l'.LoanAt i loan') (payment : UnsettledPayment Vault)
    (hcover : loan.broker.hasMinimumCover l.vault.baseExponent = .ok false)
    (hpay : (loan.payInstalments l.vault paymentType amount l.now).run = .ok (.ok payment))
    (hroom : loan.broker.coverAvailable.toRat + payment.amounts.feePaid.toRat ≤
      (10 : ℚ) ^ (16 + l.vault.baseExponent) - 10 ^ l.vault.baseExponent) :
    ∀ e, numberExponent loan'.broker.coverAvailable l.vault.baseExponent loan.broker.numericType = .ok e →
      loan.broker.coverAvailable.toRat + payment.amounts.feePaid.toRat - loan'.broker.coverAvailable.toRat <
        10 ^ e := by
  obtain ⟨r, hok, rfl, -⟩ := LendingLedger.loanPay_loans h hat hat'
  exact Loan.payment_fees_lower_bound_proof loan amount paymentType r l hr i hat payment hcover hpay hok hroom

/-- Proof body of `Lending.regularPayment_split`. -/
lemma LendingLedger.regularPayment_split_proof (l : LendingLedger) (hr : l.Reachable) (l₁ : LendingLedger) (i : Nat)
    (amount : Number) (h : (l.apply (.loanPay i .regular amount)).run = .ok (.ok l₁)) (loan loan₁ : Loan)
    (hat : l.LoanAt i loan) (hat₁ : l₁.LoanAt i loan₁) (payment : UnsettledPayment Vault)
    (hpay : (loan.payInstalments l.vault .regular amount l.now).run = .ok (.ok payment)) (l₂ : LendingLedger)
    (loan₂ : Loan) (hsep : l.SeparatePayments i payment.count l₂) (hat₂ : l₂.LoanAt i loan₂)
    (htotal : l.vault.assetsAvailable.toRat +
      (payment.amounts.principalPaid.toRat + payment.amounts.interestPaid.toRat) <
        10 ^ 16 * (10 : ℚ) ^ l.vault.baseExponent) :
    loan₂.toRawLoan = { loan₁.toRawLoan with broker := loan₂.broker } ∧
      loan₂.broker.toRawLoanBroker =
        { loan₁.broker.toRawLoanBroker with coverAvailable := loan₂.broker.coverAvailable } ∧
      l₂.vault = l₁.vault := by
  obtain ⟨r, hok, rfl, hv⟩ := LendingLedger.loanPay_loans h hat hat₁
  rw [hv]
  exact Loan.regularPayment_split_proof loan amount r l hr i hat payment l₂ loan₂ hpay hok hsep hat₂ htotal

/-- Proof body of the vault part of `Lending.fullPayment_payoff`. -/
lemma LendingLedger.fullPayment_vault_proof (l : LendingLedger) (hr : l.Reachable) (l' : LendingLedger) (i : Nat)
    (amount : Number) (h : (l.apply (.loanPay i .full amount)).run = .ok (.ok l')) (loan : Loan)
    (hat : l.LoanAt i loan) (payment : UnsettledPayment Vault)
    (rate tpo fullInterest fullInterest' managementFee : Number)
    (hpay : (loan.payInstalments l.vault .full amount l.now).run = .ok (.ok payment))
    (hrate : loan.periodicRate = .ok rate)
    (htpo : loanPrincipalFromPeriodicPayment loan.periodicPayment rate loan.paymentRemaining = .ok tpo)
    (hfi : computeFullPaymentInterest tpo rate l.now loan.schedule.paymentInterval loan.previousPaymentDueDate
      loan.schedule.startDate loan.rates.closeInterestRate = .ok fullInterest)
    (hfloor : STAmount.roundToNumericType loan.broker.numericType fullInterest .downward (some loan.loanScale) =
      .ok fullInterest')
    (hfee : computeManagementFee loan.broker.numericType fullInterest' loan.broker.managementFeeRate loan.loanScale =
      .ok managementFee) :
    payment.amounts.principalPaid = loan.principalOutstanding ∧
      payment.amounts.interestPaid.toRat = fullInterest'.toRat - managementFee.toRat := by
  obtain ⟨t, -, hreach⟩ := hr.loanAt_reachable hat
  obtain ⟨q, hq, rfl⟩ := LendingLedger.loanPay_instalments_eq h hat hpay
  exact Loan.fullPayment_vault_reachable_proof loan l.vault amount l.now t hreach q rate tpo fullInterest
    fullInterest' managementFee hq hrate htpo hfi hfloor hfee

/-- Proof body of `Lending.fullPayment_broker`. -/
lemma LendingLedger.fullPayment_broker_proof (l : LendingLedger) (hr : l.Reachable) (l' : LendingLedger) (i : Nat)
    (amount : Number) (h : (l.apply (.loanPay i .full amount)).run = .ok (.ok l')) (loan : Loan)
    (hat : l.LoanAt i loan) (payment : UnsettledPayment Vault)
    (rate tpo fullInterest fullInterest' managementFee : Number)
    (hpay : (loan.payInstalments l.vault .full amount l.now).run = .ok (.ok payment))
    (hrate : loan.periodicRate = .ok rate)
    (htpo : loanPrincipalFromPeriodicPayment loan.periodicPayment rate loan.paymentRemaining = .ok tpo)
    (hfi : computeFullPaymentInterest tpo rate l.now loan.schedule.paymentInterval loan.previousPaymentDueDate
      loan.schedule.startDate loan.rates.closeInterestRate = .ok fullInterest)
    (hfloor : STAmount.roundToNumericType loan.broker.numericType fullInterest .downward (some loan.loanScale) =
      .ok fullInterest')
    (hfee : computeManagementFee loan.broker.numericType fullInterest' loan.broker.managementFeeRate loan.loanScale =
      .ok managementFee)
    (hsum : loan.fees.closePaymentFee.toRat + managementFee.toRat < 2 ^ 63 * 10 ^ loan.loanScale) :
    payment.amounts.feePaid.toRat = loan.fees.closePaymentFee.toRat + managementFee.toRat := by
  obtain ⟨t, -, hreach⟩ := hr.loanAt_reachable hat
  obtain ⟨q, hq, rfl⟩ := LendingLedger.loanPay_instalments_eq h hat hpay
  exact Loan.fullPayment_broker_reachable_proof loan l.vault amount l.now t hreach q rate tpo fullInterest
    fullInterest' managementFee hq hrate htpo hfi hfloor hfee hsum

/-- Proof body of `Lending.payment_vault_upper_bound`. -/
lemma LendingLedger.payment_vault_upper_bound_proof (l : LendingLedger) (hr : l.Reachable) (l' : LendingLedger)
    (i : Nat) (paymentType : LoanPaymentType) (amount : Number)
    (h : (l.apply (.loanPay i paymentType amount)).run = .ok (.ok l')) (loan : Loan) (hat : l.LoanAt i loan)
    (payment : UnsettledPayment Vault)
    (hpay : (loan.payInstalments l.vault paymentType amount l.now).run = .ok (.ok payment)) :
    (l'.vault.assetsAvailable.toRat - l.vault.assetsAvailable.toRat) -
      (payment.amounts.principalPaid.toRat + payment.amounts.interestPaid.toRat) ≤ 0 := by
  obtain ⟨r, hok, -, hv⟩ := LendingLedger.loanPay_pay h hat
  rw [hv]
  exact Loan.payment_vault_upper_bound_reachable_proof loan amount paymentType r l hr i hat payment hpay hok

/-- Proof body of `Lending.payment_vault_lower_bound`. -/
lemma LendingLedger.payment_vault_lower_bound_proof (l : LendingLedger) (hr : l.Reachable) (l' : LendingLedger)
    (i : Nat) (paymentType : LoanPaymentType) (amount : Number)
    (h : (l.apply (.loanPay i paymentType amount)).run = .ok (.ok l')) (loan : Loan) (hat : l.LoanAt i loan)
    (payment : UnsettledPayment Vault)
    (hpay : (loan.payInstalments l.vault paymentType amount l.now).run = .ok (.ok payment))
    (hpaid : payment.amounts.principalPaid.toRat + payment.amounts.interestPaid.toRat ≤
      10 ^ 16 * (10 : ℚ) ^ l.vault.baseExponent)
    (hfit : l.vault.assetsAvailable.toRat +
      (payment.amounts.principalPaid.toRat + payment.amounts.interestPaid.toRat) <
        2 ^ 63 * (10 : ℚ) ^ l.vault.baseExponent) :
    ∀ e, numberExponent l'.vault.assetsAvailable l.vault.baseExponent l.vault.numericType = .ok e →
      payment.amounts.principalPaid.toRat + payment.amounts.interestPaid.toRat -
        (l'.vault.assetsAvailable.toRat - l.vault.assetsAvailable.toRat) < 10 ^ e := by
  obtain ⟨r, hok, -, hv⟩ := LendingLedger.loanPay_pay h hat
  rw [hv]
  exact Loan.payment_vault_lower_bound_proof loan amount paymentType r l hr i hat payment hpay hok hpaid hfit

/-- A payment -> YieldUnrealized' = YieldUnrealized − (interestDue − interestDue'). -/
lemma LendingLedger.payment_yield_proof (l : LendingLedger) (hr : l.Reachable) (l' : LendingLedger) (i : Nat)
    (paymentType : LoanPaymentType) (amount : Number)
    (h : (l.apply (.loanPay i paymentType amount)).run = .ok (.ok l')) (loan loan' : Loan) (hat : l.LoanAt i loan)
    (hat' : l'.LoanAt i loan') :
    l'.vault.toExact.yieldUnrealized =
      l.vault.toExact.yieldUnrealized - (loan.toExact.interestDue - loan'.toExact.interestDue) := by
  obtain ⟨r, hok, rfl, hv⟩ := LendingLedger.loanPay_loans h hat hat'
  rw [hv]
  exact Loan.payment_yield_proof loan amount paymentType r l hr i hat hok (hr.pay_yield_lt hat hok)

/-- A payment -> PrincipalOutstanding, AssetsDeployed and DebtTotal each drop by principalPaid. -/
lemma LendingLedger.payment_principal_proof (l : LendingLedger) (hr : l.Reachable) (l' : LendingLedger) (i : Nat)
    (paymentType : LoanPaymentType) (amount : Number)
    (h : (l.apply (.loanPay i paymentType amount)).run = .ok (.ok l')) (loan loan' : Loan) (hat : l.LoanAt i loan)
    (hat' : l'.LoanAt i loan') (payment : UnsettledPayment Vault)
    (hpay : (loan.payInstalments l.vault paymentType amount l.now).run = .ok (.ok payment)) :
    loan.principalOutstanding.toRat - loan'.principalOutstanding.toRat = payment.amounts.principalPaid.toRat ∧
      l.vault.assetsDeployed.toRat - l'.vault.assetsDeployed.toRat = payment.amounts.principalPaid.toRat ∧
      loan.broker.debtTotal.toRat - loan'.broker.debtTotal.toRat = payment.amounts.principalPaid.toRat := by
  obtain ⟨r, hok, rfl, hv⟩ := LendingLedger.loanPay_loans h hat hat'
  rw [hv]
  exact Loan.payment_principal_proof loan amount paymentType r l hr i hat payment hpay hok

/-- Paying an impaired loan -> LossUnrealized' = LossUnrealized − PrincipalOutstanding. -/
lemma LendingLedger.payment_unimpairs_proof (l : LendingLedger) (hr : l.Reachable) (l' : LendingLedger) (i : Nat)
    (paymentType : LoanPaymentType) (amount : Number)
    (h : (l.apply (.loanPay i paymentType amount)).run = .ok (.ok l')) (loan : Loan) (hat : l.LoanAt i loan)
    (himp : loan.isImpaired = true) :
    l'.vault.toExact.lossUnrealized = l.vault.toExact.lossUnrealized - loan.toExact.principalOutstanding := by
  obtain ⟨r, hok, -, hv⟩ := LendingLedger.loanPay_pay h hat
  rw [hv]
  exact Loan.payment_unimpairs_proof loan amount paymentType r l hr i hat himp hok

/-- Proof body of `Lending.regularPayment_yield`. -/
lemma LendingLedger.regularPayment_yield_proof (l : LendingLedger) (hr : l.Reachable) (l' : LendingLedger) (i : Nat)
    (amount : Number) (h : (l.apply (.loanPay i .regular amount)).run = .ok (.ok l')) (loan : Loan)
    (hat : l.LoanAt i loan) (payment : UnsettledPayment Vault)
    (hpay : (loan.payInstalments l.vault .regular amount l.now).run = .ok (.ok payment)) :
    (l.vault.assetsAvailable.toRat + (payment.amounts.principalPaid.toRat + payment.amounts.interestPaid.toRat) <
        10 ^ 16 * (10 : ℚ) ^ l.vault.baseExponent →
      l'.vault.toExact.assetsTotal - l.vault.toExact.assetsTotal = payment.amounts.interestPaid.toRat) ∧
    l.vault.toExact.yieldUnrealized - l'.vault.toExact.yieldUnrealized = payment.amounts.interestPaid.toRat := by
  obtain ⟨r, hok, -, hv⟩ := LendingLedger.loanPay_pay h hat
  rw [hv]
  exact ⟨fun htotal => (Loan.regularPayment_yield_proof loan amount r l hr i hat payment hpay hok htotal
      hr.yield_lt).1, Loan.regularPayment_yieldUnrealized_proof loan amount r l hr i hat payment hpay hok hr.yield_lt⟩

end XRPL.Model.Lending
