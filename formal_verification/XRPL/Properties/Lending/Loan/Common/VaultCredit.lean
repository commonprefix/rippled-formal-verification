import XRPL.Properties.Lending.Loan.Common.PayLedgerFunds
import XRPL.Properties.Lending.Loan.Common.RegularPayoffSplit

/-! # What a regular payment credits the vault, read from the loan

A vault that is not coarsened gets exactly the principal and interest a payment pays. A regular payment takes them off
the loan's TotalValueOutstanding, together with the management fee it takes off ManagementFeeOutstanding. -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault (Vault)

/-- Proof body of `Lending.Reachable.payment_vault_credit`. -/
lemma LendingLedger.payment_vault_credit_proof (l : LendingLedger) (hr : l.Reachable) (l' : LendingLedger) (i : Nat)
    (paymentType : LoanPaymentType) (amount : Number)
    (h : (l.apply (.loanPay i paymentType amount)).run = .ok (.ok l')) (loan loan' : Loan) (hat : l.LoanAt i loan)
    (hat' : l'.LoanAt i loan') (payment : UnsettledPayment Vault)
    (hpay : (loan.payInstalments l.vault paymentType amount l.now).run = .ok (.ok payment))
    (r : LoanWithAmounts Vault) (hok : (loan.pay l.vault paymentType amount l.now).run = .ok (.ok r))
    (htotal : l.vault.assetsAvailable.toRat +
      (payment.amounts.principalPaid.toRat + payment.amounts.interestPaid.toRat) <
        10 ^ 16 * (10 : ℚ) ^ l.vault.baseExponent) :
    l'.vault.assetsAvailable.toRat - l.vault.assetsAvailable.toRat = r.amountToPool.toRat ∧
      (paymentType = .regular → r.amountToPool.toRat =
        (loan.totalValueOutstanding.toRat - loan'.totalValueOutstanding.toRat) -
          (loan.managementFeeOutstanding.toRat - loan'.managementFeeOutstanding.toRat)) := by
  refine ⟨LendingLedger.payment_vault_amountToPool_proof l hr l' i paymentType amount h loan hat payment hpay r hok
    htotal, fun hpt => ?_⟩
  subst hpt
  obtain ⟨r₂, hok₂, rfl, -⟩ := LendingLedger.loanPay_loans h hat hat'
  rw [hok] at hok₂
  obtain rfl := Except.ok.inj (Except.ok.inj hok₂)
  have hpool := Loan.pay_amountToPool_exact loan l hr i hat .regular amount payment r hpay hok htotal
  have hpp := (Loan.payment_principal_proof loan amount .regular r l hr i hat payment hpay hok).1
  have hip := Loan.regularPayment_interest loan l.vault amount l.now payment (hr.loanScale_range hat) hpay

  -- the paid loan keeps the outstanding amounts of the instalments
  obtain ⟨p, hp, hs⟩ := Loan.pay_ok loan l.vault .regular amount l.now r hok
  rw [hpay] at hp
  obtain rfl := Except.ok.inj (Except.ok.inj hp)
  obtain ⟨_, _, _, _, _, _, _, -, -, -, -, hloan, -, -⟩ := UnsettledPayment.settle_ok payment r hs
  have hraw := (RawLoan.to_lawful_ok hloan).1
  have hrl : r.loan'.toExact.interestDue = payment.loan.toExact.interestDue :=
    Loan.toExact_interestDue_congr (congrArg RawLoan.totalValueOutstanding hraw :)
      (congrArg RawLoan.principalOutstanding hraw :) (congrArg RawLoan.managementFeeOutstanding hraw :)

  -- interestDue is TotalValueOutstanding − PrincipalOutstanding − ManagementFeeOutstanding
  have hI : loan.toExact.interestDue = loan.totalValueOutstanding.toRat - loan.principalOutstanding.toRat -
      loan.managementFeeOutstanding.toRat := rfl
  have hI' : r.loan'.toExact.interestDue = r.loan'.totalValueOutstanding.toRat -
      r.loan'.principalOutstanding.toRat - r.loan'.managementFeeOutstanding.toRat := rfl
  rw [hpool]
  linarith

end XRPL.Model.Lending
