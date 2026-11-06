import XRPL.Properties.Lending.Ledger.Common.PaymentShareBound

/-! # What a payment credits the vault, also once it has coarsened

The vault floors the principal and interest a payment pays at the scale of AssetsAvailable'. While the payment is
at most `10^16` base units and AssetsAvailable plus it fits a `Number`, the credit falls short by less than one unit. -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault (Vault RawVault)

variable (loan : Loan) (amount : Number) (paymentType : LoanPaymentType) (r : LoanWithAmounts Vault)

/-- Proof body of `payment_vault_lower_bound`. -/
lemma Loan.payment_vault_lower_bound_proof (l : LendingLedger) (hr : l.Reachable) (i : Nat) (hat : l.LoanAt i loan)
    (payment : UnsettledPayment Vault)
    (hpay : (loan.payInstalments l.vault paymentType amount l.now).run = .ok (.ok payment))
    (hok : (loan.pay l.vault paymentType amount l.now).run = .ok (.ok r))
    (hpaid : payment.amounts.principalPaid.toRat + payment.amounts.interestPaid.toRat ≤
      10 ^ 16 * (10 : ℚ) ^ l.vault.baseExponent)
    (hfit : l.vault.assetsAvailable.toRat +
      (payment.amounts.principalPaid.toRat + payment.amounts.interestPaid.toRat) <
        2 ^ 63 * (10 : ℚ) ^ l.vault.baseExponent) :
    ∀ e, numberExponent r.pool'.assetsAvailable l.vault.baseExponent l.vault.numericType = .ok e →
      payment.amounts.principalPaid.toRat + payment.amounts.interestPaid.toRat -
        (r.pool'.assetsAvailable.toRat - l.vault.assetsAvailable.toRat) < 10 ^ e := by
  obtain ⟨-, -, h⟩ := LendingLedger.pay_credit_floor l hr i loan hat paymentType amount payment r hpay hok hpaid hfit
  intro e he
  have := h e he
  linarith

end XRPL.Model.Lending
