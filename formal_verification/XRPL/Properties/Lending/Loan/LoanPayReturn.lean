import XRPL.Properties.Lending.Loan.Common.GuardProofs
import XRPL.Properties.Lending.Loan.Common.PayExits
import XRPL.Properties.Lending.Loan.Common.Schedule

/-! # `LoanPay` exits

The exits of `canPay` and the four payments, in the order each runs its checks. A later exit
assumes the earlier checks passed. -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol

variable (loan : Loan) (paymentType : LoanPaymentType)

/-- The exits of `canPay`, in the order it runs its checks. Each line assumes the checks before it passed. -/
theorem Loan.canPay_exits :
    (loan.isPending = true → loan.canPay paymentType = .tecNO_PERMISSION) ∧
    (loan.isPending = false → loan.allowsOverpayment = false → loan.canPay .overpayment = .tecNO_PERMISSION) ∧
    (loan.isPending = false → (paymentType = .overpayment → loan.allowsOverpayment = true) →
      (loan.paymentRemaining = 0 ∨ loan.principalOutstanding = Number.zero) →
      loan.canPay paymentType = .tecKILLED) ∧
    (loan.isPending = false → (paymentType = .overpayment → loan.allowsOverpayment = true) →
      loan.paymentRemaining ≠ 0 → loan.principalOutstanding ≠ Number.zero →
      loan.canPay paymentType = .tesSUCCESS) :=
  ⟨Loan.canPay_pending_proof loan paymentType, Loan.canPay_overpayment_not_allowed_proof loan,
    Loan.canPay_paid_off_proof loan paymentType, Loan.canPay_success_proof loan paymentType⟩

/-- Error codes: success, tecNO_PERMISSION or tecKILLED. -/
theorem Loan.canPay_error_codes :
    loan.canPay paymentType = .tesSUCCESS ∨ loan.canPay paymentType = .tecNO_PERMISSION ∨
      loan.canPay paymentType = .tecKILLED :=
  Loan.canPay_error_codes_proof loan paymentType

/-- Success ⟺ the loan is active, not paid off, and allows overpayment when one is requested. -/
theorem Loan.canPay_lawful_iff :
    loan.canPay paymentType = .tesSUCCESS ↔
      loan.isPending = false ∧ (paymentType = .overpayment → loan.allowsOverpayment = true) ∧
        loan.paymentRemaining ≠ 0 ∧ loan.principalOutstanding ≠ Number.zero :=
  Loan.canPay_lawful_iff_proof loan paymentType

/-! ## The exits of the four payments -/

section Payments

open XRPL.Model.SingleAssetVault (Vault RawVault)

variable (v : Vault) (amount : Number) (now : UInt32)

/-- The exits of a payment, in the order the model runs them: the date checks, the unimpair and the amount check, then
the settlement shared by all four payment types. Each line assumes the checks before it passed. -/
theorem Loan.payment_exits (t : UInt32) (hreach : loan.Reachable t) :
    ((loan.paymentRemaining ≠ 0 → loan.principalOutstanding ≠ Number.zero → loan.nextPaymentDueDate < now →
      (loan.regularPayment v amount now).run = .ok (.error .tecEXPIRED)) ∧
    (loan.paymentRemaining ≠ 0 → loan.principalOutstanding ≠ Number.zero → loan.nextPaymentDueDate < now →
      (loan.fullPayment v amount now).run = .ok (.error .tecEXPIRED)) ∧
    (loan.paymentRemaining ≠ 0 → loan.principalOutstanding ≠ Number.zero → loan.nextPaymentDueDate < now →
      (loan.overpayment v amount now).run = .ok (.error .tecEXPIRED)) ∧
    (loan.paymentRemaining ≠ 0 → loan.principalOutstanding ≠ Number.zero → now ≤ loan.nextPaymentDueDate →
      (loan.latePayment v amount now).run = .ok (.error .tecTOO_SOON)) ∧
    (loan.principalOutstanding ≠ Number.zero → loan.paymentRemaining = 1 → now ≤ loan.nextPaymentDueDate →
      (loan.fullPayment v amount now).run = .ok (.error .tecKILLED)) ∧
    -- `lu'` - the new LossUnrealized, LossUnrealized − PrincipalOutstanding
    (∀ (paymentType : LoanPaymentType) (aa' ad' lu' ar' yu' : Number), loan.PayChecks paymentType now →
      loan.isImpaired = true →
      Vault.AdjustSums v { loss := loan.principalOutstanding.operator_neg } aa' ad' lu' ar' yu' → lu'.signum < 0 →
      (loan.pay v paymentType amount now).run = .ok (.error .tefBAD_LEDGER)) ∧
    -- `pc` - the first instalment the payment pays
    ∀ (paymentType : LoanPaymentType) (pc : PaymentComponents) (totalDue : Number), loan.PayChecks paymentType now →
      (loan.isImpaired = true → ∃ r, (loan.manageUnimpair v).run = .ok (.ok r)) →
      loan.paymentComponents paymentType now = .ok pc → pc.totalDue = .ok totalDue →
      amount.operator_lt totalDue = true →
      (loan.pay v paymentType amount now).run = .ok (.error .tecINSUFFICIENT_PAYMENT)) ∧
    -- the settlement
    (∀ payment : UnsettledPayment Vault, (loan.payInstalments v paymentType amount now).run = .ok (.ok payment) →
      (payment.amounts.principalPaid.signum < 0 ∨ payment.amounts.interestPaid.signum < 0 ∨
        payment.amounts.feePaid.signum < 0) →
      (loan.pay v paymentType amount now).run = .ok (.error .tecLIMIT_EXCEEDED)) ∧
    -- `ad'` - the new AssetsDeployed, AssetsDeployed − principalPaid
    (∀ (payment : UnsettledPayment Vault) (toPool yieldDelta toBroker cover' debtTotal' aa' ad' lu' ar' yu' : Number),
      (loan.payInstalments v paymentType amount now).run = .ok (.ok payment) →
      payment.SettleSums toPool yieldDelta toBroker cover' debtTotal' →
      Vault.AdjustSums payment.pool (payment.change toPool yieldDelta) aa' ad' lu' ar' yu' → ad'.signum < 0 →
      (loan.pay v paymentType amount now).run = .ok (.error .tefBAD_LEDGER)) ∧
    -- `yu'` - the new YieldUnrealized, YieldUnrealized + interestDue' − interestDue
    (∀ (payment : UnsettledPayment Vault) (toPool yieldDelta toBroker cover' debtTotal' aa' ad' lu' ar' yu' : Number),
      (loan.payInstalments v paymentType amount now).run = .ok (.ok payment) →
      payment.SettleSums toPool yieldDelta toBroker cover' debtTotal' →
      Vault.AdjustSums payment.pool (payment.change toPool yieldDelta) aa' ad' lu' ar' yu' → yu'.signum < 0 →
      (loan.pay v paymentType amount now).run = .ok (.error .tefBAD_LEDGER)) ∧
    -- `lu'` - the new LossUnrealized, `ad'` - the new AssetsDeployed, AssetsDeployed − principalPaid
    (∀ (payment : UnsettledPayment Vault) (toPool yieldDelta toBroker cover' debtTotal' aa' ad' lu' ar' yu' : Number),
      (loan.payInstalments v paymentType amount now).run = .ok (.ok payment) →
      payment.SettleSums toPool yieldDelta toBroker cover' debtTotal' →
      Vault.AdjustSums payment.pool (payment.change toPool yieldDelta) aa' ad' lu' ar' yu' →
      (0 ≤ aa'.signum ∧ 0 ≤ ad'.signum ∧ 0 ≤ lu'.signum ∧ 0 ≤ yu'.signum ∧ 0 ≤ ar'.signum) →
      lu'.operator_gt ad' = true →
      (loan.pay v paymentType amount now).run = .ok (.error .tecLIMIT_EXCEEDED)) ∧
    -- `raw` - the updated vault, `broker'` - the updated broker, `loan'` - the paid loan on the updated broker
    (∀ (payment : UnsettledPayment Vault) (toPool yieldDelta toBroker cover' debtTotal' : Number) (raw : RawVault)
        (v' : Vault) (broker' : LoanBroker) (loan' : Loan) (assetsTotal' : Number),
      (loan.payInstalments v paymentType amount now).run = .ok (.ok payment) →
      payment.SettleSums toPool yieldDelta toBroker cover' debtTotal' →
      (payment.pool.adjustBalances (payment.change toPool yieldDelta)).run = .ok (.ok raw) →
      raw.to_lawful = .ok v' →
      ({ payment.loan.broker.toRawLoanBroker with debtTotal := debtTotal', coverAvailable := cover' }
        : RawLoanBroker).to_lawful = .ok broker' →
      ({ payment.loan.toRawLoan with broker := broker' } : RawLoan).to_lawful = .ok loan' →
      v'.assetsTotal = .ok assetsTotal' →
      v'.assetsAvailable = payment.pool.assetsAvailable → payment.loan.paymentRemaining ≠ 0 →
      (loan.pay v paymentType amount now).run = .ok (.error .tecPRECISION_LOSS)) ∧
    (∀ (payment : UnsettledPayment Vault) (toPool yieldDelta toBroker cover' debtTotal' : Number) (raw : RawVault)
        (v' : Vault) (broker' : LoanBroker) (loan' : Loan) (assetsTotal' : Number),
      (loan.payInstalments v paymentType amount now).run = .ok (.ok payment) →
      payment.SettleSums toPool yieldDelta toBroker cover' debtTotal' →
      (payment.pool.adjustBalances (payment.change toPool yieldDelta)).run = .ok (.ok raw) →
      raw.to_lawful = .ok v' →
      ({ payment.loan.broker.toRawLoanBroker with debtTotal := debtTotal', coverAvailable := cover' }
        : RawLoanBroker).to_lawful = .ok broker' →
      ({ payment.loan.toRawLoan with broker := broker' } : RawLoan).to_lawful = .ok loan' →
      v'.assetsTotal = .ok assetsTotal' →
      payment.loan.paymentRemaining = 0 → v'.assetsAvailable = payment.pool.assetsAvailable →
      (loan.pay v paymentType amount now).run =
        .ok (.ok { loan' := loan', pool' := v', amountToPool := toPool, amountToBroker := toBroker })) ∧
    -- `toPool` - what the vault receives, `toBroker` - what the broker receives
    ∀ (payment : UnsettledPayment Vault) (toPool yieldDelta toBroker cover' debtTotal' : Number) (raw : RawVault)
        (v' : Vault) (broker' : LoanBroker) (loan' : Loan) (assetsTotal' : Number),
      (loan.payInstalments v paymentType amount now).run = .ok (.ok payment) →
      payment.SettleSums toPool yieldDelta toBroker cover' debtTotal' →
      (payment.pool.adjustBalances (payment.change toPool yieldDelta)).run = .ok (.ok raw) →
      raw.to_lawful = .ok v' →
      ({ payment.loan.broker.toRawLoanBroker with debtTotal := debtTotal', coverAvailable := cover' }
        : RawLoanBroker).to_lawful = .ok broker' →
      ({ payment.loan.toRawLoan with broker := broker' } : RawLoan).to_lawful = .ok loan' →
      v'.assetsTotal = .ok assetsTotal' →
      (v'.assetsAvailable ≠ payment.pool.assetsAvailable ∨ payment.loan.paymentRemaining = 0) →
      (loan.pay v paymentType amount now).run =
        .ok (.ok { loan' := loan', pool' := v', amountToPool := toPool, amountToBroker := toBroker }) :=
  have hdue := Loan.Reachable.nextPaymentDueDate_ne_zero loan t hreach
  ⟨⟨fun hr hpo hlate => Loan.regularPayment_late_proof loan v amount now hr hpo hdue hlate,
      fun hr hpo hlate => Loan.fullPayment_late_proof loan v amount now hr hpo hdue hlate,
      fun hr hpo hlate => Loan.overpayment_late_proof loan v amount now hr hpo hdue hlate,
      fun hr hpo hsoon => Loan.latePayment_too_soon_proof loan v amount now hr hpo hdue hsoon,
      fun hpo hone hsoon => Loan.fullPayment_last_proof loan v amount now hpo hdue hone hsoon,
      Loan.payment_impaired_bad_ledger_proof loan v amount now, Loan.payment_insufficient_proof loan v amount now⟩,
    ⟨Loan.payment_negative_part_proof loan v amount now paymentType,
      Loan.payment_deployed_bad_ledger_proof loan v amount now paymentType,
      Loan.payment_yield_bad_ledger_proof loan v amount now paymentType,
      Loan.payment_limit_exceeded_proof loan v amount now paymentType,
      Loan.payment_precision_loss_proof loan v amount now paymentType,
      Loan.finalPayment_zero_credit_proof loan v amount now paymentType,
      Loan.payment_success_proof loan v amount now paymentType⟩⟩

/-- The only rejections of the four payments: a regular payment or an overpayment and a late payment on a loan that
isn't paid off, and a full payment on any loan. -/
theorem Loan.payment_error_codes (ter : TER) (t : UInt32) (hreach : loan.Reachable t) :
    (loan.paymentRemaining ≠ 0 → loan.principalOutstanding ≠ Number.zero →
      ((loan.regularPayment v amount now).run = .ok (.error ter) ∨
        (loan.overpayment v amount now).run = .ok (.error ter)) →
      ter = .tecEXPIRED ∨ ter = .tecINSUFFICIENT_PAYMENT ∨ ter = .tecPRECISION_LOSS ∨ ter = .tecLIMIT_EXCEEDED ∨
        ter = .tefBAD_LEDGER) ∧
    (loan.paymentRemaining ≠ 0 → loan.principalOutstanding ≠ Number.zero →
      (loan.latePayment v amount now).run = .ok (.error ter) →
      ter = .tecTOO_SOON ∨ ter = .tecINSUFFICIENT_PAYMENT ∨ ter = .tecPRECISION_LOSS ∨ ter = .tecLIMIT_EXCEEDED ∨
        ter = .tefBAD_LEDGER) ∧
    ((loan.fullPayment v amount now).run = .ok (.error ter) →
      ter = .tecEXPIRED ∨ ter = .tecKILLED ∨ ter = .tecINSUFFICIENT_PAYMENT ∨ ter = .tecLIMIT_EXCEEDED ∨
        ter = .tefBAD_LEDGER) :=
  have hdue := Loan.Reachable.nextPaymentDueDate_ne_zero loan t hreach
  ⟨fun hr hpo h => h.elim (Loan.regularPayment_error_codes_proof loan v amount now ter hr hpo hdue)
      (Loan.overpayment_error_codes_proof loan v amount now ter hr hpo hdue),
    fun hr hpo => Loan.latePayment_error_codes_proof loan v amount now ter hr hpo hdue,
    Loan.fullPayment_error_codes_proof loan v amount now ter hdue⟩

end Payments

end XRPL.Model.Lending
