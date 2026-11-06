import XRPL.Properties.Lending.Loan.Common.PayDefs
import XRPL.Properties.Vault.Proofs.Support.DepositExchange

/-! # Proof bodies for the LoanPay exits

One proof per exit, in the order a payment runs its checks, then the error codes of each payment. -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault (Vault RawVault)

open private Loan.scheduledComponents Loan.lateComponents Loan.fullComponents Loan.unimpairIfImpaired
  Loan.payScheduledInstalments UnsettledPayment.applyOverpayment UnsettledPayment.payInstalments
  Loan.doPayment Loan.settlePayment Loan.paySingleInstalment validatePostPayment
  from XRPL.Model.Lending.Loan.LoanPay

/-- A lawful vault's computed total covers its available assets. -/
private lemma Vault.assetsAvailable_le_assetsTotal (v : Vault) (assetsTotal : Number)
    (h : v.assetsTotal = .ok assetsTotal) :
    v.assetsAvailable.toRat ≤ assetsTotal.toRat := by
  have hAA := v.wf.assetsAvailable_norm
  have hAD := v.wf.assetsDeployed_norm
  have hAA0 : 0 ≤ v.assetsAvailable.toRat := v.exact.assetsAvailable_nonneg
  have hAD0 : 0 ≤ v.assetsDeployed.toRat := v.exact.assetsDeployed_nonneg
  unfold RawVault.assetsTotal at h
  by_cases hd : v.assetsDeployed.mantissa_ = 0
  · -- nothing deployed: the total is the cash
    rw [Number.eq_zero_of_mantissa_zero _ hAD hd, Number.operator_add_zero_right] at h
    obtain rfl := Except.ok.inj h
    exact le_refl _
  by_cases ha : v.assetsAvailable.mantissa_ = 0
  · -- no cash
    rw [Number.toRat_eq_zero_of_mantissa_zero _ ha]
    have h' := h
    replace h' := Number.operator_add_ok_spec h'
    unfold Number.operator_addSpec at h'
    rw [Number.operator_eq_zero_false_of_mantissa_ne _ hd, if_neg Bool.false_ne_true,
      Number.eq_zero_of_mantissa_zero _ hAA ha, if_pos (by decide)] at h'
    obtain rfl := Except.ok.inj h'
    exact hAD0
  -- both nonzero and nonnegative: a same-sign sum, which never rounds below the cash
  have hna := Number.negative_false_of_nonneg _ hAA hAA0
  have hnd := Number.negative_false_of_nonneg _ hAD hAD0
  have hnz : ¬ v.assetsAvailable.operator_eq v.assetsDeployed.operator_neg = true := by
    simp [Number.operator_eq, Number.operator_neg, hd, hna, hnd]
  obtain ⟨_, _, _, _, _, hspec⟩ := operator_add_algorithmic_facts_same_sign_downward _ _ _ hAA hAD ha hd
    (by rw [hna, hnd]) hnz h
  obtain ⟨n, hlo, hval⟩ := operator_add_rounded_downward _ _ _ hAA hAD h hspec.result_mant_ne
  rw [hval]
  exact Number.lower_tight _ n hlo _ hAA (by linarith)

/-- The pool re-check of a vault: only the precision check can fire, AssetsAvailable' never passes
AssetsTotal'. -/
private lemma validatePostPayment_run (v : Vault) (r : LoanWithAmounts Vault) (assetsTotal' : Number)
    (hat : r.pool'.assetsTotal = .ok assetsTotal') :
    (validatePostPayment v r).run =
      if (!(r.pool'.assetsAvailable.operator_ne v.assetsAvailable) && r.loan'.paymentRemaining != 0) = true then
        .ok (.error .tecPRECISION_LOSS) else .ok (.ok r) := by
  have hgt : r.pool'.assetsAvailable.operator_gt assetsTotal' = false := by
    have hle := Vault.assetsAvailable_le_assetsTotal r.pool' assetsTotal' hat
    have hn := (Vault.assetsTotal_ge_deployed r.pool' assetsTotal' hat).1
    rw [Bool.eq_false_iff]
    intro hg
    rw [operator_gt_iff _ _ r.pool'.wf.assetsAvailable_norm hn] at hg
    linarith
  simp only [validatePostPayment]
  unfold_ter
  simp only [Vault.pool_amounts, Vault.pool_assetsTotal, hat, hgt]
  split <;> rfl

/-- The settlement rejects with the code of a rejected vault update. -/
lemma UnsettledPayment.SettleSums.rejected {payment : UnsettledPayment Vault}
    {toPool yieldDelta toBroker cover' debtTotal' : Number} (ter : TER)
    (hsums : payment.SettleSums toPool yieldDelta toBroker cover' debtTotal')
    (hrej : (payment.pool.adjustBalances (payment.change toPool yieldDelta)).run = .ok (.error ter)) :
    (Loan.settlePayment payment.loan payment.pool payment.amounts payment.scheduledInterest).run =
      .ok (.error ter) := by
  rw [hsums.run_eq]
  unfold_ter
  simp [Vault.poolAdjust_rejected _ _ _ hrej]

/-- The settlement once the vault, the broker and the loan pass their re-checks: only the precision
check is left. -/
lemma UnsettledPayment.SettleSums.settled {payment : UnsettledPayment Vault}
    {toPool yieldDelta toBroker cover' debtTotal' : Number} (raw : RawVault) (v' : Vault) (broker' : LoanBroker)
    (loan' : Loan) (assetsTotal' : Number)
    (hsums : payment.SettleSums toPool yieldDelta toBroker cover' debtTotal')
    (hadj : (payment.pool.adjustBalances (payment.change toPool yieldDelta)).run = .ok (.ok raw))
    (hv' : raw.to_lawful = .ok v')
    (hbroker : ({ payment.loan.broker.toRawLoanBroker with debtTotal := debtTotal', coverAvailable := cover' }
      : RawLoanBroker).to_lawful = .ok broker')
    (hloan : ({ payment.loan.toRawLoan with broker := broker' } : RawLoan).to_lawful = .ok loan')
    (hat : v'.assetsTotal = .ok assetsTotal') :
    (Loan.settlePayment payment.loan payment.pool payment.amounts payment.scheduledInterest).run =
      if (!(v'.assetsAvailable.operator_ne payment.pool.assetsAvailable) && payment.loan.paymentRemaining != 0) = true
      then .ok (.error .tecPRECISION_LOSS)
      else .ok (.ok { loan' := loan', pool' := v', amountToPool := toPool, amountToBroker := toBroker }) := by
  have hpr : loan'.paymentRemaining = payment.loan.paymentRemaining := by
    rw [(RawLoan.to_lawful_ok hloan).1]
  rw [hsums.run_eq]
  simp only at hbroker hloan
  unfold_ter
  simp only [Vault.poolAdjust_ok _ _ raw v' hadj hv', hbroker, hloan]
  rw [← hpr]
  exact validatePostPayment_run payment.pool _ assetsTotal' hat

variable (loan : Loan) (v : Vault) (amount : Number) (now : UInt32)

/-- Proof body of the late regular payment line of `Loan.payment_exits`. -/
lemma Loan.regularPayment_late_proof (hr : loan.paymentRemaining ≠ 0)
    (hpo : loan.principalOutstanding ≠ Number.zero) (hdue : loan.paymentRemaining ≠ 0 → loan.nextPaymentDueDate ≠ 0)
    (hlate : loan.nextPaymentDueDate < now) :
    (loan.regularPayment v amount now).run = .ok (.error .tecEXPIRED) := by
  simp only [Loan.regularPayment, Loan.payScheduledInstalments]
  unfold_ter
  simp [Loan.not_paid_off loan hr hpo, Loan.nextPaymentDueDate_ne_zero loan (hdue hr), Loan.isPaymentLate, hlate]

/-- Proof body of the late full payment line of `Loan.payment_exits`. -/
lemma Loan.fullPayment_late_proof (hr : loan.paymentRemaining ≠ 0)
    (hpo : loan.principalOutstanding ≠ Number.zero) (hdue : loan.paymentRemaining ≠ 0 → loan.nextPaymentDueDate ≠ 0)
    (hlate : loan.nextPaymentDueDate < now) :
    (loan.fullPayment v amount now).run = .ok (.error .tecEXPIRED) := by
  simp only [Loan.fullPayment]
  unfold_ter
  simp [Loan.not_paid_off loan hr hpo, Loan.nextPaymentDueDate_ne_zero loan (hdue hr), Loan.isPaymentLate, hlate]

/-- Proof body of the late overpayment line of `Loan.payment_exits`. -/
lemma Loan.overpayment_late_proof (hr : loan.paymentRemaining ≠ 0)
    (hpo : loan.principalOutstanding ≠ Number.zero) (hdue : loan.paymentRemaining ≠ 0 → loan.nextPaymentDueDate ≠ 0)
    (hlate : loan.nextPaymentDueDate < now) :
    (loan.overpayment v amount now).run = .ok (.error .tecEXPIRED) := by
  simp only [Loan.overpayment, Loan.payScheduledInstalments]
  unfold_ter
  simp [Loan.not_paid_off loan hr hpo, Loan.nextPaymentDueDate_ne_zero loan (hdue hr), Loan.isPaymentLate, hlate]

/-- Proof body of the too-soon line of `Loan.payment_exits`. -/
lemma Loan.latePayment_too_soon_proof (hr : loan.paymentRemaining ≠ 0)
    (hpo : loan.principalOutstanding ≠ Number.zero) (hdue : loan.paymentRemaining ≠ 0 → loan.nextPaymentDueDate ≠ 0)
    (hsoon : now ≤ loan.nextPaymentDueDate) :
    (loan.latePayment v amount now).run = .ok (.error .tecTOO_SOON) := by
  simp only [Loan.latePayment]
  unfold_ter
  simp [Loan.not_paid_off loan hr hpo, Loan.nextPaymentDueDate_ne_zero loan (hdue hr), Loan.isPaymentLate,
    UInt32.not_lt.mpr hsoon]

/-- Proof body of the last-instalment line of `Loan.payment_exits`. -/
lemma Loan.fullPayment_last_proof (hpo : loan.principalOutstanding ≠ Number.zero)
    (hdue : loan.paymentRemaining ≠ 0 → loan.nextPaymentDueDate ≠ 0)
    (hone : loan.paymentRemaining = 1) (hsoon : now ≤ loan.nextPaymentDueDate) :
    (loan.fullPayment v amount now).run = .ok (.error .tecKILLED) := by
  have hr : loan.paymentRemaining ≠ 0 := by rw [hone]; decide
  simp only [Loan.fullPayment]
  unfold_ter
  simp [Loan.principal_operator_eq_zero loan hpo, Loan.nextPaymentDueDate_ne_zero loan (hdue hr), Loan.isPaymentLate,
    UInt32.not_lt.mpr hsoon, hone]

/-! ## The unimpair and the amount check -/

variable (paymentType : LoanPaymentType)

/-- After the checks every payment unimpairs the loan, and a rejected unimpair rejects the payment. -/
private lemma Loan.pay_unimpair_rejected (ter : TER) (hchecks : loan.PayChecks paymentType now)
    (hrej : (Loan.unimpairIfImpaired loan v).run = .ok (.error ter)) :
    (loan.pay v paymentType amount now).run = .ok (.error ter) := by
  have hr := hchecks.remaining
  have hpo := hchecks.principal
  simp only [ExceptT.run] at hrej
  cases paymentType
  · have hnl := hchecks.not_late (by decide)
    simp only [Loan.pay, Loan.regularPayment, Loan.payScheduledInstalments]
    unfold_ter
    simp [Loan.not_paid_off loan hr hpo, Loan.nextPaymentDueDate_ne_zero loan hchecks.due, Loan.isPaymentLate, hnl,
      hrej]
  · have hl : loan.nextPaymentDueDate < now := hchecks.date.mp rfl
    simp only [Loan.pay, Loan.latePayment]
    unfold_ter
    simp [Loan.not_paid_off loan hr hpo, Loan.nextPaymentDueDate_ne_zero loan hchecks.due, Loan.isPaymentLate, hl, hrej]
  · have hnl := hchecks.not_late (by decide)
    simp only [Loan.pay, Loan.fullPayment]
    unfold_ter
    simp [Loan.not_paid_off loan hr hpo, Loan.nextPaymentDueDate_ne_zero loan hchecks.due, Loan.isPaymentLate, hnl,
      hchecks.more_than_one, hrej]
  · have hnl := hchecks.not_late (by decide)
    simp only [Loan.pay, Loan.overpayment, Loan.payScheduledInstalments]
    unfold_ter
    simp [Loan.not_paid_off loan hr hpo, Loan.nextPaymentDueDate_ne_zero loan hchecks.due, Loan.isPaymentLate, hnl,
      hrej]

/-- Proof body of the LossUnrealized tefBAD_LEDGER line of `Loan.payment_exits`. -/
lemma Loan.payment_impaired_bad_ledger_proof (aa' ad' lu' ar' yu' : Number)
    (hchecks : loan.PayChecks paymentType now) (himp : loan.isImpaired = true)
    (hs : Vault.AdjustSums v { loss := loan.principalOutstanding.operator_neg } aa' ad' lu' ar' yu')
    (hneg : lu'.signum < 0) :
    (loan.pay v paymentType amount now).run = .ok (.error .tefBAD_LEDGER) := by
  apply Loan.pay_unimpair_rejected loan v amount now paymentType _ hchecks
  rw [Loan.unimpairIfImpaired_impaired loan v himp, Vault.poolAdjust_rejected v _ _
    (Vault.adjustBalances_bad_ledger v _ aa' ad' lu' ar' yu' hs (Or.inr (Or.inr (Or.inl hneg))))]

/-- The instalment loop stops at once when the amount can't cover the next scheduled instalment. -/
private lemma payInstalments_stop {α : Type} (payment : UnsettledPayment α) (n : Nat) (amount due s : Number)
    (pc : PaymentComponents) (hr : payment.loan.paymentRemaining ≠ 0)
    (hpc : Loan.scheduledComponents payment.loan = .ok pc)
    (hdue : ({ pc with untrackedManagementFee := payment.loan.fees.serviceFee } : PaymentComponents).totalDue =
      .ok due)
    (hsum : payment.totalPaid.operator_add due .to_nearest = .ok s) (hlt : amount.operator_lt s = true) :
    UnsettledPayment.payInstalments payment (n + 1) amount = .ok payment := by
  rw [UnsettledPayment.payInstalments]
  simp [hr, hpc, hdue, hsum, hlt]

/-- Proof body of the insufficient-amount line of `Loan.payment_exits`. -/
lemma Loan.payment_insufficient_proof (pc : PaymentComponents) (totalDue : Number)
    (hchecks : loan.PayChecks paymentType now)
    (hunimpair : loan.isImpaired = true → ∃ r, (loan.manageUnimpair v).run = .ok (.ok r))
    (hpc : loan.paymentComponents paymentType now = .ok pc) (hdue : pc.totalDue = .ok totalDue)
    (hlt : amount.operator_lt totalDue = true) :
    (loan.pay v paymentType amount now).run = .ok (.error .tecINSUFFICIENT_PAYMENT) := by
  have hr := hchecks.remaining
  have hpo := hchecks.principal
  obtain ⟨v1, hu⟩ := Loan.unimpairIfImpaired_ok loan v hunimpair
  simp only [ExceptT.run] at hu
  obtain ⟨i, hi⟩ := Loan.interestDue_ok loan
  cases paymentType
  · have hnl := hchecks.not_late (by decide)
    simp only [Loan.paymentComponents, bind, Except.bind] at hpc
    rcases hsc : Loan.scheduledComponents loan with e | pc0 <;> rw [hsc] at hpc <;> simp only at hpc
    · exact absurd hpc (by simp)
    · obtain rfl := Except.ok.inj hpc
      have hstop := payInstalments_stop
        { loan := loan.unimpaired, pool := v1, amounts := PaymentAmounts.zero, totalPaid := Number.zero, count := 0,
          scheduledInterest := i } 99 amount totalDue totalDue pc0 hr hsc hdue (Number.operator_add_zero_left _ _) hlt
      simp only [Loan.pay, Loan.regularPayment, Loan.payScheduledInstalments]
      unfold_ter
      simp [Loan.not_paid_off loan hr hpo, Loan.nextPaymentDueDate_ne_zero loan hchecks.due, Loan.isPaymentLate, hnl,
        hu,
        Loan.interestDue_unimpaired, hi, maxPaymentsPerTransaction, hstop]
  · have hl : loan.nextPaymentDueDate < now := hchecks.date.mp rfl
    simp only [Loan.paymentComponents] at hpc
    simp only [Loan.pay, Loan.latePayment, Loan.paySingleInstalment]
    unfold_ter
    simp [Loan.not_paid_off loan hr hpo, Loan.nextPaymentDueDate_ne_zero loan hchecks.due, Loan.isPaymentLate, hl, hu,
      Loan.lateComponents_unimpaired, hpc, hdue, hlt]
  · have hnl := hchecks.not_late (by decide)
    simp only [Loan.paymentComponents] at hpc
    simp only [Loan.pay, Loan.fullPayment, Loan.paySingleInstalment]
    unfold_ter
    simp [Loan.not_paid_off loan hr hpo, Loan.nextPaymentDueDate_ne_zero loan hchecks.due, Loan.isPaymentLate, hnl,
      hchecks.more_than_one, hu, Loan.fullComponents_unimpaired, hpc, hdue, hlt]
  · have hnl := hchecks.not_late (by decide)
    simp only [Loan.paymentComponents, bind, Except.bind] at hpc
    rcases hsc : Loan.scheduledComponents loan with e | pc0 <;> rw [hsc] at hpc <;> simp only at hpc
    · exact absurd hpc (by simp)
    · obtain rfl := Except.ok.inj hpc
      have hstop := payInstalments_stop
        { loan := loan.unimpaired, pool := v1, amounts := PaymentAmounts.zero, totalPaid := Number.zero, count := 0,
          scheduledInterest := i } 99 amount totalDue totalDue pc0 hr hsc hdue (Number.operator_add_zero_left _ _) hlt
      simp only [Loan.pay, Loan.overpayment, Loan.payScheduledInstalments]
      unfold_ter
      simp [Loan.not_paid_off loan hr hpo, Loan.nextPaymentDueDate_ne_zero loan hchecks.due, Loan.isPaymentLate, hnl,
        hu,
        Loan.interestDue_unimpaired, hi, maxPaymentsPerTransaction, hstop]

/-! ## The settlement -/

variable (payment : UnsettledPayment Vault) (toPool yieldDelta toBroker cover' debtTotal' : Number)

/-- Proof body of the negative-part line of `Loan.settlePayment_exits`. -/
lemma Loan.payment_negative_part_proof
    (hpay : (loan.payInstalments v paymentType amount now).run = .ok (.ok payment))
    (hneg : payment.amounts.principalPaid.signum < 0 ∨ payment.amounts.interestPaid.signum < 0 ∨
      payment.amounts.feePaid.signum < 0) :
    (loan.pay v paymentType amount now).run = .ok (.error .tecLIMIT_EXCEEDED) := by
  rw [Loan.pay_settle loan v paymentType amount now payment hpay]
  have hb : (payment.amounts.principalPaid.signum < 0 || payment.amounts.interestPaid.signum < 0 ||
      payment.amounts.feePaid.signum < 0) = true := by
    rcases hneg with h | h | h <;> simp [h]
  simp only [Loan.settlePayment]
  unfold_ter
  simp [hb]

/-- Proof body of the AssetsDeployed tefBAD_LEDGER line of `Loan.settlePayment_exits`. -/
lemma Loan.payment_deployed_bad_ledger_proof (aa' ad' lu' ar' yu' : Number)
    (hpay : (loan.payInstalments v paymentType amount now).run = .ok (.ok payment))
    (hsums : payment.SettleSums toPool yieldDelta toBroker cover' debtTotal')
    (hs : Vault.AdjustSums payment.pool (payment.change toPool yieldDelta) aa' ad' lu' ar' yu')
    (hneg : ad'.signum < 0) :
    (loan.pay v paymentType amount now).run = .ok (.error .tefBAD_LEDGER) := by
  rw [Loan.pay_settle loan v paymentType amount now payment hpay]
  exact hsums.rejected _ (Vault.adjustBalances_bad_ledger _ _ aa' ad' lu' ar' yu' hs (Or.inr (Or.inl hneg)))

/-- Proof body of the YieldUnrealized tefBAD_LEDGER line of `Loan.settlePayment_exits`. -/
lemma Loan.payment_yield_bad_ledger_proof (aa' ad' lu' ar' yu' : Number)
    (hpay : (loan.payInstalments v paymentType amount now).run = .ok (.ok payment))
    (hsums : payment.SettleSums toPool yieldDelta toBroker cover' debtTotal')
    (hs : Vault.AdjustSums payment.pool (payment.change toPool yieldDelta) aa' ad' lu' ar' yu')
    (hneg : yu'.signum < 0) :
    (loan.pay v paymentType amount now).run = .ok (.error .tefBAD_LEDGER) := by
  rw [Loan.pay_settle loan v paymentType amount now payment hpay]
  exact hsums.rejected _ (Vault.adjustBalances_bad_ledger _ _ aa' ad' lu' ar' yu' hs
    (Or.inr (Or.inr (Or.inr (Or.inl hneg)))))

/-- Proof body of the LossUnrealized limit line of `Loan.settlePayment_exits`. -/
lemma Loan.payment_limit_exceeded_proof (aa' ad' lu' ar' yu' : Number)
    (hpay : (loan.payInstalments v paymentType amount now).run = .ok (.ok payment))
    (hsums : payment.SettleSums toPool yieldDelta toBroker cover' debtTotal')
    (hs : Vault.AdjustSums payment.pool (payment.change toPool yieldDelta) aa' ad' lu' ar' yu')
    (hnn : 0 ≤ aa'.signum ∧ 0 ≤ ad'.signum ∧ 0 ≤ lu'.signum ∧ 0 ≤ yu'.signum ∧ 0 ≤ ar'.signum)
    (hgt : lu'.operator_gt ad' = true) :
    (loan.pay v paymentType amount now).run = .ok (.error .tecLIMIT_EXCEEDED) := by
  rw [Loan.pay_settle loan v paymentType amount now payment hpay]
  exact hsums.rejected _ (Vault.adjustBalances_limit_exceeded _ _ aa' ad' lu' ar' yu' hs hnn hgt)

variable (raw : RawVault) (v' : Vault) (broker' : LoanBroker) (loan' : Loan) (assetsTotal' : Number)

/-- Proof body of the precision-loss line of `Loan.settlePayment_exits`. -/
lemma Loan.payment_precision_loss_proof
    (hpay : (loan.payInstalments v paymentType amount now).run = .ok (.ok payment))
    (hsums : payment.SettleSums toPool yieldDelta toBroker cover' debtTotal')
    (hadj : (payment.pool.adjustBalances (payment.change toPool yieldDelta)).run = .ok (.ok raw))
    (hv' : raw.to_lawful = .ok v')
    (hbroker : ({ payment.loan.broker.toRawLoanBroker with debtTotal := debtTotal', coverAvailable := cover' }
      : RawLoanBroker).to_lawful = .ok broker')
    (hloan : ({ payment.loan.toRawLoan with broker := broker' } : RawLoan).to_lawful = .ok loan')
    (hat : v'.assetsTotal = .ok assetsTotal')
    (hsame : v'.assetsAvailable = payment.pool.assetsAvailable) (hlast : payment.loan.paymentRemaining ≠ 0) :
    (loan.pay v paymentType amount now).run = .ok (.error .tecPRECISION_LOSS) := by
  rw [Loan.pay_settle loan v paymentType amount now payment hpay,
    hsums.settled raw v' broker' loan' assetsTotal' hadj hv' hbroker hloan hat,
    (Number.operator_ne_false_iff_eq' _ _).mpr hsame, if_pos (by simpa using hlast)]

/-- Proof body of the success line of `Loan.settlePayment_exits`. -/
lemma Loan.payment_success_proof
    (hpay : (loan.payInstalments v paymentType amount now).run = .ok (.ok payment))
    (hsums : payment.SettleSums toPool yieldDelta toBroker cover' debtTotal')
    (hadj : (payment.pool.adjustBalances (payment.change toPool yieldDelta)).run = .ok (.ok raw))
    (hv' : raw.to_lawful = .ok v')
    (hbroker : ({ payment.loan.broker.toRawLoanBroker with debtTotal := debtTotal', coverAvailable := cover' }
      : RawLoanBroker).to_lawful = .ok broker')
    (hloan : ({ payment.loan.toRawLoan with broker := broker' } : RawLoan).to_lawful = .ok loan')
    (hat : v'.assetsTotal = .ok assetsTotal')
    (hcredit : v'.assetsAvailable ≠ payment.pool.assetsAvailable ∨ payment.loan.paymentRemaining = 0) :
    (loan.pay v paymentType amount now).run =
      .ok (.ok { loan' := loan', pool' := v', amountToPool := toPool, amountToBroker := toBroker }) := by
  rw [Loan.pay_settle loan v paymentType amount now payment hpay,
    hsums.settled raw v' broker' loan' assetsTotal' hadj hv' hbroker hloan hat, if_neg]
  rcases hcredit with h | h
  · have hne : v'.assetsAvailable.operator_ne payment.pool.assetsAvailable = true := by
      cases hc : v'.assetsAvailable.operator_ne payment.pool.assetsAvailable
      · exact absurd ((Number.operator_ne_false_iff_eq' _ _).mp hc) h
      · rfl
    simp [hne]
  · simp [h]

/-- Proof body of the zero-credit final payment line of `Loan.settlePayment_exits`. -/
lemma Loan.finalPayment_zero_credit_proof
    (hpay : (loan.payInstalments v paymentType amount now).run = .ok (.ok payment))
    (hsums : payment.SettleSums toPool yieldDelta toBroker cover' debtTotal')
    (hadj : (payment.pool.adjustBalances (payment.change toPool yieldDelta)).run = .ok (.ok raw))
    (hv' : raw.to_lawful = .ok v')
    (hbroker : ({ payment.loan.broker.toRawLoanBroker with debtTotal := debtTotal', coverAvailable := cover' }
      : RawLoanBroker).to_lawful = .ok broker')
    (hloan : ({ payment.loan.toRawLoan with broker := broker' } : RawLoan).to_lawful = .ok loan')
    (hat : v'.assetsTotal = .ok assetsTotal')
    (hpaid : payment.loan.paymentRemaining = 0) (hsame : v'.assetsAvailable = payment.pool.assetsAvailable) :
    (loan.pay v paymentType amount now).run =
      .ok (.ok { loan' := loan', pool' := v', amountToPool := toPool, amountToBroker := toBroker }) := by
  rw [Loan.pay_settle loan v paymentType amount now payment hpay,
    hsums.settled raw v' broker' loan' assetsTotal' hadj hv' hbroker hloan hat,
    (Number.operator_ne_false_iff_eq' _ _).mpr hsame, hpaid]
  rfl

/-- A failing step fails the block with its code, or the step passes and the rest fails. -/
private lemma TerExcept.bind_error {α β : Type} (x : TerExcept α) (f : α → TerExcept β) (t : TER)
    (h : (x >>= f).run = .ok (.error t)) :
    x.run = .ok (.error t) ∨ ∃ a, x.run = .ok (.ok a) ∧ (f a).run = .ok (.error t) := by
  simp only [ExceptT.run, bind, ExceptT.bind, ExceptT.mk, ExceptT.bindCont, Except.bind] at h ⊢
  rcases hx : x with e | t' | a
  · rw [hx] at h; exact absurd h (by simp)
  · rw [hx] at h; left; simpa using h
  · rw [hx] at h; right; exact ⟨a, rfl, h⟩

/-- A vault update rejects only with tefBAD_LEDGER or tecLIMIT_EXCEEDED. -/
private lemma Vault.adjustBalances_codes (c : PoolBalanceChange) (t : TER)
    (h : (v.adjustBalances c).run = .ok (.error t)) : t = .tefBAD_LEDGER ∨ t = .tecLIMIT_EXCEEDED := by
  simp only [XRPL.Model.SingleAssetVault.Vault.adjustBalances] at h
  unfold_ter at h
  walk_ok
  all_goals simp

private lemma Vault.poolAdjust_codes (c : PoolBalanceChange) (t : TER)
    (h : AssetPool.adjustBalances v c = .ok (.error t)) : t = .tefBAD_LEDGER ∨ t = .tecLIMIT_EXCEEDED := by
  rw [Vault.pool_adjustBalances] at h
  unfold_ter at h
  rcases hadj : v.adjustBalances c with e | t' | raw <;> rw [hadj] at h
  · exact absurd h (by simp)
  · obtain rfl : t' = t := by injection h with h; injection h
    exact Vault.adjustBalances_codes v c t' (by simp only [ExceptT.run]; exact hadj)
  · simp only at h
    split at h <;> cases h

private lemma Loan.unimpairIfImpaired_codes (t : TER) (h : (Loan.unimpairIfImpaired loan v).run = .ok (.error t)) :
    t = .tefBAD_LEDGER ∨ t = .tecLIMIT_EXCEEDED := by
  cases himp : loan.isImpaired
  · rw [Loan.unimpairIfImpaired_not loan v himp] at h; exact absurd h (by simp)
  · rw [Loan.unimpairIfImpaired_impaired loan v himp] at h
    rcases hadj : AssetPool.adjustBalances v { loss := loan.principalOutstanding.operator_neg } with e | t' | v1 <;>
      rw [hadj] at h <;> simp only at h
    · exact absurd h (by simp)
    · obtain rfl : t' = t := by injection h with h; injection h
      exact Vault.poolAdjust_codes v _ t' hadj
    · exact absurd h (by simp)

/-- The pool re-check of a vault rejects only for precision, and only before the last payment. -/
private lemma validatePostPayment_codes (r : LoanWithAmounts Vault) (t : TER)
    (h : (validatePostPayment v r).run = .ok (.error t)) :
    t = .tecPRECISION_LOSS ∧ r.loan'.paymentRemaining ≠ 0 := by
  cases hat : r.pool'.assetsTotal with
  | error e =>
    simp only [validatePostPayment] at h
    unfold_ter at h
    simp only [Vault.pool_assetsTotal, hat] at h
    cases h
  | ok assetsTotal' =>
    rw [validatePostPayment_run v r assetsTotal' hat] at h
    split at h
    · rename_i hc
      obtain rfl : TER.tecPRECISION_LOSS = t := by injection h with h; injection h
      simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at hc
      exact ⟨rfl, hc.2⟩
    · cases h

/-- The settlement rejects only for a negative part, from the vault update, or for precision before the last
payment. -/
private lemma Loan.settle_codes (l : Loan) (amounts : PaymentAmounts) (si : Number) (t : TER)
    (h : (Loan.settlePayment l v amounts si).run = .ok (.error t)) :
    t = .tefBAD_LEDGER ∨ t = .tecLIMIT_EXCEEDED ∨ (t = .tecPRECISION_LOSS ∧ l.paymentRemaining ≠ 0) := by
  simp only [Loan.settlePayment] at h
  unfold_ter at h
  walk_ok
  all_goals first
    | exact Or.inr (Or.inl rfl)
    | exact (Vault.poolAdjust_codes v _ t ‹_›).elim Or.inl (fun h => Or.inr (Or.inl h))
    | (obtain ⟨rfl, hne⟩ := validatePostPayment_codes v _ t ‹_›
       refine Or.inr (Or.inr ⟨rfl, ?_⟩)
       have hpr := congrArg RawLoan.paymentRemaining (RawLoan.to_lawful_ok ‹RawLoan.to_lawful _ = Except.ok _›).1
       simp only at hne hpr
       rwa [hpr] at hne)

/-- The scheduled instalments reject a paid-off loan, a late loan, a rejected unimpair, or an amount
that covers no instalment. -/
private lemma Loan.payScheduled_codes (t : TER)
    (hdue : loan.paymentRemaining ≠ 0 → loan.nextPaymentDueDate ≠ 0)
    (h : (Loan.payScheduledInstalments loan v amount now).run = .ok (.error t)) :
    (t = .tecKILLED ∧ (loan.paymentRemaining = 0 ∨ loan.principalOutstanding = Number.zero)) ∨
      (t = .tecEXPIRED ∧ loan.nextPaymentDueDate < now) ∨ t = .tefBAD_LEDGER ∨ t = .tecLIMIT_EXCEEDED ∨
      t = .tecINSUFFICIENT_PAYMENT := by
  simp only [Loan.payScheduledInstalments] at h
  unfold_ter at h
  walk_ok
  · exact Or.inl ⟨rfl, (Loan.paid_off_iff loan).mp ‹_›⟩
  · exact absurd ‹_› (Loan.due_date_set loan hdue ‹_›)
  · exact Or.inr (Or.inl ⟨rfl, by simpa [Loan.isPaymentLate] using ‹loan.isPaymentLate now = true›⟩)
  · simp
  · rcases Loan.unimpairIfImpaired_codes loan v t (by simp only [ExceptT.run]; assumption) with h | h <;> simp [h]

private lemma Loan.payInstalment_codes {α : Type} [AssetPool α] (l : Loan) (pool : α) (pc : PaymentComponents)
    (t : TER) (h : (l.payInstalment pool pc amount).run = .ok (.error t)) : t = .tecINSUFFICIENT_PAYMENT := by
  simp only [Loan.payInstalment] at h
  unfold_ter at h
  walk_ok
  rfl

private lemma Loan.latePayInstalments_codes (t : TER)
    (hdue : loan.paymentRemaining ≠ 0 → loan.nextPaymentDueDate ≠ 0)
    (h : (loan.payInstalments v .late amount now).run = .ok (.error t)) :
    (t = .tecKILLED ∧ (loan.paymentRemaining = 0 ∨ loan.principalOutstanding = Number.zero)) ∨
      (t = .tecTOO_SOON ∧ now ≤ loan.nextPaymentDueDate) ∨ t = .tefBAD_LEDGER ∨ t = .tecLIMIT_EXCEEDED ∨
      t = .tecINSUFFICIENT_PAYMENT := by
  simp only [Loan.payInstalments] at h
  unfold_ter at h
  walk_ok
  · exact Or.inl ⟨rfl, (Loan.paid_off_iff loan).mp ‹_›⟩
  · exact absurd ‹_› (Loan.due_date_set loan hdue ‹_›)
  · refine Or.inr (Or.inl ⟨rfl, ?_⟩)
    have h := ‹(!loan.isPaymentLate now) = true›
    simp only [Loan.isPaymentLate, Bool.not_eq_true', decide_eq_false_iff_not] at h
    exact UInt32.not_lt.mp h
  · simp [Loan.payInstalment_codes amount _ _ _ t ‹_›]
  · rcases Loan.unimpairIfImpaired_codes loan v t (by simp only [ExceptT.run]; assumption) with h | h <;> simp [h]

private lemma Loan.fullPayInstalments_codes (t : TER)
    (hdue : loan.paymentRemaining ≠ 0 → loan.nextPaymentDueDate ≠ 0)
    (h : (loan.payInstalments v .full amount now).run = .ok (.error t)) :
    (t = .tecKILLED ∧ (loan.paymentRemaining = 0 ∨ loan.principalOutstanding = Number.zero ∨
      loan.paymentRemaining = 1)) ∨
      (t = .tecEXPIRED ∧ loan.nextPaymentDueDate < now) ∨ t = .tefBAD_LEDGER ∨ t = .tecLIMIT_EXCEEDED ∨
      t = .tecINSUFFICIENT_PAYMENT := by
  simp only [Loan.payInstalments] at h
  unfold_ter at h
  walk_ok
  · exact Or.inl ⟨rfl, by rcases (Loan.paid_off_iff loan).mp ‹_› with h | h <;> simp [h]⟩
  · exact absurd ‹_› (Loan.due_date_set loan hdue ‹_›)
  · exact Or.inr (Or.inl ⟨rfl, by simpa [Loan.isPaymentLate] using ‹loan.isPaymentLate now = true›⟩)
  · refine Or.inl ⟨rfl, Or.inr (Or.inr ?_)⟩
    have hr : loan.paymentRemaining ≠ 0 := fun h0 =>
      ‹¬(loan.paymentRemaining == 0 || loan.principalOutstanding.operator_eq Number.zero) = true›
        ((Loan.paid_off_iff loan).mpr (Or.inl h0))
    have hle := ‹loan.paymentRemaining ≤ 1›
    rw [UInt32.le_iff_toNat_le] at hle
    have h0 : loan.paymentRemaining.toNat ≠ 0 := fun h0 => hr (UInt32.toNat_inj.mp (by simpa using h0))
    apply UInt32.toNat_inj.mp
    simp at hle ⊢; omega
  · simp [Loan.payInstalment_codes amount _ _ _ t ‹_›]
  · rcases Loan.unimpairIfImpaired_codes loan v t (by simp only [ExceptT.run]; assumption) with h | h <;> simp [h]

private lemma Loan.overPayInstalments_codes (t : TER)
    (h : (loan.payInstalments v .overpayment amount now).run = .ok (.error t)) :
    (Loan.payScheduledInstalments loan v amount now).run = .ok (.error t) := by
  simp only [Loan.payInstalments] at h
  rcases TerExcept.bind_error _ _ t h with h1 | ⟨p, -, h2⟩
  · exact h1
  · simp only [ExceptT.run, liftM, monadLift, MonadLift.monadLift, MonadLiftT.monadLift, ExceptT.lift, ExceptT.mk,
      Functor.map, Except.map] at h2
    split at h2 <;> cases h2

private lemma Loan.fullComponents_final (l : Loan) (pc : PaymentComponents) (h : Loan.fullComponents l now = .ok pc) :
    pc.isFinal = true := by
  simp only [Loan.fullComponents] at h
  unfold_ter at h
  walk_ok
  rfl

/-- The final instalment leaves no payments. -/
lemma Loan.doPayment_final (l l' : Loan) (pc : PaymentComponents) (hf : pc.isFinal = true)
    (h : Loan.doPayment l pc = .ok l') : l'.paymentRemaining = 0 := by
  simp only [Loan.doPayment, hf, ↓reduceIte] at h
  unfold_ter at h
  walk_ok
  exact congrArg RawLoan.paymentRemaining (RawLoan.to_lawful_ok ‹_›).1

/-- A full payment pays the loan off. -/
lemma Loan.fullPayInstalments_paid (payment : UnsettledPayment Vault)
    (h : (loan.payInstalments v .full amount now).run = .ok (.ok payment)) : payment.loan.paymentRemaining = 0 := by
  simp only [Loan.payInstalments, Loan.payInstalment] at h
  unfold_ter at h
  walk_ok
  exact Loan.doPayment_final _ _ _ (Loan.fullComponents_final now _ _ ‹_›) ‹_›

/-- Every code a payment returns, with the situation it comes from. tecINTERNAL never comes on a loan with a
due date, and AssetsAvailable' never passes AssetsTotal'. -/
lemma Loan.pay_codes (t : TER) (hdue : loan.paymentRemaining ≠ 0 → loan.nextPaymentDueDate ≠ 0)
    (h : (loan.pay v paymentType amount now).run = .ok (.error t)) :
    (t = .tecKILLED ∧ (loan.paymentRemaining = 0 ∨ loan.principalOutstanding = Number.zero ∨
        (paymentType = .full ∧ loan.paymentRemaining = 1))) ∨
      (t = .tecEXPIRED ∧ paymentType ≠ .late ∧ loan.nextPaymentDueDate < now) ∨
      (t = .tecTOO_SOON ∧ paymentType = .late ∧ now ≤ loan.nextPaymentDueDate) ∨
      t = .tefBAD_LEDGER ∨ t = .tecLIMIT_EXCEEDED ∨ t = .tecINSUFFICIENT_PAYMENT ∨
      (t = .tecPRECISION_LOSS ∧ paymentType ≠ .full) := by
  rw [Loan.pay_run] at h
  rcases TerExcept.bind_error _ _ t h with h1 | ⟨p, hp, h2⟩
  · cases paymentType
    · rcases Loan.payScheduled_codes loan v amount now t hdue h1 with ⟨rfl, h'⟩ | ⟨rfl, h'⟩ | rfl | rfl | rfl
      · exact Or.inl ⟨rfl, by tauto⟩
      · exact Or.inr (Or.inl ⟨rfl, by decide, h'⟩)
      all_goals simp
    · rcases Loan.latePayInstalments_codes loan v amount now t hdue h1 with ⟨rfl, h'⟩ | ⟨rfl, h'⟩ | rfl | rfl | rfl
      · exact Or.inl ⟨rfl, by tauto⟩
      · exact Or.inr (Or.inr (Or.inl ⟨rfl, rfl, h'⟩))
      all_goals simp
    · rcases Loan.fullPayInstalments_codes loan v amount now t hdue h1 with ⟨rfl, h'⟩ | ⟨rfl, h'⟩ | rfl | rfl | rfl
      · exact Or.inl ⟨rfl, by tauto⟩
      · exact Or.inr (Or.inl ⟨rfl, by decide, h'⟩)
      all_goals simp
    · rcases Loan.payScheduled_codes loan v amount now t hdue (Loan.overPayInstalments_codes loan v amount now t h1)
        with
        ⟨rfl, h'⟩ | ⟨rfl, h'⟩ | rfl | rfl | rfl
      · exact Or.inl ⟨rfl, by tauto⟩
      · exact Or.inr (Or.inl ⟨rfl, by decide, h'⟩)
      all_goals simp
  · rcases Loan.settle_codes p.pool p.loan p.amounts p.scheduledInterest t h2 with rfl | rfl | ⟨rfl, hpr⟩
    · simp
    · simp
    · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, ?_⟩)))))
      rintro rfl
      exact hpr (Loan.fullPayInstalments_paid loan v amount now p hp)

/-- Proof body of the regular payment part of `payment_error_codes`. -/
lemma Loan.regularPayment_error_codes_proof (ter : TER) (hr : loan.paymentRemaining ≠ 0)
    (hpo : loan.principalOutstanding ≠ Number.zero) (hdue : loan.paymentRemaining ≠ 0 → loan.nextPaymentDueDate ≠ 0)
    (h : (loan.regularPayment v amount now).run = .ok (.error ter)) :
    ter = .tecEXPIRED ∨ ter = .tecINSUFFICIENT_PAYMENT ∨ ter = .tecPRECISION_LOSS ∨ ter = .tecLIMIT_EXCEEDED ∨
      ter = .tefBAD_LEDGER := by
  rcases Loan.pay_codes loan v amount now .regular ter hdue h with
    ⟨-, h'⟩ | ⟨rfl, -⟩ | ⟨-, h', -⟩ | rfl | rfl | rfl | ⟨rfl, -⟩
  · rcases h' with h' | h' | ⟨h', -⟩
    · exact absurd h' hr
    · exact absurd h' hpo
    · exact absurd h' (by decide)
  · simp
  · exact absurd h' (by decide)
  all_goals simp

/-- Proof body of the overpayment part of `payment_error_codes`. -/
lemma Loan.overpayment_error_codes_proof (ter : TER) (hr : loan.paymentRemaining ≠ 0)
    (hpo : loan.principalOutstanding ≠ Number.zero) (hdue : loan.paymentRemaining ≠ 0 → loan.nextPaymentDueDate ≠ 0)
    (h : (loan.overpayment v amount now).run = .ok (.error ter)) :
    ter = .tecEXPIRED ∨ ter = .tecINSUFFICIENT_PAYMENT ∨ ter = .tecPRECISION_LOSS ∨ ter = .tecLIMIT_EXCEEDED ∨
      ter = .tefBAD_LEDGER := by
  rcases Loan.pay_codes loan v amount now .overpayment ter hdue h with
    ⟨-, h'⟩ | ⟨rfl, -⟩ | ⟨-, h', -⟩ | rfl | rfl | rfl | ⟨rfl, -⟩
  · rcases h' with h' | h' | ⟨h', -⟩
    · exact absurd h' hr
    · exact absurd h' hpo
    · exact absurd h' (by decide)
  · simp
  · exact absurd h' (by decide)
  all_goals simp

/-- Proof body of the late payment line of `payment_error_codes`. -/
lemma Loan.latePayment_error_codes_proof (ter : TER) (hr : loan.paymentRemaining ≠ 0)
    (hpo : loan.principalOutstanding ≠ Number.zero) (hdue : loan.paymentRemaining ≠ 0 → loan.nextPaymentDueDate ≠ 0)
    (h : (loan.latePayment v amount now).run = .ok (.error ter)) :
    ter = .tecTOO_SOON ∨ ter = .tecINSUFFICIENT_PAYMENT ∨ ter = .tecPRECISION_LOSS ∨ ter = .tecLIMIT_EXCEEDED ∨
      ter = .tefBAD_LEDGER := by
  rcases Loan.pay_codes loan v amount now .late ter hdue h with
    ⟨-, h'⟩ | ⟨-, h', -⟩ | ⟨rfl, -⟩ | rfl | rfl | rfl | ⟨rfl, -⟩
  · rcases h' with h' | h' | ⟨h', -⟩
    · exact absurd h' hr
    · exact absurd h' hpo
    · exact absurd h' (by decide)
  · exact absurd rfl h'
  all_goals simp

/-- Proof body of the full payment line of `payment_error_codes`. -/
lemma Loan.fullPayment_error_codes_proof (ter : TER) (hdue : loan.paymentRemaining ≠ 0 → loan.nextPaymentDueDate ≠ 0)
    (h : (loan.fullPayment v amount now).run = .ok (.error ter)) :
    ter = .tecEXPIRED ∨ ter = .tecKILLED ∨ ter = .tecINSUFFICIENT_PAYMENT ∨ ter = .tecLIMIT_EXCEEDED ∨
      ter = .tefBAD_LEDGER := by
  rcases Loan.pay_codes loan v amount now .full ter hdue h with
    ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨-, h', -⟩ | rfl | rfl | rfl | ⟨-, h'⟩
  · simp
  · simp
  · exact absurd h' (by decide)
  · simp
  · simp
  · simp
  · exact absurd rfl h'

end XRPL.Model.Lending
