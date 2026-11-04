import XRPL.Properties.Lending.Loan.Common.PayLedger
import XRPL.Properties.Lending.Loan.Common.PayProofs
import XRPL.Properties.Lending.Loan.Common.OverpaymentReduces
import XRPL.Properties.Lending.Loan.Common.OverpaymentDrop
import XRPL.Properties.Lending.Loan.Common.ValueDecrease

/-! # What a LoanPay transaction does to the loan

Proof bodies of the LoanPay headlines about the loan: how many instalments a payment pays, when it closes the loan,
what an overpayment adds, and which payment type the close time allows. -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault (Vault)

/-- Proof body of `Lending.payment_lateness`. -/
lemma LendingLedger.payment_lateness_proof (l : LendingLedger) (hr : l.Reachable) (i : Nat) (amount : Number)
    (loan : Loan) (hat : l.LoanAt i loan) (hc : loan.canPay .regular = .tesSUCCESS)
    (hpre : (LendingTx.loanPay i .regular amount).preflight l = .tesSUCCESS) :
    (l.now ≤ loan.nextPaymentDueDate →
      (l.apply (.loanPay i .regular amount)).run ≠ .ok (.error .tecEXPIRED) ∧
        (l.apply (.loanPay i .full amount)).run ≠ .ok (.error .tecEXPIRED) ∧
        (l.apply (.loanPay i .overpayment amount)).run ≠ .ok (.error .tecEXPIRED) ∧
        (l.apply (.loanPay i .late amount)).run = .ok (.error .tecTOO_SOON)) ∧
    (loan.nextPaymentDueDate < l.now →
      (l.apply (.loanPay i .regular amount)).run = .ok (.error .tecEXPIRED) ∧
        (l.apply (.loanPay i .full amount)).run = .ok (.error .tecEXPIRED) ∧
        (loan.allowsOverpayment = true →
          (l.apply (.loanPay i .overpayment amount)).run = .ok (.error .tecEXPIRED)) ∧
        (l.apply (.loanPay i .late amount)).run ≠ .ok (.error .tecTOO_SOON)) := by
  obtain ⟨t, -, hreach⟩ := hr.loanAt_reachable hat
  obtain ⟨hpend, hpr, hpo⟩ := Loan.canPay_active hc
  have hm := Loan.payment_lateness_proof loan l.vault amount l.now hpr hpo
    (Loan.Reachable.nextPaymentDueDate_ne_zero loan t hreach)
  obtain ⟨e, b, he, hb, hw⟩ := hat
  have hnd := hr.live_of_loan he
  -- the preflight reads only the amount, and `canPay` the payment type only for an overpayment
  have hrun : ∀ pt, pt ≠ .overpayment → ∀ x, (l.apply (.loanPay i pt amount)).run = .ok (.error x) ↔
      (loan.pay l.vault pt amount l.now).run = .ok (.error x) := fun pt hpt x => by
    have hpre' : (LendingTx.loanPay i pt amount).preflight l = .tesSUCCESS := hpre
    rw [LendingLedger.apply_loanPay_eq he hb hw hpre' hnd (by rw [Loan.canPay_eq_regular loan hpt, hc])]
    exact TerExcept.run_map_error _ _ x
  have hover : loan.allowsOverpayment = true → ∀ x, (l.apply (.loanPay i .overpayment amount)).run =
      .ok (.error x) ↔ (loan.overpayment l.vault amount l.now).run = .ok (.error x) := fun ha x => by
    have hco : loan.canPay .overpayment = .tesSUCCESS := by
      unfold Loan.canPay; simp [hpend, ha, hpr, hpo, Number.operator_eq_iff_eq]
    have hpre' : (LendingTx.loanPay i .overpayment amount).preflight l = .tesSUCCESS := hpre
    rw [LendingLedger.apply_loanPay_eq he hb hw hpre' hnd hco]
    exact TerExcept.run_map_error _ _ x
  have hno : loan.allowsOverpayment = false →
      (l.apply (.loanPay i .overpayment amount)).run = .ok (.error .tecNO_PERMISSION) := fun ha => by
    have hpre' : (LendingTx.loanPay i .overpayment amount).preflight l = .tesSUCCESS := hpre
    rw [LendingLedger.apply_loanPay_run he hb hw hpre' hnd]
    have hco : loan.canPay .overpayment = .tecNO_PERMISSION := by unfold Loan.canPay; simp [hpend, ha]
    rw [hco]
    rfl
  refine ⟨fun hnl => ?_, fun hl => ?_⟩
  · obtain ⟨h1, h2, h3, h4⟩ := hm.1 hnl
    refine ⟨(hrun .regular (by decide) _).not.mpr h1, (hrun .full (by decide) _).not.mpr h2, ?_,
      (hrun .late (by decide) _).mpr h4⟩
    cases ha : loan.allowsOverpayment
    · rw [hno ha]; simp
    · exact (hover ha _).not.mpr h3
  · obtain ⟨h1, h2, h3, h4⟩ := hm.2 hl
    exact ⟨(hrun .regular (by decide) _).mpr h1, (hrun .full (by decide) _).mpr h2, fun ha => (hover ha _).mpr h3,
      (hrun .late (by decide) _).not.mpr h4⟩

/-- Proof body of `Lending.payment_decreases`. -/
lemma LendingLedger.payment_decreases_proof (l : LendingLedger) (hr : l.Reachable) (l' : LendingLedger) (i : Nat)
    (paymentType : LoanPaymentType) (amount : Number)
    (h : (l.apply (.loanPay i paymentType amount)).run = .ok (.ok l')) (loan loan' : Loan) (hat : l.LoanAt i loan)
    (hat' : l'.LoanAt i loan')
    (hlate : paymentType = .late → ∀ pc, loan.paymentComponents .late l.now = .ok pc → pc.isFinal = false →
      0 < pc.totalValueDelta.toRat) :
    loan'.paymentRemaining < loan.paymentRemaining ∧
      loan'.totalValueOutstanding.toRat < loan.totalValueOutstanding.toRat := by
  obtain ⟨r, hok, rfl, -⟩ := LendingLedger.loanPay_loans h hat hat'
  exact Loan.payment_decreases_proof l hr i loan hat paymentType amount r hok hlate

/-- Proof body of the count part of `Lending.regularPayment_schedule`. -/
lemma LendingLedger.regularPayment_count_proof (l l' : LendingLedger) (i : Nat) (amount : Number)
    (h : (l.apply (.loanPay i .regular amount)).run = .ok (.ok l')) (loan : Loan) (hat : l.LoanAt i loan)
    (payment : UnsettledPayment Vault)
    (hpay : (loan.payInstalments l.vault .regular amount l.now).run = .ok (.ok payment)) :
    1 ≤ payment.count ∧ payment.count ≤ min 100 loan.paymentRemaining.toNat ∧
      amount.operator_lt payment.totalPaid = false ∧
      (payment.count = 100 ∨ payment.loan.paymentRemaining = 0 ∨
        ∀ pc due s, payment.loan.paymentComponents .regular l.now = .ok pc → pc.totalDue = .ok due →
          payment.totalPaid.operator_add due .to_nearest = .ok s → amount.operator_lt s = true) := by
  obtain ⟨q, hq, rfl⟩ := LendingLedger.loanPay_instalments_eq h hat hpay
  exact Loan.regularPayment_count_proof loan l.vault amount l.now q hq

/-- Proof body of the final-payment part of `Lending.regularPayment_schedule`. -/
lemma LendingLedger.regularPayment_final_proof (l l' : LendingLedger) (i : Nat) (amount : Number)
    (h : (l.apply (.loanPay i .regular amount)).run = .ok (.ok l')) (loan loan' : Loan) (hat : l.LoanAt i loan)
    (hat' : l'.LoanAt i loan') (pc : PaymentComponents) (pp' : Number)
    (hpp : STAmount.roundToNumericType loan.broker.numericType loan.periodicPayment .upward (some loan.loanScale) =
      .ok pp')
    (hfinal : loan.paymentRemaining = 1 ∨ loan.totalValueOutstanding.operator_le pp' = true)
    (hpc : loan.paymentComponents .regular l.now = .ok pc) :
    pc.totalValueDelta = loan.totalValueOutstanding ∧ loan'.paymentRemaining = 0 := by
  obtain ⟨r, hok, rfl, -⟩ := LendingLedger.loanPay_loans h hat hat'
  have hf := Loan.regularPayment_final_proof loan l.vault amount l.now pc pp' hpp hfinal hpc
  exact ⟨hf.1, hf.2 r hok⟩

/-- Proof body of `Lending.latePayment_single`. -/
lemma LendingLedger.latePayment_single_proof (l l₁ l₂ : LendingLedger) (i : Nat) (a₁ a₂ : Number)
    (h₁ : (l.apply (.loanPay i .late a₁)).run = .ok (.ok l₁)) (h₂ : (l.apply (.loanPay i .late a₂)).run = .ok (.ok l₂))
    (loan loan₁ : Loan) (hat : l.LoanAt i loan) (hat₁ : l₁.LoanAt i loan₁) (pc : PaymentComponents)
    (totalDue : Number) (hpc : loan.paymentComponents .late l.now = .ok pc) (hdue : pc.totalDue = .ok totalDue)
    (ha₁ : a₁.operator_lt totalDue = false) (ha₂ : a₂.operator_lt totalDue = false) :
    l₁ = l₂ ∧ loan₁.paymentRemaining = if pc.isFinal then 0 else loan.paymentRemaining - 1 := by
  obtain ⟨e₁, loan₀, r₁, he₁, hat₀, -, -, hok₁, hl₁, -, hat₁', -, -⟩ := LendingLedger.loanPay_ok h₁
  obtain ⟨e₂, loan₀', r₂, he₂, hat₀', -, -, hok₂, hl₂, -, -, -, -⟩ := LendingLedger.loanPay_ok h₂
  obtain rfl : loan = loan₀ := (LendingLedger.LoanAt.eq hat₀ hat).symm
  obtain rfl : loan = loan₀' := (LendingLedger.LoanAt.eq hat₀' hat).symm
  rw [he₁] at he₂
  obtain rfl := Option.some.inj he₂
  have hs := Loan.latePayment_single_proof loan l.vault l.now pc totalDue a₁ a₂ hpc hdue ha₁ ha₂
  have hok₁' : (loan.latePayment l.vault a₁ l.now).run = .ok (.ok r₁) := hok₁
  have hok₂' : (loan.latePayment l.vault a₂ l.now).run = .ok (.ok r₂) := hok₂
  rw [hs.1, hok₂'] at hok₁'
  obtain rfl : r₂ = r₁ := Except.ok.inj (Except.ok.inj hok₁')
  refine ⟨by rw [hl₁, hl₂], ?_⟩
  rw [← LendingLedger.LoanAt.eq hat₁' hat₁]
  exact hs.2 r₂ (by rw [hs.1]; exact hok₂')

/-- Proof body of the paid-off part of `Lending.fullPayment_payoff`. -/
lemma LendingLedger.fullPayment_closes_proof (l l' : LendingLedger) (i : Nat) (amount : Number)
    (h : (l.apply (.loanPay i .full amount)).run = .ok (.ok l')) (loan' : Loan) (hat' : l'.LoanAt i loan') :
    loan'.paymentRemaining = 0 ∧ loan'.totalValueOutstanding = Number.zero ∧
      loan'.principalOutstanding = Number.zero ∧ loan'.managementFeeOutstanding = Number.zero := by
  obtain ⟨-, loan, r, -, -, -, -, hok, -, -, hat'', -, -⟩ := LendingLedger.loanPay_ok h
  obtain rfl := LendingLedger.LoanAt.eq hat'' hat'
  exact Loan.fullPayment_closes_proof loan l.vault amount l.now r hok

/-- Proof body of the schedule part of `Lending.overpayment_extra`. -/
lemma LendingLedger.overpayment_schedule_proof (l l' : LendingLedger) (i : Nat) (amount : Number)
    (h : (l.apply (.loanPay i .overpayment amount)).run = .ok (.ok l')) (loan loan' : Loan) (hat : l.LoanAt i loan)
    (hat' : l'.LoanAt i loan') :
    ∃ payment, (loan.payInstalments l.vault .regular amount l.now).run = .ok (.ok payment) ∧
      loan'.paymentRemaining = payment.loan.paymentRemaining ∧
      loan'.nextPaymentDueDate = payment.loan.nextPaymentDueDate := by
  obtain ⟨r, hok, rfl, -⟩ := LendingLedger.loanPay_loans h hat hat'
  exact Loan.overpayment_schedule_proof loan l.vault amount l.now r hok

/-- Proof body of the decrease part of `Lending.overpayment_extra`. -/
lemma LendingLedger.overpayment_reduces_proof (l : LendingLedger) (hr : l.Reachable) (l' : LendingLedger) (i : Nat)
    (amount : Number) (h : (l.apply (.loanPay i .overpayment amount)).run = .ok (.ok l')) (loan loan' : Loan)
    (hat : l.LoanAt i loan) (hat' : l'.LoanAt i loan') (payment : UnsettledPayment Vault)
    (hpay : (loan.payInstalments l.vault .regular amount l.now).run = .ok (.ok payment))
    (happlied : (l.apply (.loanPay i .overpayment amount)).run ≠ (l.apply (.loanPay i .regular amount)).run) :
    loan'.principalOutstanding.toRat < payment.loan.principalOutstanding.toRat ∧
      loan'.totalValueOutstanding.toRat < payment.loan.totalValueOutstanding.toRat ∧
      loan'.periodicPayment.toRat < payment.loan.periodicPayment.toRat := by
  obtain ⟨t, -, hreach⟩ := hr.loanAt_reachable hat
  obtain ⟨r, hok, rfl, -⟩ := LendingLedger.loanPay_loans h hat hat'
  refine Loan.overpayment_reduces_proof loan l.vault amount l.now t r hreach payment hpay hok fun heq => happlied ?_
  rw [LendingLedger.apply_regular_of_overpayment h hat heq, h]

/-- Proof body of the paid-off case of `Lending.overpayment_dropped`. -/
lemma LendingLedger.overpayment_dropped_paid_off_proof (l l' : LendingLedger) (i : Nat) (amount : Number)
    (h : (l.apply (.loanPay i .overpayment amount)).run = .ok (.ok l')) (loan : Loan) (hat : l.LoanAt i loan)
    (payment : UnsettledPayment Vault) (amount' : Number)
    (hpay : (loan.payInstalments l.vault .regular amount l.now).run = .ok (.ok payment))
    (hamount : STAmount.roundToNumericType loan.broker.numericType amount .towards_zero (some loan.loanScale) =
      .ok amount')
    (hdrop : payment.loan.paymentRemaining = 0 ∨ payment.totalPaid.operator_lt amount' = false ∨
      payment.count = maxPaymentsPerTransaction) :
    (l.apply (.loanPay i .regular amount)).run = .ok (.ok l') :=
  LendingLedger.apply_regular_of_overpayment h hat
    (Loan.overpayment_dropped_paid_off_proof loan l.vault amount l.now payment amount' hpay hamount hdrop)

/-- Proof body of the zero-leftover case of `Lending.overpayment_dropped`. -/
lemma LendingLedger.overpayment_dropped_no_extra_proof (l l' : LendingLedger) (i : Nat) (amount : Number)
    (h : (l.apply (.loanPay i .overpayment amount)).run = .ok (.ok l')) (loan : Loan) (hat : l.LoanAt i loan)
    (payment : UnsettledPayment Vault) (amount' unspent extra : Number)
    (hpay : (loan.payInstalments l.vault .regular amount l.now).run = .ok (.ok payment))
    (hamount : STAmount.roundToNumericType loan.broker.numericType amount .towards_zero (some loan.loanScale) =
      .ok amount')
    (hunspent : amount'.operator_sub payment.totalPaid .to_nearest = .ok unspent)
    (hextra : STAmount.roundToNumericType loan.broker.numericType
      (Number.min unspent payment.loan.totalValueOutstanding) .downward (some loan.loanScale) = .ok extra)
    (hzero : extra.operator_gt Number.zero = false) :
    (l.apply (.loanPay i .regular amount)).run = .ok (.ok l') :=
  LendingLedger.apply_regular_of_overpayment h hat
    (Loan.overpayment_dropped_no_extra_proof loan l.vault amount l.now payment amount' unspent extra hpay hamount
      hunspent hextra hzero)

/-- Proof body of the no-principal case of `Lending.overpayment_dropped`. -/
lemma LendingLedger.overpayment_dropped_absorbed_proof (l l' : LendingLedger) (i : Nat) (amount : Number)
    (h : (l.apply (.loanPay i .overpayment amount)).run = .ok (.ok l')) (loan : Loan) (hat : l.LoanAt i loan)
    (payment : UnsettledPayment Vault) (amount' unspent extra : Number) (opc : PaymentComponents)
    (hpay : (loan.payInstalments l.vault .regular amount l.now).run = .ok (.ok payment))
    (hamount : STAmount.roundToNumericType loan.broker.numericType amount .towards_zero (some loan.loanScale) =
      .ok amount')
    (hunspent : amount'.operator_sub payment.totalPaid .to_nearest = .ok unspent)
    (hextra : STAmount.roundToNumericType loan.broker.numericType
      (Number.min unspent payment.loan.totalValueOutstanding) .downward (some loan.loanScale) = .ok extra)
    (hopc : payment.loan.computeOverpaymentComponents extra = .ok opc)
    (hprincipal : opc.principalDelta.operator_gt Number.zero = false) :
    (l.apply (.loanPay i .regular amount)).run = .ok (.ok l') :=
  LendingLedger.apply_regular_of_overpayment h hat
    (Loan.overpayment_dropped_absorbed_proof loan l.vault amount l.now payment amount' unspent extra opc hpay hamount
      hunspent hextra hopc hprincipal)

/-- Proof body of the rejected re-amortization case of `Lending.overpayment_dropped`. -/
lemma LendingLedger.overpayment_dropped_reamortization_proof (l l' : LendingLedger) (i : Nat) (amount : Number)
    (h : (l.apply (.loanPay i .overpayment amount)).run = .ok (.ok l')) (loan : Loan) (hat : l.LoanAt i loan)
    (payment : UnsettledPayment Vault) (amount' unspent extra : Number) (opc : PaymentComponents)
    (hpay : (loan.payInstalments l.vault .regular amount l.now).run = .ok (.ok payment))
    (hamount : STAmount.roundToNumericType loan.broker.numericType amount .towards_zero (some loan.loanScale) =
      .ok amount')
    (hunspent : amount'.operator_sub payment.totalPaid .to_nearest = .ok unspent)
    (hextra : STAmount.roundToNumericType loan.broker.numericType
      (Number.min unspent payment.loan.totalValueOutstanding) .downward (some loan.loanScale) = .ok extra)
    (hopc : payment.loan.computeOverpaymentComponents extra = .ok opc)
    (hre : payment.loan.overpaymentReamortization opc = .ok none) :
    (l.apply (.loanPay i .regular amount)).run = .ok (.ok l') :=
  LendingLedger.apply_regular_of_overpayment h hat
    (Loan.overpayment_dropped_reamortization_proof loan l.vault amount l.now payment amount' unspent extra opc hpay
      hamount hunspent hextra hopc hre)

end XRPL.Model.Lending
