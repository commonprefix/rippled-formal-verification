import XRPL.Properties.Lending.Loan.Common.PayBounds

/-! # When an overpayment drops its extra amount

After the scheduled payments an overpayment tries to pay the rest of the requested amount as extra principal.
Each check that drops the extra leaves the payment a regular payment of the same requested amount. -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault (Vault RawVault)

open private UnsettledPayment.applyOverpayment Loan.overpaymentComponents Loan.tryOverpayment
  from XRPL.Model.Lending.Loan.LoanPay
open private Loan.overPayInstalments_run from XRPL.Properties.Lending.Loan.Common.PayBounds

/-- The fee, interest and principal parts of an overpayment's extra amount (C++ `computeOverpaymentComponents`). -/
def Loan.computeOverpaymentComponents (loan : Loan) (extra : Number) : Except Error PaymentComponents :=
  Loan.overpaymentComponents loan extra

/-- The re-amortization of the schedule for an overpayment's extra principal (C++ `tryOverpayment`). `none` when a
re-amortization check drops the extra amount. -/
def Loan.overpaymentReamortization (loan : Loan) (opc : PaymentComponents) : Except Error (Option Reamortization) :=
  Loan.tryOverpayment loan opc

variable (loan : Loan) (v : Vault) (amount : Number) (now : UInt32)

/-- An overpayment whose extra amount is dropped is the regular payment of the same amount. -/
private lemma Loan.overpayment_eq_regular (payment : UnsettledPayment Vault)
    (hpay : (loan.payInstalments v .regular amount now).run = .ok (.ok payment))
    (hdrop : UnsettledPayment.applyOverpayment payment amount = .ok payment) :
    (loan.overpayment v amount now).run = (loan.regularPayment v amount now).run :=
  Loan.overpayment_of_same_instalments loan v amount now fun p hp => by
    rw [hpay] at hp
    obtain rfl := Except.ok.inj (Except.ok.inj hp)
    rw [Loan.overPayInstalments_run, hpay]
    simp only [hdrop]
    rfl

/-- The first check of the extra amount: an overpayment allowed, payments left, the rounded amount above what the
scheduled payments took, and room under the per-transaction cap. -/
private def UnsettledPayment.extraAllowed (payment : UnsettledPayment Vault) (amount' : Number) : Bool :=
  payment.loan.allowsOverpayment && payment.loan.paymentRemaining != 0 && payment.totalPaid.operator_lt amount' &&
    decide (payment.count < maxPaymentsPerTransaction)

section
variable (payment : UnsettledPayment Vault) (amount' unspent extra : Number) (opc : PaymentComponents)
  (hamount : STAmount.roundToNumericType payment.loan.broker.numericType amount .towards_zero
    (some payment.loan.loanScale) = .ok amount')

include hamount

private lemma UnsettledPayment.drop_of_check (hc : payment.extraAllowed amount' = false) :
    UnsettledPayment.applyOverpayment payment amount = .ok payment := by
  unfold UnsettledPayment.extraAllowed at hc
  simp only [UnsettledPayment.applyOverpayment, hamount, bind, Except.bind, hc, Bool.not_false, if_true]
  rfl

private lemma UnsettledPayment.drop_of_extra (hc : payment.extraAllowed amount' = true)
    (hunspent : amount'.operator_sub payment.totalPaid .to_nearest = .ok unspent)
    (hextra : STAmount.roundToNumericType payment.loan.broker.numericType
      (Number.min unspent payment.loan.totalValueOutstanding) .downward (some payment.loan.loanScale) = .ok extra)
    (hzero : extra.operator_gt Number.zero = false) :
    UnsettledPayment.applyOverpayment payment amount = .ok payment := by
  unfold UnsettledPayment.extraAllowed at hc
  simp only [UnsettledPayment.applyOverpayment, hamount, bind, Except.bind, hc, Bool.not_true, Bool.false_eq_true,
    if_false, hunspent, hextra, hzero, Bool.not_false, if_true]
  rfl

private lemma UnsettledPayment.drop_of_principal (hc : payment.extraAllowed amount' = true)
    (hunspent : amount'.operator_sub payment.totalPaid .to_nearest = .ok unspent)
    (hextra : STAmount.roundToNumericType payment.loan.broker.numericType
      (Number.min unspent payment.loan.totalValueOutstanding) .downward (some payment.loan.loanScale) = .ok extra)
    (hpos : extra.operator_gt Number.zero = true) (hopc : payment.loan.computeOverpaymentComponents extra = .ok opc)
    (hprincipal : opc.principalDelta.operator_gt Number.zero = false) :
    UnsettledPayment.applyOverpayment payment amount = .ok payment := by
  unfold UnsettledPayment.extraAllowed at hc
  unfold Loan.computeOverpaymentComponents at hopc
  simp only [UnsettledPayment.applyOverpayment, hamount, bind, Except.bind, hc, Bool.not_true, Bool.false_eq_true,
    if_false, hunspent, hextra, hpos, hopc, hprincipal, Bool.not_false, if_true]
  rfl

private lemma UnsettledPayment.drop_of_reamortization (hc : payment.extraAllowed amount' = true)
    (hunspent : amount'.operator_sub payment.totalPaid .to_nearest = .ok unspent)
    (hextra : STAmount.roundToNumericType payment.loan.broker.numericType
      (Number.min unspent payment.loan.totalValueOutstanding) .downward (some payment.loan.loanScale) = .ok extra)
    (hpos : extra.operator_gt Number.zero = true) (hopc : payment.loan.computeOverpaymentComponents extra = .ok opc)
    (hprincipal : opc.principalDelta.operator_gt Number.zero = true)
    (hre : payment.loan.overpaymentReamortization opc = .ok none) :
    UnsettledPayment.applyOverpayment payment amount = .ok payment := by
  unfold UnsettledPayment.extraAllowed at hc
  unfold Loan.computeOverpaymentComponents at hopc
  unfold Loan.overpaymentReamortization at hre
  simp only [UnsettledPayment.applyOverpayment, hamount, bind, Except.bind, hc, Bool.not_true, Bool.false_eq_true,
    if_false, hunspent, hextra, hpos, hopc, hprincipal, hre]
  rfl

end

section
variable (payment : UnsettledPayment Vault) (amount' unspent extra : Number) (opc : PaymentComponents)
  (hpay : (loan.payInstalments v .regular amount now).run = .ok (.ok payment))
  (hamount : STAmount.roundToNumericType loan.broker.numericType amount .towards_zero (some loan.loanScale) =
    .ok amount')

include hpay hamount

/-- The scheduled payments keep the asset and LoanScale, so the rounding of the amount reads the same. -/
private lemma Loan.payment_rounding :
    STAmount.roundToNumericType payment.loan.broker.numericType amount .towards_zero
      (some payment.loan.loanScale) = .ok amount' := by
  obtain ⟨-, -, hst, -, -⟩ := Loan.payInstalments_ok loan v .regular amount now payment hpay
  rw [hst.broker, hst.loanScale]
  exact hamount

/-- Proof body of the paid-off case of `Lending.overpayment_dropped`. -/
lemma Loan.overpayment_dropped_paid_off_proof
    (hdrop : payment.loan.paymentRemaining = 0 ∨ payment.totalPaid.operator_lt amount' = false ∨
      payment.count = maxPaymentsPerTransaction) :
    (loan.overpayment v amount now).run = (loan.regularPayment v amount now).run := by
  refine Loan.overpayment_eq_regular loan v amount now payment hpay ?_
  refine UnsettledPayment.drop_of_check amount payment amount'
    (Loan.payment_rounding loan v amount now payment amount' hpay hamount) ?_
  unfold UnsettledPayment.extraAllowed
  rcases hdrop with h | h | h
  · simp [h]
  · simp [h]
  · simp [h]

/-- Proof body of the zero-leftover case of `Lending.overpayment_dropped`. -/
lemma Loan.overpayment_dropped_no_extra_proof
    (hunspent : amount'.operator_sub payment.totalPaid .to_nearest = .ok unspent)
    (hextra : STAmount.roundToNumericType loan.broker.numericType
      (Number.min unspent payment.loan.totalValueOutstanding) .downward (some loan.loanScale) = .ok extra)
    (hzero : extra.operator_gt Number.zero = false) :
    (loan.overpayment v amount now).run = (loan.regularPayment v amount now).run := by
  have hr := Loan.payment_rounding loan v amount now payment amount' hpay hamount
  obtain ⟨-, -, hst, -, -⟩ := Loan.payInstalments_ok loan v .regular amount now payment hpay
  rw [← show loan.unimpaired.broker = loan.broker from rfl, ← show loan.unimpaired.loanScale = loan.loanScale from rfl,
    ← hst.broker, ← hst.loanScale] at hextra
  refine Loan.overpayment_eq_regular loan v amount now payment hpay ?_
  cases hc : payment.extraAllowed amount'
  · exact UnsettledPayment.drop_of_check amount payment amount' hr hc
  · exact UnsettledPayment.drop_of_extra amount payment amount' unspent extra hr hc hunspent hextra hzero

/-- Proof body of the no-principal case of `Lending.overpayment_dropped`. -/
lemma Loan.overpayment_dropped_absorbed_proof
    (hunspent : amount'.operator_sub payment.totalPaid .to_nearest = .ok unspent)
    (hextra : STAmount.roundToNumericType loan.broker.numericType
      (Number.min unspent payment.loan.totalValueOutstanding) .downward (some loan.loanScale) = .ok extra)
    (hopc : payment.loan.computeOverpaymentComponents extra = .ok opc)
    (hprincipal : opc.principalDelta.operator_gt Number.zero = false) :
    (loan.overpayment v amount now).run = (loan.regularPayment v amount now).run := by
  have hr := Loan.payment_rounding loan v amount now payment amount' hpay hamount
  obtain ⟨-, -, hst, -, -⟩ := Loan.payInstalments_ok loan v .regular amount now payment hpay
  rw [← show loan.unimpaired.broker = loan.broker from rfl, ← show loan.unimpaired.loanScale = loan.loanScale from rfl,
    ← hst.broker, ← hst.loanScale] at hextra
  refine Loan.overpayment_eq_regular loan v amount now payment hpay ?_
  cases hc : payment.extraAllowed amount'
  · exact UnsettledPayment.drop_of_check amount payment amount' hr hc
  · cases hpos : extra.operator_gt Number.zero
    · exact UnsettledPayment.drop_of_extra amount payment amount' unspent extra hr hc hunspent hextra hpos
    · exact UnsettledPayment.drop_of_principal amount payment amount' unspent extra opc hr hc hunspent hextra hpos
        hopc hprincipal

/-- Proof body of the rejected re-amortization case of `Lending.overpayment_dropped`. -/
lemma Loan.overpayment_dropped_reamortization_proof
    (hunspent : amount'.operator_sub payment.totalPaid .to_nearest = .ok unspent)
    (hextra : STAmount.roundToNumericType loan.broker.numericType
      (Number.min unspent payment.loan.totalValueOutstanding) .downward (some loan.loanScale) = .ok extra)
    (hopc : payment.loan.computeOverpaymentComponents extra = .ok opc)
    (hre : payment.loan.overpaymentReamortization opc = .ok none) :
    (loan.overpayment v amount now).run = (loan.regularPayment v amount now).run := by
  have hr := Loan.payment_rounding loan v amount now payment amount' hpay hamount
  obtain ⟨-, -, hst, -, -⟩ := Loan.payInstalments_ok loan v .regular amount now payment hpay
  rw [← show loan.unimpaired.broker = loan.broker from rfl, ← show loan.unimpaired.loanScale = loan.loanScale from rfl,
    ← hst.broker, ← hst.loanScale] at hextra
  refine Loan.overpayment_eq_regular loan v amount now payment hpay ?_
  cases hc : payment.extraAllowed amount'
  · exact UnsettledPayment.drop_of_check amount payment amount' hr hc
  · cases hpos : extra.operator_gt Number.zero
    · exact UnsettledPayment.drop_of_extra amount payment amount' unspent extra hr hc hunspent hextra hpos
    · cases hprincipal : opc.principalDelta.operator_gt Number.zero
      · exact UnsettledPayment.drop_of_principal amount payment amount' unspent extra opc hr hc hunspent hextra hpos
          hopc hprincipal
      · exact UnsettledPayment.drop_of_reamortization amount payment amount' unspent extra opc hr hc hunspent hextra
          hpos hopc hprincipal hre

end

end XRPL.Model.Lending
