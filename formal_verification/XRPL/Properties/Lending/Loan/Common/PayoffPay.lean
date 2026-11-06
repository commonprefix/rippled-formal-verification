import XRPL.Properties.Lending.Loan.Common.CreditTotal
import XRPL.Properties.Lending.Loan.Common.PayExits

/-! # A payoff of exactly its total due pays its instalment

A full payment pays one instalment, the payoff, and a regular payment with one payment left pays the last one.
With the instalment computed and the amount equal to its total due, both leave a paid-off loan. -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault (Vault RawVault)

open private Loan.fullComponents Loan.scheduledComponents Loan.doPayment UnsettledPayment.payInstalments
  Loan.unimpairIfImpaired Loan.payScheduledInstalments from XRPL.Model.Lending.Loan.LoanPay
open private Loan.doPayment_final_lawful from XRPL.Properties.Lending.Loan.Common.RecheckPayLoan

/-- The last instalment computes and leaves no payments. -/
lemma Loan.doPayment_final_ok (l : Loan) (pc : PaymentComponents) (hf : pc.isFinal = true) :
    ∃ l', Loan.doPayment l pc = .ok l' ∧ l'.paymentRemaining = 0 := by
  obtain ⟨l', hl'⟩ := Loan.doPayment_final_lawful l
  have hdo : Loan.doPayment l pc = .ok l' := by
    unfold Loan.doPayment
    simp only [hf, ↓reduceIte]
    rw [hl']
    rfl
  exact ⟨l', hdo, Loan.doPayment_final _ _ _ hf hdo⟩

/-- An amount is never below itself. -/
private lemma Number.operator_lt_self (x : Number) (hx : x.isNormalized) : x.operator_lt x = false :=
  (operator_lt_eq_false_iff x x hx hx).mpr le_rfl

/-- A full payment of exactly the payoff's total due pays the payoff instalment, on a loan that is not
impaired and not late, with two or more payments left. -/
lemma Loan.fullPayInstalments_payoff (loan : Loan) (v : Vault) (now : UInt32) (pc : PaymentComponents)
    (due : Number) (hpr : 2 ≤ loan.paymentRemaining.toNat) (hpo : loan.principalOutstanding ≠ Number.zero)
    (hdd : loan.nextPaymentDueDate ≠ 0) (hnl : now ≤ loan.nextPaymentDueDate) (himp : loan.isImpaired = false)
    (hpc : Loan.fullComponents loan now = .ok pc) (hfin : pc.isFinal = true) (hdue : pc.totalDue = .ok due)
    (hdueN : due.isNormalized) (a : PaymentAmounts) (ha : pc.paidAmounts = .ok a) (i : Number)
    (hi : loan.interestDue = .ok i) :
    ∃ l', (loan.payInstalments v .full due now).run = .ok (.ok ⟨l', v, a, due, 1, i⟩) ∧
      l'.paymentRemaining = 0 := by
  have hr : loan.paymentRemaining ≠ 0 := fun h0 => by rw [h0] at hpr; simp at hpr
  have h1 : ¬ loan.paymentRemaining ≤ 1 := by
    intro h
    have := UInt32.le_iff_toNat_le.mp h
    simp at this
    omega
  obtain ⟨l', hdo, hl'⟩ := Loan.doPayment_final_ok loan pc hfin
  have hu := Loan.unimpairIfImpaired_not loan v himp
  simp only [ExceptT.run] at hu
  refine ⟨l', ?_, hl'⟩
  simp only [Loan.payInstalments, Loan.payInstalment]
  unfold_ter
  simp only [Loan.not_paid_off loan hr hpo, Loan.nextPaymentDueDate_ne_zero loan hdd, Loan.isPaymentLate,
    decide_eq_true_eq, UInt32.not_lt.mpr hnl, Bool.false_eq_true, ↓reduceIte, h1, hu, hpc, hdue,
    Number.operator_lt_self due hdueN, hi, ha, hdo]

/-- A regular payment of exactly the last instalment's total due pays it, on a loan with one payment left
that is not impaired and not late. -/
lemma Loan.regularPayInstalments_payoff (loan : Loan) (v : Vault) (now : UInt32) (pc : PaymentComponents)
    (due : Number) (hpr : loan.paymentRemaining = 1) (hpo : loan.principalOutstanding ≠ Number.zero)
    (hdd : loan.nextPaymentDueDate ≠ 0) (hnl : now ≤ loan.nextPaymentDueDate) (himp : loan.isImpaired = false)
    (hpc : Loan.scheduledComponents loan = .ok pc) (hfin : pc.isFinal = true)
    (hdue : ({ pc with untrackedManagementFee := loan.fees.serviceFee } : PaymentComponents).totalDue = .ok due)
    (hdueN : due.isNormalized) (a : PaymentAmounts)
    (ha : ({ pc with untrackedManagementFee := loan.fees.serviceFee } : PaymentComponents).paidAmounts = .ok a)
    (i : Number) (hi : loan.interestDue = .ok i) :
    ∃ l', (loan.payInstalments v .regular due now).run = .ok (.ok ⟨l', v, a, due, 1, i⟩) ∧
      l'.paymentRemaining = 0 := by
  have hr : loan.paymentRemaining ≠ 0 := by rw [hpr]; decide
  obtain ⟨l', hdo, hl'⟩ := Loan.doPayment_final_ok loan
    ({ pc with untrackedManagementFee := loan.fees.serviceFee } : PaymentComponents) hfin
  have hu := Loan.unimpairIfImpaired_not loan v himp
  simp only [ExceptT.run] at hu
  have hloop : UnsettledPayment.payInstalments (⟨loan, v, PaymentAmounts.zero, Number.zero, 0, i⟩ :
      UnsettledPayment Vault) maxPaymentsPerTransaction due = .ok ⟨l', v, a, due, 1, i⟩ := by
    rw [show maxPaymentsPerTransaction = 99 + 1 from rfl, UnsettledPayment.payInstalments]
    have hpr0 : (loan.paymentRemaining == 0) = false := by simpa using hr
    have hdue' := hdue
    have ha' := ha
    have hdo' := hdo
    simp only [hfin] at hdue' ha' hdo'
    simp only [hpr0, Bool.false_eq_true, ↓reduceIte, hpc, bind, Except.bind, Number.operator_add_zero_left,
      Number.operator_lt_self due hdueN, hdue', ha', hdo', PaymentAmounts.zero_add, hfin, pure, Except.pure]
  refine ⟨l', ?_, hl'⟩
  simp only [Loan.payInstalments, Loan.payScheduledInstalments]
  unfold_ter
  simp only [Loan.not_paid_off loan hr hpo, Loan.nextPaymentDueDate_ne_zero loan hdd, Loan.isPaymentLate,
    decide_eq_true_eq, UInt32.not_lt.mpr hnl, Bool.false_eq_true, ↓reduceIte, hu, hi, hloop]
  rfl

end XRPL.Model.Lending
