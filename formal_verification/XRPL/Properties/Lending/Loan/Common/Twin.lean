import XRPL.Properties.Lending.Loan.Common.Frame
import XRPL.Properties.Lending.Loan.Common.PayDefs
import XRPL.Properties.Lending.Loan.Common.SetValue

/-! # Twin loans

Two loans with the same state and terms on brokers of the same asset and management fee rate compute the
same instalments, and stay twins after each one. Two LoanSets with the same terms create twins. -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault (Vault)

open private Loan.scheduledComponents Loan.lateComponents Loan.fullComponents Loan.doPayment
  from XRPL.Model.Lending.Loan.LoanPay

/-- Two loans with the same state and terms, on brokers of the same asset and management fee rate. They
differ only in the rest of their broker. -/
structure Loan.Twin (l l' : Loan) : Prop where
  raw : l'.toRawLoan = { l.toRawLoan with broker := l'.toRawLoan.broker }
  numericType : l'.broker.numericType = l.broker.numericType
  managementFeeRate : l'.broker.managementFeeRate = l.broker.managementFeeRate

/-- Twins compute the same scheduled instalment. -/
private lemma Loan.scheduledComponents_twin {l l' : Loan} (h : Loan.Twin l l') :
    Loan.scheduledComponents l' = Loan.scheduledComponents l := by
  obtain ⟨hraw, hnt, hm⟩ := h
  generalize hb : l'.toRawLoan.broker = b at hraw
  have hnt' : b.numericType = l.broker.numericType := by rw [← hb]; exact hnt
  have hm' : b.managementFeeRate = l.broker.managementFeeRate := by rw [← hb]; exact hm
  unfold Loan.scheduledComponents Loan.state Loan.periodicRate
  rw [hraw]
  simp only [hnt', hm']

/-- Twins compute the same late instalment. -/
private lemma Loan.lateComponents_twin {l l' : Loan} (h : Loan.Twin l l') (now : UInt32) :
    Loan.lateComponents l' now = Loan.lateComponents l now := by
  have hs := Loan.scheduledComponents_twin h
  obtain ⟨hraw, hnt, hm⟩ := h
  generalize hb : l'.toRawLoan.broker = b at hraw
  have hnt' : b.numericType = l.broker.numericType := by rw [← hb]; exact hnt
  have hm' : b.managementFeeRate = l.broker.managementFeeRate := by rw [← hb]; exact hm
  unfold Loan.lateComponents
  rw [hs]
  rw [hraw]
  simp only [hnt', hm']

/-- Twins compute the same full payoff. -/
private lemma Loan.fullComponents_twin {l l' : Loan} (h : Loan.Twin l l') (now : UInt32) :
    Loan.fullComponents l' now = Loan.fullComponents l now := by
  obtain ⟨hraw, hnt, hm⟩ := h
  generalize hb : l'.toRawLoan.broker = b at hraw
  have hnt' : b.numericType = l.broker.numericType := by rw [← hb]; exact hnt
  have hm' : b.managementFeeRate = l.broker.managementFeeRate := by rw [← hb]; exact hm
  unfold Loan.fullComponents Loan.state Loan.periodicRate
  rw [hraw]
  simp only [hnt', hm']

/-- Twins compute the same first instalment for every payment type and close time. -/
lemma Loan.paymentComponents_twin {l l' : Loan} (h : Loan.Twin l l') (pt : LoanPaymentType) (now : UInt32) :
    l'.paymentComponents pt now = l.paymentComponents pt now := by
  have hfee : l'.fees.serviceFee = l.fees.serviceFee := (congrArg (·.fees.serviceFee) h.raw :)
  cases pt
  · simp only [Loan.paymentComponents, Loan.scheduledComponents_twin h, hfee]
  · exact Loan.lateComponents_twin h now
  · exact Loan.fullComponents_twin h now
  · simp only [Loan.paymentComponents, Loan.scheduledComponents_twin h, hfee]

/-- What advancing a loan by one instalment writes: a paid-off loan for the final instalment, otherwise the
outstanding amounts less the instalment's deltas and the next due date. -/
private lemma Loan.doPayment_raw (x y : Loan) (pc : PaymentComponents) (h : Loan.doPayment x pc = .ok y) :
    (pc.isFinal = true ∧ y.toRawLoan = { x.toRawLoan with
      totalValueOutstanding := Number.zero, principalOutstanding := Number.zero,
      managementFeeOutstanding := Number.zero, paymentRemaining := 0,
      previousPaymentDueDate := x.nextPaymentDueDate, nextPaymentDueDate := 0 }) ∨
    (pc.isFinal = false ∧ ∃ t p m,
      x.totalValueOutstanding.operator_sub pc.totalValueDelta .to_nearest = .ok t ∧
      x.principalOutstanding.operator_sub pc.principalDelta .to_nearest = .ok p ∧
      x.managementFeeOutstanding.operator_sub pc.managementFeeDelta .to_nearest = .ok m ∧
      y.toRawLoan = { x.toRawLoan with
        totalValueOutstanding := t, principalOutstanding := p, managementFeeOutstanding := m,
        paymentRemaining := x.paymentRemaining - 1, previousPaymentDueDate := x.nextPaymentDueDate,
        nextPaymentDueDate := x.nextPaymentDueDate + x.schedule.paymentInterval }) := by
  by_cases hf : pc.isFinal = true
  · simp only [Loan.doPayment, hf, ↓reduceIte] at h
    unfold_ter at h
    walk_ok
    exact Or.inl ⟨hf, (RawLoan.to_lawful_ok ‹_›).1⟩
  · simp only [Bool.not_eq_true] at hf
    simp only [Loan.doPayment, hf, Bool.false_eq_true, ↓reduceIte] at h
    unfold_ter at h
    walk_ok
    exact Or.inr ⟨hf, _, _, _, ‹_›, ‹_›, ‹_›, (RawLoan.to_lawful_ok ‹_›).1⟩

/-- Twins advanced by the same instalment stay twins. -/
lemma Loan.doPayment_twin {l l' r r' : Loan} (h : Loan.Twin l l') (pc : PaymentComponents)
    (hr : Loan.doPayment l pc = .ok r) (hr' : Loan.doPayment l' pc = .ok r') : Loan.Twin r r' := by
  obtain ⟨hraw, hnt, hm⟩ := h
  generalize hb : l'.toRawLoan.broker = b at hraw
  -- the new loans differ only in their broker, which the instalment keeps
  have hkey : r'.toRawLoan = { r.toRawLoan with broker := b } ∧ r.broker = l.broker := by
    rcases Loan.doPayment_raw l r pc hr with ⟨hfin, h1⟩ | ⟨hfin, t, p, m, ht, hp, hmf, h1⟩ <;>
      rcases Loan.doPayment_raw l' r' pc hr' with ⟨hfin', h2⟩ | ⟨hfin', t', p', m', ht', hp', hmf', h2⟩
    · exact ⟨by rw [h2, h1, hraw], (congrArg RawLoan.broker h1 :)⟩
    · rw [hfin] at hfin'; cases hfin'
    · rw [hfin] at hfin'; cases hfin'
    · rw [show l'.totalValueOutstanding = l'.toRawLoan.totalValueOutstanding from rfl, hraw] at ht'
      rw [show l'.principalOutstanding = l'.toRawLoan.principalOutstanding from rfl, hraw] at hp'
      rw [show l'.managementFeeOutstanding = l'.toRawLoan.managementFeeOutstanding from rfl, hraw] at hmf'
      dsimp only at ht' hp' hmf'
      rw [ht] at ht'; rw [hp] at hp'; rw [hmf] at hmf'
      cases ht'; cases hp'; cases hmf'
      exact ⟨by rw [h2, h1, hraw], (congrArg RawLoan.broker h1 :)⟩
  have hbr : r'.broker = b := by rw [show r'.broker = r'.toRawLoan.broker from rfl, hkey.1]
  refine ⟨?_, ?_, ?_⟩
  · rw [hkey.1]
  · rw [hbr, hkey.2, ← hb]; exact hnt
  · rw [hbr, hkey.2, ← hb]; exact hm

/-- Loans created with the same terms and PrincipalRequested, on brokers of the same asset and management fee
rate and vaults of the same base scale, are twins. -/
lemma Loan.create_twin (b b' : LoanBroker) (v v' : Vault) (principal : Number) (rates : LoanRates)
    (fees : LoanFees) (schedule : LoanSchedule) (allowsOverpayment pending : Bool) (r r' : LoanWithDisbursement Vault)
    (hnt : b'.numericType = b.numericType) (hm : b'.managementFeeRate = b.managementFeeRate)
    (hbe : v'.baseExponent = v.baseExponent)
    (h : (Loan.create b v principal rates fees schedule allowsOverpayment pending).run = .ok (.ok r))
    (h' : (Loan.create b' v' principal rates fees schedule allowsOverpayment pending).run = .ok (.ok r')) :
    Loan.Twin r.loan' r'.loan' := by
  obtain ⟨props, _, d, bn, hc, hl, hbn⟩ := Loan.create_loan_eq _ _ _ _ _ _ _ _ r h
  obtain ⟨props', _, d', bn', hc', hl', hbn'⟩ := Loan.create_loan_eq _ _ _ _ _ _ _ _ r' h'
  have hp := hc.properties_ok
  have hp' := hc'.properties_ok
  rw [hnt, hm, hbe, hp] at hp'
  cases hp'
  have hb : r.loan'.broker = bn := by rw [show r.loan'.broker = r.loan'.toRawLoan.broker from rfl, hl]; rfl
  have hb' : r'.loan'.broker = bn' := by rw [show r'.loan'.broker = r'.loan'.toRawLoan.broker from rfl, hl']; rfl
  refine ⟨by rw [hl', hl]; rfl, ?_, ?_⟩
  · rw [hb, hb', show bn'.numericType = bn'.toRawLoanBroker.numericType from rfl, hbn',
      show bn.numericType = bn.toRawLoanBroker.numericType from rfl, hbn]
    exact hnt
  · rw [hb, hb', show bn'.managementFeeRate = bn'.toRawLoanBroker.managementFeeRate from rfl, hbn',
      show bn.managementFeeRate = bn.toRawLoanBroker.managementFeeRate from rfl, hbn]
    exact hm

/-- Twins owe the same interest. -/
lemma Loan.Twin.interestDue_eq {l l' : Loan} (h : Loan.Twin l l') :
    l'.toExact.interestDue = l.toExact.interestDue := by
  show l'.toRawLoan.totalValueOutstanding.toRat - l'.toRawLoan.principalOutstanding.toRat -
    l'.toRawLoan.managementFeeOutstanding.toRat = l.toRawLoan.totalValueOutstanding.toRat -
      l.toRawLoan.principalOutstanding.toRat - l.toRawLoan.managementFeeOutstanding.toRat
  rw [h.raw]

end XRPL.Model.Lending
