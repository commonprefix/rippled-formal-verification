import XRPL.Properties.Lending.Ledger.Common.LoanTxResults
import XRPL.Properties.Lending.Ledger.Common.PhaseProofs
import XRPL.Properties.Lending.Loan.Common.PaySteps

/-! # A payment on an impaired loan

An impaired loan on a reachable ledger is late, so only a late payment passes. It clears the impairment and pays
one instalment, which moves NextPaymentDueDate one PaymentInterval on. -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol

/-- Proof body of `Lending.Reachable.pay_unimpairs_only_current`. -/
lemma LendingLedger.pay_unimpairs_only_current_proof (l l' : LendingLedger) (hr : l.Reachable) (i : Nat)
    (paymentType : LoanPaymentType) (amount : Number)
    (h : (l.apply (.loanPay i paymentType amount)).run = .ok (.ok l')) (loan loan' : Loan)
    (hat : l.LoanAt i loan) (hat' : l'.LoanAt i loan') (hi : loan.isImpaired = true)
    (hp : loan'.paymentRemaining ≠ 0)
    (hdue : l.now.toNat ≤ loan.nextPaymentDueDate.toNat + loan.schedule.paymentInterval.toNat) :
    loan'.isImpaired = false ∧ loan'.isPaymentLate l'.now = false := by
  obtain ⟨-, loan₀, r, -, hat₀, -, -, hok, -, -, hat'', hnow, -⟩ := LendingLedger.loanPay_ok h
  obtain rfl := LendingLedger.LoanAt.eq hat₀ hat
  obtain rfl := LendingLedger.LoanAt.eq hat'' hat'
  obtain ⟨p, hpay, hs⟩ := Loan.pay_ok loan₀ l.vault paymentType amount l.now r hok
  obtain ⟨hchk, -, hst, -, -⟩ := Loan.payInstalments_ok loan₀ l.vault paymentType amount l.now p hpay
  -- an impaired loan on a reachable ledger is late, so only a late payment passes
  obtain ⟨t, hle, hreach⟩ := hr.loanAt_reachable hat₀
  have hlate := Loan.Reachable.impaired_late_proof loan₀ t hreach hi hchk.remaining
  have hlt : loan₀.nextPaymentDueDate < l.now := by
    simp only [Loan.isPaymentLate, decide_eq_true_eq, UInt32.lt_iff_toNat_lt] at hlate ⊢
    rw [UInt32.le_iff_toNat_le] at hle
    omega
  obtain rfl := hchk.date.mpr hlt
  obtain ⟨pc, -, -, hdo⟩ := Loan.latePayInstalments_ok loan₀ l.vault amount l.now p hpay
  -- the settlement changes only the loan's broker
  obtain ⟨_, _, _, _, _, _, _, -, -, -, -, hloan, -, -⟩ := UnsettledPayment.settle_ok p r hs
  have hraw := (RawLoan.to_lawful_ok hloan).1
  have hrem : r.loan'.paymentRemaining = p.loan.paymentRemaining := by
    rw [show r.loan'.paymentRemaining = r.loan'.toRawLoan.paymentRemaining from rfl, hraw]
  have himp : r.loan'.isImpaired = p.loan.isImpaired := by
    rw [show r.loan'.isImpaired = r.loan'.toRawLoan.isImpaired from rfl, hraw]
  have hnext : r.loan'.nextPaymentDueDate = p.loan.nextPaymentDueDate := by
    rw [show r.loan'.nextPaymentDueDate = r.loan'.toRawLoan.nextPaymentDueDate from rfl, hraw]
  refine ⟨by rw [himp, hst.isImpaired]; rfl, ?_⟩
  -- the last instalment leaves no payments, any other moves the due date one interval on
  cases hf : pc.isFinal
  · obtain ⟨-, hnd⟩ := Loan.doPayment_notFinal _ _ pc hf hdo
    obtain ⟨-, hfit⟩ := Loan.doPayment_ok_checks _ pc _ hf hdo
    have hsum : (loan₀.nextPaymentDueDate + loan₀.schedule.paymentInterval).toNat =
        loan₀.nextPaymentDueDate.toNat + loan₀.schedule.paymentInterval.toNat := by
      rw [UInt32.toNat_add]
      exact Nat.mod_eq_of_lt hfit
    simp only [Loan.isPaymentLate, decide_eq_false_iff_not, UInt32.lt_iff_toNat_lt, hnow, hnext, hnd]
    change ¬ (loan₀.nextPaymentDueDate + loan₀.schedule.paymentInterval).toNat < l.now.toNat
    omega
  · exact absurd (by rw [hrem]; exact Loan.doPayment_final _ _ pc hf hdo) hp

end XRPL.Model.Lending
