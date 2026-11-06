import XRPL.Properties.Lending.Loan.Common.ManageProofs
import XRPL.Properties.Lending.Loan.Common.PayMonotone
import XRPL.Properties.Lending.Loan.Common.ReachableProofs

/-! # What a reachable loan still owes

No loan transaction raises PaymentRemaining, PrincipalOutstanding, TotalValueOutstanding or
ManagementFeeOutstanding. A payment pays them down, a default clears them, the rest keep them. -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault (Vault)

open private Loan.changeImpairment from XRPL.Model.Lending.Loan.LoanManage

/-- `loan'` owes no more than `loan`: PaymentRemaining and the three outstanding amounts are no larger. -/
structure Loan.OwesNoMore (loan loan' : Loan) : Prop where
  principalOutstanding : loan'.principalOutstanding.toRat ≤ loan.principalOutstanding.toRat
  totalValueOutstanding : loan'.totalValueOutstanding.toRat ≤ loan.totalValueOutstanding.toRat
  managementFeeOutstanding : loan'.managementFeeOutstanding.toRat ≤ loan.managementFeeOutstanding.toRat
  paymentRemaining : loan'.paymentRemaining.toNat ≤ loan.paymentRemaining.toNat

/-- A loan owes no more than itself. -/
lemma Loan.OwesNoMore.refl (loan : Loan) : Loan.OwesNoMore loan loan :=
  ⟨le_refl _, le_refl _, le_refl _, le_refl _⟩

/-- Owing no more chains along a sequence of loans. -/
lemma Loan.OwesNoMore.trans {a b c : Loan} (h1 : Loan.OwesNoMore a b) (h2 : Loan.OwesNoMore b c) :
    Loan.OwesNoMore a c :=
  ⟨le_trans h2.1 h1.1, le_trans h2.2 h1.2, le_trans h2.3 h1.3, le_trans h2.4 h1.4⟩

/-- A loan rebuilt with the same outstanding amounts owes the same. -/
lemma Loan.OwesNoMore.of_raw {loan loan' : Loan} (h1 : loan'.principalOutstanding = loan.principalOutstanding)
    (h2 : loan'.totalValueOutstanding = loan.totalValueOutstanding)
    (h3 : loan'.managementFeeOutstanding = loan.managementFeeOutstanding)
    (h4 : loan'.paymentRemaining = loan.paymentRemaining) : Loan.OwesNoMore loan loan' :=
  ⟨by rw [h1], by rw [h2], by rw [h3], by rw [h4]⟩

/-- A copy of the loan on a refreshed broker owes the same. -/
private lemma Loan.refresh_owesNoMore {loan loan' : Loan} {b : LoanBroker}
    (h : RawLoan.to_lawful { loan.toRawLoan with broker := b } = .ok loan') : Loan.OwesNoMore loan loan' := by
  have hr := (RawLoan.to_lawful_ok h).1
  exact .of_raw (congrArg RawLoan.principalOutstanding hr :) (congrArg RawLoan.totalValueOutstanding hr :)
    (congrArg RawLoan.managementFeeOutstanding hr :) (congrArg RawLoan.paymentRemaining hr :)

/-- An accept owes the same. -/
private lemma Loan.accept_owesNoMore (loan : Loan) (v : Vault) (r : LoanWithPool Vault)
    (h : (loan.accept v).run = .ok (.ok r)) : Loan.OwesNoMore loan r.loan' := by
  simp only [Loan.accept] at h
  unfold_ter at h
  walk_ok
  have hr := (RawLoan.to_lawful_ok ‹RawLoan.to_lawful _ = Except.ok _›).1
  exact .of_raw (congrArg RawLoan.principalOutstanding hr :) (congrArg RawLoan.totalValueOutstanding hr :)
    (congrArg RawLoan.managementFeeOutstanding hr :) (congrArg RawLoan.paymentRemaining hr :)

/-- Changing the impairment owes the same. -/
private lemma Loan.changeImpairment_owesNoMore (loan : Loan) (v : Vault) (b : Bool) (r : LoanWithPool Vault)
    (h : (Loan.changeImpairment loan v b).run = .ok (.ok r)) : Loan.OwesNoMore loan r.loan' := by
  simp only [Loan.changeImpairment] at h
  unfold_ter at h
  walk_ok
  all_goals
    have hr := (RawLoan.to_lawful_ok ‹RawLoan.to_lawful _ = Except.ok _›).1
    exact .of_raw (congrArg RawLoan.principalOutstanding hr :) (congrArg RawLoan.totalValueOutstanding hr :)
      (congrArg RawLoan.managementFeeOutstanding hr :) (congrArg RawLoan.paymentRemaining hr :)

/-- An impair owes the same. -/
private lemma Loan.manageImpair_owesNoMore (loan : Loan) (v : Vault) (now : UInt32) (r : LoanWithPool Vault)
    (h : (loan.manageImpair v now).run = .ok (.ok r)) : Loan.OwesNoMore loan r.loan' := by
  simp only [Loan.manageImpair] at h
  unfold_ter at h
  walk_ok
  exact Loan.changeImpairment_owesNoMore loan v true r ‹_›

/-- A default leaves nothing owed. -/
private lemma Loan.manageDefault_owesNoMore (loan : Loan) (v : Vault) (r : LoanWithAmounts Vault)
    (h : (loan.manageDefault v).run = .ok (.ok r)) : Loan.OwesNoMore loan r.loan' := by
  obtain ⟨_, _, _, _, _, -, -, -, -, -, -, -, hloan, -⟩ := Loan.manageDefault_ok_parts loan v r h
  have hz : ∀ n : Number, n = Number.zero → n.toRat = 0 := fun n hn => by rw [hn, Number.toRat_zero]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hz _ (congrArg RawLoan.principalOutstanding hloan :)]
    exact (loan.exact.principalOutstanding_nonneg : 0 ≤ loan.principalOutstanding.toRat)
  · rw [hz _ (congrArg RawLoan.totalValueOutstanding hloan :)]
    exact (loan.exact.totalValueOutstanding_nonneg : 0 ≤ loan.totalValueOutstanding.toRat)
  · rw [hz _ (congrArg RawLoan.managementFeeOutstanding hloan :)]
    exact (loan.exact.managementFeeOutstanding_nonneg : 0 ≤ loan.managementFeeOutstanding.toRat)
  · rw [(congrArg RawLoan.paymentRemaining hloan :)]
    exact Nat.zero_le _

/-- A payment of any type owes no more. -/
private lemma Loan.pay_owesNoMore (loan : Loan) (v : Vault) (pt : LoanPaymentType) (amount : Number) (now : UInt32)
    (r : LoanWithAmounts Vault) (h : (loan.pay v pt amount now).run = .ok (.ok r)) : Loan.OwesNoMore loan r.loan' :=
  let ⟨h1, h2, h3, h4⟩ := Loan.pay_outstanding_le loan v pt amount now r h
  ⟨h1, h2, h3, UInt32.le_iff_toNat_le.mp h4⟩

/-- The loan part of the outstanding line of `Lending.Reachable.loan_lifetime`. -/
lemma Loan.ReachableFrom.outstanding_monotone_proof {start : Loan} {t₀ : UInt32} {loan : Loan} {t : UInt32}
    (hr : Loan.ReachableFrom start t₀ loan t) : Loan.OwesNoMore start loan := by
  induction hr with
  | refl => exact Loan.OwesNoMore.refl _
  | refresh _ _ _ _ _ _ h ih => exact ih.trans (Loan.refresh_owesNoMore h)
  | accept _ _ _ _ _ _ _ _ h ih => exact ih.trans (Loan.accept_owesNoMore _ _ _ h)
  | regularPayment _ _ _ _ _ _ _ _ _ h ih => exact ih.trans (Loan.pay_owesNoMore _ _ .regular _ _ _ h)
  | latePayment _ _ _ _ _ _ _ _ _ h ih => exact ih.trans (Loan.pay_owesNoMore _ _ .late _ _ _ h)
  | fullPayment _ _ _ _ _ _ _ _ _ h ih => exact ih.trans (Loan.pay_owesNoMore _ _ .full _ _ _ h)
  | overpayment _ _ _ _ _ _ _ _ _ h ih => exact ih.trans (Loan.pay_owesNoMore _ _ .overpayment _ _ _ h)
  | impair _ _ _ _ _ _ _ _ h ih => exact ih.trans (Loan.manageImpair_owesNoMore _ _ _ _ h)
  | unimpair _ _ _ _ _ _ _ _ h ih => exact ih.trans (Loan.changeImpairment_owesNoMore _ _ false _ h)
  | default _ _ _ _ _ _ _ _ h ih => exact ih.trans (Loan.manageDefault_owesNoMore _ _ _ h)

end XRPL.Model.Lending
