import XRPL.Properties.Lending.Ledger.Common.LoanRuns
import XRPL.Properties.Lending.Loan.Common.InterestMonotone
import XRPL.Properties.Lending.Loan.Common.Outstanding

/-! # A loan over a run of ledger transactions

The loan at `i` before and after a run: the terms stay, the amounts it owes never rise, and from a reachable ledger
interestDue never rises while the late and overpayment interest of its payments is at least zero. -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault (Vault)

/-- A loan and its copy with another broker have the same terms. -/
private lemma Loan.withBroker_keepsTerms {x y : Loan} {b : LoanBroker} (hw : x.withBroker b = .ok y) :
    Loan.KeepsTerms x y ∧ Loan.KeepsTerms y x := by
  have h : Loan.KeepsTerms x y := Loan.KeepsTerms.of_lawful (raw := { x.toRawLoan with broker := b }) hw rfl rfl
    rfl rfl rfl
  exact ⟨h, ⟨h.rates.symm, h.fees.symm, h.schedule.symm, h.loanScale.symm, h.allowsOverpayment.symm⟩⟩

/-- A loan and its copy with another broker owe the same. -/
private lemma Loan.withBroker_owesNoMore {x y : Loan} {b : LoanBroker} (hw : x.withBroker b = .ok y) :
    Loan.OwesNoMore x y ∧ Loan.OwesNoMore y x := by
  have hraw := Loan.withBroker_eq hw
  have h1 : y.principalOutstanding = x.principalOutstanding := (congrArg RawLoan.principalOutstanding hraw :)
  have h2 : y.totalValueOutstanding = x.totalValueOutstanding := (congrArg RawLoan.totalValueOutstanding hraw :)
  have h3 : y.managementFeeOutstanding = x.managementFeeOutstanding :=
    (congrArg RawLoan.managementFeeOutstanding hraw :)
  have h4 : y.paymentRemaining = x.paymentRemaining := (congrArg RawLoan.paymentRemaining hraw :)
  exact ⟨.of_raw h1 h2 h3 h4, .of_raw h1.symm h2.symm h3.symm h4.symm⟩

/-- Proof body of the fixed terms line of `Lending.Reachable.loan_lifetime`. -/
lemma LendingLedger.fixed_terms_proof (l l' : LendingLedger) (txs : List LendingTx) (i : Nat) (loan loan' : Loan)
    (hrun : LendingLedger.Reaches l txs l') (hat : l.LoanAt i loan) (hat' : l'.LoanAt i loan') :
    loan'.rates = loan.rates ∧ loan'.fees = loan.fees ∧ loan'.schedule.startDate = loan.schedule.startDate ∧
      loan'.schedule.paymentInterval = loan.schedule.paymentInterval ∧
      loan'.schedule.paymentTotal = loan.schedule.paymentTotal ∧
      loan'.schedule.gracePeriod = loan.schedule.gracePeriod ∧ loan'.loanScale = loan.loanScale ∧
      loan'.allowsOverpayment = loan.allowsOverpayment := by
  have h : Loan.KeepsTerms loan loan' := hrun.slot_rel (fun _ _ _ h₁ h₂ => h₁.trans h₂)
    (fun _ _ _ hw => Loan.withBroker_keepsTerms hw) (fun _ _ _ hf => hf.keepsTerms) hat hat'
  exact ⟨h.rates, h.fees, by rw [h.schedule], by rw [h.schedule], by rw [h.schedule], by rw [h.schedule],
    h.loanScale, h.allowsOverpayment⟩

/-- Proof body of the outstanding line of `Lending.Reachable.loan_lifetime`. -/
lemma LendingLedger.outstanding_monotone_proof (l l' : LendingLedger) (txs : List LendingTx) (i : Nat)
    (loan loan' : Loan) (hrun : LendingLedger.Reaches l txs l') (hat : l.LoanAt i loan) (hat' : l'.LoanAt i loan') :
    loan'.paymentRemaining.toNat ≤ loan.paymentRemaining.toNat ∧
      loan'.principalOutstanding.toRat ≤ loan.principalOutstanding.toRat ∧
      loan'.totalValueOutstanding.toRat ≤ loan.totalValueOutstanding.toRat ∧
      loan'.managementFeeOutstanding.toRat ≤ loan.managementFeeOutstanding.toRat :=
  let h : Loan.OwesNoMore loan loan' := hrun.slot_rel (fun _ _ _ h₁ h₂ => h₁.trans h₂)
    (fun _ _ _ hw => Loan.withBroker_owesNoMore hw) (fun _ _ _ hf => Loan.ReachableFrom.outstanding_monotone_proof hf)
    hat hat'
  ⟨h.paymentRemaining, h.principalOutstanding, h.totalValueOutstanding, h.managementFeeOutstanding⟩

/-- Proof body of `Lending.Reachable.interest_monotone`. -/
lemma LendingLedger.interest_monotone_proof (l l' : LendingLedger) (txs : List LendingTx) (i : Nat)
    (loan loan' : Loan) (hr : l.Reachable) (hrun : LendingLedger.Reaches l txs l') (hat : l.LoanAt i loan)
    (hat' : l'.LoanAt i loan')
    (hlate : ∀ (pre : List LendingTx) (l₁ l₂ : LendingLedger) (amount : Number) (loan₁ : Loan)
      (pc : PaymentComponents) (d : Number), pre ++ [.loanPay i .late amount] <+: txs →
      LendingLedger.Reaches l pre l₁ → (l₁.apply (.loanPay i .late amount)).run = .ok (.ok l₂) →
      l₁.LoanAt i loan₁ → loan₁.rates.lateInterestRate ≠ 0 → loan₁.paymentComponents .late l₁.now = .ok pc →
      pc.interestDelta = .ok d → 0 ≤ d.toRat)
    (hover : ∀ (pre : List LendingTx) (l₁ l₂ : LendingLedger) (amount : Number) (loan₁ : Loan)
      (p : UnsettledPayment Vault), pre ++ [.loanPay i .overpayment amount] <+: txs →
      LendingLedger.Reaches l pre l₁ → (l₁.apply (.loanPay i .overpayment amount)).run = .ok (.ok l₂) →
      l₁.LoanAt i loan₁ → loan₁.rates.overpaymentInterestRate ≠ 0 →
      (loan₁.payInstalments l₁.vault .regular amount l₁.now).run = .ok (.ok p) → 0 ≤ p.amounts.interestPaid.toRat) :
    loan'.toExact.interestDue ≤ loan.toExact.interestDue := by
  refine hrun.loanAt_induction (P := fun _ x => x.toExact.interestDue ≤ loan.toExact.interestDue) hr hat hat'
    (le_refl _) ?_
  intro pre lk lk' tx x y hpre hk hrk h hx hy hP hcase
  refine le_trans ?_ hP
  rcases hcase with ⟨b, -, hw⟩ | rfl | ⟨action, rfl⟩ | ⟨paymentType, amount, rfl⟩
  · have hraw := Loan.withBroker_eq hw
    exact le_of_eq (Loan.toExact_interestDue_congr (congrArg RawLoan.totalValueOutstanding hraw :)
      (congrArg RawLoan.principalOutstanding hraw :) (congrArg RawLoan.managementFeeOutstanding hraw :))
  · obtain ⟨_, x', r, -, hx', -, hok, -, -, hy', -⟩ := LendingLedger.loanAccept_ok h
    obtain rfl := hx.eq hx'
    obtain rfl := hy.eq hy'
    exact le_of_eq (Loan.accept_interestDue _ _ r hok)
  · cases action with
    | impair =>
      obtain ⟨_, x', r, -, hx', -, hok, -, -, hy', -⟩ := LendingLedger.loanImpair_ok h
      obtain rfl := hx.eq hx'
      obtain rfl := hy.eq hy'
      simp only [Loan.manageImpair] at hok
      unfold_ter at hok
      walk_ok
      exact le_of_eq (Loan.changeImpairment_interestDue _ _ true r ‹_›)
    | unimpair =>
      obtain ⟨_, x', r, -, hx', -, hok, -, -, hy', -⟩ := LendingLedger.loanUnimpair_ok h
      obtain rfl := hx.eq hx'
      obtain rfl := hy.eq hy'
      exact le_of_eq (Loan.changeImpairment_interestDue _ _ false r hok)
    | default =>
      obtain ⟨_, x', r, -, hx', -, hok, -, -, hy', -⟩ := LendingLedger.loanDefault_ok h
      obtain rfl := hx.eq hx'
      obtain rfl := hy.eq hy'
      obtain ⟨_, _, _, _, _, -, -, -, -, -, -, -, hloan, -⟩ := Loan.manageDefault_ok_parts _ _ r hok
      rw [Loan.interestDue_paid r.loan' (congrArg RawLoan.paymentRemaining hloan :)]
      obtain ⟨t, -, hre⟩ := hrk.loanAt_reachable hx
      exact Loan.Reachable.interestDue_nonneg hre
  · obtain ⟨_, x', r, -, hx', -, -, hok, -, -, hy', -⟩ := LendingLedger.loanPay_ok h
    obtain rfl := hx.eq hx'
    obtain rfl := hy.eq hy'
    obtain ⟨hlo, hhi⟩ := hrk.loanScale_range hx
    obtain ⟨t, -, hre⟩ := hrk.loanAt_reachable hx
    refine Loan.pay_interestDue_le _ _ paymentType amount _ r hlo (fun _ => hhi) (Loan.Reachable.interestDue_nonneg hre)
      ?_ ?_ hok
    · rintro rfl hne pc d hpc hd
      exact hlate pre lk lk' amount x pc d hpre hk h hx hne hpc hd
    · rintro rfl hne p hp
      exact hover pre lk lk' amount x p hpre hk h hx hne hp

end XRPL.Model.Lending
