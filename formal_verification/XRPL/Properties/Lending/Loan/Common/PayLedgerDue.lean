import XRPL.Properties.Lending.Loan.Common.PayLedger
import XRPL.Properties.Lending.Loan.Common.PayCharge
import XRPL.Properties.Lending.Loan.Common.PaySums
import XRPL.Properties.Lending.Loan.Common.ScheduledDue
import XRPL.Properties.Lending.Loan.Common.FullPaymentCost

/-! # What a LoanPay transaction charges

Proof bodies of the LoanPay headlines about the amount due: what each scheduled payment, a late payment and a payoff
charge, and how the charge splits into principal, interest and fees. -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault (Vault)

open private Loan.scheduledComponents Loan.lateComponents from XRPL.Model.Lending.Loan.LoanPay
open private Loan.payInstalment_parts Loan.instalment_charge Loan.late_instalment_charge Loan.Reachable.pay_facts
  from XRPL.Properties.Lending.Loan.Common.PaySums
open private Loan.unimpairIfImpaired_loan from XRPL.Properties.Lending.Loan.Common.PaySteps

/-- A payment of type `pt` on `loan` pays instalment `pc` of the loan `lk` it has reached, charging `q`: each scheduled
payment of a regular payment in turn, or the one late instalment on the loan without its impaired flag. -/
inductive Loan.PaysInstalment (loan : Loan) (v : Vault) (amount : Number) (now : UInt32) :
    LoanPaymentType → Loan → PaymentComponents → UnsettledPayment Vault → Prop where
  | scheduled {p : UnsettledPayment Vault} {k : Nat} {lk : Loan} {pc : PaymentComponents} {due : Number}
      {q : UnsettledPayment Vault} :
      (loan.payInstalments v .regular amount now).run = .ok (.ok p) → k < p.count → loan.ScheduledBefore now k lk →
      lk.paymentComponents .regular now = .ok pc → pc.totalDue = .ok due →
      (lk.payInstalment v pc due).run = .ok (.ok q) → Loan.PaysInstalment loan v amount now .regular lk pc q
  | late {p : UnsettledPayment Vault} {pc : PaymentComponents} :
      (loan.payInstalments v .late amount now).run = .ok (.ok p) →
      loan.unimpaired.paymentComponents .late now = .ok pc →
      Loan.PaysInstalment loan v amount now .late loan.unimpaired pc p

/-- One scheduled or late instalment of loan `l` charges exactly its totalDue: the value it takes off the loan plus
LoanServiceFee, and LatePaymentFee and the rounded late interest when late, while totalDue fits 16 digits. -/
private lemma Loan.instalment_split (l : Loan) (v : Vault) (amount : Number) (now : UInt32) (pt : LoanPaymentType)
    (pc : PaymentComponents) (q : UnsettledPayment Vault) (hlo : -81 ≤ l.loanScale)
    (hint : l.broker.numericType.isIntegral = true → l.loanScale ≤ 0) (hi : 0 ≤ l.toExact.interestDue)
    (gs : Number.OnGrid l.loanScale l.fees.serviceFee) (gl : Number.OnGrid l.loanScale l.fees.latePaymentFee)
    (hpt : pt = .regular ∨ pt = .late) (hpc : l.paymentComponents pt now = .ok pc)
    (hp : (l.payInstalment v pc amount).run = .ok (.ok q)) (hdue : q.totalPaid.toRat < 10 ^ 16 * 10 ^ l.loanScale) :
    q.amounts.principalPaid.toRat + q.amounts.interestPaid.toRat + q.amounts.feePaid.toRat = q.totalPaid.toRat ∧
      (pt = .regular → q.totalPaid.toRat = l.totalValueOutstanding.toRat -
        q.loan.totalValueOutstanding.toRat + l.fees.serviceFee.toRat) ∧
      (pt = .late → ∃ li lr, loanLatePaymentInterest l.principalOutstanding l.rates.lateInterestRate
          now l.nextPaymentDueDate = .ok li ∧
        STAmount.roundToNumericType l.broker.numericType li .to_nearest (some l.loanScale) = .ok lr ∧
        q.totalPaid.toRat = l.totalValueOutstanding.toRat - q.loan.totalValueOutstanding.toRat +
          l.fees.serviceFee.toRat + l.fees.latePaymentFee.toRat + lr.toRat) := by
  obtain ⟨hdue', hpa, hdo⟩ := Loan.payInstalment_parts l v pc amount q hp
  rcases hpt with rfl | rfl
  · simp only [Loan.paymentComponents] at hpc
    obtain ⟨pc0, hpc0, hpc⟩ := bind_ok_peel _ _ _ hpc
    obtain rfl := (Except.ok.inj hpc).symm
    have hu := (Loan.scheduledComponents_shape l pc0 hpc0).1
    obtain ⟨hsum, hval, -, -⟩ := Loan.instalment_charge l q.loan pc0
      { pc0 with untrackedManagementFee := l.fees.serviceFee } q.amounts q.totalPaid hlo hint hi hpc0 rfl rfl rfl
      rfl (by show Number.OnGrid _ pc0.untrackedInterest; rw [hu]; exact Number.OnGrid.zero _) gs
      (by show 0 ≤ pc0.untrackedInterest.toRat; rw [hu, Number.toRat_zero])
      (l.exact.serviceFee_nonneg) hpa hdue' hdo hdue
    refine ⟨hsum, fun _ => ?_, fun h => absurd h (by decide)⟩
    simp only at hval
    rw [hval, hu, Number.toRat_zero]
    ring
  · obtain ⟨hsum, hlate⟩ := Loan.late_instalment_charge l q.loan now pc q.amounts q.totalPaid hlo hint hi gs gl
      hpc hpa hdue' hdo hdue
    exact ⟨hsum, fun h => absurd h (by decide), fun _ => hlate⟩

/-- The late instalment a late payment pays on the loan without its impaired flag, on the vault after the
unimpair. -/
private lemma Loan.latePayInstalments_instalment (loan : Loan) (v : Vault) (amount : Number) (now : UInt32)
    (p : UnsettledPayment Vault) (hp : (loan.payInstalments v .late amount now).run = .ok (.ok p)) :
    ∃ v1 pc, Loan.lateComponents loan.unimpaired now = .ok pc ∧
      (loan.unimpaired.payInstalment v1 pc amount).run = .ok (.ok p) := by
  simp only [Loan.payInstalments] at hp
  unfold_ter at hp
  walk_ok
  rename_i a hu _ _ pc hpc _ hpi
  have hl := Loan.unimpairIfImpaired_loan loan v a (by simp only [ExceptT.run]; exact hu)
  obtain ⟨l1, p1⟩ := a
  simp only at hl hpc hpi
  subst hl
  exact ⟨p1, pc, hpc, by simp only [ExceptT.run]; exact hpi⟩

/-- Proof body of the requestedAmount part of `Lending.payment_charge`. -/
lemma LendingLedger.payment_charge_le_amount_proof (l : LendingLedger) (hr : l.Reachable) (l' : LendingLedger)
    (i : Nat) (paymentType : LoanPaymentType) (amount : Number)
    (h : (l.apply (.loanPay i paymentType amount)).run = .ok (.ok l')) (loan : Loan) (hat : l.LoanAt i loan)
    (p : UnsettledPayment Vault) (hp : (loan.payInstalments l.vault paymentType amount l.now).run = .ok (.ok p))
    (hdue : p.totalPaid.toRat < 10 ^ 16 * 10 ^ loan.loanScale) :
    p.amounts.principalPaid.toRat + p.amounts.interestPaid.toRat + p.amounts.feePaid.toRat ≤ amount.toRat := by
  obtain ⟨t, -, hreach⟩ := hr.loanAt_reachable hat
  have hamount := (LendingTx.loanPay_preflight_ok (LendingLedger.apply_preflight h)).1
  exact Loan.payment_charge_le_amount_proof loan l.vault amount l.now t paymentType p hreach hamount hp hdue

/-- Proof body of the totalDue part of `Lending.payment_charge`. -/
lemma LendingLedger.payment_split_proof (l : LendingLedger) (hr : l.Reachable) (l' : LendingLedger) (i : Nat)
    (paymentType : LoanPaymentType) (amount : Number)
    (h : (l.apply (.loanPay i paymentType amount)).run = .ok (.ok l')) (loan : Loan) (hat : l.LoanAt i loan)
    (lk : Loan) (pc : PaymentComponents) (q : UnsettledPayment Vault)
    (hq : loan.PaysInstalment l.vault amount l.now paymentType lk pc q)
    (hdue : q.totalPaid.toRat < 10 ^ 16 * 10 ^ loan.loanScale) :
    q.amounts.principalPaid.toRat + q.amounts.interestPaid.toRat + q.amounts.feePaid.toRat = q.totalPaid.toRat ∧
      (paymentType = .regular → q.totalPaid.toRat = lk.totalValueOutstanding.toRat -
        q.loan.totalValueOutstanding.toRat + lk.fees.serviceFee.toRat) ∧
      (paymentType = .late → ∃ li lr, loanLatePaymentInterest lk.principalOutstanding lk.rates.lateInterestRate
          l.now lk.nextPaymentDueDate = .ok li ∧
        STAmount.roundToNumericType lk.broker.numericType li .to_nearest (some lk.loanScale) = .ok lr ∧
        q.totalPaid.toRat = lk.totalValueOutstanding.toRat - q.loan.totalValueOutstanding.toRat +
          lk.fees.serviceFee.toRat + lk.fees.latePaymentFee.toRat + lr.toRat) := by
  obtain ⟨t, -, hreach⟩ := hr.loanAt_reachable hat
  obtain ⟨hlo, hint, hi, gs, gl⟩ := Loan.Reachable.pay_facts hreach
  cases hq with
  | scheduled hp hk hl hpc hdue' hq' =>
    -- the scheduled payments are the ones the transaction paid
    obtain ⟨p', -, rfl⟩ := LendingLedger.loanPay_instalments_eq h hat hp
    obtain ⟨e1, e2, e3, -, hi'⟩ := hl.facts hlo hint hi
    exact Loan.instalment_split lk l.vault _ l.now .regular pc q (by rw [e1]; exact hlo)
      (by rw [e1, e2]; exact hint) hi' (by rw [e1, e3]; exact gs) (by rw [e1, e3]; exact gl) (Or.inl rfl) hpc hq'
      (by rw [e1]; exact hdue)
  | late hp hpc =>
    -- the late instalment is the one the transaction paid
    obtain ⟨p', -, rfl⟩ := LendingLedger.loanPay_instalments_eq h hat hp
    obtain ⟨v1, pc', hpc', hpi⟩ := Loan.latePayInstalments_instalment loan l.vault amount l.now _ hp
    have hpc'' : Loan.lateComponents loan.unimpaired l.now = .ok pc := hpc
    rw [hpc''] at hpc'
    obtain rfl := Except.ok.inj hpc'
    exact Loan.instalment_split loan.unimpaired v1 amount l.now .late pc _ hlo hint hi gs gl (Or.inr rfl) hpc hpi
      hdue

/-- Proof body of `Lending.regularPayment_amount`. -/
lemma LendingLedger.regularPayment_amount_proof (l : LendingLedger) (hr : l.Reachable) (l' : LendingLedger) (i : Nat)
    (amount : Number) (h : (l.apply (.loanPay i .regular amount)).run = .ok (.ok l')) (loan : Loan)
    (hat : l.LoanAt i loan) (p : UnsettledPayment Vault)
    (hp : (loan.payInstalments l.vault .regular amount l.now).run = .ok (.ok p)) (k : Nat) (hk : k < p.count)
    (lk : Loan) (hl : loan.ScheduledBefore l.now k lk) (pc : PaymentComponents) (due pp' : Number)
    (hpc : lk.paymentComponents .regular l.now = .ok pc) (hdue : pc.totalDue = .ok due)
    (hpp : STAmount.roundToNumericType loan.broker.numericType loan.periodicPayment .upward (some loan.loanScale) =
      .ok pp')
    (hlast : lk.paymentRemaining ≠ 1) (hfit : p.totalPaid.toRat < 10 ^ 16 * 10 ^ loan.loanScale) :
    due.toRat ≤ pp'.toRat + loan.fees.serviceFee.toRat := by
  obtain ⟨t, -, hreach⟩ := hr.loanAt_reachable hat
  obtain ⟨q, hq, rfl⟩ := LendingLedger.loanPay_instalments_eq h hat hp
  exact Loan.regularPayment_amount_proof loan l.vault amount l.now t q k lk pc due pp' hreach hq hk hl hpc hdue hpp
    hlast hfit

/-- Proof body of `Lending.regularPayment_periodicPayment`. -/
lemma LendingLedger.regularPayment_periodicPayment_proof (l : LendingLedger) (hr : l.Reachable) (i : Nat)
    (amount : Number) (loan : Loan) (hat : l.LoanAt i loan) (lk : Loan) (pc : PaymentComponents)
    (q : UnsettledPayment Vault) (hq : loan.PaysInstalment l.vault amount l.now .regular lk pc q)
    (hleft : q.loan.paymentRemaining ≠ 0) :
    lk.totalValueOutstanding.toRat - q.loan.totalValueOutstanding.toRat - loan.periodicPayment.toRat <
      10 ^ loan.loanScale := by
  obtain ⟨t, -, hreach⟩ := hr.loanAt_reachable hat
  obtain ⟨hlo, hint, hi, -, -⟩ := Loan.Reachable.pay_facts hreach
  have hint0 := Loan.Reachable.loanScale_integral hreach
  cases hq with
  | scheduled _ _ hl hpc _ hpi =>
    obtain ⟨e1, e2, -, e4, hi'⟩ := hl.facts hlo hint hi
    rw [← e1, ← e4]
    exact Loan.scheduled_value_lt lk l.vault l.now pc _ q (by rw [e1]; exact hlo) (by rw [e1, e2]; exact hint0) hi'
      hpc hpi hleft

/-- Proof body of `Lending.fullPayment_cheaper`. -/
lemma LendingLedger.fullPayment_cheaper_proof (l : LendingLedger) (hr : l.Reachable) (l' : LendingLedger) (i : Nat)
    (amount : Number) (h : (l.apply (.loanPay i .full amount)).run = .ok (.ok l')) (loan : Loan)
    (hat : l.LoanAt i loan) (p : UnsettledPayment Vault)
    (hp : (loan.payInstalments l.vault .full amount l.now).run = .ok (.ok p))
    (hclose : loan.rates.closeInterestRate = 0)
    (hfee : loan.fees.closePaymentFee.toRat ≤ loan.fees.serviceFee.toRat)
    (hcover : ∀ rate tpo : Number, loan.periodicRate = .ok rate →
      loanPrincipalFromPeriodicPayment loan.periodicPayment rate loan.paymentRemaining = .ok tpo →
      tpo.toRat * rate.toRat ≤ loan.totalValueOutstanding.toRat - loan.principalOutstanding.toRat) :
    p.totalPaid.toRat ≤
      loan.totalValueOutstanding.toRat + loan.paymentRemaining.toNat * loan.fees.serviceFee.toRat := by
  obtain ⟨t, -, hreach⟩ := hr.loanAt_reachable hat
  obtain ⟨q, hq, rfl⟩ := LendingLedger.loanPay_instalments_eq h hat hp
  exact Loan.fullPayment_cheaper_proof loan l.vault amount l.now t hreach q hq hclose hfee hcover

end XRPL.Model.Lending
