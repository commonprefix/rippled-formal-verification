import XRPL.Properties.Lending.Ledger.Common.LoanAccountingDefs
import XRPL.Properties.Lending.Ledger.Common.LoanRuns
import XRPL.Properties.Lending.Loan.Common.PaymentCount
import XRPL.Properties.Lending.Loan.Common.PayPrincipal
import XRPL.Properties.Lending.Loan.Common.PaySums
import XRPL.Properties.Lending.Loan.Common.ManageProofs

/-! # Where a loan's outstanding amounts go

Along a sequence of transactions, the loan at one slot changes only through the transactions on that loan. A payment
takes each scheduled instalment it pays off the loan exactly, an overpayment then re-amortizes it, a full payment
clears it and a default writes it off. LoanAccept, impair and unimpair change none of PrincipalOutstanding,
TotalValueOutstanding, ManagementFeeOutstanding and PaymentRemaining. -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault (Vault)

open private Loan.scheduledComponents Loan.doPayment UnsettledPayment.payInstalments
  from XRPL.Model.Lending.Loan.LoanPay
open private Loan.doPayment_outstanding from XRPL.Properties.Lending.Loan.Common.RegularInterest
open private Loan.Reachable.pay_facts from XRPL.Properties.Lending.Loan.Common.PaySums
open private Loan.lateComponents_scheduled from XRPL.Properties.Lending.Loan.Common.PayMonotone
open private Loan.changeImpairment from XRPL.Model.Lending.Loan.LoanManage

/-- ManagementFeeOutstanding is below `2^63` LoanScale units. -/
private lemma Loan.managementFee_lt (l : Loan) :
    l.managementFeeOutstanding.toRat < 2 ^ 63 * (10 : ℚ) ^ l.loanScale := by
  obtain ⟨m, hm, hmv⟩ := UnitsAt.of_atExponent l.wf.managementFeeOutstanding_norm
    (Loan.grid l).managementFeeOutstanding_atExponent
  have hB := NumericType.mantissaBound_le l.toExact.numericType
  have hpos : (0 : ℚ) < (10 : ℚ) ^ l.loanScale := zpow_pos (by norm_num) _
  rw [hmv.val]
  have : (m : ℚ) < 2 ^ 63 := by exact_mod_cast lt_of_lt_of_le hm hB
  exact mul_lt_mul_of_pos_right (by exact_mod_cast this) hpos

/-- One scheduled instalment, regular or late, takes its value delta, its management fee delta and one payment off
the loan. The last one clears the loan, and it comes only when one payment is left. -/
private lemma Loan.instalment_fields (l l' : Loan) (pc0 pc : PaymentComponents) (hlo : -81 ≤ l.loanScale)
    (hint : l.broker.numericType.isIntegral = true → l.loanScale ≤ 0) (hi : 0 ≤ l.toExact.interestDue)
    (hn : l.NeedsAllPayments) (hpr0 : l.paymentRemaining ≠ 0) (hpc0 : Loan.scheduledComponents l = .ok pc0)
    (hdo : Loan.doPayment l pc = .ok l') (e1 : pc.totalValueDelta = pc0.totalValueDelta)
    (e3 : pc.managementFeeDelta = pc0.managementFeeDelta) (e4 : pc.isFinal = pc0.isFinal) :
    l'.totalValueOutstanding.toRat = l.totalValueOutstanding.toRat - pc.totalValueDelta.toRat ∧
      l'.managementFeeOutstanding.toRat = l.managementFeeOutstanding.toRat - pc.managementFeeDelta.toRat ∧
      (l'.paymentRemaining.toNat : ℚ) = l.paymentRemaining.toNat - 1 := by
  have hpos : 1 ≤ l.paymentRemaining.toNat := by
    have := UInt32.toNat_inj.not.mpr hpr0
    simp at this
    omega
  obtain ⟨hfin, hstep⟩ := Loan.doPayment_outstanding l l' pc hdo
  rcases Loan.scheduledComponents_tracked l pc0 hlo hint hi hpc0 with hf | ⟨hf, ht⟩
  · have hf' : pc.isFinal = true := by rw [e4]; exact hf
    obtain ⟨s1, -, s3⟩ := (Loan.scheduledComponents_shape l pc0 hpc0).2 hf
    obtain ⟨z1, -, z3⟩ := hfin hf'
    -- the last instalment comes only with one payment left
    have hpr1 : l.paymentRemaining.toNat = 1 := by
      by_contra hne
      have hnf := hn.not_final (by omega) pc0 hpc0
      rw [hf] at hnf
      cases hnf
    refine ⟨by rw [z1, e1, s1, Number.toRat_zero]; ring, by rw [z3, e3, s3, Number.toRat_zero]; ring, ?_⟩
    rw [Loan.doPayment_final _ _ _ hf' hdo, hpr1]
    simp
  · have hf' : pc.isFinal = false := by rw [e4]; exact hf
    obtain ⟨d1, -, d3⟩ := hstep hf'
    rw [e1] at d1 ⊢
    rw [e3] at d3 ⊢
    obtain ⟨gT, -, gM, hTb, -, -, -⟩ := Loan.outstanding_grid l
    have hs := Loan.loanScale_bounds l
    refine ⟨Number.OnGrid.sub_exact gT ht.totalValue_grid ht.totalValue_range.1 ht.totalValue_range.2 hTb hs d1,
      Number.OnGrid.sub_exact gM ht.managementFee_grid ht.managementFee_range.1 ht.managementFee_range.2
        (Loan.managementFee_lt l) hs d3, ?_⟩
    rw [(Loan.doPayment_notFinal _ _ _ hf' hdo).1,
      UInt32.toNat_sub_of_le _ _ (by rw [UInt32.le_iff_toNat_le]; simp; omega)]
    simp only [UInt32.toNat_one]
    push_cast [hpos]
    ring

/-- The instalment loop takes each instalment `Loan.scheduledInstalments` lists off the loan: its value delta, its
management fee delta and one payment. -/
private lemma UnsettledPayment.payInstalments_fields (amount : Number) :
    ∀ (n : Nat) (payment p : UnsettledPayment Vault), UnsettledPayment.payInstalments payment n amount = .ok p →
      -81 ≤ payment.loan.loanScale →
      (payment.loan.broker.numericType.isIntegral = true → payment.loan.loanScale ≤ 0) →
      0 ≤ payment.loan.toExact.interestDue → payment.loan.NeedsAllPayments →
      ∃ pcs, payment.loan.scheduledInstalments payment.totalPaid amount n = .ok pcs ∧
        p.loan.totalValueOutstanding.toRat =
          payment.loan.totalValueOutstanding.toRat - (pcs.map fun pc => pc.totalValueDelta.toRat).sum ∧
        p.loan.managementFeeOutstanding.toRat =
          payment.loan.managementFeeOutstanding.toRat - (pcs.map fun pc => pc.managementFeeDelta.toRat).sum ∧
        (p.loan.paymentRemaining.toNat : ℚ) = payment.loan.paymentRemaining.toNat - pcs.length := by
  intro n
  induction n with
  | zero =>
    intro payment p h _ _ _ _
    rw [UnsettledPayment.payInstalments] at h
    obtain rfl := Except.ok.inj h
    exact ⟨[], rfl, by simp, by simp, by simp⟩
  | succ n ih =>
    intro payment p h hlo hint hi hn
    rw [UnsettledPayment.payInstalments] at h
    unfold_ter at h
    walk_ok
    · -- the loan is paid off: no instalment
      refine ⟨[], ?_, by simp, by simp, by simp⟩
      rw [Loan.scheduledInstalments]
      unfold_ter
      simp only [‹(payment.loan.paymentRemaining == 0) = true›, ↓reduceIte]
    · -- the amount does not cover the next instalment
      refine ⟨[], ?_, by simp, by simp, by simp⟩
      rw [Loan.scheduledInstalments]
      unfold_ter
      simp only [‹¬(payment.loan.paymentRemaining == 0) = true›, ‹Loan.scheduledComponents payment.loan = _›,
        ‹PaymentComponents.totalDue _ = _›, ‹payment.totalPaid.operator_add _ _ = _›,
        ‹amount.operator_lt _ = true›, Bool.false_eq_true, ↓reduceIte]
    all_goals
      have hpr0 : payment.loan.paymentRemaining ≠ 0 := by
        simpa using ‹¬(payment.loan.paymentRemaining == 0) = true›
      have hsc := ‹Loan.scheduledComponents payment.loan = _›
      have hdo := ‹Loan.doPayment payment.loan _ = _›
      obtain ⟨f1, f3, f4⟩ := Loan.instalment_fields _ _ _ _ hlo hint hi hn hpr0 hsc hdo rfl rfl rfl
    · -- the last instalment
      rename_i hfin
      refine ⟨?pcs, ?hw, ?_, ?_, ?_⟩
      case hw =>
        rw [Loan.scheduledInstalments]
        unfold_ter
        simp only [‹¬(payment.loan.paymentRemaining == 0) = true›, hsc, ‹PaymentComponents.totalDue _ = _›,
          ‹payment.totalPaid.operator_add _ _ = _›, ‹¬amount.operator_lt _ = true›, hdo, Bool.false_eq_true,
          ↓reduceIte]
        simp only [hfin, ↓reduceIte]
        rfl
      · simpa using f1
      · simpa using f3
      · simpa using f4
    · -- an instalment that is not the last, then the rest of the loop
      rename_i hfin hrec
      obtain ⟨hn', hi'⟩ := Loan.doPayment_needs _ _ _ _ hlo hint hi hn hpr0 hsc hdo rfl rfl rfl rfl
      have hst := Loan.doPayment_sameTerms _ _ _ hdo
      obtain ⟨pcs, hw, g1, g3, g4⟩ := ih _ p hrec (by dsimp only; rw [hst.loanScale]; exact hlo)
        (by dsimp only; rw [hst.loanScale, hst.broker]; exact hint) hi' hn'
      dsimp only at hw g1 g3 g4
      refine ⟨?pc :: pcs, ?hw, ?_, ?_, ?_⟩
      case hw =>
        rw [Loan.scheduledInstalments]
        unfold_ter
        simp only [‹¬(payment.loan.paymentRemaining == 0) = true›, hsc, ‹PaymentComponents.totalDue _ = _›,
          ‹payment.totalPaid.operator_add _ _ = _›, ‹¬amount.operator_lt _ = true›, hdo, hw, Bool.false_eq_true,
          ↓reduceIte]
        simp only [hfin, Bool.false_eq_true, ↓reduceIte]
        rfl
      · rw [g1, f1]; simp only [List.map_cons, List.sum_cons]; ring
      · rw [g3, f3]; simp only [List.map_cons, List.sum_cons]; ring
      · rw [g4, f4]; simp only [List.length_cons]; push_cast; ring

/-- The loan a transaction reads at `i`. -/
private lemma LendingLedger.loanRead_of {l : LendingLedger} {i : Nat} {loan : Loan} (h : l.LoanAt i loan) :
    l.loanRead i = some loan := by
  obtain ⟨e, b, he, hb, hw⟩ := h
  simp only [LendingLedger.loanRead, he, hb, hw]

/-- Two loans with the same four outstanding amounts. -/
private def Loan.SameOutstanding (x y : Loan) : Prop :=
  y.principalOutstanding = x.principalOutstanding ∧ y.totalValueOutstanding = x.totalValueOutstanding ∧
    y.managementFeeOutstanding = x.managementFeeOutstanding ∧ y.paymentRemaining = x.paymentRemaining

/-- A loan rebuilt from a record that changes no outstanding amount keeps them. -/
private lemma Loan.SameOutstanding.of_raw {x y : Loan} {raw : RawLoan} (h : y.toRawLoan = raw)
    (h1 : raw.principalOutstanding = x.principalOutstanding)
    (h2 : raw.totalValueOutstanding = x.totalValueOutstanding)
    (h3 : raw.managementFeeOutstanding = x.managementFeeOutstanding)
    (h4 : raw.paymentRemaining = x.paymentRemaining) : x.SameOutstanding y := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [show y.principalOutstanding = y.toRawLoan.principalOutstanding from rfl, h, h1]
  · rw [show y.totalValueOutstanding = y.toRawLoan.totalValueOutstanding from rfl, h, h2]
  · rw [show y.managementFeeOutstanding = y.toRawLoan.managementFeeOutstanding from rfl, h, h3]
  · rw [show y.paymentRemaining = y.toRawLoan.paymentRemaining from rfl, h, h4]

/-- LoanAccept, impair and unimpair change none of the four outstanding amounts. -/
private lemma Loan.accept_same (loan : Loan) (v : Vault) (r : LoanWithDisbursement Vault)
    (h : (loan.accept v).run = .ok (.ok r)) : loan.SameOutstanding r.loan' := by
  simp only [Loan.accept] at h
  unfold_ter at h
  walk_ok
  have hl := ‹RawLoan.to_lawful _ = Except.ok _›
  exact Loan.SameOutstanding.of_raw (RawLoan.to_lawful_ok hl).1 rfl rfl rfl rfl

private lemma Loan.changeImpairment_same (loan : Loan) (v : Vault) (b : Bool) (r : LoanWithPool Vault)
    (h : (Loan.changeImpairment loan v b).run = .ok (.ok r)) : loan.SameOutstanding r.loan' := by
  simp only [Loan.changeImpairment] at h
  unfold_ter at h
  walk_ok
  all_goals
    have hl := ‹RawLoan.to_lawful _ = Except.ok _›
    exact Loan.SameOutstanding.of_raw (RawLoan.to_lawful_ok hl).1 rfl rfl rfl rfl

/-- A default clears all four outstanding amounts. -/
private lemma Loan.manageDefault_cleared (loan : Loan) (v : Vault) (r : LoanWithAmounts Vault)
    (h : (loan.manageDefault v).run = .ok (.ok r)) :
    r.loan'.principalOutstanding = Number.zero ∧ r.loan'.totalValueOutstanding = Number.zero ∧
      r.loan'.managementFeeOutstanding = Number.zero ∧ r.loan'.paymentRemaining = 0 := by
  obtain ⟨_, _, _, _, _, -, -, -, -, -, -, -, hloan, -⟩ := Loan.manageDefault_ok_parts loan v r h
  refine ⟨?_, ?_, ?_, ?_⟩
  · show r.loan'.toRawLoan.principalOutstanding = _; rw [hloan]; rfl
  · show r.loan'.toRawLoan.totalValueOutstanding = _; rw [hloan]; rfl
  · show r.loan'.toRawLoan.managementFeeOutstanding = _; rw [hloan]; rfl
  · show r.loan'.toRawLoan.paymentRemaining = _; rw [hloan]; rfl

/-- A LoanPay on the loan at `i` takes off the principal it pays, its scheduled instalments, its overpayment and its
full payment. -/
private lemma LendingLedger.pay_fields {l l' : LendingLedger} (hr : l.Reachable) {i : Nat} {pt : LoanPaymentType}
    {amount : Number} (h : (l.apply (.loanPay i pt amount)).run = .ok (.ok l')) {x y : Loan}
    (hx : l.LoanAt i x) (hy : l'.LoanAt i y) :
    y.principalOutstanding.toRat = x.principalOutstanding.toRat - l.loanPrincipalPaidOf i (.loanPay i pt amount) ∧
      y.totalValueOutstanding.toRat = x.totalValueOutstanding.toRat - l.scheduledValueOf i (.loanPay i pt amount) -
        l.overpaymentValueOf i (.loanPay i pt amount) - l.fullPaymentValueOf i (.loanPay i pt amount) ∧
      y.managementFeeOutstanding.toRat = x.managementFeeOutstanding.toRat -
        l.scheduledFeeOf i (.loanPay i pt amount) - l.overpaymentFeeOf i (.loanPay i pt amount) -
        l.fullPaymentFeeOf i (.loanPay i pt amount) ∧
      (y.paymentRemaining.toNat : ℚ) = x.paymentRemaining.toNat - l.scheduledPaymentsOf i (.loanPay i pt amount) -
        l.fullPaymentPaymentsOf i (.loanPay i pt amount) := by
  obtain ⟨e, loan, r, -, hat, -, -, hpay, -, -, hat', -, -⟩ := LendingLedger.loanPay_ok h
  obtain rfl := hat.eq hx
  obtain rfl := hat'.eq hy
  have hread := LendingLedger.loanRead_of hat
  obtain ⟨t, -, hreach⟩ := hr.loanAt_reachable hat
  obtain ⟨hlo, hint, hi, -, -⟩ := Loan.Reachable.pay_facts hreach
  have hn : loan.unimpaired.NeedsAllPayments :=
    (Loan.Reachable.needsAllPayments hreach).of_same rfl rfl rfl rfl rfl
  obtain ⟨p, hp, hs⟩ := Loan.pay_ok loan l.vault pt amount l.now r hpay
  -- the settlement only gives the paid loan its new broker
  obtain ⟨_, _, _, _, _, _, _, -, -, -, -, hloan, -, -⟩ := UnsettledPayment.settle_ok p r hs
  obtain ⟨y1, y2, y3, y4⟩ : p.loan.SameOutstanding r.loan' :=
    Loan.SameOutstanding.of_raw (RawLoan.to_lawful_ok hloan).1 rfl rfl rfl rfl
  obtain ⟨-, -, hpe⟩ := Loan.payInstalments_paidOn loan l.vault pt amount l.now p (hr.loanScale_range hat) hp
  have hpaid : l.loanPrincipalPaidOf i (.loanPay i pt amount) = p.amounts.principalPaid.toRat := by
    simp only [LendingLedger.loanPrincipalPaidOf, ↓reduceIte, hread, hp]
  have hpr0 := (Loan.payInstalments_ok loan l.vault pt amount l.now p hp).1.remaining
  rw [y1, y2, y3, y4, hpaid]
  refine ⟨by linarith, ?_⟩
  have u1 : loan.unimpaired.totalValueOutstanding = loan.totalValueOutstanding := rfl
  have u3 : loan.unimpaired.managementFeeOutstanding = loan.managementFeeOutstanding := rfl
  have u4 : loan.unimpaired.paymentRemaining = loan.paymentRemaining := rfl
  cases pt
  · -- regular: the scheduled instalments
    obtain ⟨si, -, hloop, -⟩ := Loan.payScheduled_loop loan l.vault amount l.now p hp
    obtain ⟨pcs, hw, g1, g3, g4⟩ := UnsettledPayment.payInstalments_fields amount _ _ p hloop hlo hint hi hn
    dsimp only at hw g1 g3 g4
    rw [u1] at g1
    rw [u3] at g3
    rw [u4] at g4
    have hsched : l.scheduledInstalmentsOf i (.loanPay i .regular amount) = pcs := by
      simp only [LendingLedger.scheduledInstalmentsOf, ↓reduceIte, hread, hw]
    simp only [LendingLedger.scheduledValueOf, LendingLedger.scheduledFeeOf, LendingLedger.scheduledPaymentsOf,
      hsched, LendingLedger.overpaymentValueOf, LendingLedger.overpaymentFeeOf, LendingLedger.fullPaymentValueOf,
      LendingLedger.fullPaymentFeeOf, LendingLedger.fullPaymentPaymentsOf]
    exact ⟨by rw [g1]; ring, by rw [g3]; ring, by rw [g4]; ring⟩
  · -- late: one scheduled instalment on the loan without its impaired flag
    obtain ⟨pc, hpc, -, hdo⟩ := Loan.latePayInstalments_ok loan l.vault amount l.now p hp
    obtain ⟨pc0, hpc0, e1, -, e3, e4⟩ := Loan.lateComponents_scheduled loan l.now pc hpc
    obtain ⟨f1, f3, f4⟩ := Loan.instalment_fields loan.unimpaired p.loan pc0 pc hlo hint hi hn hpr0
      (by rw [Loan.scheduledComponents_unimpaired]; exact hpc0) hdo e1 e3 e4
    rw [u1] at f1
    rw [u3] at f3
    rw [u4] at f4
    have hsched : l.scheduledInstalmentsOf i (.loanPay i .late amount) = [pc] := by
      simp only [LendingLedger.scheduledInstalmentsOf, ↓reduceIte, hread, Loan.paymentComponents, hpc]
    simp only [LendingLedger.scheduledValueOf, LendingLedger.scheduledFeeOf, LendingLedger.scheduledPaymentsOf,
      hsched, LendingLedger.overpaymentValueOf, LendingLedger.overpaymentFeeOf, LendingLedger.fullPaymentValueOf,
      LendingLedger.fullPaymentFeeOf, LendingLedger.fullPaymentPaymentsOf]
    refine ⟨by rw [f1]; simp, by rw [f3]; simp, by rw [f4]; simp⟩
  · -- full: the payoff clears what is left
    obtain ⟨pc, hpc, -, hdo⟩ := Loan.fullPayInstalments_ok loan l.vault amount l.now p hp
    have hf : pc.isFinal = true := by
      obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, -, -, -, -, -, -, -, -, -, -, -, rfl⟩ :=
        Loan.fullComponents_ok_inv loan l.now pc hpc
      rfl
    obtain ⟨z1, -, z3⟩ := (Loan.doPayment_outstanding _ _ _ hdo).1 hf
    have z4 := Loan.doPayment_final _ _ _ hf hdo
    simp only [LendingLedger.scheduledValueOf, LendingLedger.scheduledFeeOf, LendingLedger.scheduledPaymentsOf,
      LendingLedger.scheduledInstalmentsOf, LendingLedger.overpaymentValueOf, LendingLedger.overpaymentFeeOf,
      LendingLedger.fullPaymentValueOf, LendingLedger.fullPaymentFeeOf, LendingLedger.fullPaymentPaymentsOf,
      LendingLedger.loanField, ↓reduceIte, hread]
    rw [z1, z3, z4]
    simp [Number.toRat_zero]
  · -- overpayment: the scheduled instalments, then the re-amortization
    obtain ⟨p0, h0, h1⟩ := Loan.overPayInstalments_ok loan l.vault amount l.now p hp
    obtain ⟨si, -, hloop, -⟩ := Loan.payScheduled_loop loan l.vault amount l.now p0 h0
    obtain ⟨pcs, hw, g1, g3, g4⟩ := UnsettledPayment.payInstalments_fields amount _ _ p0 hloop hlo hint hi hn
    dsimp only at hw g1 g3 g4
    rw [u1] at g1
    rw [u3] at g3
    rw [u4] at g4
    obtain ⟨-, -, -, -, hpr, -⟩ := UnsettledPayment.applyOverpayment_sameTerms p0 p amount h1
    have hsched : l.scheduledInstalmentsOf i (.loanPay i .overpayment amount) = pcs := by
      simp only [LendingLedger.scheduledInstalmentsOf, ↓reduceIte, hread, hw]
    have hover : l.overpaymentLoans i amount = some (p0.loan, p.loan) := by
      simp only [LendingLedger.overpaymentLoans, hread, h0, hp]
    simp only [LendingLedger.scheduledValueOf, LendingLedger.scheduledFeeOf, LendingLedger.scheduledPaymentsOf,
      hsched, LendingLedger.overpaymentValueOf, LendingLedger.overpaymentFeeOf, LendingLedger.fullPaymentValueOf,
      LendingLedger.fullPaymentFeeOf, LendingLedger.fullPaymentPaymentsOf, ↓reduceIte, hover]
    exact ⟨by rw [g1]; ring, by rw [g3]; ring, by rw [hpr, g4]; ring⟩

/-- A transaction that is no LoanPay on the loan at `i` pays nothing on it. -/
private lemma LendingLedger.payOf_zero (l : LendingLedger) {i : Nat} {tx : LendingTx}
    (hop : ∀ pt amount, tx ≠ .loanPay i pt amount) :
    l.loanPrincipalPaidOf i tx = 0 ∧ l.scheduledValueOf i tx = 0 ∧ l.scheduledFeeOf i tx = 0 ∧
      l.scheduledPaymentsOf i tx = 0 ∧ l.overpaymentValueOf i tx = 0 ∧ l.overpaymentFeeOf i tx = 0 ∧
      l.fullPaymentValueOf i tx = 0 ∧ l.fullPaymentFeeOf i tx = 0 ∧ l.fullPaymentPaymentsOf i tx = 0 := by
  have hs : l.scheduledInstalmentsOf i tx = [] := by
    cases tx with
    | loanPay j pt amount =>
      have hji : j ≠ i := fun hji => hop pt amount (by rw [hji])
      simp [LendingLedger.scheduledInstalmentsOf, hji]
    | _ => rfl
  simp only [LendingLedger.scheduledValueOf, LendingLedger.scheduledFeeOf, LendingLedger.scheduledPaymentsOf, hs,
    List.map_nil, List.sum_nil, List.length_nil, Nat.cast_zero, true_and]
  cases tx with
  | loanPay j pt amount =>
    have hji : j ≠ i := fun hji => hop pt amount (by rw [hji])
    cases pt <;> simp [LendingLedger.loanPrincipalPaidOf, LendingLedger.overpaymentValueOf,
      LendingLedger.overpaymentFeeOf, LendingLedger.fullPaymentValueOf, LendingLedger.fullPaymentFeeOf,
      LendingLedger.fullPaymentPaymentsOf, hji]
  | _ => simp [LendingLedger.loanPrincipalPaidOf, LendingLedger.overpaymentValueOf,
      LendingLedger.overpaymentFeeOf, LendingLedger.fullPaymentValueOf, LendingLedger.fullPaymentFeeOf,
      LendingLedger.fullPaymentPaymentsOf]

/-- A transaction that is no default of the loan at `i` writes nothing off it. -/
private lemma LendingLedger.defaultOf_zero (l : LendingLedger) {i : Nat} {tx : LendingTx}
    (hop : tx ≠ .loanManage i .default) :
    l.defaultPrincipalOf i tx = 0 ∧ l.defaultValueOf i tx = 0 ∧ l.defaultFeeOf i tx = 0 ∧
      l.defaultPaymentsOf i tx = 0 := by
  cases tx with
  | loanManage j action =>
    cases action
    · simp [LendingLedger.defaultPrincipalOf, LendingLedger.defaultValueOf, LendingLedger.defaultFeeOf,
        LendingLedger.defaultPaymentsOf]
    · simp [LendingLedger.defaultPrincipalOf, LendingLedger.defaultValueOf, LendingLedger.defaultFeeOf,
        LendingLedger.defaultPaymentsOf]
    · have hji : j ≠ i := fun hji => hop (by rw [hji])
      simp [LendingLedger.defaultPrincipalOf, LendingLedger.defaultValueOf, LendingLedger.defaultFeeOf,
        LendingLedger.defaultPaymentsOf, hji]
  | _ => simp [LendingLedger.defaultPrincipalOf, LendingLedger.defaultValueOf, LendingLedger.defaultFeeOf,
      LendingLedger.defaultPaymentsOf]

/-- Impairing a loan changes none of its outstanding amounts. -/
private lemma Loan.manageImpair_same (loan : Loan) (v : Vault) (now : UInt32) (r : LoanWithPool Vault)
    (h : (loan.manageImpair v now).run = .ok (.ok r)) : loan.SameOutstanding r.loan' := by
  simp only [Loan.manageImpair, Loan.changeImpairment] at h
  unfold_ter at h
  walk_ok
  have hl := ‹RawLoan.to_lawful _ = Except.ok _›
  exact Loan.SameOutstanding.of_raw (RawLoan.to_lawful_ok hl).1 rfl rfl rfl rfl

/-- One transaction on a reachable ledger, read at slot `i`. The loan there loses exactly what the transaction takes
off it, and nothing when the transaction is not on that loan. -/
private lemma LendingLedger.loan_fields_step {l l' : LendingLedger} (hr : l.Reachable) {tx : LendingTx}
    (h : (l.apply tx).run = .ok (.ok l')) {i : Nat} {x y : Loan} (hx : l.LoanAt i x) (hy : l'.LoanAt i y) :
    y.principalOutstanding.toRat =
        x.principalOutstanding.toRat - l.loanPrincipalPaidOf i tx - l.defaultPrincipalOf i tx ∧
      y.totalValueOutstanding.toRat = x.totalValueOutstanding.toRat - l.scheduledValueOf i tx -
        l.overpaymentValueOf i tx - l.fullPaymentValueOf i tx - l.defaultValueOf i tx ∧
      y.managementFeeOutstanding.toRat = x.managementFeeOutstanding.toRat - l.scheduledFeeOf i tx -
        l.overpaymentFeeOf i tx - l.fullPaymentFeeOf i tx - l.defaultFeeOf i tx ∧
      (y.paymentRemaining.toNat : ℚ) = x.paymentRemaining.toNat - l.scheduledPaymentsOf i tx -
        l.fullPaymentPaymentsOf i tx - l.defaultPaymentsOf i tx := by
  -- a transaction that keeps the four amounts and takes nothing off them
  have hkeep : x.SameOutstanding y → (∀ pt amount, tx ≠ .loanPay i pt amount) → tx ≠ .loanManage i .default →
      y.principalOutstanding.toRat =
          x.principalOutstanding.toRat - l.loanPrincipalPaidOf i tx - l.defaultPrincipalOf i tx ∧
        y.totalValueOutstanding.toRat = x.totalValueOutstanding.toRat - l.scheduledValueOf i tx -
          l.overpaymentValueOf i tx - l.fullPaymentValueOf i tx - l.defaultValueOf i tx ∧
        y.managementFeeOutstanding.toRat = x.managementFeeOutstanding.toRat - l.scheduledFeeOf i tx -
          l.overpaymentFeeOf i tx - l.fullPaymentFeeOf i tx - l.defaultFeeOf i tx ∧
        (y.paymentRemaining.toNat : ℚ) = x.paymentRemaining.toNat - l.scheduledPaymentsOf i tx -
          l.fullPaymentPaymentsOf i tx - l.defaultPaymentsOf i tx := by
    intro hsame hpay hdef
    obtain ⟨s1, s2, s3, s4⟩ := hsame
    obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9⟩ := l.payOf_zero hpay
    obtain ⟨b1, b2, b3, b4⟩ := l.defaultOf_zero hdef
    rw [s1, s2, s3, s4, a1, a2, a3, a4, a5, a6, a7, a8, a9, b1, b2, b3, b4]
    simp
  by_cases hop : tx = .loanAccept i ∨ (∃ action, tx = .loanManage i action) ∨
    ∃ pt amount, tx = .loanPay i pt amount
  · rcases hop with rfl | ⟨action, rfl⟩ | ⟨pt, amount, rfl⟩
    · obtain ⟨-, loan, r, -, hat, -, hacc, -, -, hat', -, -⟩ := LendingLedger.loanAccept_ok h
      obtain rfl := hat.eq hx
      obtain rfl := hat'.eq hy
      exact hkeep (Loan.accept_same loan l.vault r hacc) (fun _ _ => by simp) (by simp)
    · cases action with
      | impair =>
        obtain ⟨-, loan, r, -, hat, -, hm, -, -, hat', -, -⟩ := LendingLedger.loanImpair_ok h
        obtain rfl := hat.eq hx
        obtain rfl := hat'.eq hy
        exact hkeep (Loan.manageImpair_same loan l.vault l.now r hm) (fun _ _ => by simp) (by simp)
      | unimpair =>
        obtain ⟨-, loan, r, -, hat, -, hm, -, -, hat', -, -⟩ := LendingLedger.loanUnimpair_ok h
        obtain rfl := hat.eq hx
        obtain rfl := hat'.eq hy
        exact hkeep (Loan.changeImpairment_same loan l.vault false r hm) (fun _ _ => by simp) (by simp)
      | default =>
        obtain ⟨-, loan, r, -, hat, -, hm, -, -, hat', -, -⟩ := LendingLedger.loanDefault_ok h
        obtain rfl := hat.eq hx
        obtain rfl := hat'.eq hy
        obtain ⟨c1, c2, c3, c4⟩ := Loan.manageDefault_cleared loan l.vault r hm
        obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9⟩ := l.payOf_zero (i := i) (tx := .loanManage i .default)
          (fun _ _ => by simp)
        have hread := LendingLedger.loanRead_of hat
        rw [a1, a2, a3, a4, a5, a6, a7, a8, a9, c1, c2, c3, c4]
        simp [LendingLedger.defaultPrincipalOf, LendingLedger.defaultValueOf, LendingLedger.defaultFeeOf,
          LendingLedger.defaultPaymentsOf, LendingLedger.loanField, hread, Number.toRat_zero]
    · obtain ⟨b1, b2, b3, b4⟩ := l.defaultOf_zero (i := i) (tx := .loanPay i pt amount) (by simp)
      obtain ⟨p1, p2, p3, p4⟩ := LendingLedger.pay_fields hr h hx hy
      rw [b1, b2, b3, b4]
      exact ⟨by rw [p1]; ring, by rw [p2]; ring, by rw [p3]; ring, by rw [p4]; ring⟩
  -- not an operation on the loan at `i`: at most its broker copy changes
  have hlt : i < l.loans.length := by
    obtain ⟨e, _, he, -⟩ := hx
    exact LendingLedger.loan?_lt he
  obtain ⟨-, hs⟩ := LendingLedger.apply_loanSlot h hlt
  rcases hs with hs | rfl | hop'
  · obtain ⟨x', b, hx', -, hw⟩ := LendingLedger.loanAt_refresh hr (hr.apply h) hs hy
    obtain rfl := hx'.eq hx
    have hraw := Loan.withBroker_eq hw
    refine hkeep (Loan.SameOutstanding.of_raw hraw rfl rfl rfl rfl)
      (fun pt amount he => hop (.inr (.inr ⟨pt, amount, he⟩)))
      (fun he => hop (.inr (.inl ⟨_, he⟩)))
  · obtain ⟨_, _, _, -, -, -, -, -, -, hnone, -⟩ := LendingLedger.loanDelete_ok h
    obtain ⟨e, _, he, -⟩ := hy
    rw [hnone] at he
    cases he
  · exact absurd hop' hop

/-- Over a sequence of transactions from a reachable ledger, a loan at slot `i` at both ends loses exactly what its
payments and its default take off it. PaymentRemaining is read as a rational. -/
lemma LendingLedger.loan_accounting_proof {start l : LendingLedger} {txs : List LendingTx} (hr : start.Reachable)
    (hrun : LendingLedger.Reaches start txs l) :
    ∀ i loan loan', start.LoanAt i loan → l.LoanAt i loan' →
      loan'.principalOutstanding.toRat =
          loan.principalOutstanding.toRat - start.loanPrincipalPaid i txs - start.defaultPrincipal i txs ∧
        loan'.totalValueOutstanding.toRat = loan.totalValueOutstanding.toRat - start.scheduledValue i txs -
          start.overpaymentValue i txs - start.fullPaymentValue i txs - start.defaultValue i txs ∧
        loan'.managementFeeOutstanding.toRat = loan.managementFeeOutstanding.toRat - start.scheduledFee i txs -
          start.overpaymentFee i txs - start.fullPaymentFee i txs - start.defaultFee i txs ∧
        (loan'.paymentRemaining.toNat : ℚ) = loan.paymentRemaining.toNat - start.scheduledPayments i txs -
          start.fullPaymentPayments i txs - start.defaultPayments i txs := by
  intro i loan loan' hat hat'
  suffices key : i < l.loans.length ∧ ∀ y, l.LoanAt i y →
      y.principalOutstanding.toRat =
          loan.principalOutstanding.toRat - start.loanPrincipalPaid i txs - start.defaultPrincipal i txs ∧
        y.totalValueOutstanding.toRat = loan.totalValueOutstanding.toRat - start.scheduledValue i txs -
          start.overpaymentValue i txs - start.fullPaymentValue i txs - start.defaultValue i txs ∧
        y.managementFeeOutstanding.toRat = loan.managementFeeOutstanding.toRat - start.scheduledFee i txs -
          start.overpaymentFee i txs - start.fullPaymentFee i txs - start.defaultFee i txs ∧
        (y.paymentRemaining.toNat : ℚ) = loan.paymentRemaining.toNat - start.scheduledPayments i txs -
          start.fullPaymentPayments i txs - start.defaultPayments i txs from key.2 loan' hat'
  clear hat'
  induction hrun with
  | refl =>
    refine ⟨?_, fun y hy => ?_⟩
    · obtain ⟨e, _, he, -⟩ := hat
      exact LendingLedger.loan?_lt he
    obtain rfl := hat.eq hy
    simp [LendingLedger.loanPrincipalPaid, LendingLedger.defaultPrincipal, LendingLedger.scheduledValue,
      LendingLedger.overpaymentValue, LendingLedger.fullPaymentValue, LendingLedger.defaultValue,
      LendingLedger.scheduledFee, LendingLedger.overpaymentFee, LendingLedger.fullPaymentFee,
      LendingLedger.defaultFee, LendingLedger.scheduledPayments, LendingLedger.fullPaymentPayments,
      LendingLedger.defaultPayments, LendingLedger.runSum]
  | @step txs₀ l₀ l₁ tx hprev hok ih =>
    obtain ⟨hik, hP⟩ := ih
    refine ⟨(LendingLedger.apply_loanSlot hok hik).1, fun y hy => ?_⟩
    have hr₀ := hprev.reachable hr
    obtain ⟨x, hx, -⟩ := LendingLedger.loanAt_apply hr₀ hok hik hy
    obtain ⟨p1, p2, p3, p4⟩ := hP x hx
    obtain ⟨s1, s2, s3, s4⟩ := LendingLedger.loan_fields_step hr₀ hok hx hy
    simp only [LendingLedger.loanPrincipalPaid, LendingLedger.defaultPrincipal, LendingLedger.scheduledValue,
      LendingLedger.overpaymentValue, LendingLedger.fullPaymentValue, LendingLedger.defaultValue,
      LendingLedger.scheduledFee, LendingLedger.overpaymentFee, LendingLedger.fullPaymentFee,
      LendingLedger.defaultFee, LendingLedger.scheduledPayments, LendingLedger.fullPaymentPayments,
      LendingLedger.defaultPayments] at p1 p2 p3 p4 ⊢
    simp only [LendingLedger.runSum_snoc hprev hok]
    exact ⟨by rw [s1, p1]; ring, by rw [s2, p2]; ring, by rw [s3, p3]; ring, by rw [s4, p4]; ring⟩

end XRPL.Model.Lending
