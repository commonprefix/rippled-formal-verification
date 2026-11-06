import XRPL.Properties.Lending.Loan.Common.InstalmentCap
import XRPL.Properties.Lending.Loan.Common.OverpaymentReduces
import XRPL.Properties.Lending.Loan.Common.PaySums

/-! # What each scheduled payment of a regular payment is due

A regular payment pays the loan's scheduled payments in turn. Each one is due at most what the payment sums, and one
that is not the loan's last is due at most ⌈PeriodicPayment⌉ + LoanServiceFee while the amount fits 16 digits. It
also takes less than PeriodicPayment + 1 ULP at LoanScale off TotalValueOutstanding. -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault (Vault RawVault)

open private Loan.scheduledComponents Loan.doPayment UnsettledPayment.payInstalments
  from XRPL.Model.Lending.Loan.LoanPay
open private Loan.payInstalment_parts Loan.Reachable.pay_facts from XRPL.Properties.Lending.Loan.Common.PaySums
open private Loan.doPayment_interestDue from XRPL.Properties.Lending.Loan.Common.InterestDue
open private Loan.scheduledComponents_sound from XRPL.Properties.Lending.Loan.Common.PayMonotone
open private Loan.doPayment_periodicPayment from XRPL.Properties.Lending.Loan.Common.OverpaymentReduces
open private ite_bind_ok_cond from XRPL.Properties.Lending.Loan.Common.InstalmentCap
open private Loan.doPayment_value from XRPL.Properties.Lending.Loan.Common.ValueDecrease

/-- `l` is the loan before scheduled payment `k` (from `0`) of a payment on `loan` at `now`: `loan` without its
impaired flag, then the loan each scheduled payment leaves (`Loan.regularPayment_scheduled` walks exactly these). -/
inductive Loan.ScheduledBefore (loan : Loan) (now : UInt32) : Nat → Loan → Prop where
  | first : Loan.ScheduledBefore loan now 0 loan.unimpaired
  | next {k : Nat} {l : Loan} (v : Vault) (pc : PaymentComponents) (due : Number) (q : UnsettledPayment Vault) :
      Loan.ScheduledBefore loan now k l → l.paymentComponents .regular now = .ok pc → pc.totalDue = .ok due →
      (l.payInstalment v pc due).run = .ok (.ok q) → Loan.ScheduledBefore loan now (k + 1) q.loan

/-- The next scheduled payment is the next scheduled instalment with LoanServiceFee. -/
private lemma Loan.paymentComponents_regular (l : Loan) (now : UInt32) (pc : PaymentComponents)
    (h : l.paymentComponents .regular now = .ok pc) :
    ∃ pc0, Loan.scheduledComponents l = .ok pc0 ∧ pc = { pc0 with untrackedManagementFee := l.fees.serviceFee } := by
  simp only [Loan.paymentComponents] at h
  obtain ⟨pc0, hpc0, h⟩ := bind_ok_peel _ _ _ h
  exact ⟨pc0, hpc0, (Except.ok.inj h).symm⟩

/-- Each place in the schedule holds one loan. -/
lemma Loan.ScheduledBefore.unique {loan : Loan} {now : UInt32} {k : Nat} {l₁ l₂ : Loan}
    (h₁ : loan.ScheduledBefore now k l₁) (h₂ : loan.ScheduledBefore now k l₂) : l₁ = l₂ := by
  induction h₁ generalizing l₂ with
  | first => cases h₂; rfl
  | next v pc due q h hpc hdue hq ih =>
    cases h₂ with
    | next v' pc' due' q' h' hpc' hdue' hq' =>
      obtain rfl := ih h'
      rw [hpc] at hpc'
      obtain rfl := Except.ok.inj hpc'
      obtain ⟨-, -, hdo⟩ := Loan.payInstalment_parts _ _ _ _ _ hq
      obtain ⟨-, -, hdo'⟩ := Loan.payInstalment_parts _ _ _ _ _ hq'
      rw [hdo] at hdo'
      exact Except.ok.inj hdo'

/-- A loan in the schedule keeps LoanScale, the broker, the fees and PeriodicPayment, and its interestDue stays at
least zero. -/
lemma Loan.ScheduledBefore.facts {loan : Loan} {now : UInt32} {k : Nat} {l : Loan}
    (h : loan.ScheduledBefore now k l) (hlo : -81 ≤ loan.loanScale)
    (hint : loan.broker.numericType.isIntegral = true → loan.loanScale ≤ 0) (hi : 0 ≤ loan.toExact.interestDue) :
    l.loanScale = loan.loanScale ∧ l.broker = loan.broker ∧ l.fees = loan.fees ∧
      l.periodicPayment = loan.periodicPayment ∧ 0 ≤ l.toExact.interestDue := by
  induction h with
  | first => exact ⟨rfl, rfl, rfl, rfl, hi⟩
  | next v pc due q h hpc hdue hq ih =>
    obtain ⟨e1, e2, e3, e4, hi'⟩ := ih
    obtain ⟨-, -, hdo⟩ := Loan.payInstalment_parts _ _ _ _ _ hq
    obtain ⟨pc0, hpc0, rfl⟩ := Loan.paymentComponents_regular _ _ _ hpc
    have hst := Loan.doPayment_sameTerms _ _ _ hdo
    have hpp := Loan.doPayment_periodicPayment _ _ _ hdo
    refine ⟨hst.loanScale.trans e1, hst.broker.trans e2, hst.fees.trans e3, hpp.trans e4, ?_⟩
    refine Loan.doPayment_interestDue _ _ _ hi' ?_ hdo
    rcases Loan.scheduledComponents_tracked _ pc0 (by rw [e1]; exact hlo) (by rw [e1, e2]; exact hint) hi' hpc0 with
      hf | ⟨hf, ht⟩
    · exact Or.inl hf
    · exact Or.inr ⟨hf, ht.totalValue_grid, ht.principal_grid, ht.managementFee_grid, ht.totalValue_range,
        ht.principal_range, ht.managementFee_range, ht.interest_le, ht.managementFee_le_value⟩

/-- The next scheduled payment of a lawful loan is due a normalized amount, at least LoanServiceFee. -/
private lemma Loan.scheduled_due_ge (l : Loan) (pc0 : PaymentComponents) (due : Number)
    (hpc0 : Loan.scheduledComponents l = .ok pc0)
    (hdue : ({ pc0 with untrackedManagementFee := l.fees.serviceFee } : PaymentComponents).totalDue = .ok due) :
    due.isNormalized ∧ l.fees.serviceFee.toRat ≤ due.toRat := by
  obtain ⟨htvN, -, -, htv0, -, -⟩ := Loan.scheduledComponents_sound _ _ hpc0
  have hui := (Loan.scheduledComponents_shape _ _ hpc0).1
  unfold PaymentComponents.totalDue at hdue
  obtain ⟨v1, hv1, hdue⟩ := bind_ok_peel _ _ _ hdue
  simp only at hv1 hdue
  rw [hui, Number.operator_add_zero_right, Except.ok.injEq] at hv1
  subst hv1
  have hf := l.wf.serviceFee_norm
  exact ⟨operator_add_isNormalized_to_nearest_sz _ _ _ htvN hf hdue,
    Number.RoundsToRepresentable.ge_of_ge_normalized _ _ (operator_add_rounded_to_nearest _ _ _ htvN hf hdue) _ hf
      (by linarith)⟩

/-- A loan in the schedule keeps the loan's fees. -/
lemma Loan.ScheduledBefore.fees {loan : Loan} {now : UInt32} {k : Nat} {l : Loan} (h : loan.ScheduledBefore now k l) :
    l.fees = loan.fees := by
  induction h with
  | first => rfl
  | next v pc due q h hpc hdue hq ih =>
    obtain ⟨-, -, hdo⟩ := Loan.payInstalment_parts _ _ _ _ _ hq
    exact (Loan.doPayment_sameTerms _ _ _ hdo).fees.trans ih

/-- What the instalment loop keeps after `q.count` scheduled payments: the loan is the next one in the schedule, the
amount paid is at least LoanServiceFee once one is paid, and each earlier payment is due at most that amount. -/
private def UnsettledPayment.PaidDues (loan : Loan) (now : UInt32) (q : UnsettledPayment Vault) : Prop :=
  q.totalPaid.isNormalized ∧ 0 ≤ q.totalPaid.toRat ∧ loan.ScheduledBefore now q.count q.loan ∧
    (1 ≤ q.count → loan.fees.serviceFee.toRat ≤ q.totalPaid.toRat) ∧
    ∀ j < q.count, ∀ l pc due, loan.ScheduledBefore now j l → l.paymentComponents .regular now = .ok pc →
      pc.totalDue = .ok due → due.toRat ≤ q.totalPaid.toRat

/-- One more scheduled payment keeps the loop's schedule facts. -/
private lemma UnsettledPayment.PaidDues.step {loan : Loan} {now : UInt32} {q : UnsettledPayment Vault}
    {pc0 : PaymentComponents} {due tp' : Number} {inst amounts' : PaymentAmounts} {loan' : Loan}
    (hq : q.PaidDues loan now) (hpc0 : Loan.scheduledComponents q.loan = .ok pc0)
    (hdue : ({ pc0 with untrackedManagementFee := q.loan.fees.serviceFee } : PaymentComponents).totalDue = .ok due)
    (htp' : q.totalPaid.operator_add due .to_nearest = .ok tp')
    (hpa : ({ pc0 with untrackedManagementFee := q.loan.fees.serviceFee } : PaymentComponents).paidAmounts = .ok inst)
    (hdo : Loan.doPayment q.loan { pc0 with untrackedManagementFee := q.loan.fees.serviceFee } = .ok loan') :
    ({ q with loan := loan', amounts := amounts', totalPaid := tp', count := q.count + 1 } :
      UnsettledPayment Vault).PaidDues loan now := by
  obtain ⟨htp, htp0, hl, -, hd⟩ := hq
  obtain ⟨hdueN, hfee⟩ := Loan.scheduled_due_ge _ _ _ hpc0 hdue
  have hf0 : 0 ≤ q.loan.fees.serviceFee.toRat := q.loan.exact.serviceFee_nonneg
  have hR := operator_add_rounded_to_nearest _ _ _ htp hdueN htp'
  have htpN := operator_add_isNormalized_to_nearest_sz _ _ _ htp hdueN htp'
  have hge1 := Number.RoundsToRepresentable.ge_of_ge_normalized _ _ hR _ htp (by linarith)
  have hge2 := Number.RoundsToRepresentable.ge_of_ge_normalized _ _ hR _ hdueN (by linarith)
  have hpcl : q.loan.paymentComponents .regular now =
      .ok { pc0 with untrackedManagementFee := q.loan.fees.serviceFee } := by
    simp only [Loan.paymentComponents, hpc0]; rfl
  obtain ⟨si, hsi⟩ := Loan.interestDue_ok q.loan
  have hlt : due.operator_lt due = false := (operator_lt_eq_false_iff _ _ hdueN hdueN).mpr le_rfl
  have hpi : (q.loan.payInstalment q.pool { pc0 with untrackedManagementFee := q.loan.fees.serviceFee } due).run =
      .ok (.ok { loan := loan', pool := q.pool, amounts := inst, totalPaid := due, count := 1,
                 scheduledInterest := si }) := by
    simp only [Loan.payInstalment]
    unfold_ter
    simp [hdue, hlt, hsi, hpa, hdo]
  refine ⟨htpN, by linarith, (Loan.ScheduledBefore.next q.pool _ due _ hl hpcl hdue hpi :), fun _ => ?_, ?_⟩
  · rw [← hl.fees]; linarith
  intro j hj l pc due' hjl hpc hdue'
  rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
  · exact le_trans (hd j hj l pc due' hjl hpc hdue') hge1
  · obtain rfl := hjl.unique hl
    rw [hpcl] at hpc
    obtain rfl := Except.ok.inj hpc
    rw [hdue] at hdue'
    obtain rfl := Except.ok.inj hdue'
    exact hge2

/-- The instalment loop pays every scheduled payment it takes in full. -/
private lemma UnsettledPayment.payInstalments_paidDues (loan : Loan) (now : UInt32) (amount : Number) :
    ∀ (n : Nat) (q p : UnsettledPayment Vault), UnsettledPayment.payInstalments q n amount = .ok p →
      q.PaidDues loan now → p.PaidDues loan now := by
  intro n
  induction n with
  | zero =>
    intro q p h hq
    rw [UnsettledPayment.payInstalments] at h
    obtain rfl := Except.ok.inj h
    exact hq
  | succ n ih =>
    intro q p h hq
    rw [UnsettledPayment.payInstalments] at h
    unfold_ter at h
    walk_ok
    · exact hq
    · exact hq
    · exact hq.step ‹Loan.scheduledComponents q.loan = _› ‹PaymentComponents.totalDue _ = _›
        ‹q.totalPaid.operator_add _ _ = _› ‹PaymentComponents.paidAmounts _ = _› ‹Loan.doPayment _ _ = _›
    · rename_i hrec
      exact ih _ p hrec (hq.step ‹Loan.scheduledComponents q.loan = _› ‹PaymentComponents.totalDue _ = _›
        ‹q.totalPaid.operator_add _ _ = _› ‹PaymentComponents.paidAmounts _ = _› ‹Loan.doPayment _ _ = _›)

/-- Every scheduled payment a regular payment pays is due at most its totalPaid, which is at least
LoanServiceFee. -/
lemma Loan.regularPayment_dues (loan : Loan) (v : Vault) (amount : Number) (now : UInt32) (p : UnsettledPayment Vault)
    (hp : (loan.payInstalments v .regular amount now).run = .ok (.ok p)) :
    loan.fees.serviceFee.toRat ≤ p.totalPaid.toRat ∧
      ∀ j < p.count, ∀ l pc due, loan.ScheduledBefore now j l → l.paymentComponents .regular now = .ok pc →
        pc.totalDue = .ok due → due.toRat ≤ p.totalPaid.toRat := by
  obtain ⟨si, -, hloop, hc⟩ := Loan.payScheduled_loop loan v amount now p hp
  obtain ⟨-, -, -, hfee, hd⟩ := UnsettledPayment.payInstalments_paidDues loan now amount _ _ _ hloop
    ⟨Number.zero_isNormalized, by rw [Number.toRat_zero], .first, fun h => absurd h (Nat.not_succ_le_zero 0),
      fun j hj => absurd hj (Nat.not_lt_zero _)⟩
  exact ⟨hfee (Nat.one_le_iff_ne_zero.mpr hc), hd⟩

/-- A regular payment pays the loan's next scheduled payments in turn: the loan it leaves is next in the schedule,
after `count` of them. -/
lemma Loan.regularPayment_scheduled (loan : Loan) (v : Vault) (amount : Number) (now : UInt32)
    (p : UnsettledPayment Vault) (hp : (loan.payInstalments v .regular amount now).run = .ok (.ok p)) :
    loan.ScheduledBefore now p.count p.loan := by
  obtain ⟨si, -, hloop, -⟩ := Loan.payScheduled_loop loan v amount now p hp
  exact (UnsettledPayment.payInstalments_paidDues loan now amount _ _ _ hloop
    ⟨Number.zero_isNormalized, by rw [Number.toRat_zero], .first, fun h => absurd h (Nat.not_succ_le_zero 0),
      fun j hj => absurd hj (Nat.not_lt_zero _)⟩).2.2.1

/-- A scheduled instalment is the last one only when one payment is left or TotalValueOutstanding is at most
⌈PeriodicPayment⌉. -/
private lemma Loan.scheduledComponents_final_cond (l : Loan) (pc : PaymentComponents) (pp' : Number)
    (hpp : STAmount.roundToNumericType l.broker.numericType l.periodicPayment .upward (some l.loanScale) = .ok pp')
    (h : Loan.scheduledComponents l = .ok pc) (hf : pc.isFinal = true) :
    l.paymentRemaining = 1 ∨ l.totalValueOutstanding.operator_le pp' = true := by
  unfold Loan.scheduledComponents at h
  obtain ⟨_, -, h⟩ := bind_ok_peel _ _ _ h
  obtain ⟨pp'', hpp'', h⟩ := bind_ok_peel _ _ _ h
  rw [hpp] at hpp''
  obtain rfl := Except.ok.inj hpp''
  dsimp only at h
  split at h
  · rename_i hc
    simpa using hc
  repeat (obtain ⟨_, -, h⟩ := bind_ok_peel _ _ _ h)
  obtain ⟨_, -, h⟩ := ite_bind_ok_cond _ _ _ _ _ h
  repeat (obtain ⟨_, -, h⟩ := bind_ok_peel _ _ _ h)
  obtain ⟨_, -, h⟩ := ite_bind_ok_cond _ _ _ _ _ h
  obtain ⟨_, -, h⟩ := bind_ok_peel _ _ _ h
  obtain rfl := (Except.ok.inj h).symm
  simp at hf

/-- A scheduled payment that is not the loan's last is due at most ⌈PeriodicPayment⌉ + LoanServiceFee, while it
is due less than `10^16` LoanScale units. -/
private lemma Loan.scheduled_due_le (l : Loan) (now : UInt32) (pc : PaymentComponents) (due pp' : Number)
    (hlo : -81 ≤ l.loanScale) (hint : l.broker.numericType.isIntegral = true → l.loanScale ≤ 0)
    (hi : 0 ≤ l.toExact.interestDue) (gfee : Number.OnGrid l.loanScale l.fees.serviceFee)
    (hpp : STAmount.roundToNumericType l.broker.numericType l.periodicPayment .upward (some l.loanScale) = .ok pp')
    (hpc : l.paymentComponents .regular now = .ok pc) (hdue : pc.totalDue = .ok due)
    (hlast : l.paymentRemaining ≠ 1) (hfit : due.toRat < 10 ^ 16 * 10 ^ l.loanScale) :
    due.toRat ≤ pp'.toRat + l.fees.serviceFee.toRat := by
  have hs := Loan.loanScale_bounds l
  have hu : (0 : ℚ) < 10 ^ l.loanScale := zpow_pos (by norm_num) _
  obtain ⟨gT, -, -, -, -, -, hT0⟩ := Loan.outstanding_grid l
  obtain ⟨pc0, hpc0, rfl⟩ := Loan.paymentComponents_regular _ _ _ hpc
  obtain ⟨hui, hfin⟩ := Loan.scheduledComponents_shape _ _ hpc0
  have hr : -81 ≤ l.loanScale ∧ l.loanScale ≤ 80 := ⟨hlo, l.wf.loanScale_range.2⟩
  have gpp := STAmount.roundToNumericType_onGrid _ _ _ _ _ hr hint hpp
  obtain ⟨gtv, htv0, htvle⟩ : Number.OnGrid l.loanScale pc0.totalValueDelta ∧ 0 ≤ pc0.totalValueDelta.toRat ∧
      pc0.totalValueDelta.toRat ≤ pp'.toRat := by
    rcases Loan.scheduledComponents_tracked l pc0 hlo hint hi hpc0 with hf | ⟨hf, ht⟩
    · have hle : l.totalValueOutstanding.operator_le pp' = true :=
        (Loan.scheduledComponents_final_cond l pc0 pp' hpp hpc0 hf).resolve_left hlast
      rw [(hfin hf).1]
      exact ⟨gT, hT0, (operator_le_iff _ _ gT.1 gpp.1).mp hle⟩
    · exact ⟨ht.totalValue_grid, ht.totalValue_range.1,
        Loan.scheduledComponents_value_le l pc0 pp' hlo hint hi hpp hpc0 hf⟩
  -- the amount due adds LoanServiceFee to it, exactly while it stays below `10^16` units
  have hf0 : 0 ≤ l.fees.serviceFee.toRat := l.exact.serviceFee_nonneg
  unfold PaymentComponents.totalDue at hdue
  obtain ⟨v1, hv1, hdue⟩ := bind_ok_peel _ _ _ hdue
  simp only at hv1 hdue
  rw [hui, Number.operator_add_zero_right, Except.ok.injEq] at hv1
  subst hv1
  obtain ⟨m, hm, hmv⟩ := Number.exists_normalized_int_mul_pow (10 ^ 16) l.loanScale (by norm_num) hs
  have hlt : pc0.totalValueDelta.toRat + l.fees.serviceFee.toRat < 10 ^ 16 * 10 ^ l.loanScale := by
    by_contra hge
    push Not at hge
    have := Number.RoundsToRepresentable.ge_of_ge_normalized _ _
      (operator_add_rounded_to_nearest _ _ _ gtv.1 gfee.1 hdue) m hm (by rw [hmv]; push_cast; linarith)
    rw [hmv] at this
    push_cast at this
    linarith
  have hv := Number.OnGrid.add_exact gtv gfee htv0 hf0 (by nlinarith) hs hdue
  linarith

/-- Proof body of `regularPayment_amount`. -/
lemma Loan.regularPayment_amount_proof (loan : Loan) (v : Vault) (amount : Number) (now t : UInt32)
    (p : UnsettledPayment Vault) (k : Nat) (l : Loan) (pc : PaymentComponents) (due pp' : Number)
    (hreach : loan.Reachable t) (hp : (loan.payInstalments v .regular amount now).run = .ok (.ok p))
    (hk : k < p.count) (hl : loan.ScheduledBefore now k l) (hpc : l.paymentComponents .regular now = .ok pc)
    (hdue : pc.totalDue = .ok due)
    (hpp : STAmount.roundToNumericType loan.broker.numericType loan.periodicPayment .upward (some loan.loanScale) =
      .ok pp')
    (hlast : l.paymentRemaining ≠ 1) (hfit : p.totalPaid.toRat < 10 ^ 16 * 10 ^ loan.loanScale) :
    due.toRat ≤ pp'.toRat + loan.fees.serviceFee.toRat := by
  obtain ⟨hlo, hint, hi, gs, -⟩ := Loan.Reachable.pay_facts hreach
  obtain ⟨e1, e2, e3, e4, hi'⟩ := hl.facts hlo hint hi
  have hle := (Loan.regularPayment_dues loan v amount now p hp).2 k hk l pc due hl hpc hdue
  have h := Loan.scheduled_due_le l now pc due pp' (by rw [e1]; exact hlo) (by rw [e1, e2]; exact hint) hi'
    (by rw [e1, e3]; exact gs) (by rw [e1, e2, e4]; exact hpp) hpc hdue hlast (by rw [e1]; linarith)
  rw [e3] at h
  exact h

/-- A scheduled instalment that isn't the last finds ⌈PeriodicPayment⌉ below TotalValueOutstanding. -/
private lemma Loan.scheduledComponents_rounded_lt (l : Loan) (pc : PaymentComponents) (hlo : -81 ≤ l.loanScale)
    (hint : l.broker.numericType.isIntegral = true → l.loanScale ≤ 0) (h : Loan.scheduledComponents l = .ok pc)
    (hf : pc.isFinal = false) :
    ∃ pp', STAmount.roundToNumericType l.broker.numericType l.periodicPayment .upward (some l.loanScale) = .ok pp' ∧
      pp'.toRat < l.totalValueOutstanding.toRat := by
  unfold Loan.scheduledComponents at h
  obtain ⟨rate, -, h⟩ := bind_ok_peel _ _ _ h
  obtain ⟨pp', hpp, h⟩ := bind_ok_peel _ _ _ h
  dsimp only at h
  split at h
  · obtain rfl := (Except.ok.inj h).symm
    simp at hf
  · rename_i hnf
    have hr : -81 ≤ l.loanScale ∧ l.loanScale ≤ 80 := ⟨hlo, l.wf.loanScale_range.2⟩
    have gpp := STAmount.roundToNumericType_onGrid _ _ _ _ _ hr hint hpp
    obtain ⟨gT, -⟩ := Loan.outstanding_grid l
    have hle : l.totalValueOutstanding.operator_le pp' = false := by
      simp only [Bool.or_eq_true, beq_iff_eq, not_or] at hnf
      simpa using hnf.2
    refine ⟨pp', hpp, ?_⟩
    rw [← not_le, ← operator_le_iff _ _ gT.1 gpp.1, hle]
    simp

/-- ⌈PeriodicPayment⌉ below TotalValueOutstanding is less than 1 ULP at LoanScale above PeriodicPayment. An integral
loan has LoanScale `0`. -/
private lemma Loan.rounded_periodicPayment_lt (l : Loan) (pp' : Number) (hlo : -81 ≤ l.loanScale)
    (hint : l.broker.numericType.isIntegral = true → l.loanScale = 0)
    (hpp : STAmount.roundToNumericType l.broker.numericType l.periodicPayment .upward (some l.loanScale) = .ok pp')
    (hlt : pp'.toRat < l.totalValueOutstanding.toRat) :
    pp'.toRat < l.periodicPayment.toRat + 10 ^ l.loanScale := by
  have hr : -81 ≤ l.loanScale ∧ l.loanScale ≤ 80 := ⟨hlo, l.wf.loanScale_range.2⟩
  have hu : (0 : ℚ) < 10 ^ l.loanScale := zpow_pos (by norm_num) _
  have hx := l.wf.periodicPayment_norm
  have h0 : 0 < l.periodicPayment.toRat := l.exact.periodicPayment_pos
  obtain ⟨m, hm, hmv⟩ := (Loan.grid l).totalValueOutstanding_atExponent
  cases hnt : l.broker.numericType with
  | integral mv mo ms msh =>
    rw [hnt] at hpp
    obtain ⟨hgf, -⟩ := STAmount.roundToNumericType_int_grid _ rfl _ _ _ _ hx h0.le (Or.inr (Or.inl rfl)) hpp
    have h1 := hgf.le_ceil h0.le
    simp only [zpow_zero, div_one, mul_one] at h1
    have h2 : (⌈l.periodicPayment.toRat⌉ : ℚ) < l.periodicPayment.toRat + 1 := Int.ceil_lt_add_one _
    rw [hint (by rw [hnt]; rfl), zpow_zero]
    linarith
  | fractional =>
    rw [hnt] at hpp
    by_cases hz : pp'.toRat = 0
    · rw [hz]
      linarith
    have hge := STAmount.roundToNumericType_frac_upward_ge _ _ _ hx h0.le hr hz hpp
    -- TotalValueOutstanding is under `10^16` units, so PeriodicPayment is under `10^16 − 1`
    have hm16 : m ≤ 10 ^ 16 - 1 := by
      have : m < 10 ^ 16 := by simpa [RawLoan.toExact, hnt, NumericType.mantissaBound] using hm
      omega
    have hT : l.totalValueOutstanding.toRat ≤ ((10 ^ 16 - 1 : ℕ) : ℚ) * 10 ^ l.loanScale := by
      have hv : l.totalValueOutstanding.toRat = (m : ℚ) * 10 ^ l.loanScale := hmv
      rw [hv]
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hm16) hu.le
    have h1 := STAmount.roundToNumericType_frac_le_ceil _ _ _ _ hx h0.le (Or.inr (Or.inl rfl)) hr
      (by linarith) hpp
    have h2 : (⌈l.periodicPayment.toRat / 10 ^ l.loanScale⌉ : ℚ) <
        l.periodicPayment.toRat / 10 ^ l.loanScale + 1 := Int.ceil_lt_add_one _
    have h3 := mul_lt_mul_of_pos_right h2 hu
    rw [add_mul, div_mul_cancel₀ _ hu.ne', one_mul] at h3
    linarith

/-- A scheduled instalment that isn't the last takes less than PeriodicPayment + 1 ULP at LoanScale off
TotalValueOutstanding. An integral loan has LoanScale `0`. -/
lemma Loan.scheduled_value_lt (l : Loan) (v : Vault) (now : UInt32) (pc : PaymentComponents) (due : Number)
    (q : UnsettledPayment Vault) (hlo : -81 ≤ l.loanScale)
    (hint : l.broker.numericType.isIntegral = true → l.loanScale = 0) (hi : 0 ≤ l.toExact.interestDue)
    (hpc : l.paymentComponents .regular now = .ok pc) (hq : (l.payInstalment v pc due).run = .ok (.ok q))
    (hleft : q.loan.paymentRemaining ≠ 0) :
    l.totalValueOutstanding.toRat - q.loan.totalValueOutstanding.toRat - l.periodicPayment.toRat <
      10 ^ l.loanScale := by
  have hint' : l.broker.numericType.isIntegral = true → l.loanScale ≤ 0 := fun h => (hint h).le
  obtain ⟨pc0, hpc0, rfl⟩ := Loan.paymentComponents_regular _ _ _ hpc
  obtain ⟨-, -, hdo⟩ := Loan.payInstalment_parts _ _ _ _ _ hq
  rcases Loan.scheduledComponents_tracked l pc0 hlo hint' hi hpc0 with hf | ⟨hf, ht⟩
  · exact absurd (Loan.doPayment_final _ _ _ hf hdo) hleft
  obtain ⟨pp', hpp, hlt⟩ := Loan.scheduledComponents_rounded_lt l pc0 hlo hint' hpc0 hf
  have hle := Loan.scheduledComponents_value_le l pc0 pp' hlo hint' hi hpp hpc0 hf
  have hval := Loan.doPayment_value l q.loan _ hf ht.totalValue_grid ht.totalValue_range.1 ht.totalValue_range.2 hdo
  have hpl := Loan.rounded_periodicPayment_lt l pp' hlo hint hpp hlt
  simp only at hval
  linarith

end XRPL.Model.Lending
