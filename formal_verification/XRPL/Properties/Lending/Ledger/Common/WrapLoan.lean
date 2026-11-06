import XRPL.Properties.Lending.Ledger.Common.WrapBroker
import XRPL.Properties.Lending.Loan.Common.PayMonotone
import XRPL.Properties.Lending.Loan.Common.PaySteps

/-! # The loan transactions never wrap around

A loan transaction runs the lending helpers, the vault and broker updates, and a few checked fixed-width
operations of its own: LoanCount and the first due date at LoanSet, LoanCount at LoanDelete, the end of the grace
period at a default, and PaymentRemaining and the next due date at each instalment. A lawful loan keeps its due date
on its schedule, and the schedule with its grace period fits the ledger clock, so the instalment and default
operations never wrap. LoanSet needs a broker below `2^32 − 1` loans, and LoanDelete a broker that counts the
loan. The amounts a payment passes from step to step are normalized, so its Number operations never wrap. -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault (Vault RawVault)

open private checkPrecisionFields from XRPL.Model.Lending.Loan.LoanSet
open private Loan.scheduledComponents Loan.lateComponents Loan.fullComponents Loan.overpaymentComponents
  Loan.tryOverpayment Loan.doPayment Loan.settlePayment Loan.paySingleInstalment UnsettledPayment.payInstalments
  Loan.unimpairIfImpaired Loan.payScheduledInstalments UnsettledPayment.applyOverpayment
  from XRPL.Model.Lending.Loan.LoanPay
open private Loan.unimpairIfImpaired_loan from XRPL.Properties.Lending.Loan.Common.PaySteps

/-- A count other than `0` is not `0`, from a `==` check that failed. -/
lemma ne_of_not_beq {α : Type} [BEq α] [LawfulBEq α] {a b : α} (h : ¬(a == b) = true) : a ≠ b := by
  rintro rfl
  exact h (beq_self_eq_true a)

macro_rules
  | `(tactic| wrap_rule) => `(tactic| exact XRPL.Model.Lending.ne_of_not_beq ‹_›)

/-- Every amount of a payment's components is normalized. -/
structure PaymentComponents.Normalized (c : PaymentComponents) : Prop where
  totalValueDelta : c.totalValueDelta.isNormalized
  principalDelta : c.principalDelta.isNormalized
  managementFeeDelta : c.managementFeeDelta.isNormalized
  untrackedInterest : c.untrackedInterest.isNormalized
  untrackedManagementFee : c.untrackedManagementFee.isNormalized

/-- Every amount a payment moves is normalized. -/
structure PaymentAmounts.Normalized (a : PaymentAmounts) : Prop where
  principalPaid : a.principalPaid.isNormalized
  interestPaid : a.interestPaid.isNormalized
  feePaid : a.feePaid.isNormalized

/-- The amounts, the total paid and the scheduled interest of an unsettled payment are normalized. -/
structure UnsettledPayment.Normalized {α : Type} (p : UnsettledPayment α) : Prop where
  amounts : p.amounts.Normalized
  totalPaid : p.totalPaid.isNormalized
  scheduledInterest : p.scheduledInterest.isNormalized

lemma PaymentAmounts.zero_normalized : PaymentAmounts.zero.Normalized :=
  ⟨Number.zero_isNormalized, Number.zero_isNormalized, Number.zero_isNormalized⟩

macro_rules
  | `(tactic| wrap_rule) => `(tactic| exact XRPL.Model.Lending.PaymentAmounts.zero_normalized)

lemma PaymentAmounts.add_ne_wrap (a b : PaymentAmounts) (ha : a.Normalized) (hb : b.Normalized) :
    a.add b ≠ .error .wrap := by
  intro h; wrap_leaf

lemma PaymentAmounts.add_normalized {a b r : PaymentAmounts} (ha : a.Normalized) (hb : b.Normalized)
    (h : a.add b = .ok r) : r.Normalized := by
  wrap_side

lemma PaymentComponents.interestDelta_ne_wrap (c : PaymentComponents) (hc : c.Normalized) :
    c.interestDelta ≠ .error .wrap := by
  intro h; wrap_leaf

lemma PaymentComponents.interestDelta_isNormalized {c : PaymentComponents} {n : Number} (hc : c.Normalized)
    (h : c.interestDelta = .ok n) : n.isNormalized := by
  wrap_side

lemma PaymentComponents.totalDue_ne_wrap (c : PaymentComponents) (hc : c.Normalized) : c.totalDue ≠ .error .wrap := by
  intro h; wrap_leaf

lemma PaymentComponents.totalDue_isNormalized {c : PaymentComponents} {n : Number} (hc : c.Normalized)
    (h : c.totalDue = .ok n) : n.isNormalized := by
  wrap_side

lemma PaymentComponents.paidAmounts_ne_wrap (c : PaymentComponents) (hc : c.Normalized) :
    c.paidAmounts ≠ .error .wrap := by
  intro h; wrap_leaf

lemma PaymentComponents.paidAmounts_normalized {c : PaymentComponents} {a : PaymentAmounts} (hc : c.Normalized)
    (h : c.paidAmounts = .ok a) : a.Normalized := by
  wrap_side

private lemma checkPrecisionFields_ne_wrap (principal : Number) (fees : LoanFees) (f : Number → Except Error Bool)
    (hf : ∀ x, f x ≠ .error .wrap) : checkPrecisionFields principal fees f ≠ .error .wrap := by
  intro h
  unfold checkPrecisionFields LoanFees.amountFields at h
  simp only [List.forIn_cons, List.forIn_nil, bind, Except.bind, pure, Except.pure] at h
  walk_ok
  all_goals exact hf _ ‹_›

lemma isRounded_ne_wrap (value : Number) (scale : Int) (nt : NumericType) :
    isRounded value scale nt ≠ .error .wrap := by
  intro h; wrap_leaf

/-- The LoanSet checks never wrap. -/
lemma Loan.canCreate_ne_wrap (broker : LoanBroker) (v : Vault) (principal : Number) (fees : LoanFees)
    (schedule : LoanSchedule) (now : UInt32) (twoStep : Bool) :
    Loan.canCreate broker v principal fees schedule now twoStep ≠ .error .wrap := by
  intro h
  unfold Loan.canCreate at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  walk_ok
  all_goals first
    | wrap_leaf
    | (refine checkPrecisionFields_ne_wrap _ _ _ ?_ ‹_›; exact fun _ => nofun)

/-- A create never wraps when the schedule has a payment, LoanCount has a successor and the first due date fits. -/
lemma Loan.create_ne_wrap (broker : LoanBroker) (v : Vault) (principal : Number) (rates : LoanRates)
    (fees : LoanFees) (schedule : LoanSchedule) (allowsOverpayment pending : Bool)
    (hpr : schedule.paymentTotal ≠ 0) (hcount : broker.loanCount.toNat + 1 < 2 ^ 32)
    (hdue : schedule.startDate.toNat + schedule.paymentInterval.toNat < 2 ^ 32) (hp : principal.isNormalized) :
    (Loan.create broker v principal rates fees schedule allowsOverpayment pending).run ≠ .error .wrap := by
  intro h
  simp only [Loan.create] at h
  unfold_ter at h
  walk_facts
  all_goals first
    | wrap_leaf
    | (refine checkPrecisionFields_ne_wrap _ _ _ ?_ ‹_›; exact fun _ => isRounded_ne_wrap _ _ _)

lemma LoanBroker.releaseLoan_ne_wrap (lb : LoanBroker) (d : Number) (hc0 : lb.loanCount ≠ 0) :
    lb.releaseLoan d ≠ .error .wrap := by
  unfold LoanBroker.releaseLoan
  rw [UInt32.subChecked_of_le (UInt32.one_le_of_ne_zero hc0)]
  exact RawLoanBroker.to_lawful_ne_wrap _

/-- A delete never wraps when the broker counts the loan. -/
lemma Loan.delete_ne_wrap (loan : Loan) (v : Vault) (hc0 : loan.broker.loanCount ≠ 0) :
    (loan.delete v).run ≠ .error .wrap := by
  intro h; wrap_leaf

/-- The default check adds the grace period to the due date, which a lawful loan keeps within the ledger clock. -/
lemma Loan.canManage_ne_wrap (loan : Loan) (action : LoanManageAction) (now : UInt32) :
    loan.canManage action now ≠ .error .wrap := by
  unfold Loan.canManage
  simp only [bind, Except.bind, pure, Except.pure, UInt32.addChecked_of_lt loan.gracePeriodEnd_lt]
  split_ifs <;> exact nofun

lemma Loan.manageUnimpair_ne_wrap (loan : Loan) (v : Vault) : (loan.manageUnimpair v).run ≠ .error .wrap := by
  intro h; wrap_leaf

lemma Loan.manage_ne_wrap (loan : Loan) (action : LoanManageAction) (v : Vault) (now : UInt32) :
    (loan.manage action v now).run ≠ .error .wrap := by
  intro h; wrap_leaf

lemma Loan.canAccept_ne_wrap (loan : Loan) (v : Vault) (now : UInt32) : loan.canAccept v now ≠ .error .wrap := by
  intro h; wrap_leaf

lemma Loan.accept_ne_wrap (loan : Loan) (v : Vault) : (loan.accept v).run ≠ .error .wrap := by
  intro h; wrap_leaf

/-- The next scheduled instalment counts the instalments left after it only when one is left. -/
private lemma Loan.scheduledComponents_ne_wrap (loan : Loan) (hr : loan.paymentRemaining ≠ 0) :
    Loan.scheduledComponents loan ≠ .error .wrap := by
  intro h
  unfold Loan.scheduledComponents at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  rw [UInt32.subChecked_of_le (UInt32.one_le_of_ne_zero hr)] at h
  walk_facts
  all_goals wrap_leaf

private lemma Loan.scheduledComponents_normalized {loan : Loan} {pc : PaymentComponents}
    (h : Loan.scheduledComponents loan = .ok pc) : pc.Normalized := by
  unfold Loan.scheduledComponents at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  walk_facts
  all_goals wrap_side

private lemma Loan.lateComponents_ne_wrap (loan : Loan) (now : UInt32) (hr : loan.paymentRemaining ≠ 0) :
    Loan.lateComponents loan now ≠ .error .wrap := by
  intro h
  unfold Loan.lateComponents at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  walk_facts
  all_goals wrap_leaf

private lemma Loan.lateComponents_normalized {loan : Loan} {now : UInt32} {pc : PaymentComponents}
    (h : Loan.lateComponents loan now = .ok pc) : pc.Normalized := by
  unfold Loan.lateComponents at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  walk_facts
  all_goals wrap_side

private lemma Loan.fullComponents_ne_wrap (loan : Loan) (now : UInt32) :
    Loan.fullComponents loan now ≠ .error .wrap := by
  intro h
  unfold Loan.fullComponents at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  walk_facts
  all_goals wrap_leaf

private lemma Loan.fullComponents_normalized {loan : Loan} {now : UInt32} {pc : PaymentComponents}
    (h : Loan.fullComponents loan now = .ok pc) : pc.Normalized := by
  unfold Loan.fullComponents at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  walk_facts
  all_goals wrap_side

private lemma Loan.overpaymentComponents_ne_wrap (loan : Loan) (x : Number) (hx : x.isNormalized) :
    Loan.overpaymentComponents loan x ≠ .error .wrap := by
  intro h
  unfold Loan.overpaymentComponents at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  walk_facts
  all_goals wrap_leaf

private lemma Loan.overpaymentComponents_normalized {loan : Loan} {x : Number} {pc : PaymentComponents}
    (hx : x.isNormalized) (h : Loan.overpaymentComponents loan x = .ok pc) : pc.Normalized := by
  unfold Loan.overpaymentComponents at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  walk_facts
  all_goals wrap_side

/-- An instalment other than the last takes one off PaymentRemaining and moves the due date one interval on. -/
private lemma Loan.doPayment_ne_wrap (loan : Loan) (pc : PaymentComponents)
    (h2 : pc.isFinal = false → 2 ≤ loan.paymentRemaining.toNat) (hpc : pc.Normalized) :
    Loan.doPayment loan pc ≠ .error .wrap := by
  intro h
  unfold Loan.doPayment at h
  cases hf : pc.isFinal
  · have h2 := h2 hf
    have hpr : (1 : UInt32) ≤ loan.paymentRemaining := by
      rw [UInt32.le_iff_toNat_le, UInt32.toNat_one]; omega
    simp only [hf, Bool.false_eq_true, ↓reduceIte, bind, Except.bind, pure, Except.pure,
      UInt32.subChecked_of_le hpr, UInt32.addChecked_of_lt (loan.nextDue_lt h2)] at h
    walk_ok
    all_goals wrap_leaf
  · simp only [hf, ↓reduceIte, bind, Except.bind, pure, Except.pure] at h
    walk_ok
    all_goals wrap_leaf

private lemma Loan.settlePayment_ne_wrap (loan : Loan) (v : Vault) (amounts : PaymentAmounts) (si : Number)
    (ha : amounts.Normalized) (hsi : si.isNormalized) :
    (Loan.settlePayment loan v amounts si).run ≠ .error .wrap := by
  intro h
  simp only [Loan.settlePayment] at h
  unfold_ter at h
  walk_facts
  all_goals wrap_leaf

private lemma Loan.paySingleInstalment_ne_wrap (loan : Loan) (v : Vault) (pc : PaymentComponents) (amount : Number)
    (h2 : pc.isFinal = false → 2 ≤ loan.paymentRemaining.toNat) (hpc : pc.Normalized) :
    (Loan.paySingleInstalment loan v pc amount).run ≠ .error .wrap := by
  intro h; wrap_leaf

/-- The instalment loop pays one instalment at a time while one is left. -/
private lemma UnsettledPayment.payInstalments_ne_wrap (amount : Number) :
    ∀ (n : Nat) (p : UnsettledPayment Vault), p.Normalized →
      UnsettledPayment.payInstalments p n amount ≠ .error .wrap := by
  intro n
  induction n with
  | zero =>
    intro p _ h
    rw [UnsettledPayment.payInstalments] at h
    cases h
  | succ n ih =>
    intro p hp h
    rw [UnsettledPayment.payInstalments] at h
    unfold_ter at h
    walk_facts
    all_goals first
      | wrap_leaf
      | (refine ih _ ?_ ‹_›; wrap_side)
      | (have hr := ne_of_not_beq ‹¬ (p.loan.paymentRemaining == 0) = true›
         have hpc := ‹Loan.scheduledComponents p.loan = Except.ok _›
         refine Loan.doPayment_ne_wrap _ _ ?_ ?_ ‹_›
         · exact fun hf => Loan.scheduledComponents_two_le _ _ hpc hr hf
         · wrap_side)

/-- The instalment loop keeps the amounts of the payment normalized. -/
private lemma UnsettledPayment.payInstalments_normalized (amount : Number) :
    ∀ (n : Nat) (p r : UnsettledPayment Vault), p.Normalized →
      UnsettledPayment.payInstalments p n amount = .ok r → r.Normalized := by
  intro n
  induction n with
  | zero =>
    intro p r hp h
    rw [UnsettledPayment.payInstalments] at h
    cases h
    exact hp
  | succ n ih =>
    intro p r hp h
    rw [UnsettledPayment.payInstalments] at h
    unfold_ter at h
    walk_facts
    all_goals first
      | wrap_side
      | (refine ih _ _ ?_ ‹_›; wrap_side)

private lemma Loan.unimpairIfImpaired_ne_wrap (loan : Loan) (v : Vault) :
    (Loan.unimpairIfImpaired loan v).run ≠ .error .wrap := by
  intro h; wrap_leaf

private lemma Loan.payScheduledInstalments_ne_wrap (loan : Loan) (v : Vault) (amount : Number) (now : UInt32) :
    (Loan.payScheduledInstalments loan v amount now).run ≠ .error .wrap := by
  intro h
  simp only [Loan.payScheduledInstalments] at h
  unfold_ter at h
  walk_ok
  all_goals wrap_leaf

private lemma Loan.payScheduledInstalments_normalized {loan : Loan} {v : Vault} {amount : Number} {now : UInt32}
    {r : UnsettledPayment Vault} (h : (Loan.payScheduledInstalments loan v amount now).run = .ok (.ok r)) :
    r.Normalized := by
  simp only [Loan.payScheduledInstalments] at h
  unfold_ter at h
  walk_ok
  all_goals wrap_side

/-- The re-amortization after an overpayment counts the instalments left after the next one, so it needs one. -/
private lemma Loan.tryOverpayment_ne_wrap (loan : Loan) (opc : PaymentComponents) (hr : loan.paymentRemaining ≠ 0)
    (hopc : opc.Normalized) : Loan.tryOverpayment loan opc ≠ .error .wrap := by
  intro h
  unfold Loan.tryOverpayment at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  walk_facts
  all_goals wrap_leaf

private lemma Loan.tryOverpayment_normalized {loan : Loan} {opc : PaymentComponents} {r : Reamortization}
    (hopc : opc.Normalized) (h : Loan.tryOverpayment loan opc = .ok (some r)) : r.amounts.Normalized := by
  unfold Loan.tryOverpayment at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  walk_facts
  all_goals wrap_side

private lemma UnsettledPayment.applyOverpayment_ne_wrap (p : UnsettledPayment Vault) (amount : Number)
    (hp : p.Normalized) : UnsettledPayment.applyOverpayment p amount ≠ .error .wrap := by
  intro h
  unfold UnsettledPayment.applyOverpayment at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  walk_facts
  all_goals first
    | wrap_leaf
    | (refine Loan.tryOverpayment_ne_wrap p.loan _ (by
        intro h0
        apply ‹¬(!(p.loan.allowsOverpayment && p.loan.paymentRemaining != 0 && _ && _)) = true›
        simp [h0]) ?_ ‹_›; wrap_side)

private lemma UnsettledPayment.applyOverpayment_normalized {p r : UnsettledPayment Vault} {amount : Number}
    (hp : p.Normalized) (h : UnsettledPayment.applyOverpayment p amount = .ok r) : r.Normalized := by
  unfold UnsettledPayment.applyOverpayment at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  walk_facts
  all_goals wrap_side

/-- A payment on a lawful loan never wraps. -/
lemma Loan.pay_ne_wrap (loan : Loan) (v : Vault) (pt : LoanPaymentType) (amount : Number) (now : UInt32) :
    (loan.pay v pt amount now).run ≠ .error .wrap := by
  intro h
  cases pt with
  | regular =>
    simp only [Loan.pay, Loan.regularPayment] at h
    unfold_ter at h
    walk_ok
    all_goals wrap_leaf
  | overpayment =>
    simp only [Loan.pay, Loan.overpayment] at h
    unfold_ter at h
    walk_ok
    all_goals wrap_leaf
  | late =>
    simp only [Loan.pay, Loan.latePayment] at h
    unfold_ter at h
    walk_ok
    all_goals first
      | exact Loan.unimpairIfImpaired_ne_wrap _ _ ‹_›
      | skip
    all_goals
      have hu := Loan.unimpairIfImpaired_loan _ _ _ ‹_›
      have hr : loan.unimpaired.paymentRemaining ≠ 0 := by
        have := ‹¬ (loan.paymentRemaining == 0 || _) = true›
        intro h0; apply this; simp [show loan.paymentRemaining = 0 from h0]
    · have h' := ‹Loan.lateComponents _ now = Except.error Error.wrap›
      rw [hu] at h'
      exact Loan.lateComponents_ne_wrap loan.unimpaired now hr h'
    · have hpc := ‹Loan.lateComponents _ now = Except.ok _›
      have h' := ‹Loan.paySingleInstalment _ _ _ _ = Except.error Error.wrap›
      have hn := Loan.lateComponents_normalized hpc
      rw [hu] at hpc h'
      obtain ⟨pc0, hpc0, hfin⟩ := Loan.lateComponents_final _ _ _ hpc
      exact Loan.paySingleInstalment_ne_wrap loan.unimpaired _ _ _
        (fun hf => Loan.scheduledComponents_two_le _ _ hpc0 hr (hfin ▸ hf)) hn h'
  | full =>
    simp only [Loan.pay, Loan.fullPayment] at h
    unfold_ter at h
    walk_ok
    all_goals first
      | exact Loan.unimpairIfImpaired_ne_wrap _ _ ‹_›
      | exact Loan.fullComponents_ne_wrap _ _ ‹_›
      | skip
    have hu := Loan.unimpairIfImpaired_loan _ _ _ ‹_›
    have h2 : 2 ≤ loan.paymentRemaining.toNat := by
      have := ‹¬ loan.paymentRemaining ≤ 1›
      rw [UInt32.le_iff_toNat_le, UInt32.toNat_one] at this
      omega
    have hn := Loan.fullComponents_normalized ‹Loan.fullComponents _ now = Except.ok _›
    have h' := ‹Loan.paySingleInstalment _ _ _ _ = Except.error Error.wrap›
    rw [hu] at h'
    exact Loan.paySingleInstalment_ne_wrap loan.unimpaired _ _ _ (fun _ => h2) hn h'

end XRPL.Model.Lending
