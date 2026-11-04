import XRPL.Properties.Lending.Loan.Common.PayPrincipal
import XRPL.Properties.Lending.Loan.Common.YieldGrid

/-! # The principal and interest a payment pays, on the LoanScale grid

Every instalment's principal and interest are whole numbers of LoanScale units, so the sums a payment
settles with the vault are whole units too, for every payment type. -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault (Vault RawVault)

open private Loan.scheduledComponents Loan.lateComponents Loan.fullComponents Loan.doPayment
  UnsettledPayment.payInstalments UnsettledPayment.applyOverpayment Loan.tryOverpayment Loan.overpaymentComponents
  roundAndSplitInterest from XRPL.Model.Lending.Loan.LoanPay
open private Loan.tryOverpayment_principal from XRPL.Properties.Lending.Loan.Common.PayPrincipal

/-- The principal and interest summed so far are whole numbers of `10^s` units. -/
def PaymentAmounts.OnGrid (s : Int) (a : PaymentAmounts) : Prop :=
  Number.OnGrid s a.principalPaid ∧ Number.OnGrid s a.interestPaid

private lemma PaymentAmounts.zero_onGrid (s : Int) : PaymentAmounts.zero.OnGrid s :=
  ⟨Number.OnGrid.zero s, Number.OnGrid.zero s⟩

private lemma PaymentAmounts.add_onGrid {s : Int} {a b c : PaymentAmounts}
    (hs : minExponent + 18 ≤ s ∧ s ≤ maxExponent - 1) (ha : a.OnGrid s) (hb : b.OnGrid s) (h : a.add b = .ok c) :
    c.OnGrid s := by
  unfold PaymentAmounts.add at h
  simp only [bind, Except.bind] at h
  walk_ok
  obtain rfl := (Except.ok.inj ‹pure _ = Except.ok c›)
  exact ⟨Number.OnGrid.add ha.1 hb.1 hs ‹_›, Number.OnGrid.add ha.2 hb.2 hs ‹_›⟩

/-- An instalment whose deltas and untracked interest are on the grid pays principal and interest on it. -/
private lemma PaymentComponents.paidAmounts_onGrid {s : Int} {pc : PaymentComponents} {a : PaymentAmounts}
    (hp : pc.paidAmounts = .ok a) (hs : minExponent + 18 ≤ s ∧ s ≤ maxExponent - 1)
    (h1 : Number.OnGrid s pc.totalValueDelta) (h2 : Number.OnGrid s pc.principalDelta)
    (h3 : Number.OnGrid s pc.managementFeeDelta) (h4 : Number.OnGrid s pc.untrackedInterest) : a.OnGrid s := by
  obtain ⟨vap, id, e1, e2, e3, -, e5⟩ := PaymentComponents.paidAmounts_ok_inv pc a hp
  refine ⟨by rw [e5]; exact h2, ?_⟩
  exact Number.OnGrid.add (Number.OnGrid.sub (Number.OnGrid.sub h1 h2 hs e1) h3 hs e2) h4 hs e3

/-- The next scheduled instalment takes whole LoanScale units off the loan, and has no untracked interest. -/
private lemma Loan.scheduledComponents_onGrid (l : Loan) (pc : PaymentComponents)
    (hr : -81 ≤ l.loanScale ∧ l.loanScale ≤ 0) (h : Loan.scheduledComponents l = .ok pc) :
    Number.OnGrid l.loanScale pc.totalValueDelta ∧ Number.OnGrid l.loanScale pc.principalDelta ∧
      Number.OnGrid l.loanScale pc.managementFeeDelta ∧ pc.untrackedInterest = Number.zero := by
  have hsb := Loan.loanScale_bounds l
  obtain ⟨gT, gP, gM⟩ := Loan.outstanding_onGrid l
  unfold Loan.scheduledComponents at h
  simp only [bind, Except.bind] at h
  walk_ok
  all_goals
    simp only [pure, Except.pure, Except.ok.injEq] at *
    subst_vars
  all_goals first
    | exact ⟨gT, gP, gM, rfl⟩
    | (obtain ⟨t, p, m, -, -, -, ht, hp, hm, hi, -, -, -, -⟩ := Loan.state_units l _ ‹l.state = _›
       have g1 := ht.onGrid
       have g2 := hp.onGrid
       have g3 := hm.onGrid
       have g4 := hi.onGrid
       grid_forward l.loanScale
       refine ⟨?_, ?_, ?_, rfl⟩ <;> grid_prove)

/-- A management fee is a rounding at the grid's exponent. -/
private lemma computeManagementFee_onGrid (nt : NumericType) (x : Number) (rate : TenthBips16) (s : Int)
    (fee : Number) (hr : -81 ≤ s ∧ s ≤ 0) (h : computeManagementFee nt x rate s = .ok fee) : Number.OnGrid s fee := by
  unfold computeManagementFee at h
  simp only [bind, Except.bind] at h
  split at h
  · cases h
  · exact STAmount.roundToNumericType_onGrid _ _ _ _ _ ⟨hr.1, by omega⟩ (fun _ => hr.2) h

/-- The interest split is on the grid of its exponent. -/
private lemma roundAndSplitInterest_onGrid (interest : Number) (rate : TenthBips16) (mode : rounding_mode)
    (nt : NumericType) (s : Int) (net fee : Number) (hr : -81 ≤ s ∧ s ≤ 0)
    (hs : minExponent + 18 ≤ s ∧ s ≤ maxExponent - 1)
    (h : roundAndSplitInterest interest rate mode nt s = .ok (net, fee)) :
    Number.OnGrid s net ∧ Number.OnGrid s fee := by
  obtain ⟨i', h1, h2, h3⟩ := roundAndSplitInterest_ok_inv _ _ _ _ _ _ _ h
  have g1 := STAmount.roundToNumericType_onGrid _ _ _ _ _ ⟨hr.1, by omega⟩ (fun _ => hr.2) h1
  have g2 := computeManagementFee_onGrid _ _ _ _ _ hr h2
  exact ⟨Number.OnGrid.sub g1 g2 hs h3, g2⟩

/-- The late instalment pays the scheduled deltas and late interest on the grid. -/
private lemma Loan.lateComponents_onGrid (l : Loan) (now : UInt32) (pc : PaymentComponents)
    (hr : -81 ≤ l.loanScale ∧ l.loanScale ≤ 0) (h : Loan.lateComponents l now = .ok pc) :
    Number.OnGrid l.loanScale pc.totalValueDelta ∧ Number.OnGrid l.loanScale pc.principalDelta ∧
      Number.OnGrid l.loanScale pc.managementFeeDelta ∧ Number.OnGrid l.loanScale pc.untrackedInterest := by
  have hsb := Loan.loanScale_bounds l
  unfold Loan.lateComponents at h
  simp only [bind, Except.bind] at h
  walk_ok
  obtain rfl := (Except.ok.inj ‹pure _ = Except.ok pc›)
  obtain ⟨g1, g2, g3, -⟩ := Loan.scheduledComponents_onGrid l _ hr ‹Loan.scheduledComponents l = _›
  obtain ⟨g4, -⟩ := roundAndSplitInterest_onGrid _ _ _ _ _ _ _ hr hsb ‹roundAndSplitInterest _ _ _ _ _ = _›
  exact ⟨g1, g2, g3, g4⟩

/-- The full payoff pays its deltas and its untracked interest on the grid. -/
private lemma Loan.fullComponents_onGrid (l : Loan) (now : UInt32) (pc : PaymentComponents)
    (hr : -81 ≤ l.loanScale ∧ l.loanScale ≤ 0) (h : Loan.fullComponents l now = .ok pc) :
    Number.OnGrid l.loanScale pc.totalValueDelta ∧ Number.OnGrid l.loanScale pc.principalDelta ∧
      Number.OnGrid l.loanScale pc.managementFeeDelta ∧ Number.OnGrid l.loanScale pc.untrackedInterest := by
  have hsb := Loan.loanScale_bounds l
  obtain ⟨_, _, _, net, split, state, cf, ppi, tracked, cfm, uf, ui, -, -, -, hsplit, hstate, -, hppi, htracked,
    -, -, hui, rfl⟩ := Loan.fullComponents_ok_inv l now pc h
  obtain ⟨t, p, m, -, -, -, ht, hp, hm, hi, -, -, -, -⟩ := Loan.state_units l state hstate
  obtain ⟨gn, -⟩ := roundAndSplitInterest_onGrid _ _ _ _ _ _ _ hr hsb hsplit
  have gppi := Number.OnGrid.add hp.onGrid hi.onGrid hsb hppi
  exact ⟨Number.OnGrid.add gppi hm.onGrid hsb htracked, hp.onGrid, hm.onGrid, Number.OnGrid.sub gn hi.onGrid hsb hui⟩

/-- The scheduled instalments sum principal and interest on the grid. -/
private lemma UnsettledPayment.payInstalments_onGrid {α : Type} (amount : Number) (s : Int)
    (hr : -81 ≤ s ∧ s ≤ 0) :
    ∀ (n : Nat) (payment p : UnsettledPayment α), UnsettledPayment.payInstalments payment n amount = .ok p →
      payment.loan.loanScale = s → payment.amounts.OnGrid s → p.amounts.OnGrid s := by
  intro n
  induction n with
  | zero =>
    intro payment p h _ hp
    unfold UnsettledPayment.payInstalments at h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    exact hp
  | succ k ih =>
    intro payment p h hls hp
    unfold UnsettledPayment.payInstalments at h
    unfold_ter at h
    walk_ok'
    all_goals first
      | exact hp
      | (have hsb := Loan.loanScale_bounds payment.loan
         rw [hls] at hsb
         obtain ⟨g1, g2, g3, g4⟩ := Loan.scheduledComponents_onGrid payment.loan _ (hls ▸ hr)
           ‹Loan.scheduledComponents payment.loan = _›
         rw [hls] at g1 g2 g3
         have hpaid := ‹PaymentComponents.paidAmounts _ = _›
         have hinst := PaymentComponents.paidAmounts_onGrid hpaid hsb g1 g2 g3 (by rw [g4]; exact Number.OnGrid.zero s)
         have hsum := PaymentAmounts.add_onGrid hsb hp hinst ‹PaymentAmounts.add _ _ = _›
         first
           | exact hsum
           | (have hls' := (Loan.doPayment_sameTerms _ _ _ ‹Loan.doPayment _ _ = _›).loanScale
              exact ih _ _ ‹UnsettledPayment.payInstalments _ k amount = _› (hls'.trans hls) hsum))

/-- The overpayment split pays its interest on the grid. -/
private lemma Loan.overpaymentComponents_onGrid (l : Loan) (x : Number) (opc : PaymentComponents)
    (hr : -81 ≤ l.loanScale ∧ l.loanScale ≤ 0) (h : Loan.overpaymentComponents l x = .ok opc) :
    Number.OnGrid l.loanScale opc.untrackedInterest := by
  have hsb := Loan.loanScale_bounds l
  unfold Loan.overpaymentComponents at h
  simp only [bind, Except.bind] at h
  walk_ok
  obtain rfl := (Except.ok.inj ‹pure _ = Except.ok opc›)
  exact (roundAndSplitInterest_onGrid _ _ _ _ _ _ _ hr hsb ‹roundAndSplitInterest _ _ _ _ _ = _›).1

/-- A re-amortization pays its principal and its interest on the grid. -/
private lemma Loan.tryOverpayment_onGrid (l : Loan) (opc : PaymentComponents) (re : Reamortization)
    (hr : -81 ≤ l.loanScale ∧ l.loanScale ≤ 0) (hopc : Number.OnGrid l.loanScale opc.untrackedInterest)
    (h : Loan.tryOverpayment l opc = .ok (some re)) : re.amounts.OnGrid l.loanScale := by
  refine ⟨(Loan.tryOverpayment_principal l opc re hr h).1, ?_⟩
  unfold Loan.tryOverpayment at h
  simp only [bind, Except.bind] at h
  walk_ok
  all_goals first
    | (have hn := Except.ok.inj ‹pure none = Except.ok (some re)›; cases hn)
    | skip
  obtain rfl := Option.some.inj (Except.ok.inj ‹pure (some _) = Except.ok (some re)›)
  exact hopc

/-- The overpayment tail keeps the principal and interest sums on the grid. -/
private lemma UnsettledPayment.applyOverpayment_onGrid (payment p' : UnsettledPayment Vault) (amount : Number)
    (s : Int) (hr : -81 ≤ s ∧ s ≤ 0) (hls : payment.loan.loanScale = s) (hp : payment.amounts.OnGrid s)
    (h : UnsettledPayment.applyOverpayment payment amount = .ok p') : p'.amounts.OnGrid s := by
  simp only [UnsettledPayment.applyOverpayment] at h
  unfold_ter at h
  walk_ok
  all_goals first
    | exact hp
    | skip
  subst hls
  have hsb := Loan.loanScale_bounds payment.loan
  have hopc := Loan.overpaymentComponents_onGrid _ _ _ hr ‹Loan.overpaymentComponents _ _ = _›
  have hre := Loan.tryOverpayment_onGrid _ _ _ hr hopc ‹Loan.tryOverpayment _ _ = _›
  exact PaymentAmounts.add_onGrid hsb hp hre ‹PaymentAmounts.add _ _ = _›

/-- A payment pays its principal and its interest in whole LoanScale units, for every payment type. -/
lemma Loan.payInstalments_onGrid (loan : Loan) (v : Vault) (pt : LoanPaymentType) (amount : Number) (now : UInt32)
    (p : UnsettledPayment Vault) (hr : -81 ≤ loan.loanScale ∧ loan.loanScale ≤ 0)
    (h : (loan.payInstalments v pt amount now).run = .ok (.ok p)) : p.amounts.OnGrid loan.loanScale := by
  have hsb := Loan.loanScale_bounds loan
  have hreg : ∀ p0 : UnsettledPayment Vault, (loan.payInstalments v .regular amount now).run = .ok (.ok p0) →
      p0.amounts.OnGrid loan.loanScale ∧ p0.loan.loanScale = loan.loanScale := by
    intro p0 hp0
    obtain ⟨si, -, hloop, -⟩ := Loan.payScheduled_loop loan v amount now p0 hp0
    refine ⟨UnsettledPayment.payInstalments_onGrid amount _ hr _ _ _ hloop rfl (PaymentAmounts.zero_onGrid _), ?_⟩
    obtain ⟨-, -, hst, -, -⟩ := Loan.payInstalments_ok loan v .regular amount now p0 hp0
    exact hst.loanScale
  cases pt
  · exact (hreg p h).1
  · obtain ⟨pc, hpc, hamt, -⟩ := Loan.latePayInstalments_ok loan v amount now p h
    obtain ⟨g1, g2, g3, g4⟩ := Loan.lateComponents_onGrid loan now pc hr hpc
    exact PaymentComponents.paidAmounts_onGrid hamt hsb g1 g2 g3 g4
  · obtain ⟨pc, hpc, hamt, -⟩ := Loan.fullPayInstalments_ok loan v amount now p h
    obtain ⟨g1, g2, g3, g4⟩ := Loan.fullComponents_onGrid loan now pc hr hpc
    exact PaymentComponents.paidAmounts_onGrid hamt hsb g1 g2 g3 g4
  · obtain ⟨p0, h0, h1⟩ := Loan.overPayInstalments_ok loan v amount now p h
    obtain ⟨hp0, hls0⟩ := hreg p0 h0
    exact UnsettledPayment.applyOverpayment_onGrid p0 p amount _ hr hls0 hp0 h1

private lemma PaymentAmounts.add_fee_onGrid {s : Int} {a b c : PaymentAmounts}
    (hs : minExponent + 18 ≤ s ∧ s ≤ maxExponent - 1) (ha : Number.OnGrid s a.feePaid)
    (hb : Number.OnGrid s b.feePaid) (h : a.add b = .ok c) : Number.OnGrid s c.feePaid := by
  unfold PaymentAmounts.add at h
  simp only [bind, Except.bind] at h
  walk_ok
  obtain rfl := (Except.ok.inj ‹pure _ = Except.ok c›)
  exact Number.OnGrid.add ha hb hs ‹_›

/-- The scheduled instalments sum their fees on the grid, while LoanServiceFee is on it. -/
private lemma UnsettledPayment.payInstalments_fee_onGrid {α : Type} (amount : Number) (s : Int)
    (hr : -81 ≤ s ∧ s ≤ 0) (fee : Number) (gfee : Number.OnGrid s fee) :
    ∀ (n : Nat) (payment p : UnsettledPayment α), UnsettledPayment.payInstalments payment n amount = .ok p →
      payment.loan.loanScale = s → payment.loan.fees.serviceFee = fee → Number.OnGrid s payment.amounts.feePaid →
      Number.OnGrid s p.amounts.feePaid := by
  intro n
  induction n with
  | zero =>
    intro payment p h _ _ hp
    unfold UnsettledPayment.payInstalments at h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    exact hp
  | succ k ih =>
    intro payment p h hls hfee hp
    unfold UnsettledPayment.payInstalments at h
    unfold_ter at h
    walk_ok'
    all_goals first
      | exact hp
      | (have hsb := Loan.loanScale_bounds payment.loan
         rw [hls] at hsb
         obtain ⟨-, -, g3, -⟩ := Loan.scheduledComponents_onGrid payment.loan _ (hls ▸ hr)
           ‹Loan.scheduledComponents payment.loan = _›
         rw [hls] at g3
         obtain ⟨-, -, -, -, -, e4, -⟩ := PaymentComponents.paidAmounts_ok_inv _ _
           ‹PaymentComponents.paidAmounts _ = _›
         have hinst := Number.OnGrid.add g3 (by rw [hfee]; exact gfee) hsb e4
         have hsum := PaymentAmounts.add_fee_onGrid hsb hp hinst ‹PaymentAmounts.add _ _ = _›
         first
           | exact hsum
           | (have hst := Loan.doPayment_sameTerms _ _ _ ‹Loan.doPayment _ _ = _›
              exact ih _ _ ‹UnsettledPayment.payInstalments _ k amount = _› (hst.loanScale.trans hls)
                ((congrArg LoanFees.serviceFee hst.fees).trans hfee) hsum))

/-- The late instalment pays its fees on the grid, while LoanServiceFee and LatePaymentFee are on it. -/
private lemma Loan.lateComponents_fee_onGrid (l : Loan) (now : UInt32) (pc : PaymentComponents)
    (hr : -81 ≤ l.loanScale ∧ l.loanScale ≤ 0) (gs : Number.OnGrid l.loanScale l.fees.serviceFee)
    (gl : Number.OnGrid l.loanScale l.fees.latePaymentFee) (h : Loan.lateComponents l now = .ok pc) :
    Number.OnGrid l.loanScale pc.managementFeeDelta ∧ Number.OnGrid l.loanScale pc.untrackedManagementFee := by
  have hsb := Loan.loanScale_bounds l
  unfold Loan.lateComponents at h
  simp only [bind, Except.bind] at h
  walk_ok
  obtain rfl := (Except.ok.inj ‹pure _ = Except.ok pc›)
  obtain ⟨-, -, g3, -⟩ := Loan.scheduledComponents_onGrid l _ hr ‹Loan.scheduledComponents l = _›
  obtain ⟨-, g4⟩ := roundAndSplitInterest_onGrid _ _ _ _ _ _ _ hr hsb ‹roundAndSplitInterest _ _ _ _ _ = _›
  have g5 := Number.OnGrid.add gs gl hsb ‹l.fees.serviceFee.operator_add l.fees.latePaymentFee .to_nearest = _›
  exact ⟨g3, Number.OnGrid.add g5 g4 hsb ‹_›⟩

/-- The full payoff pays its fees on the grid. -/
private lemma Loan.fullComponents_fee_onGrid (l : Loan) (now : UInt32) (pc : PaymentComponents)
    (hr : -81 ≤ l.loanScale ∧ l.loanScale ≤ 0) (h : Loan.fullComponents l now = .ok pc) :
    Number.OnGrid l.loanScale pc.managementFeeDelta ∧ Number.OnGrid l.loanScale pc.untrackedManagementFee := by
  have hsb := Loan.loanScale_bounds l
  obtain ⟨_, _, _, net, split, state, cf, ppi, tracked, cfm, uf, ui, -, -, -, hsplit, hstate, hcf, -, -,
    hcfm, huf, -, rfl⟩ := Loan.fullComponents_ok_inv l now pc h
  obtain ⟨t, p, m, -, -, -, ht, hp, hm, hi, -, -, -, -⟩ := Loan.state_units l state hstate
  obtain ⟨-, gs⟩ := roundAndSplitInterest_onGrid _ _ _ _ _ _ _ hr hsb hsplit
  have gcf := STAmount.roundToNumericType_onGrid _ _ _ _ _ ⟨hr.1, by omega⟩ (fun _ => hr.2) hcf
  exact ⟨hm.onGrid, Number.OnGrid.sub (Number.OnGrid.add gcf gs hsb hcfm) hm.onGrid hsb huf⟩

/-- The overpayment split pays its fees on the grid. -/
private lemma Loan.overpaymentComponents_fee_onGrid (l : Loan) (x : Number) (opc : PaymentComponents)
    (hr : -81 ≤ l.loanScale ∧ l.loanScale ≤ 0) (h : Loan.overpaymentComponents l x = .ok opc) :
    Number.OnGrid l.loanScale opc.managementFeeDelta ∧ Number.OnGrid l.loanScale opc.untrackedManagementFee := by
  have hsb := Loan.loanScale_bounds l
  unfold Loan.overpaymentComponents at h
  simp only [bind, Except.bind] at h
  walk_ok
  obtain rfl := (Except.ok.inj ‹pure _ = Except.ok opc›)
  exact ⟨(roundAndSplitInterest_onGrid _ _ _ _ _ _ _ hr hsb ‹roundAndSplitInterest _ _ _ _ _ = _›).2,
    STAmount.roundToNumericType_onGrid _ _ _ _ _ ⟨hr.1, by omega⟩ (fun _ => hr.2)
      ‹STAmount.roundToNumericType _ _ _ _ = _›⟩

/-- A re-amortization pays the fees of the overpayment split. -/
private lemma Loan.tryOverpayment_fee_onGrid (l : Loan) (opc : PaymentComponents) (re : Reamortization)
    (hs : minExponent + 18 ≤ l.loanScale ∧ l.loanScale ≤ maxExponent - 1)
    (g1 : Number.OnGrid l.loanScale opc.managementFeeDelta)
    (g2 : Number.OnGrid l.loanScale opc.untrackedManagementFee)
    (h : Loan.tryOverpayment l opc = .ok (some re)) : Number.OnGrid l.loanScale re.amounts.feePaid := by
  unfold Loan.tryOverpayment at h
  simp only [bind, Except.bind] at h
  walk_ok
  all_goals first
    | (have hn := Except.ok.inj ‹pure none = Except.ok (some re)›; cases hn)
    | skip
  obtain rfl := Option.some.inj (Except.ok.inj ‹pure (some _) = Except.ok (some re)›)
  exact Number.OnGrid.add g1 g2 hs ‹_›

/-- The overpayment tail keeps the fee sum on the grid. -/
private lemma UnsettledPayment.applyOverpayment_fee_onGrid (payment p' : UnsettledPayment Vault) (amount : Number)
    (s : Int) (hr : -81 ≤ s ∧ s ≤ 0) (hls : payment.loan.loanScale = s) (hp : Number.OnGrid s payment.amounts.feePaid)
    (h : UnsettledPayment.applyOverpayment payment amount = .ok p') : Number.OnGrid s p'.amounts.feePaid := by
  simp only [UnsettledPayment.applyOverpayment] at h
  unfold_ter at h
  walk_ok
  all_goals first
    | exact hp
    | skip
  subst hls
  have hsb := Loan.loanScale_bounds payment.loan
  obtain ⟨g1, g2⟩ := Loan.overpaymentComponents_fee_onGrid _ _ _ hr ‹Loan.overpaymentComponents _ _ = _›
  have hre := Loan.tryOverpayment_fee_onGrid _ _ _ hsb g1 g2 ‹Loan.tryOverpayment _ _ = _›
  exact PaymentAmounts.add_fee_onGrid hsb hp hre ‹PaymentAmounts.add _ _ = _›

/-- A payment pays its fee in whole LoanScale units, for every payment type, while LoanServiceFee and
LatePaymentFee are whole units. -/
lemma Loan.payInstalments_fee_onGrid (loan : Loan) (v : Vault) (pt : LoanPaymentType) (amount : Number)
    (now : UInt32) (p : UnsettledPayment Vault) (hr : -81 ≤ loan.loanScale ∧ loan.loanScale ≤ 0)
    (gs : Number.OnGrid loan.loanScale loan.fees.serviceFee)
    (gl : Number.OnGrid loan.loanScale loan.fees.latePaymentFee)
    (h : (loan.payInstalments v pt amount now).run = .ok (.ok p)) :
    Number.OnGrid loan.loanScale p.amounts.feePaid := by
  have hsb := Loan.loanScale_bounds loan
  have hreg : ∀ p0 : UnsettledPayment Vault, (loan.payInstalments v .regular amount now).run = .ok (.ok p0) →
      Number.OnGrid loan.loanScale p0.amounts.feePaid ∧ p0.loan.loanScale = loan.loanScale := by
    intro p0 hp0
    obtain ⟨si, -, hloop, -⟩ := Loan.payScheduled_loop loan v amount now p0 hp0
    refine ⟨UnsettledPayment.payInstalments_fee_onGrid amount _ hr _ gs _ _ _ hloop rfl rfl
      (Number.OnGrid.zero _), ?_⟩
    obtain ⟨-, -, hst, -, -⟩ := Loan.payInstalments_ok loan v .regular amount now p0 hp0
    exact hst.loanScale
  cases pt
  · exact (hreg p h).1
  · obtain ⟨pc, hpc, hamt, -⟩ := Loan.latePayInstalments_ok loan v amount now p h
    obtain ⟨g1, g2⟩ := Loan.lateComponents_fee_onGrid loan now pc hr gs gl hpc
    obtain ⟨-, -, -, -, -, e4, -⟩ := PaymentComponents.paidAmounts_ok_inv pc _ hamt
    exact Number.OnGrid.add g1 g2 hsb e4
  · obtain ⟨pc, hpc, hamt, -⟩ := Loan.fullPayInstalments_ok loan v amount now p h
    obtain ⟨g1, g2⟩ := Loan.fullComponents_fee_onGrid loan now pc hr hpc
    obtain ⟨-, -, -, -, -, e4, -⟩ := PaymentComponents.paidAmounts_ok_inv pc _ hamt
    exact Number.OnGrid.add g1 g2 hsb e4
  · obtain ⟨p0, h0, h1⟩ := Loan.overPayInstalments_ok loan v amount now p h
    obtain ⟨hp0, hls0⟩ := hreg p0 h0
    exact UnsettledPayment.applyOverpayment_fee_onGrid p0 p amount _ hr hls0 hp0 h1

end XRPL.Model.Lending
