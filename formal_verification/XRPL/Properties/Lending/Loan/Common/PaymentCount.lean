import XRPL.Properties.Lending.Loan.Common.CreatedSize
import XRPL.Properties.Lending.Loan.Common.InstalmentCap
import XRPL.Properties.Lending.Loan.Common.InterestMonotone
import XRPL.Properties.Lending.Loan.Common.Outstanding
import XRPL.Properties.Lending.Loan.Common.RegularInterest
import XRPL.Properties.Lending.Loan.Common.Schedule
import XRPL.Properties.Lending.Loan.Common.SetInterest
import XRPL.Properties.Protocol.Number.ToRep.ToRep

/-! # A reachable loan needs every payment it has left

The amortization guards of LoanSet and of each re-amortization keep PaymentRemaining − 1 rounded-up
PeriodicPayments below TotalValueOutstanding, and an instalment that isn't the last takes at most one off. -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault (Vault RawVault)

open private Loan.scheduledComponents Loan.lateComponents Loan.doPayment UnsettledPayment.payInstalments
  UnsettledPayment.applyOverpayment Loan.tryOverpayment Loan.settlePayment from XRPL.Model.Lending.Loan.LoanPay
open private Loan.changeImpairment from XRPL.Model.Lending.Loan.LoanManage
open private LoanState.build_fields Loan.lateComponents_scheduled from XRPL.Properties.Lending.Loan.Common.PayMonotone
open private Loan.doPayment_outstanding from XRPL.Properties.Lending.Loan.Common.RegularInterest
open private Loan.doPayment_interestDue ite_bind_ok from XRPL.Properties.Lending.Loan.Common.InterestDue

/-- The loan needs every payment it has left: PaymentRemaining − 1 PeriodicPayments rounded up at LoanScale fall
short of TotalValueOutstanding. -/
def Loan.NeedsAllPayments (loan : Loan) : Prop :=
  loan.paymentRemaining ≠ 0 → ∀ pp' : Number,
    STAmount.roundToNumericType loan.broker.numericType loan.periodicPayment .upward (some loan.loanScale) =
      .ok pp' → ((loan.paymentRemaining.toNat : ℚ) - 1) * pp'.toRat < loan.totalValueOutstanding.toRat

/-- A loan with the same count, PeriodicPayment, TotalValueOutstanding, LoanScale and asset needs the same. -/
lemma Loan.NeedsAllPayments.of_same {l l' : Loan} (h : l.NeedsAllPayments)
    (h1 : l'.paymentRemaining = l.paymentRemaining) (h2 : l'.periodicPayment = l.periodicPayment)
    (h3 : l'.totalValueOutstanding = l.totalValueOutstanding) (h4 : l'.loanScale = l.loanScale)
    (h5 : l'.broker.numericType = l.broker.numericType) : l'.NeedsAllPayments := by
  intro hpr pp' hpp
  rw [h2, h4, h5] at hpp
  rw [h1, h3]
  exact h (by rw [← h1]; exact hpr) pp' hpp

/-- A loan rebuilt with the same amounts, schedule position and asset needs the same. -/
lemma Loan.NeedsAllPayments.of_raw {l l' : Loan} {raw : RawLoan} (h : l.NeedsAllPayments)
    (hl : raw.to_lawful = .ok l') (h1 : raw.paymentRemaining = l.paymentRemaining)
    (h2 : raw.periodicPayment = l.periodicPayment) (h3 : raw.totalValueOutstanding = l.totalValueOutstanding)
    (h4 : raw.loanScale = l.loanScale) (h5 : raw.broker.numericType = l.broker.numericType) :
    l'.NeedsAllPayments := by
  have hr := (RawLoan.to_lawful_ok hl).1
  exact h.of_same (by rw [← h1, ← hr]) (by rw [← h2, ← hr]) (by rw [← h3, ← hr]) (by rw [← h4, ← hr])
    (by rw [← h5, ← hr])

/-- A loan with no payments left needs none. -/
lemma Loan.NeedsAllPayments.of_paid {l : Loan} (h : l.paymentRemaining = 0) : l.NeedsAllPayments :=
  fun h0 => absurd h h0

/-- With two or more payments left, the next scheduled instalment isn't the last. -/
lemma Loan.NeedsAllPayments.not_final {l : Loan} (h : l.NeedsAllPayments) (hpr : 2 ≤ l.paymentRemaining.toNat)
    (pc : PaymentComponents) (hpc : Loan.scheduledComponents l = .ok pc) : pc.isFinal = false := by
  unfold Loan.scheduledComponents at hpc
  obtain ⟨rate, -, hpc⟩ := bind_ok_peel _ _ _ hpc
  obtain ⟨pp', hpp, hpc⟩ := bind_ok_peel _ _ _ hpc
  dsimp only at hpc
  split at hpc
  · rename_i hfin
    exfalso
    have hpr0 : l.paymentRemaining ≠ 0 := fun h0 => by rw [h0] at hpr; simp at hpr
    have hlt := h hpr0 pp' hpp
    have hT0 : 0 ≤ l.totalValueOutstanding.toRat := l.exact.totalValueOutstanding_nonneg
    have h2 : (1 : ℚ) ≤ (l.paymentRemaining.toNat : ℚ) - 1 := by
      have : (2 : ℚ) ≤ l.paymentRemaining.toNat := by exact_mod_cast hpr
      linarith
    simp only [Bool.or_eq_true, beq_iff_eq] at hfin
    rcases hfin with h1 | hle
    · rw [h1] at hpr; simp at hpr
    · have hle' := (operator_le_iff _ _ l.wf.totalValueOutstanding_norm
        (STAmount.roundToNumericType_isNormalized _ _ _ _ _ hpp)).mp hle
      by_cases hpp0 : 0 ≤ pp'.toRat
      · nlinarith
      · linarith
  · repeat (obtain ⟨_, -, hpc⟩ := bind_ok_peel _ _ _ hpc)
    obtain ⟨_, -, hpc⟩ := ite_bind_ok _ _ _ _ _ hpc
    repeat (obtain ⟨_, -, hpc⟩ := bind_ok_peel _ _ _ hpc)
    obtain ⟨_, -, hpc⟩ := ite_bind_ok _ _ _ _ _ hpc
    repeat (obtain ⟨_, -, hpc⟩ := bind_ok_peel _ _ _ hpc)
    obtain rfl := (Except.ok.inj hpc).symm
    rfl

/-- One instalment keeps the loan needing every payment it has left, and its interestDue at least zero. One
that isn't the last takes at most a rounded-up PeriodicPayment off, and exactly its value delta. -/
lemma Loan.doPayment_needs (l l' : Loan) (pc0 pc : PaymentComponents) (hlo : -81 ≤ l.loanScale)
    (hint : l.broker.numericType.isIntegral = true → l.loanScale ≤ 0) (hi : 0 ≤ l.toExact.interestDue)
    (hn : l.NeedsAllPayments) (hpr0 : l.paymentRemaining ≠ 0) (hpc0 : Loan.scheduledComponents l = .ok pc0)
    (hdo : Loan.doPayment l pc = .ok l') (e1 : pc.totalValueDelta = pc0.totalValueDelta)
    (e2 : pc.principalDelta = pc0.principalDelta) (e3 : pc.managementFeeDelta = pc0.managementFeeDelta)
    (e4 : pc.isFinal = pc0.isFinal) : l'.NeedsAllPayments ∧ 0 ≤ l'.toExact.interestDue := by
  rcases Loan.scheduledComponents_tracked l pc0 hlo hint hi hpc0 with hf | ⟨hf, ht⟩
  · have hf' : pc.isFinal = true := by rw [e4]; exact hf
    exact ⟨Loan.NeedsAllPayments.of_paid (Loan.doPayment_final _ _ _ hf' hdo),
      Loan.doPayment_interestDue l l' pc hi (Or.inl hf') hdo⟩
  have hf' : pc.isFinal = false := by rw [e4]; exact hf
  obtain ⟨g1, g2, g3, r1, r2, r3, hle, hmv⟩ := ht
  have htr : pc.Tracked l := ⟨by rw [e1]; exact g1, by rw [e2]; exact g2, by rw [e3]; exact g3, by rw [e1]; exact r1,
    by rw [e2]; exact r2, by rw [e3]; exact r3, by rw [e1, e2, e3]; exact hle, by rw [e1, e3]; exact hmv⟩
  refine ⟨?_, Loan.doPayment_interestDue l l' pc hi (Or.inr ⟨hf', htr⟩) hdo⟩
  -- the instalment takes exactly its value delta, at most a rounded-up PeriodicPayment
  obtain ⟨d1, -, -⟩ := (Loan.doPayment_outstanding l l' pc hdo).2 hf'
  obtain ⟨gT, -, -, hTb, -, -, -⟩ := Loan.outstanding_grid l
  have vT := Number.OnGrid.sub_exact gT htr.totalValue_grid htr.totalValue_range.1 htr.totalValue_range.2 hTb
    (Loan.loanScale_bounds l) d1
  have hst := Loan.doPayment_sameTerms _ _ _ hdo
  have hpr' := (Loan.doPayment_notFinal _ _ _ hf' hdo).1
  have hpp' : l'.periodicPayment = l.periodicPayment := by
    unfold Loan.doPayment at hdo
    simp only [hf', Bool.false_eq_true, ↓reduceIte] at hdo
    unfold_ter at hdo
    walk_ok
    exact (congrArg RawLoan.periodicPayment (RawLoan.to_lawful_ok ‹_›).1 :)
  intro h0 pp' hpp
  rw [hpp', hst.loanScale, hst.broker] at hpp
  have hcap := Loan.scheduledComponents_value_le l pc0 pp' hlo hint hi hpp hpc0 hf
  rw [← e1] at hcap
  have hlt := hn hpr0 pp' hpp
  have h2 : 2 ≤ l.paymentRemaining.toNat := by
    have h1 := Loan.scheduledComponents_not_last _ _ hpc0 hf
    have a := UInt32.toNat_inj.not.mpr hpr0
    have b := UInt32.toNat_inj.not.mpr h1
    simp at a b; omega
  have hsub : (l'.paymentRemaining.toNat : ℚ) = (l.paymentRemaining.toNat : ℚ) - 1 := by
    rw [hpr', UInt32.toNat_sub_of_le _ _ (by rw [UInt32.le_iff_toNat_le]; simp; omega)]
    simp only [UInt32.toNat_one]
    push_cast [show 1 ≤ l.paymentRemaining.toNat by omega]
    ring
  rw [hsub, vT]
  linarith

/-- The instalment loop keeps the loan needing every payment it has left. -/
private lemma UnsettledPayment.payInstalments_needs {α : Type} (amount : Number) :
    ∀ (n : Nat) (payment p' : UnsettledPayment α), UnsettledPayment.payInstalments payment n amount = .ok p' →
      -81 ≤ payment.loan.loanScale →
      (payment.loan.broker.numericType.isIntegral = true → payment.loan.loanScale ≤ 0) →
      0 ≤ payment.loan.toExact.interestDue → payment.loan.NeedsAllPayments →
      p'.loan.NeedsAllPayments ∧ 0 ≤ p'.loan.toExact.interestDue := by
  intro n
  induction n with
  | zero =>
    intro payment p' h _ _ hi hn
    rw [UnsettledPayment.payInstalments] at h
    obtain rfl := Except.ok.inj h
    exact ⟨hn, hi⟩
  | succ n ih =>
    intro payment p' h hlo hint hi hn
    rw [UnsettledPayment.payInstalments] at h
    unfold_ter at h
    walk_ok
    · exact ⟨hn, hi⟩
    · exact ⟨hn, hi⟩
    all_goals
      have hpr0 : payment.loan.paymentRemaining ≠ 0 := by
        simpa using ‹¬(payment.loan.paymentRemaining == 0) = true›
      have hdo := ‹Loan.doPayment _ _ = _›
      have hsc := ‹Loan.scheduledComponents payment.loan = _›
      have hstep := Loan.doPayment_needs _ _ _ _ hlo hint hi hn hpr0 hsc hdo rfl rfl rfl rfl
      have hst := Loan.doPayment_sameTerms _ _ _ hdo
    · exact hstep
    · have h3 := ‹UnsettledPayment.payInstalments _ n amount = _›
      refine ih _ p' h3 ?_ ?_ hstep.2 hstep.1
      · dsimp only; rw [hst.loanScale]; exact hlo
      · dsimp only; rw [hst.loanScale, hst.broker]; exact hint

/-- A re-amortization that passes leaves the loan needing every payment it has left. It passes the amortization
guards on its new PeriodicPayment and TotalValueOutstanding. -/
private lemma Loan.tryOverpayment_needs (l : Loan) (opc : PaymentComponents) (re : Reamortization)
    (h : Loan.tryOverpayment l opc = .ok (some re)) (hs : -81 ≤ l.loanScale ∧ l.loanScale ≤ 80)
    (hpr : l.paymentRemaining ≠ 0) (hppN : re.periodicPayment.isNormalized)
    (htvN : re.state.valueOutstanding.isNormalized) (pp' : Number)
    (hpp : STAmount.roundToNumericType l.broker.numericType re.periodicPayment .upward (some l.loanScale) =
      .ok pp') :
    ((l.paymentRemaining.toNat : ℚ) - 1) * pp'.toRat < re.state.valueOutstanding.toRat := by
  unfold Loan.tryOverpayment at h
  simp only [bind, Except.bind] at h
  walk_ok
  all_goals first
    | (have hn := Except.ok.inj ‹pure none = Except.ok (some re)›; cases hn)
    | skip
  obtain rfl := Option.some.inj (Except.ok.inj ‹pure (some _) = Except.ok (some re)›)
  rename_i _ g hg hgs _ _ _ hsig _ _ _ _ _ _ _ _ _
  obtain ⟨hb1, -, -⟩ := LoanState.build_fields _ _ _ _ ‹LoanState.build _ _ _ = _›
  simp only [hb1] at htvN ⊢
  have hgt : g.isTesSuccess = true := by revert hgs; cases g.isTesSuccess <;> decide
  rw [(TER.isTesSuccess_iff g).mp hgt] at hg
  simp only [Bool.or_eq_true, decide_eq_true_eq, not_or, not_le] at hsig
  have hpp0 := (Number.signum_pos_iff_toRat hppN).mp hsig.1.1
  obtain ⟨rp, hrp, -, key⟩ := LoanProperties.amortizationGuards_room _ _ _ _ _ hpr hg htvN hppN hpp0.le hs
  simp only at hrp key hpp
  rw [hpp] at hrp
  obtain rfl := Except.ok.inj hrp
  exact key

/-- The overpayment tail keeps the loan needing every payment it has left. -/
private lemma UnsettledPayment.applyOverpayment_needs (payment p' : UnsettledPayment Vault) (amount : Number)
    (hn : payment.loan.NeedsAllPayments) (hs : -81 ≤ payment.loan.loanScale ∧ payment.loan.loanScale ≤ 80)
    (h : UnsettledPayment.applyOverpayment payment amount = .ok p') : p'.loan.NeedsAllPayments := by
  unfold UnsettledPayment.applyOverpayment at h
  unfold_ter at h
  walk_ok
  all_goals first
    | exact hn
    | skip
  rename_i re hre _ _ _ _ loan' hl
  obtain ⟨he, -, -⟩ := RawLoan.to_lawful_ok hl
  have hn' : loan'.paymentRemaining = payment.loan.paymentRemaining := by
    rw [show loan'.paymentRemaining = loan'.toRawLoan.paymentRemaining from rfl, he]
  have hpp : loan'.periodicPayment = re.periodicPayment := by
    rw [show loan'.periodicPayment = loan'.toRawLoan.periodicPayment from rfl, he]
  have htv : loan'.totalValueOutstanding = re.state.valueOutstanding := by
    rw [show loan'.totalValueOutstanding = loan'.toRawLoan.totalValueOutstanding from rfl, he]
  have hls : loan'.loanScale = payment.loan.loanScale := by
    rw [show loan'.loanScale = loan'.toRawLoan.loanScale from rfl, he]
  have hnt : loan'.broker = payment.loan.broker := by
    rw [show loan'.broker = loan'.toRawLoan.broker from rfl, he]
  intro hpr pp' hpp'
  rw [hn'] at hpr
  rw [hpp, hls, hnt] at hpp'
  rw [hn', htv]
  exact Loan.tryOverpayment_needs _ _ _ hre hs hpr (by rw [← hpp]; exact loan'.wf.periodicPayment_norm)
    (by rw [← htv]; exact loan'.wf.totalValueOutstanding_norm) pp' hpp'

/-- A payment of any type keeps the loan needing every payment it has left. -/
lemma Loan.pay_needs (loan : Loan) (v : Vault) (pt : LoanPaymentType) (amount : Number) (now : UInt32)
    (r : LoanWithAmounts Vault) (hlo : -81 ≤ loan.loanScale) (hhi : loan.loanScale ≤ 80)
    (hint : loan.broker.numericType.isIntegral = true → loan.loanScale ≤ 0) (hi : 0 ≤ loan.toExact.interestDue)
    (hn : loan.NeedsAllPayments) (h : (loan.pay v pt amount now).run = .ok (.ok r)) :
    r.loan'.NeedsAllPayments := by
  obtain ⟨p, hp, hsettle⟩ := Loan.pay_ok loan v pt amount now r h
  obtain ⟨_, _, _, _, _, _, broker', -, -, -, hbroker, hloan, -, -⟩ := UnsettledPayment.settle_ok p r hsettle
  suffices hp' : p.loan.NeedsAllPayments by
    refine hp'.of_raw hloan rfl rfl rfl rfl ?_
    show broker'.toRawLoanBroker.numericType = _
    rw [(RawLoanBroker.to_lawful_ok hbroker).1]
  have hu : loan.unimpaired.NeedsAllPayments := hn.of_same rfl rfl rfl rfl rfl
  have hiu : 0 ≤ loan.unimpaired.toExact.interestDue := hi
  have hpr0 : loan.paymentRemaining ≠ 0 := (Loan.payInstalments_ok loan v pt amount now p hp).1.remaining
  cases pt
  · obtain ⟨si, -, hloop, -⟩ := Loan.payScheduled_loop loan v amount now p hp
    exact (UnsettledPayment.payInstalments_needs amount _ _ p hloop hlo hint hiu hu).1
  · obtain ⟨pc, hpc, -, hdo⟩ := Loan.latePayInstalments_ok loan v amount now p hp
    obtain ⟨pc0, hpc0, e1, e2, e3, e4⟩ := Loan.lateComponents_scheduled loan now pc hpc
    exact (Loan.doPayment_needs loan.unimpaired p.loan pc0 pc hlo hint hiu hu hpr0
      (by rw [Loan.scheduledComponents_unimpaired]; exact hpc0) hdo e1 e2 e3 e4).1
  · exact Loan.NeedsAllPayments.of_paid (Loan.fullPayInstalments_paid loan v amount now p hp)
  · obtain ⟨p0, h0, h1⟩ := Loan.overPayInstalments_ok loan v amount now p hp
    obtain ⟨si, -, hloop, -⟩ := Loan.payScheduled_loop loan v amount now p0 h0
    have hn0 := (UnsettledPayment.payInstalments_needs amount _ _ p0 hloop hlo hint hiu hu).1
    obtain ⟨-, -, hst, -, -⟩ := Loan.payInstalments_ok loan v .regular amount now p0 h0
    exact UnsettledPayment.applyOverpayment_needs p0 p amount hn0
      (by rw [hst.loanScale]; exact ⟨hlo, hhi⟩) h1

/-- An accept keeps the loan needing every payment it has left. -/
private lemma Loan.accept_needs (loan : Loan) (v : Vault) (r : LoanWithDisbursement Vault)
    (hn : loan.NeedsAllPayments) (h : (loan.accept v).run = .ok (.ok r)) : r.loan'.NeedsAllPayments := by
  simp only [Loan.accept] at h
  unfold_ter at h
  walk_ok
  have hl := ‹RawLoan.to_lawful _ = Except.ok _›
  exact hn.of_raw hl rfl rfl rfl rfl rfl

/-- Changing the impairment keeps the loan needing every payment it has left. -/
private lemma Loan.changeImpairment_needs (loan : Loan) (v : Vault) (b : Bool) (r : LoanWithPool Vault)
    (hn : loan.NeedsAllPayments) (h : (Loan.changeImpairment loan v b).run = .ok (.ok r)) :
    r.loan'.NeedsAllPayments := by
  simp only [Loan.changeImpairment] at h
  unfold_ter at h
  walk_ok
  all_goals
    have hl := ‹RawLoan.to_lawful _ = Except.ok _›
    exact hn.of_raw hl rfl rfl rfl rfl rfl

/-- A loan a LoanSet creates needs every payment it has. -/
lemma Loan.Created.needsAllPayments {start : Loan} {t₀ : UInt32} (h : Loan.Created start t₀) :
    start.NeedsAllPayments := by
  obtain ⟨broker, v, principal, rates, fees, pi, pt, gp, sd, twoStep, allowsOverpayment, r, -, hok, rfl⟩ := h
  obtain ⟨props, _, _, _, broker', _, _, _, _, _, hchecks, -, -, -, hl, hb⟩ :=
    Loan.create_pool_sums broker v principal rates fees _ allowsOverpayment twoStep r hok
  have hexg := r.loan'.grid
  have hwf := r.loan'.wf
  have hTV : r.loan'.totalValueOutstanding = props.totalValueOutstanding := by
    show r.loan'.toRawLoan.totalValueOutstanding = _; rw [hl]; rfl
  have hPP : r.loan'.periodicPayment = props.periodicPayment := by
    show r.loan'.toRawLoan.periodicPayment = _; rw [hl]; rfl
  have hLS : r.loan'.loanScale = props.loanScale := by
    show r.loan'.toRawLoan.loanScale = _; rw [hl]; rfl
  have hN : r.loan'.paymentRemaining = (LoanSchedule.build pi pt gp sd t₀ twoStep).paymentTotal := by
    show r.loan'.toRawLoan.paymentRemaining = _; rw [hl]; rfl
  have hNT : r.loan'.broker.numericType = broker.numericType := by
    show r.loan'.toRawLoan.broker.toRawLoanBroker.numericType = _; rw [hl]
    show broker'.toRawLoanBroker.numericType = _; rw [hb]
  have hrange := hexg.loanScale_range
  simp only [RawLoan.toExact] at hrange
  rw [hLS] at hrange
  obtain ⟨hlo, hhi, -⟩ := Loan.create_loanScale_range broker v principal rates fees _ props _ _ hchecks hrange.2
  have hpp0 : 0 < props.periodicPayment.toRat := by
    have := r.loan'.exact.periodicPayment_pos; simp only [RawLoan.toExact] at this; rwa [hPP] at this
  intro hpr pp' hpp
  rw [hN] at hpr ⊢
  rw [hPP, hLS, hNT] at hpp
  rw [hTV]
  obtain ⟨rp, hrp, -, key⟩ := LoanProperties.amortizationGuards_room _ _ _ _ _ hpr
    (LoanProperties.checkGuards_amortization _ _ _ _ _ hchecks.guards) (hTV ▸ hwf.totalValueOutstanding_norm)
    (hPP ▸ hwf.periodicPayment_norm) hpp0.le ⟨by omega, hhi⟩
  rw [hpp] at hrp
  obtain rfl := Except.ok.inj hrp
  exact key

/-- Every loan reachable from a LoanSet needs every payment it has left. -/
lemma Loan.ReachableFrom.needsAllPayments {start : Loan} {t₀ : UInt32} {loan : Loan} {t : UInt32}
    (hc : Loan.Created start t₀) (hr : Loan.ReachableFrom start t₀ loan t) : loan.NeedsAllPayments := by
  have hlo := Loan.Created.loanScale_ge hc
  have hhi : start.loanScale ≤ 80 := by
    have := start.wf.loanScale_range.2; unfold cMaxOffset at this; exact this
  have hint := Loan.Created.loanScale_integral hc
  have hi0 := hc.interestDue_nonneg
  have hpay : ∀ {l : Loan} {t' : UInt32}, Loan.ReachableFrom start t₀ l t' → l.NeedsAllPayments →
      ∀ (v : Vault) (pt : LoanPaymentType) (amount : Number) (now : UInt32) (r : LoanWithAmounts Vault),
      (l.pay v pt amount now).run = .ok (.ok r) → r.loan'.NeedsAllPayments := by
    intro l t' hr' hn v pt amount now r h
    have hft := Loan.ReachableFrom.fixed_terms_proof _ _ _ _ hr'
    have hls := hft.2.2.2.2.2.2.1
    have hnt := Loan.ReachableFrom.numericType hr'
    exact Loan.pay_needs l v pt amount now r (by rw [hls]; omega) (by rw [hls]; exact hhi)
      (by rw [hls, hnt]; exact hint) (hr'.interestDue_nonneg hi0 (by omega)) hn h
  induction hr with
  | refl => exact Loan.Created.needsAllPayments hc
  | refresh _ _ _ _ _ hnt h ih => exact ih.of_raw h rfl rfl rfl rfl hnt
  | accept _ _ _ _ _ _ _ _ h ih => exact Loan.accept_needs _ _ _ ih h
  | regularPayment _ _ _ _ _ _ hr' _ _ h ih => exact hpay hr' ih _ .regular _ _ _ h
  | latePayment _ _ _ _ _ _ hr' _ _ h ih => exact hpay hr' ih _ .late _ _ _ h
  | fullPayment _ _ _ _ _ _ hr' _ _ h ih => exact hpay hr' ih _ .full _ _ _ h
  | overpayment _ _ _ _ _ _ hr' _ _ h ih => exact hpay hr' ih _ .overpayment _ _ _ h
  | impair _ _ _ _ _ _ _ _ h ih =>
    simp only [Loan.manageImpair] at h
    unfold_ter at h
    walk_ok
    exact Loan.changeImpairment_needs _ _ true _ ih ‹_›
  | unimpair _ _ _ _ _ _ _ _ h ih => exact Loan.changeImpairment_needs _ _ false _ ih h
  | default _ _ _ _ _ _ _ _ h ih => exact Loan.NeedsAllPayments.of_paid (Loan.manageDefault_paid _ _ _ h)

/-- Every reachable loan needs every payment it has left. -/
lemma Loan.Reachable.needsAllPayments {loan : Loan} {t : UInt32} (hr : loan.Reachable t) :
    loan.NeedsAllPayments := by
  obtain ⟨start, t₀, hc, hr'⟩ := hr
  exact hr'.needsAllPayments hc

end XRPL.Model.Lending
