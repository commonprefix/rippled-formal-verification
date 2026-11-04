import XRPL.Properties.Lending.Loan.Common.CreatedSize
import XRPL.Properties.Lending.Loan.Common.Outstanding
import XRPL.Properties.Lending.Loan.Common.RoundToNearest
import XRPL.Properties.Lending.Loan.Common.InterestDue
import XRPL.Properties.Lending.Loan.Common.Schedule

/-! # The room a reachable loan keeps for a payoff

With two or more payments left, the payments left times PeriodicPayment stay at most twice what the loan owed when
created, and the next due date stays at most one PaymentInterval after the last payment. -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault (Vault RawVault)

open private Loan.doPayment UnsettledPayment.payInstalments UnsettledPayment.applyOverpayment Loan.tryOverpayment
  Loan.settlePayment Loan.unimpairIfImpaired Loan.payScheduledInstalments from XRPL.Model.Lending.Loan.LoanPay
open private Loan.changeImpairment from XRPL.Model.Lending.Loan.LoanManage
open private LoanState.build_fields from XRPL.Properties.Lending.Loan.Common.PayMonotone

/-- Rounding up at a scale never lowers a value at least zero, unless it lands on zero. -/
lemma STAmount.roundToNumericType_upward_ge (nt : NumericType) (x T : Number) (s : ℤ) (hx : x.isNormalized)
    (h0 : 0 ≤ x.toRat) (hs : -81 ≤ s ∧ s ≤ 80) (hT : T.toRat ≠ 0)
    (hok : STAmount.roundToNumericType nt x .upward (some s) = .ok T) : x.toRat ≤ T.toRat := by
  cases hnt : nt with
  | fractional =>
    rw [hnt] at hok
    exact STAmount.roundToNumericType_frac_upward_ge x T s hx h0 hs hT hok
  | integral mv mo ms msh =>
    rw [hnt] at hok
    exact (STAmount.roundToNumericType_int_grid _ rfl x T .upward _ hx h0 (Or.inr (Or.inl rfl)) hok).2.2.1 rfl

/-- Guards that pass leave `n` periodic payments at most twice TotalValueOutstanding, for `n` at least two. -/
lemma LoanProperties.amortizationGuards_periodic (props : LoanProperties) (principal : Number) (expect : Bool)
    (n : UInt32) (nt : NumericType) (hn : 2 ≤ n.toNat)
    (h : props.amortizationGuards principal expect n nt = .ok .tesSUCCESS)
    (htv : props.totalValueOutstanding.isNormalized) (hpp : props.periodicPayment.isNormalized)
    (hpp0 : 0 ≤ props.periodicPayment.toRat) (hs : -81 ≤ props.loanScale ∧ props.loanScale ≤ 80) :
    (n.toNat : ℚ) * props.periodicPayment.toRat ≤ 2 * props.totalValueOutstanding.toRat := by
  have hn0 : n ≠ 0 := fun h0 => by rw [h0] at hn; simp at hn
  obtain ⟨rp, hrp, hrp0, hroom⟩ :=
    LoanProperties.amortizationGuards_room props principal expect n nt hn0 h htv hpp hpp0 hs
  have hle := STAmount.roundToNumericType_upward_ge nt _ rp _ hpp hpp0 hs (ne_of_gt hrp0) hrp
  have hn2 : (2 : ℚ) ≤ n.toNat := by exact_mod_cast hn
  calc (n.toNat : ℚ) * props.periodicPayment.toRat ≤ 2 * ((n.toNat : ℚ) - 1) * props.periodicPayment.toRat := by
        nlinarith
    _ ≤ 2 * ((n.toNat : ℚ) - 1) * rp.toRat := by gcongr; linarith
    _ = 2 * (((n.toNat : ℚ) - 1) * rp.toRat) := by ring
    _ ≤ 2 * props.totalValueOutstanding.toRat := by linarith

/-- A re-amortization that passes leaves `n` new periodic payments at most twice the new TotalValueOutstanding,
for `n` at least two. -/
private lemma Loan.tryOverpayment_periodic (l : Loan) (opc : PaymentComponents) (re : Reamortization)
    (h : Loan.tryOverpayment l opc = .ok (some re)) (hs : -81 ≤ l.loanScale ∧ l.loanScale ≤ 80)
    (hn : 2 ≤ l.paymentRemaining.toNat) (hppN : re.periodicPayment.isNormalized)
    (htvN : re.state.valueOutstanding.isNormalized) :
    (l.paymentRemaining.toNat : ℚ) * re.periodicPayment.toRat ≤ 2 * re.state.valueOutstanding.toRat := by
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
  have key := LoanProperties.amortizationGuards_periodic _ _ _ _ _ hn hg htvN hppN hpp0.le hs
  dsimp only at key
  exact key

/-- The room a loan keeps for a payoff, against `T0`: with two or more payments left, the payments left times
PeriodicPayment are at most `2·T0`, and the next due date is at most one PaymentInterval after the last payment. -/
structure Loan.PaymentRoom (T0 : ℚ) (loan : Loan) : Prop where
  periodic : 2 ≤ loan.paymentRemaining.toNat →
    (loan.paymentRemaining.toNat : ℚ) * loan.periodicPayment.toRat ≤ 2 * T0
  lastDue : loan.paymentRemaining ≠ 0 → loan.nextPaymentDueDate.toNat ≤
    (if loan.previousPaymentDueDate < loan.schedule.startDate then loan.schedule.startDate
      else loan.previousPaymentDueDate).toNat + loan.schedule.paymentInterval.toNat

/-- A loan with the same count, PeriodicPayment, due dates and schedule keeps the room. -/
lemma Loan.PaymentRoom.of_same {T0 : ℚ} {l l' : Loan} (h : l.PaymentRoom T0)
    (h1 : l'.paymentRemaining = l.paymentRemaining) (h2 : l'.periodicPayment = l.periodicPayment)
    (h3 : l'.previousPaymentDueDate = l.previousPaymentDueDate)
    (h4 : l'.nextPaymentDueDate = l.nextPaymentDueDate) (h5 : l'.schedule = l.schedule) : l'.PaymentRoom T0 :=
  ⟨by rw [h1, h2]; exact h.periodic, by rw [h1, h3, h4, h5]; exact h.lastDue⟩

/-- A loan rebuilt with the same count, PeriodicPayment, due dates and schedule keeps the room. -/
lemma Loan.PaymentRoom.of_raw {T0 : ℚ} {l l' : Loan} {raw : RawLoan} (h : l.PaymentRoom T0)
    (hl : raw.to_lawful = .ok l') (h1 : raw.paymentRemaining = l.paymentRemaining)
    (h2 : raw.periodicPayment = l.periodicPayment) (h3 : raw.previousPaymentDueDate = l.previousPaymentDueDate)
    (h4 : raw.nextPaymentDueDate = l.nextPaymentDueDate) (h5 : raw.schedule = l.schedule) : l'.PaymentRoom T0 := by
  have hr := (RawLoan.to_lawful_ok hl).1
  exact h.of_same (by rw [← h1, ← hr]) (by rw [← h2, ← hr]) (by rw [← h3, ← hr])
    (by rw [← h4, ← hr]) (by rw [← h5, ← hr])

/-- A loan with no payments left has the room. -/
lemma Loan.PaymentRoom.of_paid {T0 : ℚ} {l : Loan} (h : l.paymentRemaining = 0) : l.PaymentRoom T0 :=
  ⟨fun h2 => by rw [h] at h2; simp at h2, fun h0 => absurd h h0⟩

/-- One instalment keeps the room. The last one leaves no payments, any other takes one payment and makes
the old due date the last payment. -/
private lemma Loan.doPayment_room {T0 : ℚ} (l l' : Loan) (pc : PaymentComponents) (hroom : l.PaymentRoom T0)
    (hl0 : l.paymentRemaining ≠ 0) (h : Loan.doPayment l pc = .ok l') : l'.PaymentRoom T0 := by
  unfold Loan.doPayment at h
  dsimp only at h
  split at h
  · obtain ⟨l1, hl, h⟩ := bind_ok_peel _ _ _ h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    obtain ⟨he, -, -⟩ := RawLoan.to_lawful_ok hl
    exact Loan.PaymentRoom.of_paid (by rw [show l1.paymentRemaining = l1.toRawLoan.paymentRemaining from rfl, he])
  · obtain ⟨_, -, h⟩ := bind_ok_peel _ _ _ h
    obtain ⟨_, -, h⟩ := bind_ok_peel _ _ _ h
    obtain ⟨_, -, h⟩ := bind_ok_peel _ _ _ h
    obtain ⟨_, -, h⟩ := bind_ok_peel _ _ _ h
    obtain ⟨he, -, -⟩ := RawLoan.to_lawful_ok h
    have hn : l'.paymentRemaining = l.paymentRemaining - 1 := by
      rw [show l'.paymentRemaining = l'.toRawLoan.paymentRemaining from rfl, he]
    have hpp : l'.periodicPayment = l.periodicPayment := by
      rw [show l'.periodicPayment = l'.toRawLoan.periodicPayment from rfl, he]
    have hprev : l'.previousPaymentDueDate = l.nextPaymentDueDate := by
      rw [show l'.previousPaymentDueDate = l'.toRawLoan.previousPaymentDueDate from rfl, he]
    have hnext : l'.nextPaymentDueDate = l.nextPaymentDueDate + l.schedule.paymentInterval := by
      rw [show l'.nextPaymentDueDate = l'.toRawLoan.nextPaymentDueDate from rfl, he]
    have hsch : l'.schedule = l.schedule := by
      rw [show l'.schedule = l'.toRawLoan.schedule from rfl, he]
    refine ⟨fun h2 => ?_, fun _ => ?_⟩
    · -- one payment fewer at the same PeriodicPayment
      have hsub : (l.paymentRemaining - 1).toNat = l.paymentRemaining.toNat - 1 := by
        rw [UInt32.toNat_sub_of_le _ _ (by
          rw [UInt32.le_iff_toNat_le]
          have : l.paymentRemaining.toNat ≠ 0 := fun h0 => hl0 (UInt32.toNat_inj.mp (by simpa using h0))
          simp; omega)]
        simp
      rw [hn, hsub] at h2 ⊢
      rw [hpp]
      have h3 : 2 ≤ l.paymentRemaining.toNat := by omega
      have := hroom.periodic h3
      have hpp0 : 0 ≤ l.periodicPayment.toRat := l.exact.periodicPayment_pos.le
      have hcast : ((l.paymentRemaining.toNat - 1 : ℕ) : ℚ) ≤ l.paymentRemaining.toNat := by
        exact_mod_cast Nat.sub_le _ _
      nlinarith
    · -- the old due date is the last payment
      rw [hnext, hprev, hsch, UInt32.toNat_add]
      have hmod := Nat.mod_le (l.nextPaymentDueDate.toNat + l.schedule.paymentInterval.toNat) (2 ^ 32)
      have hge : l.nextPaymentDueDate.toNat ≤
          (if l.nextPaymentDueDate < l.schedule.startDate then l.schedule.startDate
            else l.nextPaymentDueDate).toNat := by
        split
        · rename_i hlt; exact le_of_lt (UInt32.lt_iff_toNat_lt.mp hlt)
        · exact le_rfl
      omega

/-- The instalment loop keeps the room. -/
private lemma UnsettledPayment.payInstalments_room {α : Type} {T0 : ℚ} (amount : Number) :
    ∀ (n : Nat) (payment p' : UnsettledPayment α), payment.loan.PaymentRoom T0 →
      UnsettledPayment.payInstalments payment n amount = .ok p' → p'.loan.PaymentRoom T0 := by
  intro n
  induction n with
  | zero =>
    intro payment p' hroom h
    rw [UnsettledPayment.payInstalments] at h
    obtain rfl := Except.ok.inj h
    exact hroom
  | succ n ih =>
    intro payment p' hroom h
    rw [UnsettledPayment.payInstalments] at h
    unfold_ter at h
    walk_ok
    · exact hroom
    · exact hroom
    all_goals
      have hl0 : payment.loan.paymentRemaining ≠ 0 := by
        have := ‹¬(payment.loan.paymentRemaining == 0) = true›
        simpa using this
      have hstep := Loan.doPayment_room _ _ _ hroom hl0 ‹Loan.doPayment _ _ = _›
    · exact hstep
    · exact ih _ p' hstep ‹UnsettledPayment.payInstalments _ n amount = _›

/-- The overpayment tail keeps the room, while the loan it leaves owes at most `T0`. The re-amortization passes
the amortization guards on its new PeriodicPayment and TotalValueOutstanding. -/
private lemma UnsettledPayment.applyOverpayment_room {T0 : ℚ} (payment p' : UnsettledPayment Vault)
    (amount : Number) (hroom : payment.loan.PaymentRoom T0)
    (hs : -81 ≤ payment.loan.loanScale ∧ payment.loan.loanScale ≤ 80)
    (hT : p'.loan.totalValueOutstanding.toRat ≤ T0)
    (h : UnsettledPayment.applyOverpayment payment amount = .ok p') : p'.loan.PaymentRoom T0 := by
  unfold UnsettledPayment.applyOverpayment at h
  unfold_ter at h
  walk_ok
  all_goals first
    | exact hroom
    | skip
  rename_i re hre _ _ _ _ loan' hl
  obtain ⟨he, -, -⟩ := RawLoan.to_lawful_ok hl
  have hn : loan'.paymentRemaining = payment.loan.paymentRemaining := by
    rw [show loan'.paymentRemaining = loan'.toRawLoan.paymentRemaining from rfl, he]
  have hpp : loan'.periodicPayment = re.periodicPayment := by
    rw [show loan'.periodicPayment = loan'.toRawLoan.periodicPayment from rfl, he]
  have htv : loan'.totalValueOutstanding = re.state.valueOutstanding := by
    rw [show loan'.totalValueOutstanding = loan'.toRawLoan.totalValueOutstanding from rfl, he]
  have hprev : loan'.previousPaymentDueDate = payment.loan.previousPaymentDueDate := by
    rw [show loan'.previousPaymentDueDate = loan'.toRawLoan.previousPaymentDueDate from rfl, he]
  have hnext : loan'.nextPaymentDueDate = payment.loan.nextPaymentDueDate := by
    rw [show loan'.nextPaymentDueDate = loan'.toRawLoan.nextPaymentDueDate from rfl, he]
  have hsch : loan'.schedule = payment.loan.schedule := by
    rw [show loan'.schedule = loan'.toRawLoan.schedule from rfl, he]
  refine ⟨fun h2 => ?_, by rw [hn, hprev, hnext, hsch]; exact hroom.lastDue⟩
  rw [hn] at h2 ⊢
  have key := Loan.tryOverpayment_periodic _ _ _ hre hs h2 (by rw [← hpp]; exact loan'.wf.periodicPayment_norm)
    (by rw [← htv]; exact loan'.wf.totalValueOutstanding_norm)
  rw [hpp]
  have hT' : loan'.totalValueOutstanding.toRat ≤ T0 := hT
  rw [htv] at hT'
  linarith

/-- A payment of any type keeps the room, for a loan at a LoanScale in range that owes at most `T0`. -/
lemma Loan.pay_room {T0 : ℚ} (loan : Loan) (v : Vault) (pt : LoanPaymentType) (amount : Number) (now : UInt32)
    (r : LoanWithAmounts Vault) (hroom : loan.PaymentRoom T0) (hs : -81 ≤ loan.loanScale ∧ loan.loanScale ≤ 80)
    (hT : loan.totalValueOutstanding.toRat ≤ T0) (h : (loan.pay v pt amount now).run = .ok (.ok r)) :
    r.loan'.PaymentRoom T0 := by
  obtain ⟨p, hp, hsettle⟩ := Loan.pay_ok loan v pt amount now r h
  obtain ⟨_, _, _, _, _, _, _, -, -, -, -, hloan, -, -⟩ := UnsettledPayment.settle_ok p r hsettle
  suffices hp' : p.loan.PaymentRoom T0 from hp'.of_raw hloan rfl rfl rfl rfl rfl
  have hu : loan.unimpaired.PaymentRoom T0 := hroom.of_same rfl rfl rfl rfl rfl
  have hl0 : loan.paymentRemaining ≠ 0 := (Loan.payInstalments_ok loan v pt amount now p hp).1.remaining
  cases pt
  · obtain ⟨si, -, hloop, -⟩ := Loan.payScheduled_loop loan v amount now p hp
    exact UnsettledPayment.payInstalments_room amount _ _ p hu hloop
  · obtain ⟨pc, -, -, hdo⟩ := Loan.latePayInstalments_ok loan v amount now p hp
    exact Loan.doPayment_room _ _ _ hu hl0 hdo
  · obtain ⟨pc, -, -, hdo⟩ := Loan.fullPayInstalments_ok loan v amount now p hp
    exact Loan.doPayment_room _ _ _ hu hl0 hdo
  · obtain ⟨p0, h0, h1⟩ := Loan.overPayInstalments_ok loan v amount now p hp
    obtain ⟨si, -, hloop, -⟩ := Loan.payScheduled_loop loan v amount now p0 h0
    have hr0 := UnsettledPayment.payInstalments_room amount _ _ p0 hu hloop
    obtain ⟨-, -, hst, -, -⟩ := Loan.payInstalments_ok loan v .regular amount now p0 h0
    have hT' : p.loan.totalValueOutstanding.toRat ≤ T0 := by
      have h1 := (Loan.pay_outstanding_le loan v .overpayment amount now r h).2.1
      have hrt : r.loan'.totalValueOutstanding = p.loan.totalValueOutstanding :=
        (congrArg RawLoan.totalValueOutstanding (RawLoan.to_lawful_ok hloan).1 :)
      rw [hrt] at h1
      linarith
    exact UnsettledPayment.applyOverpayment_room p0 p amount hr0 (by rw [hst.loanScale]; exact hs) hT' h1

/-- An accept keeps the room. -/
private lemma Loan.accept_room {T0 : ℚ} (loan : Loan) (v : Vault) (r : LoanWithPool Vault)
    (hroom : loan.PaymentRoom T0) (h : (loan.accept v).run = .ok (.ok r)) : r.loan'.PaymentRoom T0 := by
  simp only [Loan.accept] at h
  unfold_ter at h
  walk_ok
  have hl := ‹RawLoan.to_lawful _ = Except.ok _›
  exact hroom.of_raw hl rfl rfl rfl rfl rfl

/-- Changing the impairment keeps the room. -/
private lemma Loan.changeImpairment_room {T0 : ℚ} (loan : Loan) (v : Vault) (b : Bool) (r : LoanWithPool Vault)
    (hroom : loan.PaymentRoom T0) (h : (Loan.changeImpairment loan v b).run = .ok (.ok r)) :
    r.loan'.PaymentRoom T0 := by
  simp only [Loan.changeImpairment] at h
  unfold_ter at h
  walk_ok
  all_goals
    have hl := ‹RawLoan.to_lawful _ = Except.ok _›
    exact hroom.of_raw hl rfl rfl rfl rfl rfl

/-- An impair keeps the room. -/
private lemma Loan.manageImpair_room {T0 : ℚ} (loan : Loan) (v : Vault) (now : UInt32) (r : LoanWithPool Vault)
    (hroom : loan.PaymentRoom T0) (h : (loan.manageImpair v now).run = .ok (.ok r)) : r.loan'.PaymentRoom T0 := by
  simp only [Loan.manageImpair] at h
  unfold_ter at h
  walk_ok
  exact Loan.changeImpairment_room loan v true r hroom ‹_›

/-- A loan a LoanSet creates has the room against its own TotalValueOutstanding. -/
lemma Loan.Created.paymentRoom {start : Loan} {t₀ : UInt32} (h : Loan.Created start t₀) :
    start.PaymentRoom start.totalValueOutstanding.toRat := by
  obtain ⟨broker, v, principal, rates, fees, pi, pt, gp, sd, twoStep, allowsOverpayment, r, -, hok, rfl⟩ := h
  obtain ⟨props, _, _, _, broker', _, _, _, _, _, hchecks, -, -, -, hl, -⟩ :=
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
  have hprev : r.loan'.previousPaymentDueDate = 0 := by
    show r.loan'.toRawLoan.previousPaymentDueDate = _; rw [hl]; rfl
  have hnext : r.loan'.nextPaymentDueDate = r.loan'.schedule.startDate + r.loan'.schedule.paymentInterval := by
    show r.loan'.toRawLoan.nextPaymentDueDate = r.loan'.toRawLoan.schedule.startDate + _; rw [hl]; rfl
  have hrange := hexg.loanScale_range
  simp only [RawLoan.toExact] at hrange
  rw [hLS] at hrange
  obtain ⟨hlo, hhi, -⟩ := Loan.create_loanScale_range broker v principal rates fees _ props _ _ hchecks hrange.2
  have hpp0 : 0 < props.periodicPayment.toRat := by
    have := r.loan'.exact.periodicPayment_pos; simp only [RawLoan.toExact] at this; rwa [hPP] at this
  refine ⟨fun h2 => ?_, fun _ => ?_⟩
  · rw [hN] at h2 ⊢
    rw [hPP, hTV]
    exact LoanProperties.amortizationGuards_periodic _ _ _ _ _ h2
      (LoanProperties.checkGuards_amortization _ _ _ _ _ hchecks.guards) (hTV ▸ hwf.totalValueOutstanding_norm)
      (hPP ▸ hwf.periodicPayment_norm) hpp0.le ⟨by omega, hhi⟩
  · rw [hprev, hnext, UInt32.toNat_add]
    have hmod := Nat.mod_le (r.loan'.schedule.startDate.toNat + r.loan'.schedule.paymentInterval.toNat) (2 ^ 32)
    have hge : r.loan'.schedule.startDate.toNat ≤
        (if (0 : UInt32) < r.loan'.schedule.startDate then r.loan'.schedule.startDate else 0).toNat := by
      split
      · exact le_rfl
      · rename_i hz
        rw [UInt32.lt_iff_toNat_lt] at hz
        simp only [UInt32.toNat_zero] at hz ⊢
        omega
    omega

/-- Every loan reachable from a LoanSet keeps the room against what it was created owing. -/
lemma Loan.ReachableFrom.paymentRoom {start : Loan} {t₀ : UInt32} {loan : Loan} {t : UInt32}
    (hc : Loan.Created start t₀) (hr : Loan.ReachableFrom start t₀ loan t) :
    loan.PaymentRoom start.totalValueOutstanding.toRat := by
  have hlo := Loan.Created.loanScale_ge hc
  have hhi : start.loanScale ≤ 80 := by
    have := start.wf.loanScale_range.2; unfold cMaxOffset at this; exact this
  have hpay : ∀ {l : Loan} {t' : UInt32}, Loan.ReachableFrom start t₀ l t' →
      l.PaymentRoom start.totalValueOutstanding.toRat → ∀ (v : Vault) (pt : LoanPaymentType) (amount : Number)
      (now : UInt32) (r : LoanWithAmounts Vault), (l.pay v pt amount now).run = .ok (.ok r) →
      r.loan'.PaymentRoom start.totalValueOutstanding.toRat := by
    intro l t' hr' hroom v pt amount now r h
    have hT := (Loan.ReachableFrom.outstanding_monotone_proof hr').totalValueOutstanding
    have hls := (Loan.ReachableFrom.fixed_terms_proof _ _ _ _ hr').2.2.2.2.2.2.1
    exact Loan.pay_room l v pt amount now r hroom (by rw [hls]; exact ⟨by omega, hhi⟩) hT h
  induction hr with
  | refl => exact Loan.Created.paymentRoom hc
  | refresh _ _ _ _ _ _ h ih => exact ih.of_raw h rfl rfl rfl rfl rfl
  | accept _ _ _ _ _ _ _ _ h ih => exact Loan.accept_room _ _ _ ih h
  | regularPayment _ _ _ _ _ _ hr' _ _ h ih => exact hpay hr' ih _ .regular _ _ _ h
  | latePayment _ _ _ _ _ _ hr' _ _ h ih => exact hpay hr' ih _ .late _ _ _ h
  | fullPayment _ _ _ _ _ _ hr' _ _ h ih => exact hpay hr' ih _ .full _ _ _ h
  | overpayment _ _ _ _ _ _ hr' _ _ h ih => exact hpay hr' ih _ .overpayment _ _ _ h
  | impair _ _ _ _ _ _ _ _ h ih => exact Loan.manageImpair_room _ _ _ _ ih h
  | unimpair _ _ _ _ _ _ _ _ h ih => exact Loan.changeImpairment_room _ _ false _ ih h
  | default _ _ _ _ _ _ _ _ h ih => exact Loan.PaymentRoom.of_paid (Loan.manageDefault_paid _ _ _ h)

/-- A reachable loan owes at most `10^16 + 1` LoanScale units. -/
lemma Loan.Reachable.totalValue_le {loan : Loan} {t : UInt32} (hr : loan.Reachable t) :
    loan.totalValueOutstanding.toRat ≤ (10 ^ 16 + 1) * 10 ^ loan.loanScale := by
  obtain ⟨start, t₀, hc, hr⟩ := hr
  have hT := (Loan.ReachableFrom.outstanding_monotone_proof hr).totalValueOutstanding
  have hls := (Loan.ReachableFrom.fixed_terms_proof _ _ _ _ hr).2.2.2.2.2.2.1
  rw [hls]
  exact le_trans hT (Loan.Created.totalValue_le hc)

/-- A reachable loan owes less than `9·10^15 + 1` LoanScale units of principal. PrincipalOutstanding never
rises above PrincipalRequested. -/
lemma Loan.Reachable.principal_lt {loan : Loan} {t : UInt32} (hr : loan.Reachable t) :
    loan.principalOutstanding.toRat < (9 * 10 ^ 15 + 1) * 10 ^ loan.loanScale := by
  obtain ⟨start, t₀, hc, hr⟩ := hr
  have hP := (Loan.ReachableFrom.outstanding_monotone_proof hr).principalOutstanding
  have hls := (Loan.ReachableFrom.fixed_terms_proof _ _ _ _ hr).2.2.2.2.2.2.1
  rw [hls]
  exact lt_of_le_of_lt hP (Loan.Created.principal_lt hc)

/-- A reachable loan keeps the room against `10^16 + 1` LoanScale units. -/
lemma Loan.Reachable.paymentRoom {loan : Loan} {t : UInt32} (hr : loan.Reachable t) :
    loan.PaymentRoom ((10 ^ 16 + 1) * 10 ^ loan.loanScale) := by
  obtain ⟨start, t₀, hc, hr'⟩ := hr
  have h := hr'.paymentRoom hc
  have hls := (Loan.ReachableFrom.fixed_terms_proof _ _ _ _ hr').2.2.2.2.2.2.1
  have hT := Loan.Created.totalValue_le hc
  rw [← hls] at hT
  exact ⟨fun h2 => le_trans (h.periodic h2) (by linarith), h.lastDue⟩

end XRPL.Model.Lending
