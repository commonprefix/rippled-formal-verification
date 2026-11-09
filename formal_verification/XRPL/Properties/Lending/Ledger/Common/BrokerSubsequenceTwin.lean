import XRPL.Properties.Lending.Ledger.Common.BrokerSubsequenceDefs
import XRPL.Properties.Lending.Ledger.Common.LoanSubsequenceTwin
import XRPL.Properties.Lending.Ledger.Common.DefaultOrder

/-! # One broker in a sequence and in its subsequence

What a transaction on another broker or its loans keeps: broker `k` and its loans. A transaction on broker `k` or on
one of its loans, run on two copies of the broker that differ only in CoverAvailable, leaves two such copies. The
covers stay equal while they were equal and, for a default, neither vault is coarsened. -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault (Vault)

open private LendingLedger.applyBroker_index LendingLedger.applyLoan_effect
  from XRPL.Properties.Lending.Ledger.Common.Isolation
open private LendingLedger.apply_other LendingLedger.apply_brokers
  from XRPL.Properties.Lending.Ledger.Common.BrokerAccounting
open private LendingLedger.default_at_base Loan.manageDefault_broker_record
  from XRPL.Properties.Lending.Ledger.Common.DefaultOrder
open private LendingLedger.loanAt_twin from XRPL.Properties.Lending.Ledger.Common.LoanSubsequenceTwin

/-- Brokers with the same fields are the same broker. -/
private lemma LoanBroker.eq_of_raw {b b' : LoanBroker} (h : b'.toRawLoanBroker = b.toRawLoanBroker) : b' = b := by
  obtain ⟨rb', wf', valid'⟩ := b'
  obtain ⟨rb, wf, valid⟩ := b
  simp only at h
  subst h
  rfl

/-- Two copies of a broker that differ at most in CoverAvailable are equal when their covers have the same value. -/
private lemma LoanBroker.raw_eq_of_cover {b b' : LoanBroker}
    (h : b'.toRawLoanBroker = { b.toRawLoanBroker with coverAvailable := b'.coverAvailable })
    (hc : b'.coverAvailable.toRat = b.coverAvailable.toRat) : b'.toRawLoanBroker = b.toRawLoanBroker := by
  have hcv : b'.coverAvailable = b.coverAvailable :=
    Number.isNormalized.toRat_inj b'.wf.coverAvailable_norm b.wf.coverAvailable_norm hc
  rw [h, hcv]

/-- A loan transaction acts on the broker of its loan, or of its LoanSet. -/
private lemma LendingLedger.txBroker?_of_isLoan (l : LendingLedger) {tx : LendingTx} (hl : tx.isLoan = true) :
    l.txBroker? tx = l.loanTxBroker? tx := by
  cases tx <;> simp_all [LendingTx.isLoan, LendingLedger.txBroker?]

/-- A loan transaction stores its loan under the broker it acts on. -/
private lemma LendingLedger.applyLoan_entry {l : LendingLedger} {tx : LendingTx} {u : LoanEffect}
    (hu : (l.applyLoan tx).run = .ok (.ok u)) : ∀ e, u.loan = some e → e.brokerIndex = u.brokerIndex := by
  cases tx with
  | loanSet i principal rates fees pi pt gp sd twoStep ao =>
    simp only [LendingLedger.applyLoan] at hu
    obtain ⟨broker, r, -, -, -, rfl⟩ := l.applyLoanSet_inv _ _ _ _ _ _ _ _ hu
    intro e he
    simp only [LoanEffect.ofCreate, Option.some.injEq] at he
    subst he
    rfl
  | loanAccept i =>
    obtain ⟨e0, -, -, -, -, -, -, -, -, rfl⟩ := l.applyLoan_accept_inv u i hu
    intro e he
    simp only [LoanEffect.ofLoan, Option.some.injEq] at he
    subst he
    rfl
  | loanDelete i =>
    obtain ⟨e0, -, -, -, -, -, -, -, -, rfl⟩ := l.applyLoan_delete_inv u i hu
    intro e he
    cases he
  | loanManage i action =>
    obtain ⟨e0, -, -, -, -, -, -, -, -, rfl⟩ := l.applyLoan_manage_inv u i action hu
    intro e he
    simp only [LoanEffect.ofLoan, Option.some.injEq] at he
    subst he
    rfl
  | loanPay i pt amount =>
    obtain ⟨e0, -, -, -, -, -, -, -, -, rfl⟩ := l.applyLoan_pay_inv u i pt amount hu
    intro e he
    simp only [LoanEffect.ofLoan, Option.some.injEq] at he
    subst he
    rfl
  | _ => simp only [LendingLedger.applyLoan] at hu; cases hu

/-- A broker transaction writes an old slot or the next free one. -/
private lemma LendingLedger.applyBroker_slot {l : LendingLedger} {tx : LendingTx} {u : BrokerEffect}
    (hu : (l.applyBroker tx).run = .ok (.ok u)) : u.index ≤ l.brokers.length := by
  rcases LendingLedger.applyBroker_cases l tx u hu with ⟨hi, -⟩ | ⟨b, -, hb, -⟩ | ⟨b, hb, -⟩
  · omega
  · exact (LendingLedger.broker?_lt hb).le
  · exact (LendingLedger.broker?_lt hb).le

/-- A transaction that does not act on broker `k` keeps its slot, and keeps it free while it is past the end. -/
private lemma LendingLedger.apply_keeps_broker {l l₂ : LendingLedger} {tx : LendingTx} {k : Nat}
    (h : (l.apply tx).run = .ok (.ok l₂)) (hk : l.txBroker? tx ≠ some k) :
    l₂.broker? k = l.broker? k ∧ (l.brokers.length ≤ k → l₂.brokers.length ≤ k) := by
  by_cases hb : tx.isBroker = true
  · obtain ⟨u, hu, rfl⟩ := LendingLedger.apply_broker hb h
    have hidx := LendingLedger.applyBroker_index hu
    have hne : u.index ≠ k := fun h0 => hk (by rw [hidx, h0])
    have hle := LendingLedger.applyBroker_slot hu
    refine ⟨?_, fun hlk => ?_⟩
    · rw [LendingLedger.broker?_commitBroker, if_neg]
      split <;> omega
    · show (storeSlot l.brokers u.index u.broker).length ≤ k
      unfold storeSlot
      split
      · simpa using hlk
      · simp only [List.length_append, List.length_singleton]
        omega
  by_cases hl : tx.isLoan = true
  · obtain ⟨u, hu, rfl⟩ := LendingLedger.apply_loan hl h
    obtain ⟨-, hbk, b0, hb0, -⟩ := LendingLedger.applyLoan_effect hu
    rw [LendingLedger.txBroker?_of_isLoan l hl, hbk] at hk
    have hne : k ≠ u.brokerIndex := fun h0 => hk (by rw [h0])
    refine ⟨by rw [LendingLedger.broker?_commitLoan l u b0 hb0, if_neg hne], fun hlk => ?_⟩
    simpa [LendingLedger.commitLoan] using hlk
  have hbr := LendingLedger.apply_brokers hb hl h
  refine ⟨by unfold LendingLedger.broker?; rw [hbr], fun hlk => by rw [hbr]; exact hlk⟩

/-- A transaction that does not act on broker `k` keeps its loans: a loan of `k` after it was stored before. -/
private lemma LendingLedger.apply_keeps_loans {l l₂ : LendingLedger} {tx : LendingTx} {k : Nat}
    (h : (l.apply tx).run = .ok (.ok l₂)) (hk : l.txBroker? tx ≠ some k) :
    ∀ i e, l₂.loan? i = some e → e.brokerIndex = k → l.loan? i = some e := by
  intro i e he hek
  by_cases hl : tx.isLoan = true
  · obtain ⟨u, hu, rfl⟩ := LendingLedger.apply_loan hl h
    obtain ⟨-, hbk, -⟩ := LendingLedger.applyLoan_effect hu
    rw [LendingLedger.txBroker?_of_isLoan l hl, hbk] at hk
    rw [LendingLedger.loan?_commitLoan] at he
    by_cases hi : i = (if u.loanIndex < l.loans.length then u.loanIndex else l.loans.length)
    · rw [if_pos hi] at he
      have := LendingLedger.applyLoan_entry hu e he
      exact absurd (by rw [← this, hek]) hk
    · rw [if_neg hi] at he
      exact he
  have hloans : l₂.loans = l.loans := by
    by_cases hv : tx.isVault = true
    · obtain ⟨u, -, rfl⟩ := LendingLedger.apply_vault hv h
      unfold LendingLedger.commitVault; split <;> simp [LendingLedger.setShares]
    by_cases hb : tx.isBroker = true
    · obtain ⟨u, -, rfl⟩ := LendingLedger.apply_broker hb h
      rfl
    exact (LendingLedger.apply_other hv hb hl h).2.2
  unfold LendingLedger.loan? at he ⊢
  rw [← hloans]
  exact he

/-- A release of a loan takes one off LoanCount and sets DebtTotal, to zero with the last loan. -/
private lemma LoanBroker.releaseLoan_raw {lb lb' : LoanBroker} {d : Number} (h : lb.releaseLoan d = .ok lb') :
    lb'.toRawLoanBroker = { lb.toRawLoanBroker with
      loanCount := lb.loanCount - 1, debtTotal := if lb.loanCount - 1 == 0 then Number.zero else d } := by
  unfold LoanBroker.releaseLoan at h
  simp only [bind, Except.bind] at h
  split at h
  · cases h
  rename_i _ hc
  obtain ⟨-, rfl⟩ := UInt32.subChecked_eq_ok.mp hc
  exact (RawLoanBroker.to_lawful_ok h).1

/-- A LoanDelete releases the loan from its broker: a pending loan with its principal off DebtTotal, a closed loan
with DebtTotal kept. -/
private lemma Loan.delete_broker_raw (loan : Loan) (v : Vault) (r : LoanBrokerWithPool Vault)
    (h : (loan.delete v).run = .ok (.ok r)) :
    ∃ d, (loan.isPending = true → loan.broker.debtTotal.operator_sub loan.principalOutstanding .to_nearest = .ok d) ∧
      (loan.isPending = false → d = loan.broker.debtTotal) ∧
      r.broker'.toRawLoanBroker = { loan.broker.toRawLoanBroker with
        loanCount := loan.broker.loanCount - 1
        debtTotal := if loan.broker.loanCount - 1 == 0 then Number.zero else d } := by
  cases hp : loan.isPending
  · exact ⟨loan.broker.debtTotal, (fun h0 => by cases h0), fun _ => rfl,
      LoanBroker.releaseLoan_raw (Loan.delete_active_ok_inv loan v r hp h).1⟩
  · obtain ⟨_, _, d, -, -, -, hd, hrel⟩ := Loan.delete_pending_ok_inv loan v r hp h
    exact ⟨d, fun _ => hd, (fun h0 => by cases h0), LoanBroker.releaseLoan_raw hrel⟩

/-- A new loan adds its principal to its broker's DebtTotal and one to LoanCount. -/
private lemma Loan.create_broker_raw (broker : LoanBroker) (v : Vault) (principal : Number) (rates : LoanRates)
    (fees : LoanFees) (schedule : LoanSchedule) (allowsOverpayment pending : Bool) (r : LoanWithDisbursement Vault)
    (h : (Loan.create broker v principal rates fees schedule allowsOverpayment pending).run = .ok (.ok r)) :
    ∃ d, broker.debtTotal.operator_add principal .to_nearest = .ok d ∧
      r.loan'.broker.toRawLoanBroker = { broker.toRawLoanBroker with
        debtTotal := d, loanCount := broker.loanCount + 1 } := by
  obtain ⟨_, _, d, b', hc, hl, hb'⟩ := Loan.create_loan_eq _ _ _ _ _ _ _ _ r h
  have hrb : r.loan'.broker = b' := by rw [show r.loan'.broker = r.loan'.toRawLoan.broker from rfl, hl]; rfl
  exact ⟨d, hc.debt, by rw [hrb, hb']⟩

/-- Twins paid the same way at the same close time leave brokers that differ at most in CoverAvailable, and that
have the same cover too when the twins read the same broker. -/
private lemma Loan.pay_broker_twin {loan loan' : Loan} (ht : Loan.Twin loan loan')
    (hbraw : loan'.broker.toRawLoanBroker =
      { loan.broker.toRawLoanBroker with coverAvailable := loan'.broker.coverAvailable })
    (v v' : Vault) (hbe : v'.baseExponent = v.baseExponent) (pt : LoanPaymentType) (amount : Number) (now : UInt32)
    {r r' : LoanWithAmounts Vault}
    (h : (loan.pay v pt amount now).run = .ok (.ok r)) (h' : (loan'.pay v' pt amount now).run = .ok (.ok r')) :
    r'.loan'.broker.toRawLoanBroker =
        { r.loan'.broker.toRawLoanBroker with coverAvailable := r'.loan'.broker.coverAvailable } ∧
      (loan'.broker = loan.broker → r'.loan'.broker.coverAvailable = r.loan'.broker.coverAvailable) := by
  obtain ⟨p, hp, hs⟩ := Loan.pay_ok loan v pt amount now r h
  obtain ⟨q, hq, hs'⟩ := Loan.pay_ok loan' v' pt amount now r' h'
  obtain ⟨-, hu, hst, -, -⟩ := Loan.payInstalments_ok loan v pt amount now p hp
  obtain ⟨-, hu', hst', -, -⟩ := Loan.payInstalments_ok loan' v' pt amount now q hq
  obtain ⟨q', hq', -, ha, -⟩ := Loan.payInstalments_twin ht v v' q.pool pt amount now p hu' hp
  rw [hq] at hq'
  obtain rfl : q = q' := by injection hq' with hq'; injection hq'
  obtain ⟨_, _, _, cv, dt, _, b1, hss, -, -, hb1, hl1, -, -⟩ := UnsettledPayment.settle_ok p r hs
  obtain ⟨_, _, _, cv', dt', _, b2, hss', -, -, hb2, hl2, -, -⟩ := UnsettledPayment.settle_ok q r' hs'
  have hrb : r.loan'.broker = b1 := (congrArg RawLoan.broker (RawLoan.to_lawful_ok hl1).1 :)
  have hrb' : r'.loan'.broker = b2 := (congrArg RawLoan.broker (RawLoan.to_lawful_ok hl2).1 :)
  have hpb : p.loan.broker = loan.broker := hst.broker
  have hqb : q.loan.broker = loan'.broker := hst'.broker
  have hpbe : p.pool.baseExponent = v.baseExponent := Loan.unimpairIfImpaired_baseExponent loan v p.pool _ hu
  have hqbe : q.pool.baseExponent = v'.baseExponent := Loan.unimpairIfImpaired_baseExponent loan' v' q.pool _ hu'
  have hdebt : loan'.broker.debtTotal = loan.broker.debtTotal := (congrArg RawLoanBroker.debtTotal hbraw :)
  have hd := hss.debt
  have hd' := hss'.debt
  rw [hpb] at hd
  rw [hqb, ha, hdebt, hd] at hd'
  obtain rfl : dt = dt' := Except.ok.inj hd'
  have hr1 := (RawLoanBroker.to_lawful_ok hb1).1
  have hr2 := (RawLoanBroker.to_lawful_ok hb2).1
  refine ⟨by rw [hrb, hrb', hr2, hr1, hpb, hqb, hbraw], fun hbb => ?_⟩
  rw [hrb, hrb', show b2.coverAvailable = b2.toRawLoanBroker.coverAvailable from rfl,
    show b1.coverAvailable = b1.toRawLoanBroker.coverAvailable from rfl, hr1, hr2]
  show cv' = cv
  have hfee := hss.fee
  have hfee' := hss'.fee
  rw [hpb, hpbe] at hfee
  rw [hqb, hbb, hqbe, hbe, ha] at hfee'
  rcases hfee with ⟨h1, -, rfl⟩ | ⟨h1, fc, hfc, hfb, hcv⟩ <;>
    rcases hfee' with ⟨h2, -, rfl⟩ | ⟨h2, fc', hfc', hfb', hcv'⟩
  · rfl
  · rw [h1] at h2; cases h2
  · rw [h1] at h2; cases h2
  · rw [hfc] at hfc'
    obtain rfl := Except.ok.inj hfc'
    rw [hfb] at hfb'
    obtain rfl := Except.ok.inj hfb'
    rw [hcv] at hcv'
    exact (Except.ok.inj hcv').symm

/-- Two broker records that differ at most in CoverAvailable stay so when both get the same DebtTotal and LoanCount,
whatever covers they get. -/
private lemma RawLoanBroker.update_twin {b b' x x' : RawLoanBroker} {d c c' : Number} {n n' : UInt32}
    (hb : b' = { b with coverAvailable := b'.coverAvailable }) (hn : n' = n)
    (hx : x = { b with debtTotal := d, loanCount := n, coverAvailable := c })
    (hx' : x' = { b' with debtTotal := d, loanCount := n', coverAvailable := c' }) :
    x' = { x with coverAvailable := x'.coverAvailable } := by
  subst hx hx' hn
  rw [hb]

/-- The loan read at `j` carries the broker stored in its broker slot. -/
private lemma LendingLedger.LoanAt.broker_eq {l : LendingLedger} {j : Nat} {e : LoanEntry} {b : LoanBroker}
    {loan : Loan} (hat : l.LoanAt j loan) (he : l.loan? j = some e) (hb : l.broker? e.brokerIndex = some b) :
    loan.broker = b := by
  obtain ⟨e1, b1, he1, hb1, hw⟩ := hat
  rw [he] at he1
  obtain rfl := Option.some.inj he1
  rw [hb] at hb1
  obtain rfl := Option.some.inj hb1
  rw [show loan.broker = loan.toRawLoan.broker from rfl, Loan.withBroker_eq hw]

/-- A LoanAccept, LoanDelete, LoanManage or LoanPay that succeeds on twins of a loan, read with two copies of their
broker that differ at most in CoverAvailable, leaves two such copies. -/
private lemma LendingLedger.loanTx_broker_twin {l L l₂ L₂ : LendingLedger} (hr : l.Reachable) (hR : L.Reachable)
    {j j' : Nat} {e e' : LoanEntry} (he : l.loan? j = some e) (he' : L.loan? j' = some e')
    (hraw : e'.loan.toRawLoan = { e.loan.toRawLoan with broker := e'.loan.toRawLoan.broker })
    (hnow : L.now = l.now) (hnt : L.vault.numericType = l.vault.numericType)
    (hscale : L.vault.scale = l.vault.scale)
    {b b' : LoanBroker} (hb : l.broker? e.brokerIndex = some b) (hb' : L.broker? e'.brokerIndex = some b')
    (hbraw : b'.toRawLoanBroker = { b.toRawLoanBroker with coverAvailable := b'.coverAvailable })
    (tx : LendingTx) (htx : tx.loanIndex? = some j)
    (hok : (l.apply tx).run = .ok (.ok l₂)) (hok' : (L.apply (tx.withLoan j')).run = .ok (.ok L₂)) :
    ∃ c c', l₂.broker? e.brokerIndex = some c ∧ L₂.broker? e'.brokerIndex = some c' ∧
      c'.toRawLoanBroker = { c.toRawLoanBroker with coverAvailable := c'.coverAvailable } ∧
      (b'.coverAvailable = b.coverAvailable → l.NotCoarsened → L.NotCoarsened →
        c'.coverAvailable = c.coverAvailable) := by
  have hfee : ∀ b0 b0', l.broker? e.brokerIndex = some b0 → L.broker? e'.brokerIndex = some b0' →
      b0'.managementFeeRate = b0.managementFeeRate := by
    intro b0 b0' h0 h0'
    rw [hb] at h0
    rw [hb'] at h0'
    obtain rfl := Option.some.inj h0
    obtain rfl := Option.some.inj h0'
    exact (congrArg RawLoanBroker.managementFeeRate hbraw :)
  have htwin : ∀ loan loan', l.LoanAt j loan → L.LoanAt j' loan' → Loan.Twin loan loan' :=
    fun _ _ hat hat' => LendingLedger.loanAt_twin hr hR he he' hraw hnt hfee hat hat'
  have hdebt : b'.debtTotal = b.debtTotal := (congrArg RawLoanBroker.debtTotal hbraw :)
  have hbb : b'.coverAvailable = b.coverAvailable → b' = b := fun hc =>
    LoanBroker.eq_of_raw (by rw [hbraw, hc])
  cases tx <;> simp only [LendingTx.loanIndex?, Option.some.injEq, reduceCtorEq] at htx <;> subst htx <;>
    dsimp only [LendingTx.withLoan] at hok'
  · obtain ⟨e0, loan, r, he0, hat, -, hacc, rfl, -, -, -, hbr⟩ := LendingLedger.loanAccept_ok hok
    obtain ⟨e0', loan', r', he0', hat', -, hacc', rfl, -, -, -, hbr'⟩ := LendingLedger.loanAccept_ok hok'
    rw [he] at he0
    rw [he'] at he0'
    obtain rfl := Option.some.inj he0
    obtain rfl := Option.some.inj he0'
    refine ⟨b, b', ?_, ?_, hbraw, fun hc _ _ => hc⟩
    · rw [hbr, if_pos rfl, Loan.accept_broker loan _ r hacc, hat.broker_eq he hb]
    · rw [hbr', if_pos rfl, Loan.accept_broker loan' _ r' hacc', hat'.broker_eq he' hb']
  · obtain ⟨e0, loan, r, he0, hat, -, hd, rfl, -, -, -, hbr⟩ := LendingLedger.loanDelete_ok hok
    obtain ⟨e0', loan', r', he0', hat', -, hd', rfl, -, -, -, hbr'⟩ := LendingLedger.loanDelete_ok hok'
    rw [he] at he0
    rw [he'] at he0'
    obtain rfl := Option.some.inj he0
    obtain rfl := Option.some.inj he0'
    have ht := htwin loan loan' hat hat'
    have hlb := hat.broker_eq he hb
    have hlb' := hat'.broker_eq he' hb'
    have hpend : loan'.isPending = loan.isPending := (congrArg RawLoan.isPending ht.raw :)
    have hpo : loan'.principalOutstanding = loan.principalOutstanding :=
      (congrArg RawLoan.principalOutstanding ht.raw :)
    have hlc : b'.loanCount = b.loanCount := (congrArg RawLoanBroker.loanCount hbraw :)
    obtain ⟨d, hdp, hda, hrd⟩ := Loan.delete_broker_raw loan _ r hd
    obtain ⟨d', hdp', hda', hrd'⟩ := Loan.delete_broker_raw loan' _ r' hd'
    rw [hlb] at hdp hda hrd
    rw [hlb', hpend, hpo, hdebt] at hdp'
    rw [hlb', hpend, hdebt] at hda'
    rw [hlb', hlc] at hrd'
    have hdd : d' = d := by
      cases hp : loan.isPending
      · rw [hda hp, hda' hp]
      · have h2 := hdp' hp
        rw [hdp hp] at h2
        exact (Except.ok.inj h2).symm
    rw [hdd] at hrd'
    refine ⟨r.broker', r'.broker', by rw [hbr, if_pos rfl], by rw [hbr', if_pos rfl], ?_, fun hc _ _ => ?_⟩
    · exact RawLoanBroker.update_twin hbraw rfl hrd hrd'
    · rw [show r'.broker'.coverAvailable = r'.broker'.toRawLoanBroker.coverAvailable from rfl,
        show r.broker'.coverAvailable = r.broker'.toRawLoanBroker.coverAvailable from rfl, hrd, hrd']
      exact hc
  · rename_i action
    cases action with
    | impair =>
      obtain ⟨e0, loan, r, he0, hat, -, hm, rfl, -, -, -, hbr⟩ := LendingLedger.loanImpair_ok hok
      obtain ⟨e0', loan', r', he0', hat', -, hm', rfl, -, -, -, hbr'⟩ := LendingLedger.loanImpair_ok hok'
      rw [he] at he0
      rw [he'] at he0'
      obtain rfl := Option.some.inj he0
      obtain rfl := Option.some.inj he0'
      refine ⟨b, b', ?_, ?_, hbraw, fun hc _ _ => hc⟩
      · rw [hbr, if_pos rfl, (Loan.manageImpair_debt loan _ _ r hm).1, hat.broker_eq he hb]
      · rw [hbr', if_pos rfl, (Loan.manageImpair_debt loan' _ _ r' hm').1, hat'.broker_eq he' hb']
    | unimpair =>
      obtain ⟨e0, loan, r, he0, hat, -, hm, rfl, -, -, -, hbr⟩ := LendingLedger.loanUnimpair_ok hok
      obtain ⟨e0', loan', r', he0', hat', -, hm', rfl, -, -, -, hbr'⟩ := LendingLedger.loanUnimpair_ok hok'
      rw [he] at he0
      rw [he'] at he0'
      obtain rfl := Option.some.inj he0
      obtain rfl := Option.some.inj he0'
      refine ⟨b, b', ?_, ?_, hbraw, fun hc _ _ => hc⟩
      · rw [hbr, if_pos rfl, (Loan.manageUnimpair_debt loan _ r hm).1, hat.broker_eq he hb]
      · rw [hbr', if_pos rfl, (Loan.manageUnimpair_debt loan' _ r' hm').1, hat'.broker_eq he' hb']
    | default =>
      obtain ⟨e0, loan, r, he0, hat, -, hm, rfl, -, -, -, hbr⟩ := LendingLedger.loanDefault_ok hok
      obtain ⟨e0', loan', r', he0', hat', -, hm', rfl, -, -, -, hbr'⟩ := LendingLedger.loanDefault_ok hok'
      rw [he] at he0
      rw [he'] at he0'
      obtain rfl := Option.some.inj he0
      obtain rfl := Option.some.inj he0'
      have ht := htwin loan loan' hat hat'
      have hlb := hat.broker_eq he hb
      have hlb' := hat'.broker_eq he' hb'
      have hpo : loan'.principalOutstanding = loan.principalOutstanding :=
        (congrArg RawLoan.principalOutstanding ht.raw :)
      obtain ⟨hrec, hdt, hcv, hpn⟩ := Loan.manageDefault_broker_record loan _ r hm
      obtain ⟨hrec', hdt', hcv', hpn'⟩ := Loan.manageDefault_broker_record loan' _ r' hm'
      rw [hlb', hdebt, hpo, ← hlb, hdt] at hdt'
      have hdeq : r'.loan'.broker.debtTotal = r.loan'.broker.debtTotal := (Except.ok.inj hdt').symm
      rw [hlb] at hrec
      rw [hlb', hdeq] at hrec'
      refine ⟨r.loan'.broker, r'.loan'.broker, by rw [hbr, if_pos rfl], by rw [hbr', if_pos rfl],
        RawLoanBroker.update_twin hbraw (congrArg RawLoanBroker.loanCount hbraw :) hrec hrec', fun hc hn hn' => ?_⟩
      have hbe : L.vault.baseExponent = l.vault.baseExponent := by
        unfold XRPL.Model.SingleAssetVault.Vault.baseExponent; rw [hnt, hscale]
      have hll : loan'.broker = loan.broker := by rw [hlb, hlb', hbb hc]
      obtain ⟨⟨mc, liq, hmc, hliq, hatp⟩, -⟩ := LendingLedger.default_at_base hr hat hm hn
      obtain ⟨⟨mc', liq', hmc', hliq', hatp'⟩, -⟩ := LendingLedger.default_at_base hR hat' hm' hn'
      rw [hll, hmc] at hmc'
      obtain rfl := Except.ok.inj hmc'
      rw [hll, hliq] at hliq'
      obtain rfl := Except.ok.inj hliq'
      rw [hpo, hll, hbe, ← hatp] at hatp'
      have hatq := Number.isNormalized.toRat_inj hpn' hpn hatp'
      rw [hll, hatq, hcv] at hcv'
      exact (Except.ok.inj hcv').symm
  · obtain ⟨e0, loan, r, he0, hat, -, -, hpay, rfl, -, -, -, hbr⟩ := LendingLedger.loanPay_ok hok
    obtain ⟨e0', loan', r', he0', hat', -, -, hpay', rfl, -, -, -, hbr'⟩ := LendingLedger.loanPay_ok hok'
    rw [he] at he0
    rw [he'] at he0'
    obtain rfl := Option.some.inj he0
    obtain rfl := Option.some.inj he0'
    have hlb := hat.broker_eq he hb
    have hlb' := hat'.broker_eq he' hb'
    have hbe : L.vault.baseExponent = l.vault.baseExponent := by
      unfold XRPL.Model.SingleAssetVault.Vault.baseExponent; rw [hnt, hscale]
    rw [hnow] at hpay'
    obtain ⟨h1, h2⟩ := Loan.pay_broker_twin (htwin loan loan' hat hat') (by rw [hlb, hlb']; exact hbraw) _ _ hbe
      _ _ _ hpay hpay'
    exact ⟨r.loan'.broker, r'.loan'.broker, by rw [hbr, if_pos rfl], by rw [hbr', if_pos rfl], h1,
      fun hc _ _ => h2 (by rw [hlb, hlb', hbb hc])⟩

/-- The same LoanSet on broker `k` of `l` and broker `k'` of `L`, two copies that differ at most in CoverAvailable,
stores twin loans at the end of both lists and leaves two such copies with the covers they had. -/
private lemma LendingLedger.loanSet_broker_twin {l L l₂ L₂ : LendingLedger} (hnow : L.now = l.now)
    (hnt : L.vault.numericType = l.vault.numericType) (hscale : L.vault.scale = l.vault.scale)
    {k k' : Nat} {b b' : LoanBroker} (hb : l.broker? k = some b) (hb' : L.broker? k' = some b')
    (hbraw : b'.toRawLoanBroker = { b.toRawLoanBroker with coverAvailable := b'.coverAvailable })
    {tx : LendingTx} (hset : tx.isLoan = true ∧ tx.loanIndex? = none) (hk : l.loanTxBroker? tx = some k)
    (h : (l.apply tx).run = .ok (.ok l₂)) (h' : (L.apply (tx.withBroker k')).run = .ok (.ok L₂)) :
    (∃ f f', l₂.loan? l.loans.length = some f ∧ L₂.loan? L.loans.length = some f' ∧ f.brokerIndex = k ∧
      f'.brokerIndex = k' ∧ f'.loan.toRawLoan = { f.loan.toRawLoan with broker := f'.loan.toRawLoan.broker }) ∧
    ∃ c c', l₂.broker? k = some c ∧ L₂.broker? k' = some c' ∧
      c'.toRawLoanBroker = { c.toRawLoanBroker with coverAvailable := c'.coverAvailable } ∧
      c.coverAvailable = b.coverAvailable ∧ c'.coverAvailable = b'.coverAvailable := by
  cases tx <;> simp only [LendingTx.isLoan, LendingTx.loanIndex?, Bool.false_eq_true, reduceCtorEq, and_true,
    and_false] at hset
  rename_i k0 principal rates fees pi pt gp sd twoStep ao
  simp only [LendingLedger.loanTxBroker?, Option.some.injEq] at hk
  subst hk
  dsimp only [LendingTx.withBroker] at h'
  obtain ⟨b0, r, hb0, -, -, -, hcr, rfl, -, -, -, hbr⟩ := LendingLedger.loanSet_ok h
  obtain ⟨b0', r', hb0', -, -, -, hcr', rfl, -, -, -, hbr'⟩ := LendingLedger.loanSet_ok h'
  rw [hb] at hb0
  obtain rfl := Option.some.inj hb0
  rw [hb'] at hb0'
  obtain rfl := Option.some.inj hb0'
  rw [hnow] at hcr'
  have hbe : L.vault.baseExponent = l.vault.baseExponent := by
    unfold XRPL.Model.SingleAssetVault.Vault.baseExponent; rw [hnt, hscale]
  have ht := Loan.create_twin b b' l.vault L.vault principal rates fees _ ao twoStep r r'
    (congrArg RawLoanBroker.numericType hbraw :) (congrArg RawLoanBroker.managementFeeRate hbraw :) hbe hcr hcr'
  have hdebt : b'.debtTotal = b.debtTotal := (congrArg RawLoanBroker.debtTotal hbraw :)
  have hlc : b'.loanCount = b.loanCount := (congrArg RawLoanBroker.loanCount hbraw :)
  obtain ⟨d, hd, hrb⟩ := Loan.create_broker_raw _ _ _ _ _ _ _ _ r hcr
  obtain ⟨d', hd', hrb'⟩ := Loan.create_broker_raw _ _ _ _ _ _ _ _ r' hcr'
  rw [hdebt, hd] at hd'
  obtain rfl := Except.ok.inj hd'
  refine ⟨⟨{ brokerIndex := k0, loan := r.loan' }, { brokerIndex := k', loan := r'.loan' }, ?_, ?_, rfl, rfl,
    ht.raw⟩, r.loan'.broker, r'.loan'.broker, by rw [hbr, if_pos rfl], by rw [hbr', if_pos rfl],
    RawLoanBroker.update_twin hbraw (by rw [hlc]) hrb hrb', ?_, ?_⟩
  · rw [LendingLedger.loan?_commitLoan]; simp [LoanEffect.ofCreate]
  · rw [LendingLedger.loan?_commitLoan]; simp [LoanEffect.ofCreate]
  · rw [show r.loan'.broker.coverAvailable = r.loan'.broker.toRawLoanBroker.coverAvailable from rfl, hrb]
  · rw [show r'.loan'.broker.coverAvailable = r'.loan'.broker.toRawLoanBroker.coverAvailable from rfl, hrb']

/-- A successful LoanBrokerCreate adds the broker its fields build for the vault's asset at the end of the list. -/
private lemma LendingLedger.applyBroker_create {l : LendingLedger} {ctx : LoanBrokerSetCreate} {u : BrokerEffect}
    (hu : (l.applyBroker (.loanBrokerCreate ctx)).run = .ok (.ok u)) :
    ∃ nb, LoanBroker.create ctx l.vault.numericType = .ok nb ∧
      u = { index := l.brokers.length, broker := some nb } := by
  simp only [LendingLedger.applyBroker] at hu
  unfold_ter at hu
  walk_ok
  exact ⟨_, ‹_›, rfl⟩

/-- The same LoanBrokerCreate on two vaults of the same asset adds the same broker at the end of both lists and keeps
the loans. -/
private lemma LendingLedger.brokerCreate_twin {l L l₂ L₂ : LendingLedger} {ctx : LoanBrokerSetCreate}
    (hnt : L.vault.numericType = l.vault.numericType) (h : (l.apply (.loanBrokerCreate ctx)).run = .ok (.ok l₂))
    (h' : (L.apply (.loanBrokerCreate ctx)).run = .ok (.ok L₂)) :
    ∃ nb, l₂.broker? l.brokers.length = some nb ∧ L₂.broker? L.brokers.length = some nb ∧ l₂.loans = l.loans ∧
      L₂.loans = L.loans ∧ l₂.brokers.length = l.brokers.length + 1 := by
  obtain ⟨u, hu, rfl⟩ := LendingLedger.apply_broker rfl h
  obtain ⟨u', hu', rfl⟩ := LendingLedger.apply_broker rfl h'
  obtain ⟨nb, hnb, rfl⟩ := LendingLedger.applyBroker_create hu
  obtain ⟨nb', hnb', rfl⟩ := LendingLedger.applyBroker_create hu'
  rw [hnt, hnb] at hnb'
  obtain rfl := Except.ok.inj hnb'
  refine ⟨nb, ?_, ?_, rfl, rfl, ?_⟩
  · rw [LendingLedger.broker?_commitBroker]; simp
  · rw [LendingLedger.broker?_commitBroker]; simp
  · simp [LendingLedger.commitBroker, storeSlot]

end XRPL.Model.Lending
