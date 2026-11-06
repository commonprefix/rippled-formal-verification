import XRPL.Properties.Lending.Ledger.Common.BrokerSubsequenceTwin
import XRPL.Properties.Lending.Ledger.Common.LoanSubsequence

/-! # One broker's transactions alone

Broker `k` in a sequence of transactions from a reachable ledger, and the same broker in the subsequence of its own
and its loans' transactions, renumbered to `k'`: on both it is not created yet, deleted, or stored as two copies that
differ at most in CoverAvailable, and each of its loans has a twin under its number in the subsequence. The covers
are equal too while neither run is coarsened. Once the openings succeed, every other transaction the subsequence
keeps succeeds as well, when loan and broker transactions replay on twins. -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol

open private LendingLedger.apply_scale LendingLedger.apply_now LendingLedger.apply_close LendingLedger.apply_loans
  LendingLedger.apply_named_loan LendingLedger.loanTx_twin
  from XRPL.Properties.Lending.Ledger.Common.LoanSubsequenceTwin
open private LendingLedger.Reaches.split from XRPL.Properties.Lending.Ledger.Common.LoanSubsequence
open private LoanBroker.raw_eq_of_cover LendingLedger.apply_keeps_broker
  LendingLedger.apply_keeps_loans LendingLedger.loanTx_broker_twin LendingLedger.loanSet_broker_twin
  LendingLedger.brokerCreate_twin from XRPL.Properties.Lending.Ledger.Common.BrokerSubsequenceTwin
open private LendingLedger.apply_brokers_length from XRPL.Properties.Lending.Ledger.Common.BrokerAccounting
open private LendingLedger.apply_deleted_empty from XRPL.Properties.Lending.Loan.Common.PayLedger
open private LendingLedger.applyLoan_effect from XRPL.Properties.Lending.Ledger.Common.Isolation

/-- Broker `k` of the sequence's ledger `l` and broker `k'` of the subsequence's ledger `L`: deleted on both, or two
copies that differ at most in CoverAvailable, with covers of the same value while `E` holds. -/
private def LendingLedger.BrokerTwin (E : Prop) (k k' : Nat) (l L : LendingLedger) : Prop :=
  (l.broker? k = none ∧ L.broker? k' = none) ∨ ∃ b b', l.broker? k = some b ∧ L.broker? k' = some b' ∧
    b'.toRawLoanBroker = { b.toRawLoanBroker with coverAvailable := b'.coverAvailable } ∧
    (E → b'.coverAvailable.toRat = b.coverAvailable.toRat)

/-- Broker `k` is not created yet on either ledger, or created on both. -/
private def LendingLedger.BrokerPair (E : Prop) (k k' : Nat) (l L : LendingLedger) : Prop :=
  (l.brokers.length ≤ k ∧ L.brokers.length = k') ∨ (k < l.brokers.length ∧ LendingLedger.BrokerTwin E k k' l L)

/-- Every loan of broker `k` on the sequence's ledger has a twin on broker `k'` under its number in the subsequence.
The `base` loans of the start ledger keep their number and the new loans `created` follow them. -/
private structure LendingLedger.LoansPair (k k' base : Nat) (created : List Nat) (l L : LendingLedger) : Prop where
  base_le : base ≤ l.loans.length
  length : L.loans.length = base + created.length
  created_mem : ∀ i ∈ created, base ≤ i ∧ i < l.loans.length
  twin : ∀ i e, l.loan? i = some e → e.brokerIndex = k → ∃ e', L.loan? (subLoanIndex base created i) = some e' ∧
    e'.brokerIndex = k' ∧ e'.loan.toRawLoan = { e.loan.toRawLoan with broker := e'.loan.toRawLoan.broker }

/-- The sequence's ledger `l` and the subsequence's ledger `L` for broker `k`: both reachable, at the same close
time, with the same vault asset and scale, and broker `k` and its loans paired with broker `k'` and theirs. -/
private structure LendingLedger.BPair (E : Prop) (k k' base : Nat) (created : List Nat) (l L : LendingLedger) :
    Prop where
  reachable : l.Reachable
  reachable' : L.Reachable
  now : L.now = l.now
  numericType : L.vault.numericType = l.vault.numericType
  scale : L.vault.scale = l.vault.scale
  broker : LendingLedger.BrokerPair E k k' l L
  loans : LendingLedger.LoansPair k k' base created l L

/-- A stored loan in the subsequence under the number of loan `i` means `i` is a start loan or a new one. -/
private lemma subLoanIndex_scope {base : Nat} {created : List Nat} {L : LendingLedger} {i : Nat} {e' : LoanEntry}
    (hlen : L.loans.length = base + created.length) (he' : L.loan? (subLoanIndex base created i) = some e') :
    i < base ∨ i ∈ created := by
  by_cases hi : i < base
  · exact Or.inl hi
  right
  by_contra hm
  have hlt := LendingLedger.loan?_lt he'
  rw [subLoanIndex, if_neg hi, List.idxOf_eq_length hm] at hlt
  omega

/-- Loans of the start ledger and new loans get different numbers in the subsequence. -/
private lemma subLoanIndex_inj {base : Nat} {created : List Nat} (hge : ∀ x ∈ created, base ≤ x) {i j : Nat}
    (hi : i < base ∨ i ∈ created) (hj : j < base ∨ j ∈ created)
    (h : subLoanIndex base created i = subLoanIndex base created j) : i = j := by
  unfold subLoanIndex at h
  rcases hi with hi | hi <;> rcases hj with hj | hj
  · rwa [if_pos hi, if_pos hj] at h
  · have := hge j hj
    rw [if_pos hi, if_neg (by omega)] at h
    omega
  · have := hge i hi
    rw [if_neg (by omega), if_pos hj] at h
    omega
  · have h1 := hge i hi
    have h2 := hge j hj
    rw [if_neg (by omega), if_neg (by omega)] at h
    exact (List.idxOf_inj hi).mp (by omega)

/-- A loan already numbered keeps its number when a new loan joins `created`. -/
private lemma subLoanIndex_append {base : Nat} {created : List Nat} {i : Nat} (n : Nat)
    (hi : i < base ∨ i ∈ created) : subLoanIndex base (created ++ [n]) i = subLoanIndex base created i := by
  unfold subLoanIndex
  rcases hi with hi | hi
  · rw [if_pos hi, if_pos hi]
  · split
    · rfl
    · rw [List.idxOf_append_of_mem hi]

/-- A new loan gets the next number after the loans numbered so far. -/
private lemma subLoanIndex_new {base : Nat} {created : List Nat} {n : Nat} (hbn : base ≤ n) (hn : n ∉ created) :
    subLoanIndex base (created ++ [n]) n = base + created.length := by
  unfold subLoanIndex
  rw [if_neg (by omega), List.idxOf_append_of_notMem hn]
  simp

/-- What `brokerTxsFrom` keeps of one transaction run on `l`, and the new loans of the broker after it. -/
private def LendingLedger.brokerStep (k k' base : Nat) (created : List Nat) (l : LendingLedger) (tx : LendingTx) :
    List LendingTx × List Nat :=
  match tx with
  | .close _ => ([tx], created)
  | .loanSet .. =>
    if l.loanTxBroker? tx = some k then ([tx.withBroker k'], created ++ [l.loans.length]) else ([], created)
  | _ =>
    if l.txBroker? tx = some k then
      match tx.loanIndex? with
      | some i => ([tx.withLoan (subLoanIndex base created i)], created)
      | none => ([tx.withBroker k'], created)
    else ([], created)

/-- After a transaction that succeeds, `brokerTxsFrom` keeps its part of it and goes on from the ledger it leaves. -/
private lemma LendingLedger.brokerTxsFrom_cons {k k' base : Nat} {created : List Nat} {l l' : LendingLedger}
    {tx : LendingTx} (txs : List LendingTx) (h : (l.apply tx).run = .ok (.ok l')) :
    l.brokerTxsFrom k k' base created (tx :: txs) = (l.brokerStep k k' base created tx).1 ++
      l'.brokerTxsFrom k k' base (l.brokerStep k k' base created tx).2 txs := by
  rw [LendingLedger.brokerTxsFrom.eq_def]
  dsimp only
  rw [h]
  cases tx <;> rfl

/-- `brokerTxsFrom` drops a transaction, keeps a close, keeps a LoanSet on broker `k` with its new loan, keeps a
transaction on a loan of `k` renumbered, or keeps a broker transaction on `k`. -/
private lemma LendingLedger.brokerStep_cases (k k' base : Nat) (created : List Nat) (l : LendingLedger)
    (tx : LendingTx) :
    (l.brokerStep k k' base created tx = ([], created) ∧ (∀ t, tx ≠ .close t) ∧ l.txBroker? tx ≠ some k) ∨
      (∃ t, tx = .close t ∧ l.brokerStep k k' base created tx = ([tx], created)) ∨
      (tx.isLoan = true ∧ tx.loanIndex? = none ∧ l.loanTxBroker? tx = some k ∧
        l.brokerStep k k' base created tx = ([tx.withBroker k'], created ++ [l.loans.length])) ∨
      (∃ i, tx.loanIndex? = some i ∧ l.txBroker? tx = some k ∧
        l.brokerStep k k' base created tx = ([tx.withLoan (subLoanIndex base created i)], created)) ∨
      (tx.isBroker = true ∧ l.txBroker? tx = some k ∧
        l.brokerStep k k' base created tx = ([tx.withBroker k'], created)) := by
  by_cases hc : ∃ t, tx = .close t
  · obtain ⟨t, rfl⟩ := hc
    exact Or.inr (Or.inl ⟨t, rfl, rfl⟩)
  have hc' : ∀ t, tx ≠ .close t := fun t h => hc ⟨t, h⟩
  by_cases hk : l.txBroker? tx = some k
  · cases tx with
    | close t => exact absurd rfl (hc' t)
    | loanSet =>
      exact Or.inr (Or.inr (Or.inl ⟨rfl, rfl, hk, by simp only [LendingLedger.brokerStep]; exact if_pos hk⟩))
    | loanAccept i | loanDelete i | loanManage i _ | loanPay i _ _ =>
      exact Or.inr (Or.inr (Or.inr (Or.inl ⟨i, rfl, hk, by simp [LendingLedger.brokerStep, hk,
        LendingTx.loanIndex?]⟩)))
    | loanBrokerCreate _ | loanBrokerUpdate _ _ | loanBrokerCoverDeposit _ _ | loanBrokerCoverWithdraw _ _
    | loanBrokerCoverClawback _ _ | loanBrokerDelete _ =>
      exact Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, hk, by simp [LendingLedger.brokerStep, hk,
        LendingTx.loanIndex?]⟩)))
    | _ => simp [LendingLedger.txBroker?, LendingLedger.loanTxBroker?, LendingTx.loanIndex?] at hk
  · left
    refine ⟨?_, hc', hk⟩
    cases tx with
    | close t => exact absurd rfl (hc' t)
    | _ => simp_all [LendingLedger.brokerStep, LendingLedger.txBroker?]

/-- A reachable ledger that stores a broker still has its vault. -/
private lemma LendingLedger.Reachable.live_of_broker {l : LendingLedger} (hr : l.Reachable) {k : Nat}
    {b : LoanBroker} (hb : l.broker? k = some b) : l.vaultDeleted = false := by
  have hinv : l.vaultDeleted = true → l.brokers.any Option.isSome = false :=
    LendingLedger.Reachable.invariant (Inv := fun l => l.vaultDeleted = true → l.brokers.any Option.isSome = false)
      (fun g hg hd => by rw [hg.not_deleted] at hd; cases hd)
      (fun _ _ _ hi ha => LendingLedger.apply_deleted_empty hi ha) hr
  cases hd : l.vaultDeleted
  · rfl
  · have hany := hinv hd
    unfold LendingLedger.broker? at hb
    cases hj : l.brokers[k]? with
    | none => rw [hj] at hb; cases hb
    | some x =>
      have hx : (some x).join = some b := by rw [← hj]; exact hb
      have hmem := List.mem_of_getElem? hj
      have : l.brokers.any Option.isSome = true := List.any_eq_true.mpr ⟨x, hmem, by cases x <;> simp_all⟩
      rw [hany] at this
      cases this

/-- A broker transaction on `k` that succeeds is a LoanBrokerCreate adding broker `k`, or finds broker `k` stored. -/
private lemma LendingLedger.apply_brokerTx_on {l l₂ : LendingLedger} {tx : LendingTx} {k : Nat}
    (h : (l.apply tx).run = .ok (.ok l₂)) (hb : tx.isBroker = true) (hk : l.txBroker? tx = some k) :
    (∃ ctx, tx = .loanBrokerCreate ctx ∧ k = l.brokers.length) ∨ ∃ b, l.broker? k = some b := by
  obtain ⟨u, hu, -⟩ := LendingLedger.apply_broker hb h
  cases tx <;> simp only [LendingTx.isBroker, Bool.false_eq_true] at hb <;>
    simp only [LendingLedger.txBroker?, Option.some.injEq] at hk
  · exact Or.inl ⟨_, rfl, hk.symm⟩
  all_goals
    subst hk
    simp only [LendingLedger.applyBroker] at hu
    unfold_ter at hu
    walk_ok
    exact Or.inr ⟨_, ‹_›⟩

/-- The start ledger with itself: broker `k` keeps its number when it is stored, else it gets the next free slot,
and its loans keep theirs. -/
private lemma LendingLedger.BPair.start {start : LendingLedger} (hr : start.Reachable) (E : Prop) (k : Nat) :
    LendingLedger.BPair E k (start.aloneBrokerIndex k) start.loans.length [] start start := by
  refine ⟨hr, hr, rfl, rfl, rfl, ?_, ⟨le_refl _, by simp, (fun i hi => by cases hi), fun i e he hek => ?_⟩⟩
  · unfold LendingLedger.BrokerPair LendingLedger.BrokerTwin LendingLedger.aloneBrokerIndex
    by_cases hk : k < start.brokers.length
    · rw [min_eq_left hk.le]
      refine Or.inr ⟨hk, ?_⟩
      cases hb : start.broker? k with
      | none => exact Or.inl ⟨rfl, rfl⟩
      | some b => exact Or.inr ⟨b, b, rfl, rfl, rfl, fun _ => rfl⟩
    · rw [min_eq_right (by omega)]
      exact Or.inl ⟨by omega, rfl⟩
  · obtain ⟨b, hb⟩ := hr.loanCountInv.broker_of_loan he
    rw [hek] at hb
    have hk := LendingLedger.broker?_lt hb
    refine ⟨e, ?_, ?_, rfl⟩
    · rw [subLoanIndex, if_pos (LendingLedger.loan?_lt he)]
      exact he
    · rw [hek, LendingLedger.aloneBrokerIndex, min_eq_left hk.le]

/-- The pairing of the loans holds on ledgers with the same loans. -/
private lemma LendingLedger.LoansPair.of_loans {k k' base : Nat} {created : List Nat} {l L l₂ L₂ : LendingLedger}
    (hp : LendingLedger.LoansPair k k' base created l L) (hl : l₂.loans = l.loans) (hL : L₂.loans = L.loans) :
    LendingLedger.LoansPair k k' base created l₂ L₂ := by
  have h1 : ∀ i, l₂.loan? i = l.loan? i := fun i => by unfold LendingLedger.loan?; rw [hl]
  have h2 : ∀ i, L₂.loan? i = L.loan? i := fun i => by unfold LendingLedger.loan?; rw [hL]
  refine ⟨by rw [hl]; exact hp.base_le, by rw [hL]; exact hp.length, fun i hi => by rw [hl]; exact hp.created_mem i hi,
    fun i e he hek => ?_⟩
  rw [h1] at he
  obtain ⟨e', he', h⟩ := hp.twin i e he hek
  exact ⟨e', by rw [h2]; exact he', h⟩

/-- A loan of broker `k` other than loan `i` keeps its twin when only loan `i` and its number `j'` were written. -/
private lemma LendingLedger.LoansPair.twin_other {k k' base : Nat} {created : List Nat}
    {l L l₂ L₂ : LendingLedger} (hp : LendingLedger.LoansPair k k' base created l L) {i : Nat}
    (hsi : i < base ∨ i ∈ created) (hl₂ : l₂.loans.length = l.loans.length)
    (hslot : ∀ j, j < l.loans.length → j ≠ i → l₂.loan? j = l.loan? j)
    (hLslot : ∀ j, j < L.loans.length → j ≠ subLoanIndex base created i → L₂.loan? j = L.loan? j)
    {j : Nat} {f : LoanEntry} (hji : j ≠ i) (hf : l₂.loan? j = some f) (hfk : f.brokerIndex = k) :
    ∃ f', L₂.loan? (subLoanIndex base created j) = some f' ∧ f'.brokerIndex = k' ∧
      f'.loan.toRawLoan = { f.loan.toRawLoan with broker := f'.loan.toRawLoan.broker } := by
  have hge : ∀ x ∈ created, base ≤ x := fun x hx => (hp.created_mem x hx).1
  have hjlt : j < l.loans.length := by
    have := LendingLedger.loan?_lt hf
    omega
  rw [hslot j hjlt hji] at hf
  obtain ⟨f', hf', hfb, hfr⟩ := hp.twin j f hf hfk
  have hsj := subLoanIndex_scope hp.length hf'
  have hne : subLoanIndex base created j ≠ subLoanIndex base created i :=
    fun h0 => hji (subLoanIndex_inj hge hsj hsi h0)
  refine ⟨f', ?_, hfb, hfr⟩
  rw [hLslot _ (LendingLedger.loan?_lt hf') hne]
  exact hf'

/-- Renumbering the broker keeps the kind of transaction and the loan it names. -/
private lemma LendingTx.withBroker_kind (k' : Nat) (tx : LendingTx) :
    (tx.withBroker k').isLoan = tx.isLoan ∧ (tx.withBroker k').isBroker = tx.isBroker ∧
      (tx.withBroker k').loanIndex? = tx.loanIndex? := by
  cases tx <;> exact ⟨rfl, rfl, rfl⟩

/-- A transaction that names a loan is a loan transaction, and still names one after renumbering. -/
private lemma LendingTx.named_loan {tx : LendingTx} {i : Nat} (h : tx.loanIndex? = some i) (j : Nat) :
    tx.isLoan = true ∧ (tx.withLoan j).loanIndex? = some j := by
  cases tx <;> simp only [LendingTx.loanIndex?, reduceCtorEq] at h <;> exact ⟨rfl, rfl⟩

/-- A transaction on a stored loan that acts on broker `k` names a loan of `k`. -/
private lemma LendingLedger.named_loan_broker {l : LendingLedger} {tx : LendingTx} {i k : Nat} {e : LoanEntry}
    (hi : tx.loanIndex? = some i) (he : l.loan? i = some e) (hk : l.txBroker? tx = some k) : e.brokerIndex = k := by
  cases tx <;> simp only [LendingTx.loanIndex?, reduceCtorEq, Option.some.injEq] at hi <;> subst hi <;>
    simp only [LendingLedger.txBroker?, LendingLedger.loanTxBroker?, LendingTx.loanIndex?, Option.bind_some, he,
      Option.map_some, Option.some.injEq] at hk <;> exact hk

/-- One transaction of the sequence, with the part of it the subsequence keeps, keeps the pair. `hbtx` gives the
broker after a broker transaction on `k` other than its creation. -/
private lemma LendingLedger.BPair.step {E : Prop} {k k' base : Nat} {created : List Nat}
    {l L l₂ L₂ : LendingLedger} {tx : LendingTx} (hp : LendingLedger.BPair E k k' base created l L)
    (h : (l.apply tx).run = .ok (.ok l₂))
    (hs : LendingLedger.Reaches L (l.brokerStep k k' base created tx).1 L₂)
    (hnc : E → l.NotCoarsened ∧ L.NotCoarsened)
    (hbtx : tx.isBroker = true → l.txBroker? tx = some k → ∀ b b', l.broker? k = some b → L.broker? k' = some b' →
      b'.toRawLoanBroker = { b.toRawLoanBroker with coverAvailable := b'.coverAvailable } →
      (E → b'.coverAvailable.toRat = b.coverAvailable.toRat) →
      (L.apply (tx.withBroker k')).run = .ok (.ok L₂) → LendingLedger.BrokerTwin E k k' l₂ L₂) :
    LendingLedger.BPair E k k' base (l.brokerStep k k' base created tx).2 l₂ L₂ := by
  have hr₂ := hp.reachable.apply h
  obtain ⟨hlen, hslot⟩ := LendingLedger.apply_loans h
  have hlen₂ : l.loans.length ≤ l₂.loans.length := by rcases hlen with h1 | ⟨h1, -⟩ <;> omega
  have hblen := LendingLedger.apply_brokers_length h
  have htw : ∀ b, l.broker? k = some b → k < l.brokers.length ∧ ∃ b', L.broker? k' = some b' ∧
      b'.toRawLoanBroker = { b.toRawLoanBroker with coverAvailable := b'.coverAvailable } ∧
      (E → b'.coverAvailable.toRat = b.coverAvailable.toRat) := by
    intro b hb
    have hk := LendingLedger.broker?_lt hb
    refine ⟨hk, ?_⟩
    rcases hp.broker with ⟨hle, -⟩ | ⟨-, ⟨hn, -⟩ | ⟨b0, b0', hb0, hb0', hraw, hE⟩⟩
    · omega
    · rw [hn] at hb
      cases hb
    · rw [hb] at hb0
      obtain rfl := Option.some.inj hb0
      exact ⟨b0', hb0', hraw, hE⟩
  rcases LendingLedger.brokerStep_cases k k' base created l tx with ⟨hst, hc, hk⟩ | ⟨t, rfl, hst⟩ |
    ⟨hl, hn, hk, hst⟩ | ⟨i, hi, hk, hst⟩ | ⟨hb, hk, hst⟩ <;> rw [hst] at hs ⊢ <;> dsimp only at hs ⊢
  · obtain rfl := LendingLedger.Reaches.nil_inv hs
    obtain ⟨hbk, hblk⟩ := LendingLedger.apply_keeps_broker h hk
    refine ⟨hr₂, hp.reachable', by rw [LendingLedger.apply_now h hc]; exact hp.now,
      by rw [LendingLedger.apply_numericType h]; exact hp.numericType,
      by rw [LendingLedger.apply_scale h]; exact hp.scale, ?_, ?_⟩
    · rcases hp.broker with ⟨hle, hL⟩ | ⟨hlt, htwn⟩
      · exact Or.inl ⟨hblk hle, hL⟩
      · refine Or.inr ⟨by omega, ?_⟩
        unfold LendingLedger.BrokerTwin at htwn ⊢
        rw [hbk]
        exact htwn
    · refine ⟨le_trans hp.loans.base_le hlen₂, hp.loans.length, fun i hi => ?_,
        fun i e he hek => hp.loans.twin i e (LendingLedger.apply_keeps_loans h hk i e he hek) hek⟩
      obtain ⟨h1, h2⟩ := hp.loans.created_mem i hi
      exact ⟨h1, by omega⟩
  · obtain ⟨L₁, hL₁, hs⟩ := LendingLedger.Reaches.cons_inv hs
    obtain rfl := LendingLedger.Reaches.nil_inv hs
    have e1 := (LendingLedger.apply_close l t).symm.trans h
    have e2 := (LendingLedger.apply_close L t).symm.trans hL₁
    injection e1 with e1
    injection e1 with e1
    injection e2 with e2
    injection e2 with e2
    subst e1 e2
    exact ⟨hr₂, hp.reachable'.apply hL₁, by show max L.now t = max l.now t; rw [hp.now], hp.numericType, hp.scale,
      hp.broker, ⟨hp.loans.base_le, hp.loans.length, hp.loans.created_mem, hp.loans.twin⟩⟩
  · obtain ⟨L₁, hL₁, hs⟩ := LendingLedger.Reaches.cons_inv hs
    obtain rfl := LendingLedger.Reaches.nil_inv hs
    have hc : ∀ t, tx ≠ .close t := by
      rintro t rfl
      cases hl
    have hl' : (tx.withBroker k').isLoan = true := by rw [(LendingTx.withBroker_kind k' tx).1]; exact hl
    have hn' : (tx.withBroker k').loanIndex? = none := by rw [(LendingTx.withBroker_kind k' tx).2.2]; exact hn
    have hc' : ∀ t, tx.withBroker k' ≠ .close t := by
      intro t h0
      rw [h0] at hl'
      cases hl'
    obtain ⟨u, hu, -⟩ := LendingLedger.apply_loan hl h
    obtain ⟨-, hbk, b, hb, -⟩ := LendingLedger.applyLoan_effect hu
    rw [hk] at hbk
    rw [← Option.some.inj hbk] at hb
    obtain ⟨hklt, b', hb', hraw, hE⟩ := htw b hb
    obtain ⟨⟨f, f', hf, hf', hfb, hfb', hfr⟩, c, c', hcb, hcb', hcr, hcc, hcc'⟩ :=
      LendingLedger.loanSet_broker_twin hp.now hp.numericType hp.scale hb hb' hraw ⟨hl, hn⟩ hk h hL₁
    have hLlen := hp.loans.length
    obtain ⟨hLlen₂, hLslot⟩ := LendingLedger.apply_loans hL₁
    have hl₂len : l₂.loans.length = l.loans.length + 1 := by
      have := LendingLedger.loan?_lt hf
      rcases hlen with h1 | ⟨h1, -⟩ <;> omega
    have hL₂len : L₂.loans.length = L.loans.length + 1 := by
      have := LendingLedger.loan?_lt hf'
      rcases hLlen₂ with h1 | ⟨h1, -⟩ <;> omega
    have hnew : l.loans.length ∉ created := fun hm => by
      have := (hp.loans.created_mem _ hm).2
      omega
    refine ⟨hr₂, hp.reachable'.apply hL₁,
      by rw [LendingLedger.apply_now hL₁ hc', LendingLedger.apply_now h hc]; exact hp.now,
      by rw [LendingLedger.apply_numericType hL₁, LendingLedger.apply_numericType h]; exact hp.numericType,
      by rw [LendingLedger.apply_scale hL₁, LendingLedger.apply_scale h]; exact hp.scale,
      Or.inr ⟨by omega, Or.inr ⟨c, c', hcb, hcb', hcr, (fun hE' => by rw [hcc, hcc']; exact hE hE')⟩⟩, ?_⟩
    refine ⟨le_trans hp.loans.base_le hlen₂, by rw [hL₂len, hLlen, List.length_append]; rfl, fun i hi => ?_,
      fun i e he hek => ?_⟩
    · rcases List.mem_append.mp hi with hi | hi
      · obtain ⟨h1, h2⟩ := hp.loans.created_mem i hi
        exact ⟨h1, by omega⟩
      · rw [List.mem_singleton] at hi
        subst hi
        exact ⟨hp.loans.base_le, by omega⟩
    · by_cases hin : i = l.loans.length
      · subst hin
        rw [hf] at he
        obtain rfl := Option.some.inj he
        refine ⟨f', ?_, hfb', hfr⟩
        rw [subLoanIndex_new hp.loans.base_le hnew, ← hLlen]
        exact hf'
      · have hilt : i < l.loans.length := by
          have := LendingLedger.loan?_lt he
          omega
        rw [hslot i hilt (by rw [hn]; simp)] at he
        obtain ⟨e', he', hbe', hraw'⟩ := hp.loans.twin i e he hek
        have hscope := subLoanIndex_scope hLlen he'
        refine ⟨e', ?_, hbe', hraw'⟩
        rw [subLoanIndex_append _ hscope, hLslot _ (LendingLedger.loan?_lt he') (by rw [hn']; simp)]
        exact he'
  · obtain ⟨L₁, hL₁, hs⟩ := LendingLedger.Reaches.cons_inv hs
    obtain rfl := LendingLedger.Reaches.nil_inv hs
    obtain ⟨e, he⟩ := LendingLedger.apply_named_loan h hi
    have hek : e.brokerIndex = k := LendingLedger.named_loan_broker hi he hk
    have hc : ∀ t, tx ≠ .close t := by
      rintro t rfl
      cases hi
    have hi' := (LendingTx.named_loan hi (subLoanIndex base created i)).2
    have hc' : ∀ t, tx.withLoan (subLoanIndex base created i) ≠ .close t := by
      intro t h0
      rw [h0] at hi'
      cases hi'
    obtain ⟨b, hb⟩ := hp.reachable.loanCountInv.broker_of_loan he
    rw [hek] at hb
    obtain ⟨hklt, b', hb', hraw, hE⟩ := htw b hb
    obtain ⟨e', he', he'b, he'raw⟩ := hp.loans.twin i e he hek
    have hfee : ∀ b0 b0', l.broker? e.brokerIndex = some b0 → L.broker? e'.brokerIndex = some b0' →
        b0'.managementFeeRate = b0.managementFeeRate := by
      intro b0 b0' h0 h0'
      rw [hek, hb] at h0
      rw [he'b, hb'] at h0'
      obtain rfl := Option.some.inj h0
      obtain rfl := Option.some.inj h0'
      exact (congrArg RawLoanBroker.managementFeeRate hraw :)
    obtain ⟨c, c', hcb, hcb', hcr, hcc⟩ := LendingLedger.loanTx_broker_twin hp.reachable hp.reachable' he he'
      he'raw hp.now hp.numericType hp.scale (by rw [hek]; exact hb) (by rw [he'b]; exact hb') hraw tx hi h hL₁
    have hLlen := hp.loans.length
    obtain ⟨hLlen₂, hLslot⟩ := LendingLedger.apply_loans hL₁
    have hl₂len : l₂.loans.length = l.loans.length := by
      rcases hlen with h1 | ⟨-, -, h1⟩
      · exact h1
      · rw [hi] at h1
        cases h1
    have hL₂len : L₂.loans.length = L.loans.length := by
      rcases hLlen₂ with h1 | ⟨-, -, h1⟩
      · exact h1
      · rw [hi'] at h1
        cases h1
    have hsi := subLoanIndex_scope hLlen he'
    refine ⟨hr₂, hp.reachable'.apply hL₁,
      by rw [LendingLedger.apply_now hL₁ hc', LendingLedger.apply_now h hc]; exact hp.now,
      by rw [LendingLedger.apply_numericType hL₁, LendingLedger.apply_numericType h]; exact hp.numericType,
      by rw [LendingLedger.apply_scale hL₁, LendingLedger.apply_scale h]; exact hp.scale,
      Or.inr ⟨by omega, Or.inr ⟨c, c', by rw [← hek]; exact hcb, by rw [← he'b]; exact hcb', hcr,
        (fun hE' => ?_)⟩⟩, ?_⟩
    · have hbc : b'.coverAvailable = b.coverAvailable :=
        Number.isNormalized.toRat_inj b'.wf.coverAvailable_norm b.wf.coverAvailable_norm (hE hE')
      rw [hcc hbc (hnc hE').1 (hnc hE').2]
    refine ⟨le_trans hp.loans.base_le hlen₂, by rw [hL₂len]; exact hLlen, fun j hj => ?_, fun j f hf hfk => ?_⟩
    · obtain ⟨h1, h2⟩ := hp.loans.created_mem j hj
      exact ⟨h1, by omega⟩
    have hslot' : ∀ j, j < l.loans.length → j ≠ i → l₂.loan? j = l.loan? j :=
      fun j hj hji => hslot j hj (by rw [hi]; simp [Ne.symm hji])
    have hLslot' : ∀ j, j < L.loans.length → j ≠ subLoanIndex base created i → L₂.loan? j = L.loan? j :=
      fun j hj hji => hLslot j hj (by rw [hi']; simp [Ne.symm hji])
    by_cases hji : j = i
    · subst hji
      rcases LendingLedger.loanTx_twin hp.reachable hp.reachable' he he' he'raw hp.now hp.numericType hfee tx hi h
        hL₁ with ⟨hn₁, -⟩ | ⟨g, g', hg, hg', -, hgb', hgr⟩
      · rw [hn₁] at hf
        cases hf
      · rw [hg] at hf
        obtain rfl := Option.some.inj hf
        exact ⟨g', hg', by rw [hgb', he'b], hgr⟩
    · exact hp.loans.twin_other hsi hl₂len hslot' hLslot' hji hf hfk
  · obtain ⟨L₁, hL₁, hs⟩ := LendingLedger.Reaches.cons_inv hs
    obtain rfl := LendingLedger.Reaches.nil_inv hs
    have hloans : l₂.loans = l.loans := (LendingLedger.broker_ops_scope_proof l l₂ tx hb h).1
    have hbL : (tx.withBroker k').isBroker = true := by rw [(LendingTx.withBroker_kind k' tx).2.1]; exact hb
    have hLloans : L₂.loans = L.loans := (LendingLedger.broker_ops_scope_proof L L₂ _ hbL hL₁).1
    have hc : ∀ t, tx ≠ .close t := by
      rintro t rfl
      cases hb
    have hc' : ∀ t, tx.withBroker k' ≠ .close t := by
      intro t h0
      rw [h0] at hbL
      cases hbL
    have hnow₂ : L₂.now = l₂.now := by
      rw [LendingLedger.apply_now hL₁ hc', LendingLedger.apply_now h hc]
      exact hp.now
    have hnt₂ : L₂.vault.numericType = l₂.vault.numericType := by
      rw [LendingLedger.apply_numericType hL₁, LendingLedger.apply_numericType h]
      exact hp.numericType
    have hsc₂ : L₂.vault.scale = l₂.vault.scale := by
      rw [LendingLedger.apply_scale hL₁, LendingLedger.apply_scale h]
      exact hp.scale
    rcases LendingLedger.apply_brokerTx_on h hb hk with ⟨ctx, rfl, hkl⟩ | ⟨b, hbk⟩
    · have hL : L.brokers.length = k' := by
        rcases hp.broker with ⟨-, hL⟩ | ⟨hlt, -⟩
        · exact hL
        · omega
      obtain ⟨nb, hnb, hnb', -, -, hl₂len⟩ := LendingLedger.brokerCreate_twin hp.numericType h hL₁
      exact ⟨hr₂, hp.reachable'.apply hL₁, hnow₂, hnt₂, hsc₂,
        Or.inr ⟨by omega, Or.inr ⟨nb, nb, by rw [hkl]; exact hnb, by rw [← hL]; exact hnb', rfl, fun _ => rfl⟩⟩,
        hp.loans.of_loans hloans hLloans⟩
    · obtain ⟨hklt, b', hb', hraw, hE⟩ := htw b hbk
      exact ⟨hr₂, hp.reachable'.apply hL₁, hnow₂, hnt₂, hsc₂,
        Or.inr ⟨by omega, hbtx hb hk b b' hbk hb' hraw hE hL₁⟩, hp.loans.of_loans hloans hLloans⟩

/-- What `LendingLedger.brokerTx_result_same` states: a broker transaction other than LoanBrokerCreate that succeeds
on two copies of a broker that differ at most in CoverAvailable leaves two such copies, with equal covers kept. -/
private def LendingLedger.BrokerResultsSame : Prop :=
  ∀ {l L lb Lb : LendingLedger} {k k' : Nat} {b b' : LoanBroker}, l.broker? k = some b → L.broker? k' = some b' →
    b'.toRawLoanBroker = { b.toRawLoanBroker with coverAvailable := b'.coverAvailable } →
    L.vault.numericType = l.vault.numericType → L.vault.scale = l.vault.scale →
    ∀ (tx : LendingTx), tx.isBroker = true → l.txBroker? tx = some k → (l.apply tx).run = .ok (.ok lb) →
    (L.apply (tx.withBroker k')).run = .ok (.ok Lb) →
    (lb.broker? k = none ∧ Lb.broker? k' = none) ∨ ∃ c c', lb.broker? k = some c ∧ Lb.broker? k' = some c' ∧
      c'.toRawLoanBroker = { c.toRawLoanBroker with coverAvailable := c'.coverAvailable } ∧
      (b'.coverAvailable.toRat = b.coverAvailable.toRat → c'.coverAvailable.toRat = c.coverAvailable.toRat)

/-- The pair holds along the whole sequence and its subsequence. While `E` holds neither run is coarsened. -/
private lemma LendingLedger.BPair.run (hR3 : LendingLedger.BrokerResultsSame) {E : Prop} {start : LendingLedger}
    {k k' base : Nat} {T S : List LendingTx} (hE : E → start.NotCoarsenedAlong T ∧ start.NotCoarsenedAlong S) :
    ∀ (rest : List LendingTx) {created : List Nat} {l L l₁ L₁ : LendingLedger} {p q : List LendingTx},
      LendingLedger.BPair E k k' base created l L → LendingLedger.Reaches start p l → p ++ rest = T →
      LendingLedger.Reaches start q L → q ++ l.brokerTxsFrom k k' base created rest = S →
      LendingLedger.Reaches l rest l₁ → LendingLedger.Reaches L (l.brokerTxsFrom k k' base created rest) L₁ →
      ∃ created₁, LendingLedger.BPair E k k' base created₁ l₁ L₁
  | [], created, _, _, _, _, _, _, hp, _, _, _, _, h, hs => by
    obtain rfl := LendingLedger.Reaches.nil_inv h
    obtain rfl := LendingLedger.Reaches.nil_inv hs
    exact ⟨created, hp⟩
  | tx :: rest, created, l, L, l₁, L₁, p, q, hp, hpl, hpT, hqL, hqS, h, hs => by
    obtain ⟨l₂, h₁, h₂⟩ := LendingLedger.Reaches.cons_inv h
    rw [LendingLedger.brokerTxsFrom_cons rest h₁] at hs hqS
    obtain ⟨L₂, hs₁, hs₂⟩ := LendingLedger.Reaches.split hs
    have hnc : E → l.NotCoarsened ∧ L.NotCoarsened := fun hE' =>
      ⟨(hE hE').1 p l ⟨_, hpT⟩ hpl, (hE hE').2 q L ⟨_, hqS⟩ hqL⟩
    have hp₂ := hp.step h₁ hs₁ hnc fun htx hk b b' hb hb' hraw hcov hL₂ => by
      rcases hR3 hb hb' hraw hp.numericType hp.scale tx htx hk h₁ hL₂ with hn | ⟨c, c', hc, hc', hcr, hcc⟩
      · exact Or.inl hn
      · exact Or.inr ⟨c, c', hc, hc', hcr, fun hE' => hcc (hcov hE')⟩
    exact LendingLedger.BPair.run hR3 hE rest hp₂ (LendingLedger.Reaches.step tx hpl h₁)
      (by rw [List.append_assoc]; exact hpT) (hqL.trans hs₁) (by rw [List.append_assoc]; exact hqS) h₂ hs₂

/-- Proof body of the fields part of `Lending.Reachable.broker_subsequence`: the broker ends with the same fields in the
sequence and in its subsequence but CoverAvailable, and the same cover too while neither run is coarsened. -/
lemma LendingLedger.broker_subsequence_fields_proof
    (hR2 : ∀ {l L lb Lb : LendingLedger} {k k' : Nat} {b b' : LoanBroker}, l.broker? k = some b →
      L.broker? k' = some b' → b'.toRawLoanBroker = { b.toRawLoanBroker with coverAvailable := b'.coverAvailable } →
      L.vault.numericType = l.vault.numericType → L.vault.scale = l.vault.scale →
      ∀ (tx : LendingTx), tx.isBroker = true → l.txBroker? tx = some k → (l.apply tx).run = .ok (.ok lb) →
      (L.apply (tx.withBroker k')).run = .ok (.ok Lb) →
      (lb.broker? k = none ∧ Lb.broker? k' = none) ∨ ∃ c c', lb.broker? k = some c ∧ Lb.broker? k' = some c' ∧
        c'.toRawLoanBroker = { c.toRawLoanBroker with coverAvailable := c'.coverAvailable } ∧
        (b'.coverAvailable.toRat = b.coverAvailable.toRat → c'.coverAvailable.toRat = c.coverAvailable.toRat))
    {start l m : LendingLedger} {txs : List LendingTx} {k : Nat} (hr : start.Reachable)
    (hrun : LendingLedger.Reaches start txs l)
    (hsub : LendingLedger.Reaches start (start.brokerSubsequence k txs) m) {b b' : LoanBroker}
    (hb : l.broker? k = some b) (hb' : m.broker? (start.aloneBrokerIndex k) = some b') :
    b'.toRawLoanBroker = { b.toRawLoanBroker with coverAvailable := b'.coverAvailable } ∧
      (start.NotCoarsenedAlong txs → start.NotCoarsenedAlong (start.brokerSubsequence k txs) →
        b'.coverAvailable.toRat = b.coverAvailable.toRat) := by
  obtain ⟨created, hp⟩ := LendingLedger.BPair.run hR2
    (E := start.NotCoarsenedAlong txs ∧ start.NotCoarsenedAlong (start.brokerSubsequence k txs)) id txs
    (LendingLedger.BPair.start hr _ k) .refl (List.nil_append _) .refl (List.nil_append _) hrun hsub
  rcases hp.broker with ⟨hle, -⟩ | ⟨-, ⟨hn, -⟩ | ⟨c, c', hc, hc', hcr, hcc⟩⟩
  · have := LendingLedger.broker?_lt hb
    omega
  · rw [hn] at hb
    cases hb
  · rw [hc] at hb
    rw [hc'] at hb'
    obtain rfl := Option.some.inj hb
    obtain rfl := Option.some.inj hb'
    exact ⟨hcr, fun h1 h2 => hcc ⟨h1, h2⟩⟩

/-- What `LendingLedger.loanTx_replay_twin_at` states: a LoanDelete, LoanManage or LoanPay that succeeded on a stored
loan succeeds on a twin stored on another reachable ledger, whose broker has the same management fee rate. -/
private def LendingLedger.LoanReplaysAt : Prop :=
  ∀ {l L lb : LendingLedger}, l.Reachable → L.Reachable → ∀ {j j' : Nat} {e e' : LoanEntry},
    l.loan? j = some e → L.loan? j' = some e' →
    e'.loan.toRawLoan = { e.loan.toRawLoan with broker := e'.loan.toRawLoan.broker } →
    L.now = l.now → L.vaultDeleted = false → L.vault.numericType = l.vault.numericType →
    (∀ b, l.broker? e.brokerIndex = some b →
      ∃ b', L.broker? e'.brokerIndex = some b' ∧ b'.managementFeeRate = b.managementFeeRate) →
    ∀ (tx : LendingTx), tx.loanIndex? = some j → (∀ k, tx ≠ .loanAccept k) →
    (l.apply tx).run = .ok (.ok lb) → L.NotCoarsened →
    (∀ b, L.broker? e'.brokerIndex = some b → b.coverAvailable.toRat < 10 ^ 96) →
    (∀ pt amount, tx = .loanPay j pt amount → L.CreditFits j' pt amount ∧ L.FeeFits j' pt amount) →
    ∃ L', (L.apply (tx.withLoan j')).run = .ok (.ok L')

/-- What `LendingLedger.brokerTx_replay_same` states: a broker transaction other than LoanBrokerCreate that succeeded
replays on an equal broker and leaves equal brokers. -/
private def LendingLedger.BrokerReplaysSame : Prop :=
  ∀ {l L lb : LendingLedger} {k k' : Nat} {b b' : LoanBroker}, l.broker? k = some b → L.broker? k' = some b' →
    b'.toRawLoanBroker = b.toRawLoanBroker → L.vaultDeleted = false →
    L.vault.numericType = l.vault.numericType → L.vault.scale = l.vault.scale →
    ∀ (tx : LendingTx), tx.isBroker = true → l.txBroker? tx = some k → (l.apply tx).run = .ok (.ok lb) →
    ∃ Lb, (L.apply (tx.withBroker k')).run = .ok (.ok Lb) ∧
      (lb.broker? k).map LoanBroker.toRawLoanBroker = (Lb.broker? k').map LoanBroker.toRawLoanBroker

/-- A LoanSet renumbered to another broker is still an opening. -/
private lemma LendingTx.loanSet_isOpening {tx : LendingTx} (hl : tx.isLoan = true) (hn : tx.loanIndex? = none)
    (k' : Nat) : (tx.withBroker k').isOpening = true := by
  cases tx <;> simp only [LendingTx.isLoan, LendingTx.loanIndex?, Bool.false_eq_true, reduceCtorEq] at hl hn
  rfl

/-- Every transaction the subsequence keeps from `l` on succeeds when its openings succeed, neither run is coarsened
and the balances the model does not track fit. -/
private lemma LendingLedger.BPair.success (hloan : LendingLedger.LoanReplaysAt)
    (hbroker : LendingLedger.BrokerReplaysSame) {start : LendingLedger} {k k' base : Nat} {T S : List LendingTx}
    (hopen : start.OpeningsSucceedAlong S) (hncT : start.NotCoarsenedAlong T) (hncS : start.NotCoarsenedAlong S)
    (hfit : start.BrokerUntrackedFitsAlong k' S) :
    ∀ (rest : List LendingTx) {created : List Nat} {l L l₁ : LendingLedger} {p q : List LendingTx},
      LendingLedger.BPair True k k' base created l L → LendingLedger.Reaches start p l → p ++ rest = T →
      LendingLedger.Reaches start q L → q ++ l.brokerTxsFrom k k' base created rest = S →
      LendingLedger.Reaches l rest l₁ → ∃ m, LendingLedger.Reaches start S m
  | [], created, l, L, _, _, q, _, _, _, hqL, hqS, _ => by
    have h0 : l.brokerTxsFrom k k' base created [] = [] := rfl
    rw [h0, List.append_nil] at hqS
    exact ⟨L, hqS ▸ hqL⟩
  | tx :: rest, created, l, L, l₁, p, q, hp, hpl, hpT, hqL, hqS, h => by
    obtain ⟨l₂, h₁, h₂⟩ := LendingLedger.Reaches.cons_inv h
    rw [LendingLedger.brokerTxsFrom_cons rest h₁] at hqS
    have hnc : True → l.NotCoarsened ∧ L.NotCoarsened := fun _ =>
      ⟨hncT p l ⟨_, hpT⟩ hpl, hncS q L ⟨_, hqS⟩ hqL⟩
    have hpre : ∀ tx', (l.brokerStep k k' base created tx).1 = [tx'] → q ++ [tx'] <+: S := fun tx' hk1 =>
      ⟨l₂.brokerTxsFrom k k' base (l.brokerStep k k' base created tx).2 rest, by
        rw [List.append_assoc, ← hk1]; exact hqS⟩
    have hopen' : ∀ tx', (l.brokerStep k k' base created tx).1 = [tx'] → tx'.isOpening = true →
        ∃ L₂, LendingLedger.Reaches L (l.brokerStep k k' base created tx).1 L₂ := fun tx' hk1 ho => by
      obtain ⟨m', hm'⟩ := hopen q L tx' (hpre tx' hk1) hqL ho
      exact ⟨m', by rw [hk1]; exact LendingLedger.Reaches.single hm'⟩
    have htw : ∀ b, l.broker? k = some b → ∃ b', L.broker? k' = some b' ∧
        b'.toRawLoanBroker = b.toRawLoanBroker := by
      intro b hb
      rcases hp.broker with ⟨hle, -⟩ | ⟨-, ⟨hn, -⟩ | ⟨b0, b0', hb0, hb0', hraw, hE⟩⟩
      · have := LendingLedger.broker?_lt hb
        omega
      · rw [hn] at hb
        cases hb
      · rw [hb] at hb0
        obtain rfl := Option.some.inj hb0
        exact ⟨b0', hb0', LoanBroker.raw_eq_of_cover hraw (hE trivial)⟩
    have hbtx : ∀ L₂', tx.isBroker = true → l.txBroker? tx = some k → ∀ b b', l.broker? k = some b →
        L.broker? k' = some b' → b'.toRawLoanBroker = { b.toRawLoanBroker with coverAvailable := b'.coverAvailable } →
        (True → b'.coverAvailable.toRat = b.coverAvailable.toRat) →
        (L.apply (tx.withBroker k')).run = .ok (.ok L₂') → LendingLedger.BrokerTwin True k k' l₂ L₂' := by
      intro L₂' htx hk b b' hb hb' hraw hcov hL₂
      obtain ⟨Lb, hLb, hmap⟩ := hbroker hb hb' (LoanBroker.raw_eq_of_cover hraw (hcov trivial))
        (hp.reachable'.live_of_broker hb') hp.numericType hp.scale tx htx hk h₁
      rw [hL₂] at hLb
      obtain rfl : L₂' = Lb := Except.ok.inj (Except.ok.inj hLb)
      unfold LendingLedger.BrokerTwin
      cases hc : l₂.broker? k with
      | none =>
        rw [hc, Option.map_none] at hmap
        exact Or.inl ⟨rfl, Option.map_eq_none_iff.mp hmap.symm⟩
      | some c =>
        rw [hc, Option.map_some] at hmap
        obtain ⟨c', hc', hcr⟩ := Option.map_eq_some_iff.mp hmap.symm
        refine Or.inr ⟨c, c', rfl, hc', by rw [hcr], fun _ => ?_⟩
        rw [show c'.coverAvailable = c'.toRawLoanBroker.coverAvailable from rfl, hcr]
    obtain ⟨L₂, hs⟩ : ∃ L₂, LendingLedger.Reaches L (l.brokerStep k k' base created tx).1 L₂ := by
      rcases LendingLedger.brokerStep_cases k k' base created l tx with ⟨hst, -, -⟩ | ⟨t, rfl, hst⟩ |
        ⟨hl, hn, -, hst⟩ | ⟨i, hi, hk, hst⟩ | ⟨hb, hk, hst⟩
      · exact ⟨L, by rw [hst]; exact .refl⟩
      · exact ⟨_, by rw [hst]; exact LendingLedger.Reaches.single (LendingLedger.apply_close L t)⟩
      · exact hopen' _ (by rw [hst]) (LendingTx.loanSet_isOpening hl hn k')
      · by_cases hacc : ∃ j, tx = .loanAccept j
        · obtain ⟨j, rfl⟩ := hacc
          exact hopen' _ (by rw [hst]) rfl
        have hacc' : ∀ j, tx ≠ .loanAccept j := fun j hj => hacc ⟨j, hj⟩
        obtain ⟨e, he⟩ := LendingLedger.apply_named_loan h₁ hi
        have hek := LendingLedger.named_loan_broker hi he hk
        obtain ⟨e', he', he'b, he'raw⟩ := hp.loans.twin i e he hek
        have hpre' := hpre _ (by rw [hst])
        obtain ⟨hca, hfits⟩ := hfit q L _ hpre' hqL
        obtain ⟨L₂, hL₂⟩ := hloan hp.reachable hp.reachable' he he' he'raw hp.now
          (hp.reachable'.live_of_loan he') hp.numericType
          (fun b hb => by
            rw [hek] at hb
            obtain ⟨b', hb', hraw⟩ := htw b hb
            exact ⟨b', by rw [he'b]; exact hb', (congrArg RawLoanBroker.managementFeeRate hraw :)⟩)
          tx hi hacc' h₁ (hncS q L ⟨_, hqS⟩ hqL) (fun b hb => hca b (by rw [← he'b]; exact hb))
          (fun pt amount htx => by subst htx; exact hfits _ pt amount rfl)
        exact ⟨L₂, by rw [hst]; exact LendingLedger.Reaches.single hL₂⟩
      · rcases LendingLedger.apply_brokerTx_on h₁ hb hk with ⟨ctx, rfl, -⟩ | ⟨b, hbk⟩
        · exact hopen' _ (by rw [hst]) rfl
        · obtain ⟨b', hb', hraw⟩ := htw b hbk
          obtain ⟨Lb, hLb, -⟩ := hbroker hbk hb' hraw (hp.reachable'.live_of_broker hb') hp.numericType hp.scale
            tx hb hk h₁
          exact ⟨Lb, by rw [hst]; exact LendingLedger.Reaches.single hLb⟩
    have hp₂ := hp.step h₁ hs hnc (hbtx L₂)
    exact LendingLedger.BPair.success hloan hbroker hopen hncT hncS hfit rest hp₂
      (LendingLedger.Reaches.step tx hpl h₁) (by rw [List.append_assoc]; exact hpT) (hqL.trans hs)
      (by rw [List.append_assoc]; exact hqS) h₂

/-- Proof body of the success part of `Lending.Reachable.broker_subsequence`, with the one-step replays of
`LendingLedger.loanTx_replay_twin_at` as `hloan` and `LendingLedger.brokerTx_replay_same` as `hbroker`. -/
lemma LendingLedger.broker_subsequence_success_of_replay
    (hloan : ∀ {l L lb : LendingLedger}, l.Reachable → L.Reachable → ∀ {j j' : Nat} {e e' : LoanEntry},
      l.loan? j = some e → L.loan? j' = some e' →
      e'.loan.toRawLoan = { e.loan.toRawLoan with broker := e'.loan.toRawLoan.broker } →
      L.now = l.now → L.vaultDeleted = false → L.vault.numericType = l.vault.numericType →
      (∀ b, l.broker? e.brokerIndex = some b →
        ∃ b', L.broker? e'.brokerIndex = some b' ∧ b'.managementFeeRate = b.managementFeeRate) →
      ∀ (tx : LendingTx), tx.loanIndex? = some j → (∀ k, tx ≠ .loanAccept k) →
      (l.apply tx).run = .ok (.ok lb) → L.NotCoarsened →
      (∀ b, L.broker? e'.brokerIndex = some b → b.coverAvailable.toRat < 10 ^ 96) →
      (∀ pt amount, tx = .loanPay j pt amount → L.CreditFits j' pt amount ∧ L.FeeFits j' pt amount) →
      ∃ L', (L.apply (tx.withLoan j')).run = .ok (.ok L'))
    (hbroker : ∀ {l L lb : LendingLedger} {k k' : Nat} {b b' : LoanBroker}, l.broker? k = some b →
      L.broker? k' = some b' → b'.toRawLoanBroker = b.toRawLoanBroker → L.vaultDeleted = false →
      L.vault.numericType = l.vault.numericType → L.vault.scale = l.vault.scale →
      ∀ (tx : LendingTx), tx.isBroker = true → l.txBroker? tx = some k → (l.apply tx).run = .ok (.ok lb) →
      ∃ Lb, (L.apply (tx.withBroker k')).run = .ok (.ok Lb) ∧
        (lb.broker? k).map LoanBroker.toRawLoanBroker = (Lb.broker? k').map LoanBroker.toRawLoanBroker)
    {start l : LendingLedger} {txs : List LendingTx} {k : Nat} (hr : start.Reachable)
    (hrun : LendingLedger.Reaches start txs l) :
    start.OpeningsSucceedAlong (start.brokerSubsequence k txs) → start.NotCoarsenedAlong txs →
      start.NotCoarsenedAlong (start.brokerSubsequence k txs) →
      start.BrokerUntrackedFitsAlong (start.aloneBrokerIndex k) (start.brokerSubsequence k txs) →
      ∃ m, LendingLedger.Reaches start (start.brokerSubsequence k txs) m := fun hopen hncT hncS hfit =>
  LendingLedger.BPair.success hloan hbroker hopen hncT hncS hfit txs (LendingLedger.BPair.start hr True k) .refl
    (List.nil_append _) .refl (List.nil_append _) hrun

end XRPL.Model.Lending
