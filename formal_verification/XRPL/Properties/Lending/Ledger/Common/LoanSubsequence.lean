import XRPL.Properties.Lending.Ledger.Common.LoanSubsequenceTwin
import XRPL.Properties.Lending.Loan.Common.PayLedger

/-! # One loan's transactions alone

Loan `i` in a sequence of transactions from a reachable ledger, and the same loan in the subsequence of its own
transactions, renumbered to `i'`: on both it is not created yet, deleted, or stored as twins, the same loan but for
the copy of its broker. So its fields end the same in both. Once it is active, every later transaction on it that
succeeds in the sequence succeeds in the subsequence as well, when such a transaction replays on a twin. -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol

open private LendingLedger.apply_scale LendingLedger.apply_now LendingLedger.apply_close
  LendingLedger.apply_feeRate LendingLedger.apply_brokers_length_eq LendingLedger.apply_loans
  LendingLedger.apply_named_loan LendingLedger.loanTx_twin LendingLedger.loanSet_twin
  LendingLedger.accept_pending LendingLedger.apply_keeps_active
  from XRPL.Properties.Lending.Ledger.Common.LoanSubsequenceTwin
open private LendingLedger.apply_brokers_length from XRPL.Properties.Lending.Ledger.Common.BrokerAccounting

/-- Loan `i` of the sequence's ledger `l` and loan `i'` of the subsequence's ledger `L`: not created on either,
or created on both and then deleted on both or stored as twins. -/
private def LendingLedger.LoanPair (i i' : Nat) (l L : LendingLedger) : Prop :=
  (l.loans.length ≤ i ∧ L.loans.length = i') ∨
    (i < l.loans.length ∧ ((l.loan? i = none ∧ L.loan? i' = none) ∨
      ∃ e e', l.loan? i = some e ∧ L.loan? i' = some e' ∧ e'.brokerIndex = e.brokerIndex ∧
        e'.loan.toRawLoan = { e.loan.toRawLoan with broker := e'.loan.toRawLoan.broker }))

/-- What the subsequence's ledger `L` shares with the sequence's ledger `l` apart from the close time and the loan:
the vault's asset and scale, and the management fee rate of every broker it holds. -/
private structure LendingLedger.SubFrame (l L : LendingLedger) : Prop where
  numericType : L.vault.numericType = l.vault.numericType
  scale : L.vault.scale = l.vault.scale
  brokers : L.brokers.length ≤ l.brokers.length
  fee : ∀ k b b', l.broker? k = some b → L.broker? k = some b' → b'.managementFeeRate = b.managementFeeRate

/-- The sequence's ledger `l` and the subsequence's ledger `L`, both reachable, at the same close time, with the
same vault settings and broker fee rates, and loan `i` of `l` paired with loan `i'` of `L`. -/
private structure LendingLedger.SubPair (i i' : Nat) (l L : LendingLedger) : Prop where
  reachable : l.Reachable
  reachable' : L.Reachable
  now : L.now = l.now
  frame : LendingLedger.SubFrame l L
  loan : LendingLedger.LoanPair i i' l L

/-- A transaction of the sequence keeps the frame. -/
private lemma LendingLedger.SubFrame.full_step {l L l₂ : LendingLedger} {tx : LendingTx}
    (hf : LendingLedger.SubFrame l L) (h : (l.apply tx).run = .ok (.ok l₂)) : LendingLedger.SubFrame l₂ L := by
  refine ⟨by rw [LendingLedger.apply_numericType h]; exact hf.numericType,
    by rw [LendingLedger.apply_scale h]; exact hf.scale,
    le_trans hf.brokers (LendingLedger.apply_brokers_length h), fun k b2 b' hb2 hb' => ?_⟩
  rcases LendingLedger.apply_feeRate h hb2 with hk | ⟨b, hb, hm⟩
  · have := LendingLedger.broker?_lt hb'
    have := hf.brokers
    omega
  · rw [hm]; exact hf.fee k b b' hb hb'

/-- A loan transaction or a close on the subsequence's ledger keeps the frame. -/
private lemma LendingLedger.SubFrame.sub_step {l L L₂ : LendingLedger} {tx : LendingTx}
    (hf : LendingLedger.SubFrame l L) (h : (L.apply tx).run = .ok (.ok L₂))
    (hk : tx.isLoan = true ∨ ∃ t, tx = .close t) : LendingLedger.SubFrame l L₂ := by
  have hlen := LendingLedger.apply_brokers_length_eq h hk
  refine ⟨by rw [LendingLedger.apply_numericType h]; exact hf.numericType,
    by rw [LendingLedger.apply_scale h]; exact hf.scale, by rw [hlen]; exact hf.brokers, fun k b b2 hb hb2 => ?_⟩
  rcases LendingLedger.apply_feeRate h hb2 with hk | ⟨b', hb', hm⟩
  · have := LendingLedger.broker?_lt hb2
    omega
  · rw [hm]; exact hf.fee k b b' hb hb'

/-- What `loanTxsFrom` keeps of one transaction run on `l`. -/
private def LendingLedger.keptTx (i i' : Nat) (l : LendingLedger) (tx : LendingTx) : List LendingTx :=
  match tx with
  | .close _ => [tx]
  | .loanSet .. => if l.loans.length = i then [tx] else []
  | _ => if tx.loanIndex? = some i then [tx.withLoan i'] else []

/-- After a transaction that succeeds, `loanTxsFrom` keeps its part of it and goes on from the ledger it leaves. -/
private lemma LendingLedger.loanTxsFrom_cons {i i' : Nat} {l l' : LendingLedger} {tx : LendingTx}
    (txs : List LendingTx) (h : (l.apply tx).run = .ok (.ok l')) :
    l.loanTxsFrom i i' (tx :: txs) = l.keptTx i i' tx ++ l'.loanTxsFrom i i' txs := by
  rw [LendingLedger.loanTxsFrom.eq_def]
  dsimp only
  rw [h]
  cases tx <;> rfl

/-- `loanTxsFrom` drops a transaction, keeps a close, keeps the LoanSet of loan `i`, or keeps a transaction on
loan `i` renumbered. -/
private lemma LendingLedger.keptTx_cases (i i' : Nat) (l : LendingLedger) (tx : LendingTx) :
    (l.keptTx i i' tx = [] ∧ (∀ t, tx ≠ .close t) ∧ tx.loanIndex? ≠ some i ∧
        (tx.isLoan = true → tx.loanIndex? = none → l.loans.length ≠ i)) ∨
      (∃ t, tx = .close t ∧ l.keptTx i i' tx = [tx]) ∨
      (tx.isLoan = true ∧ tx.loanIndex? = none ∧ l.loans.length = i ∧ l.keptTx i i' tx = [tx]) ∨
      (tx.loanIndex? = some i ∧ l.keptTx i i' tx = [tx.withLoan i']) := by
  cases tx with
  | close t => exact Or.inr (Or.inl ⟨t, rfl, rfl⟩)
  | loanSet =>
    by_cases h : l.loans.length = i
    · exact Or.inr (Or.inr (Or.inl ⟨rfl, rfl, h, by simp [LendingLedger.keptTx, h]⟩))
    · exact Or.inl ⟨by simp [LendingLedger.keptTx, h], fun t => by simp, by simp [LendingTx.loanIndex?],
        fun _ _ => h⟩
  | loanAccept j | loanDelete j | loanManage j _ | loanPay j _ _ =>
    by_cases h : j = i
    · subst h
      exact Or.inr (Or.inr (Or.inr ⟨rfl, by simp [LendingLedger.keptTx, LendingTx.loanIndex?]⟩))
    · exact Or.inl ⟨by simp [LendingLedger.keptTx, LendingTx.loanIndex?, h], fun t => by simp,
        by simp [LendingTx.loanIndex?, h], fun _ h0 => by simp [LendingTx.loanIndex?] at h0⟩
  | _ =>
    exact Or.inl ⟨by simp [LendingLedger.keptTx, LendingTx.loanIndex?], fun t => by simp,
      by simp [LendingTx.loanIndex?], fun h0 => by simp [LendingTx.isLoan] at h0⟩

/-- A run splits into its first transactions and the rest. -/
private lemma LendingLedger.Reaches.split {start l : LendingLedger} :
    ∀ {pre post : List LendingTx}, LendingLedger.Reaches start (pre ++ post) l →
      ∃ m, LendingLedger.Reaches start pre m ∧ LendingLedger.Reaches m post l
  | [], _, h => ⟨start, .refl, by simpa using h⟩
  | tx :: pre, post, h => by
    obtain ⟨s₁, h₁, h₂⟩ := LendingLedger.Reaches.cons_inv h
    obtain ⟨m, hm₁, hm₂⟩ := LendingLedger.Reaches.split (start := s₁) (pre := pre) h₂
    exact ⟨m, (LendingLedger.Reaches.single h₁).trans hm₁, hm₂⟩

/-- `loanTxsFrom` of a run in two parts is its first part followed by the second part from where the first ends. -/
private lemma LendingLedger.loanTxsFrom_append {i i' : Nat} (post : List LendingTx) :
    ∀ {l l₁ : LendingLedger} {pre : List LendingTx}, LendingLedger.Reaches l pre l₁ →
      l.loanTxsFrom i i' (pre ++ post) = l.loanTxsFrom i i' pre ++ l₁.loanTxsFrom i i' post
  | l, l₁, [], h => by
    obtain rfl := h.nil_inv
    rfl
  | l, l₁, tx :: pre, h => by
    obtain ⟨s₁, h₁, h₂⟩ := LendingLedger.Reaches.cons_inv h
    rw [List.cons_append, LendingLedger.loanTxsFrom_cons _ h₁, LendingLedger.loanTxsFrom_cons _ h₁,
      LendingLedger.loanTxsFrom_append post h₂, List.append_assoc]

/-- The ledger with itself: loan `i` keeps its number when it is stored, else it gets the next free slot. -/
private lemma LendingLedger.SubPair.start {start : LendingLedger} (hr : start.Reachable) (i : Nat) :
    LendingLedger.SubPair i (start.aloneIndex i) start start := by
  refine ⟨hr, hr, rfl, ⟨rfl, rfl, le_refl _, fun k b b' hb hb' => ?_⟩, ?_⟩
  · rw [hb] at hb'
    obtain rfl := Option.some.inj hb'
    rfl
  · unfold LendingLedger.LoanPair LendingLedger.aloneIndex
    by_cases hi : i < start.loans.length
    · rw [min_eq_left hi.le]
      refine Or.inr ⟨hi, ?_⟩
      cases he : start.loan? i with
      | none => exact Or.inl ⟨rfl, rfl⟩
      | some e => exact Or.inr ⟨e, e, rfl, rfl, rfl, rfl⟩
    · rw [min_eq_right (by omega)]
      exact Or.inl ⟨by omega, rfl⟩

/-- One transaction of the sequence, with the part of it the subsequence keeps, keeps the pair. -/
private lemma LendingLedger.SubPair.step {i i' : Nat} {l L l₂ L₂ : LendingLedger} {tx : LendingTx}
    (hp : LendingLedger.SubPair i i' l L) (h : (l.apply tx).run = .ok (.ok l₂))
    (hs : LendingLedger.Reaches L (l.keptTx i i' tx) L₂) : LendingLedger.SubPair i i' l₂ L₂ := by
  have hr₂ := hp.reachable.apply h
  obtain ⟨hlen, hslot⟩ := LendingLedger.apply_loans h
  rcases LendingLedger.keptTx_cases i i' l tx with ⟨hk, hc, hj, hset⟩ | ⟨t, rfl, hk⟩ | ⟨hl, hn, hli, hk⟩ |
    ⟨hj, hk⟩
  · rw [hk] at hs
    obtain rfl := LendingLedger.Reaches.nil_inv hs
    refine ⟨hr₂, hp.reachable', by rw [LendingLedger.apply_now h hc]; exact hp.now, hp.frame.full_step h, ?_⟩
    rcases hp.loan with ⟨hle, hL⟩ | ⟨hlt, hpair⟩
    · refine Or.inl ⟨?_, hL⟩
      rcases hlen with h1 | ⟨h1, hl, hn⟩
      · omega
      · have := hset hl hn
        omega
    · refine Or.inr ⟨by rcases hlen with h1 | ⟨h1, -⟩ <;> omega, ?_⟩
      rw [hslot i hlt hj]
      exact hpair
  · rw [hk] at hs
    obtain ⟨L₁, hL₁, hs⟩ := LendingLedger.Reaches.cons_inv hs
    obtain rfl := LendingLedger.Reaches.nil_inv hs
    have e1 := (LendingLedger.apply_close l t).symm.trans h
    have e2 := (LendingLedger.apply_close L t).symm.trans hL₁
    injection e1 with e1
    injection e1 with e1
    injection e2 with e2
    injection e2 with e2
    subst e1 e2
    exact ⟨hr₂, hp.reachable'.apply hL₁, by show max L.now t = max l.now t; rw [hp.now],
      ⟨hp.frame.numericType, hp.frame.scale, hp.frame.brokers, hp.frame.fee⟩, hp.loan⟩
  · rw [hk] at hs
    obtain ⟨L₁, hL₁, hs⟩ := LendingLedger.Reaches.cons_inv hs
    obtain rfl := LendingLedger.Reaches.nil_inv hs
    have hc : ∀ t, tx ≠ .close t := by
      rintro t rfl
      simp [LendingTx.isLoan] at hl
    have hpair : L.loans.length = i' := by
      rcases hp.loan with ⟨-, hL⟩ | ⟨hlt, -⟩
      · exact hL
      · omega
    obtain ⟨f, f', hf, hf', hbi, hraw⟩ := LendingLedger.loanSet_twin hp.reachable hp.reachable' hp.now
      hp.frame.numericType hp.frame.scale hp.frame.fee ⟨hl, hn⟩ h hL₁
    rw [hli] at hf
    rw [hpair] at hf'
    refine ⟨hr₂, hp.reachable'.apply hL₁,
      by rw [LendingLedger.apply_now hL₁ hc, LendingLedger.apply_now h hc]; exact hp.now,
      (hp.frame.full_step h).sub_step hL₁ (Or.inl hl),
      Or.inr ⟨LendingLedger.loan?_lt hf, Or.inr ⟨f, f', hf, hf', hbi, hraw⟩⟩⟩
  · rw [hk] at hs
    obtain ⟨L₁, hL₁, hs⟩ := LendingLedger.Reaches.cons_inv hs
    obtain rfl := LendingLedger.Reaches.nil_inv hs
    obtain ⟨e, he⟩ := LendingLedger.apply_named_loan h hj
    have hc : ∀ t, tx ≠ .close t := by
      rintro t rfl
      simp [LendingTx.loanIndex?] at hj
    have hl' : (tx.withLoan i').isLoan = true := by
      cases tx <;> simp_all [LendingTx.loanIndex?, LendingTx.withLoan, LendingTx.isLoan]
    have hc' : ∀ t, tx.withLoan i' ≠ .close t := by
      intro t h0
      rw [h0] at hl'
      simp [LendingTx.isLoan] at hl'
    rcases hp.loan with ⟨hle, -⟩ | ⟨hlt, ⟨hn, -⟩ | ⟨e1, e', he1, he', hbi, hraw⟩⟩
    · have := LendingLedger.loan?_lt he
      omega
    · rw [hn] at he
      cases he
    · rw [he] at he1
      obtain rfl := Option.some.inj he1
      refine ⟨hr₂, hp.reachable'.apply hL₁,
        by rw [LendingLedger.apply_now hL₁ hc', LendingLedger.apply_now h hc]; exact hp.now,
        (hp.frame.full_step h).sub_step hL₁ (Or.inl hl'),
        Or.inr ⟨by rcases hlen with h1 | ⟨h1, -⟩ <;> omega, ?_⟩⟩
      rcases LendingLedger.loanTx_twin hp.reachable hp.reachable' he he' hraw hp.now hp.frame.numericType
        (fun b b' hb hb' => hp.frame.fee _ b b' hb (by rw [← hbi]; exact hb')) tx hj h hL₁ with
        hn | ⟨f, f', hf, hf', hfb, hfb', hfr⟩
      · exact Or.inl hn
      · exact Or.inr ⟨f, f', hf, hf', by rw [hfb', hfb, hbi], hfr⟩

/-- The pair holds along the whole sequence and its subsequence. -/
private lemma LendingLedger.SubPair.run {i i' : Nat} : ∀ (txs : List LendingTx) {l L l₁ L₁ : LendingLedger},
    LendingLedger.SubPair i i' l L → LendingLedger.Reaches l txs l₁ →
    LendingLedger.Reaches L (l.loanTxsFrom i i' txs) L₁ → LendingLedger.SubPair i i' l₁ L₁
  | [], _, _, _, _, hp, h, hs => by
    obtain rfl := LendingLedger.Reaches.nil_inv h
    obtain rfl := LendingLedger.Reaches.nil_inv hs
    exact hp
  | tx :: txs, _, _, _, _, hp, h, hs => by
    obtain ⟨l₂, h₁, h₂⟩ := LendingLedger.Reaches.cons_inv h
    rw [LendingLedger.loanTxsFrom_cons txs h₁] at hs
    obtain ⟨L₂, hs₁, hs₂⟩ := LendingLedger.Reaches.split hs
    exact LendingLedger.SubPair.run txs (hp.step h₁ hs₁) h₂ hs₂

/-- Proof body of the fields part of `Lending.Reachable.loan_subsequence`: the loan ends with the same fields in the
sequence and in its subsequence, but for the copy of its broker. -/
lemma LendingLedger.loan_subsequence_fields_proof {start l m : LendingLedger} {txs : List LendingTx} {i : Nat}
    (hr : start.Reachable) (hrun : LendingLedger.Reaches start txs l)
    (hsub : LendingLedger.Reaches start (start.loanSubsequence i txs) m) {loan loan' : Loan}
    (hat : l.LoanAt i loan) (hat' : m.LoanAt (start.aloneIndex i) loan') :
    loan'.toRawLoan = { loan.toRawLoan with broker := loan'.toRawLoan.broker } := by
  have hp := LendingLedger.SubPair.run txs (LendingLedger.SubPair.start hr i) hrun hsub
  obtain ⟨e0, b, he0, -, hw⟩ := hat
  obtain ⟨e0', b', he0', -, hw'⟩ := hat'
  rcases hp.loan with ⟨hle, -⟩ | ⟨-, ⟨hn, -⟩ | ⟨e, e', he, he', -, hraw⟩⟩
  · have := LendingLedger.loan?_lt he0
    omega
  · rw [hn] at he0
    cases he0
  · rw [he] at he0
    rw [he'] at he0'
    obtain rfl := Option.some.inj he0
    obtain rfl := Option.some.inj he0'
    rw [Loan.withBroker_eq hw', Loan.withBroker_eq hw, hraw]

/-- What `LendingLedger.loanTx_replay_twin` states: a LoanDelete, LoanManage or LoanPay that succeeded on a stored
loan succeeds on a twin stored on another reachable ledger. -/
private def LendingLedger.ReplaysOnTwin : Prop :=
  ∀ {l L lb : LendingLedger}, l.Reachable → L.Reachable → ∀ {j j' : Nat} {e e' : LoanEntry},
    l.loan? j = some e → L.loan? j' = some e' → e'.brokerIndex = e.brokerIndex →
    e'.loan.toRawLoan = { e.loan.toRawLoan with broker := e'.loan.toRawLoan.broker } →
    L.now = l.now → L.vaultDeleted = false → L.vault.numericType = l.vault.numericType →
    (∀ b, l.broker? e.brokerIndex = some b →
      ∃ b', L.broker? e.brokerIndex = some b' ∧ b'.managementFeeRate = b.managementFeeRate) →
    ∀ (tx : LendingTx), tx.loanIndex? = some j → (∀ k, tx ≠ .loanAccept k) →
    (l.apply tx).run = .ok (.ok lb) → L.NotCoarsened →
    (∀ b, L.broker? e.brokerIndex = some b → b.coverAvailable.toRat < 10 ^ 96) →
    (∀ pt amount, tx = .loanPay j pt amount → L.CreditFits j' pt amount ∧ L.FeeFits j' pt amount) →
    ∃ L', (L.apply (tx.withLoan j')).run = .ok (.ok L')

/-- Once loan `i` is created and not pending, every transaction the subsequence keeps from `l` on succeeds. -/
private lemma LendingLedger.SubPair.success (hreplay : LendingLedger.ReplaysOnTwin) {start : LendingLedger}
    {i i' : Nat} {sub : List LendingTx} (hnc : start.NotCoarsenedAlong sub)
    (hfit : start.UntrackedFitsAlong i' sub) :
    ∀ (post : List LendingTx) {l L l₁ : LendingLedger} {q : List LendingTx}, LendingLedger.SubPair i i' l L →
      i < l.loans.length → (∀ e, l.loan? i = some e → e.loan.isPending = false) →
      LendingLedger.Reaches l post l₁ → LendingLedger.Reaches start q L → q ++ l.loanTxsFrom i i' post = sub →
      ∃ m, LendingLedger.Reaches start sub m
  | [], _, L, _, _, _, _, _, _, hq, hsub => ⟨L, by rw [← hsub]; exact (List.append_nil _).symm ▸ hq⟩
  | tx :: post, l, L, l₁, q, hp, hlt, hact, h, hq, hsub => by
    obtain ⟨l₂, h₁, h₂⟩ := LendingLedger.Reaches.cons_inv h
    rw [LendingLedger.loanTxsFrom_cons post h₁] at hsub
    obtain ⟨hlen, hslot⟩ := LendingLedger.apply_loans h₁
    have hlt₂ : i < l₂.loans.length := by rcases hlen with h1 | ⟨h1, -⟩ <;> omega
    have hkeep : tx.loanIndex? ≠ some i → ∀ e, l₂.loan? i = some e → e.loan.isPending = false := by
      intro hj e he
      rw [hslot i hlt hj] at he
      exact hact e he
    rcases LendingLedger.keptTx_cases i i' l tx with ⟨hk, -, hj, -⟩ | ⟨t, rfl, hk⟩ | ⟨-, -, hli, -⟩ | ⟨hj, hk⟩
    · rw [hk, List.nil_append] at hsub
      exact LendingLedger.SubPair.success hreplay hnc hfit post (hp.step h₁ (by rw [hk]; exact .refl)) hlt₂
        (hkeep hj) h₂ hq hsub
    · rw [hk] at hsub
      have hL := LendingLedger.apply_close L t
      exact LendingLedger.SubPair.success hreplay hnc hfit post
        (hp.step h₁ (by rw [hk]; exact LendingLedger.Reaches.single hL)) hlt₂
        (hkeep (by simp [LendingTx.loanIndex?])) h₂ (LendingLedger.Reaches.step _ hq hL)
        (by rw [List.append_assoc]; exact hsub)
    · omega
    · rw [hk] at hsub
      obtain ⟨e, he⟩ := LendingLedger.apply_named_loan h₁ hj
      rcases hp.loan with ⟨hle, -⟩ | ⟨-, ⟨hn, -⟩ | ⟨e1, e', he1, he', hbi, hraw⟩⟩
      · omega
      · rw [hn] at he
        cases he
      rw [he] at he1
      obtain rfl := Option.some.inj he1
      have hacc : ∀ k, tx ≠ .loanAccept k := by
        rintro k rfl
        simp only [LendingTx.loanIndex?, Option.some.injEq] at hj
        subst hj
        have := LendingLedger.accept_pending he h₁
        rw [hact e he] at this
        cases this
      obtain ⟨B, hB⟩ := hp.reachable'.loanCountInv.broker_of_loan he'
      rw [hbi] at hB
      have hpre : q <+: sub := ⟨_, hsub⟩
      have hpre' : q ++ [tx.withLoan i'] <+: sub :=
        ⟨l₂.loanTxsFrom i i' post, by rw [List.append_assoc]; exact hsub⟩
      obtain ⟨hca, hfits⟩ := hfit q L (tx.withLoan i') hpre' hq
      obtain ⟨L₂, hL₂⟩ := hreplay hp.reachable hp.reachable' he he' hbi hraw hp.now
        (hp.reachable'.live_of_loan he') hp.frame.numericType
        (fun b hb => ⟨B, hB, hp.frame.fee _ b B hb hB⟩) tx hj hacc h₁ (hnc q L hpre hq)
        (fun b hb => hca e' b he' (by rw [hbi]; exact hb))
        (fun pt amount htx => by subst htx; exact hfits pt amount rfl)
      exact LendingLedger.SubPair.success hreplay hnc hfit post
        (hp.step h₁ (by rw [hk]; exact LendingLedger.Reaches.single hL₂)) hlt₂
        (LendingLedger.apply_keeps_active h₁ hj hacc hact) h₂ (LendingLedger.Reaches.step _ hq hL₂)
        (by rw [List.append_assoc]; exact hsub)

/-- Proof body of the success part of `Lending.Reachable.loan_subsequence`, with the one-step replay of
`LendingLedger.loanTx_replay_twin` as `hreplay`. -/
lemma LendingLedger.loan_subsequence_success_of_replay
    (hreplay : ∀ {l L lb : LendingLedger}, l.Reachable → L.Reachable → ∀ {j j' : Nat} {e e' : LoanEntry},
      l.loan? j = some e → L.loan? j' = some e' → e'.brokerIndex = e.brokerIndex →
      e'.loan.toRawLoan = { e.loan.toRawLoan with broker := e'.loan.toRawLoan.broker } →
      L.now = l.now → L.vaultDeleted = false → L.vault.numericType = l.vault.numericType →
      (∀ b, l.broker? e.brokerIndex = some b →
        ∃ b', L.broker? e.brokerIndex = some b' ∧ b'.managementFeeRate = b.managementFeeRate) →
      ∀ (tx : LendingTx), tx.loanIndex? = some j → (∀ k, tx ≠ .loanAccept k) →
      (l.apply tx).run = .ok (.ok lb) → L.NotCoarsened →
      (∀ b, L.broker? e.brokerIndex = some b → b.coverAvailable.toRat < 10 ^ 96) →
      (∀ pt amount, tx = .loanPay j pt amount → L.CreditFits j' pt amount ∧ L.FeeFits j' pt amount) →
      ∃ L', (L.apply (tx.withLoan j')).run = .ok (.ok L'))
    {start l : LendingLedger} {txs : List LendingTx} {i : Nat} (hr : start.Reachable)
    (hrun : LendingLedger.Reaches start txs l) :
    ∀ (pre post : List LendingTx) (m : LendingLedger) (loan : Loan), txs = pre ++ post →
      LendingLedger.Reaches start (start.loanSubsequence i pre) m → m.LoanAt (start.aloneIndex i) loan →
      loan.isPending = false → start.NotCoarsenedAlong (start.loanSubsequence i txs) →
      start.UntrackedFitsAlong (start.aloneIndex i) (start.loanSubsequence i txs) →
      ∃ m', LendingLedger.Reaches start (start.loanSubsequence i txs) m' := by
  intro pre post m loan htxs hm hat hpend hnc hfit
  subst htxs
  obtain ⟨l₁, h₁, h₂⟩ := LendingLedger.Reaches.split hrun
  have hp := LendingLedger.SubPair.run pre (LendingLedger.SubPair.start hr i) h₁ hm
  have happ : start.loanSubsequence i (pre ++ post) =
      start.loanSubsequence i pre ++ l₁.loanTxsFrom i (start.aloneIndex i) post :=
    LendingLedger.loanTxsFrom_append post h₁
  obtain ⟨e0', b', he0', -, hw'⟩ := hat
  rcases hp.loan with ⟨-, hL⟩ | ⟨hlt, ⟨-, hn⟩ | ⟨e, e', he, he', -, hraw⟩⟩
  · have := LendingLedger.loan?_lt he0'
    omega
  · rw [hn] at he0'
    cases he0'
  rw [he'] at he0'
  obtain rfl := Option.some.inj he0'
  have hact : ∀ f, l₁.loan? i = some f → f.loan.isPending = false := by
    intro f hf
    rw [he] at hf
    cases hf
    have h1 : loan.isPending = e'.loan.isPending := (congrArg RawLoan.isPending (Loan.withBroker_eq hw') :)
    have h2 : e'.loan.isPending = e.loan.isPending := (congrArg RawLoan.isPending hraw :)
    rw [← h2, ← h1, hpend]
  exact LendingLedger.SubPair.success hreplay hnc hfit post hp hlt hact h₂ hm happ.symm

end XRPL.Model.Lending
