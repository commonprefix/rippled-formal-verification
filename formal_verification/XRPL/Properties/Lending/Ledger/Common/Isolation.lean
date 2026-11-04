import XRPL.Properties.Lending.Ledger.Common.IsolationDefs
import XRPL.Properties.Lending.Ledger.Common.PayReplay
import XRPL.Properties.Lending.Ledger.Common.BrokerSteps

/-! # Isolation of loan transactions

A transaction on one loan or broker leaves another loan as it was and gives its broker back with the same terms.
So a transaction on the other loan that succeeded before succeeds after it as well, while a LoanAccept still fits
the Open limit and the vault is not coarsened. -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault (Vault RawVault)

/-- A release of a loan keeps the broker's management fee rate. -/
private lemma LoanBroker.releaseLoan_rate (lb lb' : LoanBroker) (d : Number) (h : lb.releaseLoan d = .ok lb') :
    lb'.managementFeeRate = lb.managementFeeRate := by
  unfold LoanBroker.releaseLoan at h
  exact (congrArg RawLoanBroker.managementFeeRate (RawLoanBroker.to_lawful_ok h).1 :)

/-- What a loan transaction writes: the slot of its loan, or the end of the list for a LoanSet, and the slot of
the broker it acts on, holding that broker with the same management fee rate. -/
private lemma LendingLedger.applyLoan_effect {l : LendingLedger} {tx : LendingTx} {u : LoanEffect}
    (hu : (l.applyLoan tx).run = .ok (.ok u)) :
    (tx.loanIndex? = some u.loanIndex ∨ u.loanIndex = l.loans.length) ∧ l.loanTxBroker? tx = some u.brokerIndex ∧
      ∃ b, l.broker? u.brokerIndex = some b ∧ u.broker.managementFeeRate = b.managementFeeRate := by
  cases tx with
  | loanSet i principal rates fees pi pt gp sd twoStep ao =>
    simp only [LendingLedger.applyLoan] at hu
    obtain ⟨broker, r, hb, -, hcr, rfl⟩ := l.applyLoanSet_inv _ _ _ _ _ _ _ _ hu
    obtain ⟨_, _, _, b'', -, hl, hb''⟩ := Loan.create_loan_eq _ _ _ _ _ _ _ _ r hcr
    refine ⟨Or.inr rfl, rfl, broker, hb, ?_⟩
    show r.loan'.broker.managementFeeRate = _
    rw [show r.loan'.broker = r.loan'.toRawLoan.broker from rfl, hl]
    show b''.toRawLoanBroker.managementFeeRate = _
    rw [hb'']
  | loanAccept i =>
    obtain ⟨e, broker, loan, r, he, hb, hw, -, hr, rfl⟩ := l.applyLoan_accept_inv u i hu
    have hlb : loan.broker = broker := (congrArg RawLoan.broker (Loan.withBroker_eq hw) :)
    refine ⟨Or.inl rfl, by simp [LendingLedger.loanTxBroker?, LendingTx.loanIndex?, he, LoanEffect.ofLoan],
      broker, hb, ?_⟩
    show r.loan'.broker.managementFeeRate = _
    rw [Loan.accept_broker loan _ r hr, hlb]
  | loanDelete i =>
    obtain ⟨e, broker, loan, r, he, hb, hw, -, hr, rfl⟩ := l.applyLoan_delete_inv u i hu
    have hlb : loan.broker = broker := (congrArg RawLoan.broker (Loan.withBroker_eq hw) :)
    refine ⟨Or.inl rfl, by simp [LendingLedger.loanTxBroker?, LendingTx.loanIndex?, he], broker, hb, ?_⟩
    show r.broker'.managementFeeRate = _
    rw [← hlb]
    by_cases hp : loan.isPending = true
    · obtain ⟨_, _, _, -, -, -, -, hrel⟩ := Loan.delete_pending_ok_inv loan _ r hp hr
      exact LoanBroker.releaseLoan_rate _ _ _ hrel
    · simp only [Bool.not_eq_true] at hp
      rw [Loan.delete_active_reduce loan _ hp] at hr
      obtain ⟨b', hb', -⟩ := Loan.deleteActive_ok loan.broker
      rw [hb'] at hr
      obtain rfl : b' = r.broker' := by injection hr with hr; injection hr with hr; rw [← hr]
      exact LoanBroker.releaseLoan_rate _ _ _ hb'
  | loanManage i action =>
    obtain ⟨e, broker, loan, r, he, hb, hw, -, hr, rfl⟩ := l.applyLoan_manage_inv u i action hu
    have hlb : loan.broker = broker := (congrArg RawLoan.broker (Loan.withBroker_eq hw) :)
    refine ⟨Or.inl rfl, by simp [LendingLedger.loanTxBroker?, LendingTx.loanIndex?, he, LoanEffect.ofLoan],
      broker, hb, ?_⟩
    show r.loan'.broker.managementFeeRate = _
    rw [← hlb]
    cases action with
    | impair => rw [(Loan.manageImpair_debt loan _ _ r hr).1]
    | unimpair => rw [(Loan.manageUnimpair_debt loan _ r hr).1]
    | default =>
      simp only [Loan.manage] at hr
      unfold_ter at hr
      walk_ok
      rename_i rd hd
      obtain ⟨_, _, _, _, b, -, -, -, -, -, -, hbr, hloan, -⟩ := Loan.manageDefault_ok_parts loan _ rd hd
      have hrb : rd.loan'.broker = b := by
        rw [show rd.loan'.broker = rd.loan'.toRawLoan.broker from rfl, hloan]; rfl
      show rd.loan'.broker.managementFeeRate = _
      rw [hrb, show b.managementFeeRate = b.toRawLoanBroker.managementFeeRate from rfl, hbr]
      rfl
  | loanPay i paymentType amount =>
    obtain ⟨e, broker, loan, r, he, hb, hw, -, hr, rfl⟩ := l.applyLoan_pay_inv u i paymentType amount hu
    have hlb : loan.broker = broker := (congrArg RawLoan.broker (Loan.withBroker_eq hw) :)
    refine ⟨Or.inl rfl, by simp [LendingLedger.loanTxBroker?, LendingTx.loanIndex?, he, LoanEffect.ofLoan],
      broker, hb, ?_⟩
    show r.loan'.broker.managementFeeRate = _
    rw [← hlb, show r.loan'.broker.managementFeeRate = r.loan'.broker.toRawLoanBroker.managementFeeRate from rfl,
      Loan.pay_broker_fields loan _ _ _ _ r hr]
  | _ => simp only [LendingLedger.applyLoan] at hu; cases hu

/-- A broker transaction writes the slot of the broker it acts on. -/
private lemma LendingLedger.applyBroker_index {l : LendingLedger} {tx : LendingTx} {u : BrokerEffect}
    (hu : (l.applyBroker tx).run = .ok (.ok u)) : l.txBroker? tx = some u.index := by
  cases tx <;> simp only [LendingLedger.applyBroker] at hu <;> try cases hu
  all_goals
    unfold_ter at hu
    walk_ok
    rfl

/-- A loan transaction that does not name loan `j` keeps what a transaction on `j` reads. On another broker it
also keeps the broker of `j`. -/
private lemma LendingLedger.keepsLoan_of_loanTx {l la : LendingLedger} {tx : LendingTx} {j : Nat} {e : LoanEntry}
    (he : l.loan? j = some e) (hl : tx.isLoan = true) (hj : tx.loanIndex? ≠ some j)
    (ha : (l.apply tx).run = .ok (.ok la)) :
    l.KeepsLoan la j e ∧ (l.loanTxBroker? tx ≠ some e.brokerIndex →
      ∀ b, l.broker? e.brokerIndex = some b → la.broker? e.brokerIndex = some b) := by
  obtain ⟨u, hu, rfl⟩ := LendingLedger.apply_loan hl ha
  obtain ⟨hslot, hbk, b0, hb0, hrate⟩ := LendingLedger.applyLoan_effect hu
  have hjl := LendingLedger.loan?_lt he
  have hloan : (l.commitLoan u).loan? j = some e := by
    rw [LendingLedger.loan?_commitLoan, if_neg, he]
    intro hjeq
    split at hjeq
    · rcases hslot with h | h
      · exact hj (by rw [h, hjeq])
      · omega
    · omega
  have hbr := LendingLedger.broker?_commitLoan l u b0 hb0 e.brokerIndex
  refine ⟨⟨rfl, rfl, l.applyLoan_keepsSettings tx u hu, hloan, fun b hb => ?_⟩, fun hne b hb => ?_⟩
  · rw [hbr]
    by_cases hk : e.brokerIndex = u.brokerIndex
    · rw [if_pos hk]
      rw [hk, hb0] at hb
      obtain rfl := Option.some.inj hb
      exact ⟨_, rfl, hrate⟩
    · rw [if_neg hk]; exact ⟨b, hb, rfl⟩
  · rw [hbr, if_neg (fun hk => hne (by rw [hbk, hk]))]
    exact hb

/-- A broker transaction on another broker keeps what a transaction on loan `j` reads, the broker of `j` and
the vault. -/
private lemma LendingLedger.keepsLoan_of_brokerTx {l la : LendingLedger} {tx : LendingTx} {j : Nat} {e : LoanEntry}
    (he : l.loan? j = some e) (hb : tx.isBroker = true) (hk : l.txBroker? tx ≠ some e.brokerIndex)
    (ha : (l.apply tx).run = .ok (.ok la)) :
    l.KeepsLoan la j e ∧ ∀ b, l.broker? e.brokerIndex = some b → la.broker? e.brokerIndex = some b := by
  obtain ⟨u, hu, rfl⟩ := LendingLedger.apply_broker hb ha
  have hidx := LendingLedger.applyBroker_index hu
  have hkeep : ∀ b, l.broker? e.brokerIndex = some b → (l.commitBroker u).broker? e.brokerIndex = some b := by
    intro b hb
    have hlt := LendingLedger.broker?_lt hb
    rw [LendingLedger.broker?_commitBroker, if_neg, hb]
    intro heq
    split at heq
    · exact hk (by rw [hidx, heq])
    · omega
  exact ⟨⟨rfl, rfl, Vault.KeepsSettings.refl _, he, fun b hb => ⟨b, hkeep b hb, rfl⟩⟩, hkeep⟩

/-- A transaction on stored loan `j` replays on a reachable ledger that keeps what it reads, while a LoanAccept
still fits the Open limit, the vault is not coarsened, and the balances the model does not track fit. -/
private lemma LendingLedger.loanTx_replay {l L lb : LendingLedger} (hr : l.Reachable) (hR : L.Reachable) {j : Nat}
    {e : LoanEntry} (hk : l.KeepsLoan L j e) (he : l.loan? j = some e) (tx : LendingTx)
    (htx : tx.loanIndex? = some j) (hb : (l.apply tx).run = .ok (.ok lb))
    (hopen : ∀ x, tx = .loanAccept j → e.loan.interestDue = .ok x → L.vault.exceedsOpenLimit x = .ok false)
    (htotal : L.vault.assetsAvailable.toRat + L.vault.assetsDeployed.toRat <
      10 ^ 16 * (10 : ℚ) ^ L.vault.baseExponent)
    (hca : ∀ b, L.broker? e.brokerIndex = some b → b.coverAvailable.toRat < 10 ^ 96)
    (hcredit : ∀ pt amount, tx = .loanPay j pt amount → L.CreditFits j pt amount)
    (hfee : (∀ b, l.broker? e.brokerIndex = some b → L.broker? e.brokerIndex = some b) ∨
      ∀ pt amount, tx = .loanPay j pt amount → L.FeeFits j pt amount) :
    ∃ L', (L.apply tx).run = .ok (.ok L') := by
  cases tx <;> simp only [LendingTx.loanIndex?, Option.some.injEq, reduceCtorEq] at htx
  · subst htx; exact LendingLedger.accept_replay hR hk he hb (fun x hx => hopen x rfl hx)
  · subst htx; exact LendingLedger.delete_replay hR hk he hb htotal
  · subst htx; exact LendingLedger.manage_replay hR hk he _ hb htotal hca
  · subst htx
    exact LendingLedger.pay_replay hr hR hk he _ _ hb htotal hca (hcredit _ _ rfl)
      (hfee.imp id fun h => h _ _ rfl)

/-- A transaction acting on a broker through a loan is a loan transaction. -/
private lemma LendingLedger.loanTxBroker?_isLoan {l : LendingLedger} {tx : LendingTx} {k : Nat}
    (h : l.loanTxBroker? tx = some k) : tx.isLoan = true := by
  cases tx <;> simp_all [LendingLedger.loanTxBroker?, LendingTx.loanIndex?, LendingTx.isLoan]

/-- A transaction acting on a broker is a broker transaction or acts on it through a loan. -/
private lemma LendingLedger.txBroker?_cases {l : LendingLedger} {tx : LendingTx} {k : Nat}
    (h : l.txBroker? tx = some k) : tx.isBroker = true ∨ l.loanTxBroker? tx = some k := by
  cases tx <;> simp_all [LendingLedger.txBroker?, LendingTx.isBroker]

/-- A transaction on stored loan `j` acts on the broker of `j`. -/
private lemma LendingLedger.loanTxBroker?_of_loanIndex {l : LendingLedger} {tx : LendingTx} {j : Nat}
    {e : LoanEntry} (htx : tx.loanIndex? = some j) (he : l.loan? j = some e) :
    l.loanTxBroker? tx = some e.brokerIndex := by
  cases tx <;> simp_all [LendingLedger.loanTxBroker?, LendingTx.loanIndex?]

/-- Proof body of the same-broker line of `Lending.isolation`. -/
lemma LendingLedger.payment_isolation_proof (l la lb : LendingLedger) (hr : l.Reachable) (j : Nat) (e' : LoanEntry)
    (tx tx' : LendingTx) (he' : l.loan? j = some e') (hon : l.loanTxBroker? tx = some e'.brokerIndex)
    (hj : tx.loanIndex? ≠ some j) (htx' : tx'.loanIndex? = some j)
    (ha : (l.apply tx).run = .ok (.ok la)) (hb : (l.apply tx').run = .ok (.ok lb))
    (hopen : ∀ x, tx' = .loanAccept j → e'.loan.interestDue = .ok x → la.vault.exceedsOpenLimit x = .ok false)
    (htotal : la.vault.assetsAvailable.toRat + la.vault.assetsDeployed.toRat <
      10 ^ 16 * (10 : ℚ) ^ la.vault.baseExponent)
    (hca : ∀ b, la.broker? e'.brokerIndex = some b → b.coverAvailable.toRat < 10 ^ 96)
    (hcredit : ∀ pt amount, tx' = .loanPay j pt amount → la.CreditFits j pt amount)
    (hfee : ∀ pt amount, tx' = .loanPay j pt amount → la.FeeFits j pt amount) :
    ∃ lab, (la.apply tx').run = .ok (.ok lab) := by
  obtain ⟨hk, -⟩ := LendingLedger.keepsLoan_of_loanTx he' (LendingLedger.loanTxBroker?_isLoan hon) hj ha
  exact LendingLedger.loanTx_replay hr (hr.apply ha) hk he' tx' htx' hb hopen htotal hca hcredit (Or.inr hfee)

/-- Proof body of the other-broker line of `Lending.isolation`. -/
lemma LendingLedger.broker_isolation_proof (l la lb : LendingLedger) (hr : l.Reachable) (j k : Nat)
    (e' : LoanEntry) (tx tx' : LendingTx) (he' : l.loan? j = some e') (hon : l.txBroker? tx = some k)
    (hkj : k ≠ e'.brokerIndex) (htx' : tx'.loanIndex? = some j)
    (ha : (l.apply tx).run = .ok (.ok la)) (hb : (l.apply tx').run = .ok (.ok lb))
    (hopen : ∀ x, tx' = .loanAccept j → e'.loan.interestDue = .ok x → la.vault.exceedsOpenLimit x = .ok false)
    (htotal : la.vault.assetsAvailable.toRat + la.vault.assetsDeployed.toRat <
      10 ^ 16 * (10 : ℚ) ^ la.vault.baseExponent)
    (hca : ∀ b, la.broker? e'.brokerIndex = some b → b.coverAvailable.toRat < 10 ^ 96)
    (hcredit : ∀ pt amount, tx' = .loanPay j pt amount → la.CreditFits j pt amount) :
    ∃ lab, (la.apply tx').run = .ok (.ok lab) := by
  have hne : some k ≠ some e'.brokerIndex := fun h => hkj (Option.some.inj h)
  rcases LendingLedger.txBroker?_cases hon with hbk | hlb
  · obtain ⟨hk, hsame⟩ := LendingLedger.keepsLoan_of_brokerTx he' hbk (by rw [hon]; exact hne) ha
    exact LendingLedger.loanTx_replay hr (hr.apply ha) hk he' tx' htx' hb hopen htotal hca hcredit (Or.inl hsame)
  · have hj : tx.loanIndex? ≠ some j := fun h => hne (by
      rw [← hlb]; exact LendingLedger.loanTxBroker?_of_loanIndex h he')
    obtain ⟨hk, hsame⟩ := LendingLedger.keepsLoan_of_loanTx he' (LendingLedger.loanTxBroker?_isLoan hlb) hj ha
    exact LendingLedger.loanTx_replay hr (hr.apply ha) hk he' tx' htx' hb hopen htotal hca hcredit
      (Or.inl (hsame (by rw [hlb]; exact hne)))

end XRPL.Model.Lending
