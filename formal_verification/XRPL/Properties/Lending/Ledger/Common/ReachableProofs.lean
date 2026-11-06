import XRPL.Properties.Lending.Common.PoolBalances
import XRPL.Properties.Lending.Ledger.Common.ReachableDefs
import XRPL.Properties.Lending.Loan.LoanValid

/-! # Reachability induction proofs

General lemmas for proofs over reachable lending ledgers: joining traces, turning a `run` into a
reachability proof, induction over the transactions, and what each kind of transaction can
change. -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol

/-- Two runs in a row reach the ledger the second one ends in. -/
lemma LendingLedger.Reaches.trans {start l l' : LendingLedger} {txs txs' : List LendingTx}
    (h₁ : LendingLedger.Reaches start txs l) (h₂ : LendingLedger.Reaches l txs' l') :
    LendingLedger.Reaches start (txs ++ txs') l' := by
  induction h₂ with
  | refl => simpa using h₁
  | step tx _ ha ih => rw [← List.append_assoc]; exact .step tx ih ha

/-- One transaction reaches its result. -/
lemma LendingLedger.Reaches.single {l l' : LendingLedger} {tx : LendingTx}
    (h : (l.apply tx).run = .ok (.ok l')) : LendingLedger.Reaches l [tx] l' := by
  simpa using LendingLedger.Reaches.step tx .refl h

/-- A run applies a sublist of its transactions, the ones not rejected, and reaches its result
with them. -/
private lemma LendingLedger.run_reaches {l l' : LendingLedger} {txs : List LendingTx}
    (h : l.run txs = .ok l') :
    ∃ applied : List LendingTx, applied.Sublist txs ∧ LendingLedger.Reaches l applied l' := by
  induction txs generalizing l with
  | nil =>
    simp only [LendingLedger.run, Except.ok.injEq] at h
    exact ⟨[], .slnil, h ▸ .refl⟩
  | cons tx txs ih =>
    simp only [LendingLedger.run] at h
    cases ha : (l.apply tx).run with
    | error e => simp [ha, bind, Except.bind] at h
    | ok r =>
      cases r with
      | error ter =>
        simp only [ha, bind, Except.bind] at h
        obtain ⟨applied, hsub, hr⟩ := ih h
        exact ⟨applied, hsub.cons tx, hr⟩
      | ok l₁ =>
        simp only [ha, bind, Except.bind] at h
        obtain ⟨applied, hsub, hr⟩ := ih h
        exact ⟨tx :: applied, hsub.cons_cons tx, by
          simpa using (LendingLedger.Reaches.single ha).trans hr⟩

/-- A run from a genesis ledger reaches a ledger reachable with the transactions it was given. -/
lemma LendingLedger.ReachableBy.of_run {allowed : LendingTx → Prop} {genesis l : LendingLedger}
    {txs : List LendingTx} (hg : genesis.Genesis) (h : genesis.run txs = .ok l)
    (hall : ∀ tx ∈ txs, allowed tx) : l.ReachableBy allowed := by
  obtain ⟨applied, hsub, hr⟩ := LendingLedger.run_reaches h
  exact ⟨genesis, applied, hg, hr, fun tx htx => hall tx (hsub.subset htx)⟩

/-- A run from a genesis ledger reaches a reachable ledger. -/
lemma LendingLedger.Reachable.of_run {genesis l : LendingLedger} {txs : List LendingTx}
    (hg : genesis.Genesis) (h : genesis.run txs = .ok l) : l.Reachable :=
  LendingLedger.ReachableBy.of_run hg h fun _ _ => trivial

/-- A successful transaction on a reachable ledger leads to a reachable ledger. -/
lemma LendingLedger.Reachable.apply {l l' : LendingLedger} (hr : l.Reachable) {tx : LendingTx}
    (h : (l.apply tx).run = .ok (.ok l')) : l'.Reachable := by
  obtain ⟨g, txs, hg, hreach, -⟩ := hr
  exact ⟨g, txs ++ [tx], hg, hreach.step tx h, fun _ _ => trivial⟩

/-- A property every transaction keeps holds after any run. -/
lemma LendingLedger.Reaches.invariant {Inv : LendingLedger → Prop} {start l : LendingLedger}
    {txs : List LendingTx} (h0 : Inv start)
    (hstep : ∀ (l l' : LendingLedger) (tx : LendingTx), tx ∈ txs → Inv l →
      (l.apply tx).run = .ok (.ok l') → Inv l')
    (h : LendingLedger.Reaches start txs l) : Inv l := by
  induction h with
  | refl => exact h0
  | step tx _ ha ih =>
    exact hstep _ _ tx (by simp) (ih fun l l' tx' hm => hstep l l' tx' (by simp [hm])) ha

/-- A property that holds on genesis ledgers and that every allowed transaction keeps holds on every
ledger reachable with those transactions. -/
lemma LendingLedger.ReachableBy.invariant {allowed : LendingTx → Prop} {Inv : LendingLedger → Prop}
    (h0 : ∀ g : LendingLedger, g.Genesis → Inv g)
    (hstep : ∀ (l l' : LendingLedger) (tx : LendingTx), allowed tx → Inv l →
      (l.apply tx).run = .ok (.ok l') → Inv l')
    {l : LendingLedger} (h : l.ReachableBy allowed) : Inv l :=
  let ⟨g, _, hg, hr, hall⟩ := h
  hr.invariant (h0 g hg) fun l l' tx hm hi ha => hstep l l' tx (hall tx hm) hi ha

/-- A property that holds on genesis ledgers and that every transaction keeps holds on every
reachable ledger. -/
lemma LendingLedger.Reachable.invariant {Inv : LendingLedger → Prop}
    (h0 : ∀ g : LendingLedger, g.Genesis → Inv g)
    (hstep : ∀ (l l' : LendingLedger) (tx : LendingTx), Inv l → (l.apply tx).run = .ok (.ok l') → Inv l')
    {l : LendingLedger} (h : l.Reachable) : Inv l :=
  LendingLedger.ReachableBy.invariant h0 (fun l l' tx _ => hstep l l' tx) h

/-- A step that ends by mapping the result of `x` came from a successful `x`. -/
lemma TerExcept.map_ok {ε β : Type} {x : TerExcept ε} {f : ε → β} {b : β}
    (h : (f <$> x).run = .ok (.ok b)) : ∃ u, x.run = .ok (.ok u) ∧ b = f u := by
  simp only [ExceptT.run, Functor.map, ExceptT.map, ExceptT.mk, bind, Except.bind] at h ⊢
  cases hx : x with
  | error e => rw [hx] at h; cases h
  | ok r =>
    cases r with
    | error t => rw [hx] at h; cases h
    | ok u => rw [hx] at h; cases h; exact ⟨u, rfl, rfl⟩

/-- A thrown code is a rejection. -/
private lemma TerExcept.throw_run {β : Type} (t : TER) : (throw t : TerExcept β).run = .ok (.error t) := rfl

/-- A successful transaction passed its preflight and its checks and operation succeeded. -/
lemma LendingLedger.apply_checked {l l' : LendingLedger} {tx : LendingTx} (h : (l.apply tx).run = .ok (.ok l')) :
    (tx.preflight l).isTesSuccess = true ∧ (l.applyChecked tx).run = .ok (.ok l') := by
  unfold LendingLedger.apply at h
  generalize tx.preflight l = p at h ⊢
  dsimp only at h
  cases hp : p.isTesSuccess
  · rw [hp, if_pos (by decide), TerExcept.throw_run] at h; cases h
  · rw [hp, if_neg (by decide)] at h; exact ⟨rfl, h⟩

/-- A successful loan transaction wrote its loan effect. -/
lemma LendingLedger.apply_loan {l l' : LendingLedger} {tx : LendingTx} (hl : tx.isLoan = true)
    (h : (l.apply tx).run = .ok (.ok l')) :
    ∃ u, (l.applyLoan tx).run = .ok (.ok u) ∧ l' = l.commitLoan u := by
  have h := (LendingLedger.apply_checked h).2
  cases tx <;> simp only [LendingTx.isLoan, Bool.false_eq_true] at hl <;>
  · simp only [LendingLedger.applyChecked, LendingTx.isVault, LendingTx.isBroker, Bool.false_eq_true,
      ↓reduceIte] at h
    split at h
    · rw [TerExcept.throw_run] at h; cases h
    · exact TerExcept.map_ok h

/-- A successful vault transaction wrote its vault effect. -/
lemma LendingLedger.apply_vault {l l' : LendingLedger} {tx : LendingTx} (hv : tx.isVault = true)
    (h : (l.apply tx).run = .ok (.ok l')) :
    ∃ u, (l.applyVault tx).run = .ok (.ok u) ∧ l' = l.commitVault u := by
  have h := (LendingLedger.apply_checked h).2
  cases tx <;> simp only [LendingTx.isVault, Bool.false_eq_true] at hv <;>
  · simp only [LendingLedger.applyChecked, LendingTx.isVault, ↓reduceIte] at h
    split at h
    · rw [TerExcept.throw_run] at h; cases h
    · exact TerExcept.map_ok h

/-- A successful broker transaction wrote its broker effect. -/
lemma LendingLedger.apply_broker {l l' : LendingLedger} {tx : LendingTx} (hb : tx.isBroker = true)
    (h : (l.apply tx).run = .ok (.ok l')) :
    ∃ u, (l.applyBroker tx).run = .ok (.ok u) ∧ l' = l.commitBroker u := by
  have h := (LendingLedger.apply_checked h).2
  cases tx <;> simp only [LendingTx.isBroker, Bool.false_eq_true] at hb <;>
  · simp only [LendingLedger.applyChecked, LendingTx.isVault, LendingTx.isBroker, Bool.false_eq_true,
      ↓reduceIte] at h
    split at h
    · rw [TerExcept.throw_run] at h; cases h
    · exact TerExcept.map_ok h

/-- Refreshing the broker changes nothing else in the loan. -/
lemma Loan.withBroker_eq {loan loan' : Loan} {broker : LoanBroker}
    (h : loan.withBroker broker = .ok loan') :
    loan'.toRawLoan = { loan.toRawLoan with broker := broker } :=
  (RawLoan.to_lawful_ok h).1

end XRPL.Model.Lending
