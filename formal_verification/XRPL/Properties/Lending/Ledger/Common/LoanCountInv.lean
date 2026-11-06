import XRPL.Properties.Lending.Ledger.Common.BrokerSteps
import XRPL.Properties.Lending.Ledger.Common.LoanSteps
import XRPL.Properties.Lending.Ledger.Common.VaultSteps
import XRPL.Properties.Lending.Loan.Common.LoanCount
import XRPL.Properties.Lending.Loan.Common.PayMonotone

/-! # Loan counts on a reachable ledger

A stored broker's LoanCount is the number of stored loans on it, and no stored loan names an empty
broker slot. A LoanSet adds a loan and one to the count, a delete removes both. -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault (Vault)

/-- The number of stored loans on broker `j`. -/
def LendingLedger.loansOf (l : LendingLedger) (j : Nat) : Nat :=
  l.loans.countP fun o => o.any (·.brokerIndex == j)

/-- With no loan left no broker has a loan. -/
lemma LendingLedger.loansOf_none {l : LendingLedger} (h : ∀ i, l.loan? i = none) (j : Nat) :
    l.loansOf j = 0 := by
  unfold LendingLedger.loansOf
  rw [List.countP_eq_zero]
  intro o ho
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem ho
  have hn := h k
  unfold LendingLedger.loan? at hn
  rw [List.getElem?_eq_getElem hk] at hn
  cases hx : l.loans[k] with
  | none => simp
  | some e => rw [hx] at hn; simp at hn

/-- Rewriting one slot changes a count by what the slot held before and after. -/
private lemma List.countP_set_add {α : Type} (p : α → Bool) (xs : List α) (i : Nat) (a : α) (hi : i < xs.length) :
    (xs.set i a).countP p + (if p xs[i] then 1 else 0) = xs.countP p + (if p a then 1 else 0) := by
  rw [List.countP_set hi]
  have : p xs[i] = true → 1 ≤ xs.countP p := fun h =>
    List.countP_pos_iff.mpr ⟨xs[i], List.getElem_mem hi, h⟩
  split <;> split <;> simp_all

/-- A stored loan is the slot's entry. -/
lemma LendingLedger.loan?_getElem {l : LendingLedger} {i : Nat} {e : LoanEntry} (h : l.loan? i = some e) :
    ∃ hi : i < l.loans.length, l.loans[i] = some e := by
  have hi := LendingLedger.loan?_lt h
  refine ⟨hi, ?_⟩
  unfold LendingLedger.loan? at h
  rw [List.getElem?_eq_getElem hi] at h
  simpa using h

/-- What every reachable ledger keeps about loan counts: a stored broker's LoanCount is the number of its
stored loans, and no stored loan names an empty broker slot. -/
structure LendingLedger.LoanCountInv (l : LendingLedger) : Prop where
  counted : ∀ (j : Nat) (b : LoanBroker), l.broker? j = some b → b.loanCount.toNat = l.loansOf j
  orphans : ∀ j, l.broker? j = none → l.loansOf j = 0

/-- Rewriting a loan's slot with an entry on the same broker keeps every broker's count. -/
private lemma LendingLedger.loansOf_rewrite (l : LendingLedger) (i : Nat) (e e' : LoanEntry) (he : l.loan? i = some e)
    (hb : e'.brokerIndex = e.brokerIndex) (j : Nat) :
    (storeSlot l.loans i (some e')).countP (fun o => o.any (·.brokerIndex == j)) = l.loansOf j := by
  obtain ⟨hi, hei⟩ := LendingLedger.loan?_getElem he
  unfold storeSlot LendingLedger.loansOf
  rw [if_pos hi]
  have := List.countP_set_add (fun o : Option LoanEntry => o.any (·.brokerIndex == j)) l.loans i (some e') hi
  simp only [hei, Option.any_some, hb] at this
  omega

/-- The counts after a delete: the deleted loan's broker has one loan fewer. -/
private lemma LendingLedger.loansOf_delete (l : LendingLedger) (i : Nat) (e : LoanEntry) (he : l.loan? i = some e)
    (j : Nat) :
    (storeSlot l.loans i none).countP (fun o => o.any (·.brokerIndex == j)) + (if e.brokerIndex = j then 1 else 0) =
      l.loansOf j := by
  obtain ⟨hi, hei⟩ := LendingLedger.loan?_getElem he
  unfold storeSlot LendingLedger.loansOf
  rw [if_pos hi]
  have := List.countP_set_add (fun o : Option LoanEntry => o.any (·.brokerIndex == j)) l.loans i none hi
  simp only [hei, Option.any_some, Option.any_none, beq_iff_eq] at this
  simpa using this

/-- The counts after a LoanSet: the new loan's broker has one loan more. -/
private lemma LendingLedger.loansOf_create (l : LendingLedger) (e : LoanEntry) (j : Nat) :
    (storeSlot l.loans l.loans.length (some e)).countP (fun o => o.any (·.brokerIndex == j)) =
      l.loansOf j + (if e.brokerIndex = j then 1 else 0) := by
  unfold storeSlot LendingLedger.loansOf
  rw [if_neg (lt_irrefl _), List.countP_append]
  simp

/-- A loan effect keeps the invariant when every other broker keeps its count and the loan's broker
holds its new count. -/
lemma LendingLedger.LoanCountInv.commitLoan {l : LendingLedger} (hinv : l.LoanCountInv) {u : LoanEffect}
    {b : LoanBroker} (hb : l.broker? u.brokerIndex = some b)
    (hothers : ∀ j, j ≠ u.brokerIndex →
      (storeSlot l.loans u.loanIndex u.loan).countP (fun o => o.any (·.brokerIndex == j)) = l.loansOf j)
    (hmine : u.broker.loanCount.toNat =
      (storeSlot l.loans u.loanIndex u.loan).countP (fun o => o.any (·.brokerIndex == u.brokerIndex))) :
    (l.commitLoan u).LoanCountInv := by
  have hloans : ∀ j, (l.commitLoan u).loansOf j =
      (storeSlot l.loans u.loanIndex u.loan).countP (fun o => o.any (·.brokerIndex == j)) := fun _ => rfl
  refine ⟨fun j b' hb' => ?_, fun j hj => ?_⟩
  · rw [LendingLedger.broker?_commitLoan l u b hb] at hb'
    rw [hloans]
    split at hb'
    · subst_vars; cases hb'; exact hmine
    · rw [hothers j ‹_›]; exact hinv.counted j b' hb'
  · rw [LendingLedger.broker?_commitLoan l u b hb] at hj
    rw [hloans]
    split at hj
    · cases hj
    · rw [hothers j ‹_›]; exact hinv.orphans j hj

/-- A LoanSet that passed its preflight lends a normalized principal above zero. -/
lemma LendingTx.preflight_loanSet_principal (l : LendingLedger) (i : Nat) (principal : Number) (rates : LoanRates)
    (fees : LoanFees) (pi pt gp : Option UInt32) (sd : UInt32) (twoStep ao : Bool)
    (h : ((LendingTx.loanSet i principal rates fees pi pt gp sd twoStep ao).preflight l).isTesSuccess = true) :
    principal.isNormalized ∧ 0 < principal.toRat := by
  simp only [LendingTx.preflight] at h
  split at h
  · rename_i hc
    have hpi : isPositiveInput principal = true := by
      simp only [Bool.and_eq_true] at hc
      repeat (first | exact hc | replace hc := hc.1)
    unfold isPositiveInput at hpi
    rw [Bool.and_eq_true] at hpi
    have hn := of_decide_eq_true hpi.1
    have hlt := hpi.2
    refine ⟨hn, ?_⟩
    have := (operator_lt_iff _ _ Number.zero_isNormalized hn).mp hlt
    rwa [Number.toRat_zero] at this
  · exact absurd h (by rw [show TER.temINVALID.isTesSuccess = false from rfl]; decide)

/-- An operation that keeps a loan and its broker's LoanCount keeps the invariant. -/
lemma LendingLedger.LoanCountInv.ofLoan {l : LendingLedger} (hinv : l.LoanCountInv) {i : Nat} {e : LoanEntry}
    {broker : LoanBroker} {loan loan' : Loan} {v' : Vault} (he : l.loan? i = some e)
    (hb : l.broker? e.brokerIndex = some broker) (hw : e.loan.withBroker broker = .ok loan)
    (hcount : loan'.broker.loanCount = loan.broker.loanCount) :
    (l.commitLoan (LoanEffect.ofLoan i e loan' v')).LoanCountInv := by
  have hlb : loan.broker = broker := (congrArg RawLoan.broker (Loan.withBroker_eq hw) :)
  refine hinv.commitLoan (b := broker) hb (fun j _ => (l.loansOf_rewrite i e { e with loan := loan' } he rfl j :)) ?_
  show loan'.broker.loanCount.toNat =
    (storeSlot l.loans i (some { e with loan := loan' })).countP (fun o => o.any (·.brokerIndex == e.brokerIndex))
  rw [l.loansOf_rewrite i e { e with loan := loan' } he rfl e.brokerIndex, hcount, hlb]
  exact hinv.counted _ broker hb

/-- A loan transaction keeps the invariant. -/
lemma LendingLedger.LoanCountInv.loan_step {l : LendingLedger} (hinv : l.LoanCountInv) {tx : LendingTx}
    (hpre : (tx.preflight l).isTesSuccess = true) {u : LoanEffect} (hu : (l.applyLoan tx).run = .ok (.ok u)) :
    (l.commitLoan u).LoanCountInv := by
  cases tx with
  | loanSet i principal rates fees pi pt gp sd twoStep ao =>
    obtain ⟨hpn, hpos⟩ := LendingTx.preflight_loanSet_principal l i principal rates fees pi pt gp sd twoStep ao hpre
    simp only [LendingLedger.applyLoan] at hu
    obtain ⟨broker, r, hb, -, hcr, rfl⟩ := l.applyLoanSet_inv _ _ _ _ _ _ _ _ hu
    refine hinv.commitLoan (b := broker) hb (fun j hj => ?_) ?_
    · show (storeSlot l.loans l.loans.length (some { brokerIndex := i, loan := r.loan' })).countP
        (fun o => o.any (·.brokerIndex == j)) = _
      have hj' : i ≠ j := fun h => hj (h ▸ rfl)
      rw [l.loansOf_create]
      simp only [if_neg hj', Nat.add_zero]
    · show r.loan'.broker.loanCount.toNat = (storeSlot l.loans l.loans.length
        (some { brokerIndex := i, loan := r.loan' })).countP (fun o => o.any (·.brokerIndex == i))
      rw [l.loansOf_create, Loan.create_loanCount _ _ _ _ _ _ _ _ r hpn hpos hcr, hinv.counted i broker hb]
      simp
  | loanAccept i =>
    obtain ⟨e, broker, loan, r, he, hb, hw, -, hr, rfl⟩ := l.applyLoan_accept_inv u i hu
    exact hinv.ofLoan he hb hw (by rw [Loan.accept_broker loan _ r hr])
  | loanManage i action =>
    obtain ⟨e, broker, loan, r, he, hb, hw, -, hr, rfl⟩ := l.applyLoan_manage_inv u i action hu
    refine hinv.ofLoan he hb hw ?_
    cases action with
    | impair => rw [(Loan.manageImpair_debt loan _ _ r hr).1]
    | unimpair => rw [(Loan.manageUnimpair_debt loan _ r hr).1]
    | default =>
      simp only [Loan.manage] at hr
      unfold_ter at hr
      walk_ok
      exact Loan.manageDefault_loanCount loan _ _ ‹_›
  | loanPay i paymentType amount =>
    obtain ⟨e, broker, loan, r, he, hb, hw, -, hr, rfl⟩ := l.applyLoan_pay_inv u i paymentType amount hu
    refine hinv.ofLoan he hb hw ?_
    exact (congrArg RawLoanBroker.loanCount (Loan.pay_broker_fields loan _ _ _ _ r hr) :)
  | loanDelete i =>
    obtain ⟨e, broker, loan, r, he, hb, hw, -, hr, rfl⟩ := l.applyLoan_delete_inv u i hu
    have hlb : loan.broker = broker := (congrArg RawLoan.broker (Loan.withBroker_eq hw) :)
    have hdel := l.loansOf_delete i e he
    refine hinv.commitLoan (b := broker) hb (fun j hj => ?_) ?_
    · show (storeSlot l.loans i none).countP (fun o => o.any (·.brokerIndex == j)) = _
      have hj' : e.brokerIndex ≠ j := fun h => hj (h ▸ rfl)
      have := hdel j
      rw [if_neg hj'] at this
      exact this
    · show r.broker'.loanCount.toNat =
        (storeSlot l.loans i none).countP (fun o => o.any (·.brokerIndex == e.brokerIndex))
      have h1 := hdel e.brokerIndex
      rw [if_pos rfl] at h1
      have hc := hinv.counted _ broker hb
      rw [Loan.delete_loanCount loan _ r hr, hlb, UInt32.toNat_sub_of_le _ _ (by
        rw [UInt32.le_iff_toNat_le]; show 1 ≤ broker.loanCount.toNat; omega)]
      show broker.loanCount.toNat - 1 = _
      omega
  | _ => simp only [LendingLedger.applyLoan] at hu; cases hu

/-- A broker transaction keeps the invariant. -/
lemma LendingLedger.LoanCountInv.broker_step {l : LendingLedger} (hinv : l.LoanCountInv) {tx : LendingTx}
    {u : BrokerEffect} (hu : (l.applyBroker tx).run = .ok (.ok u)) : (l.commitBroker u).LoanCountInv := by
  have hloans : ∀ j, (l.commitBroker u).loansOf j = l.loansOf j := fun _ => rfl
  have hnone : ∀ j, l.brokers.length ≤ j → l.broker? j = none := fun j hj => by
    unfold LendingLedger.broker?; rw [List.getElem?_eq_none hj]; rfl
  have hk : (∀ b', u.broker = some b' →
      b'.loanCount.toNat = l.loansOf (if u.index < l.brokers.length then u.index else l.brokers.length)) ∧
      (u.broker = none → l.loansOf (if u.index < l.brokers.length then u.index else l.brokers.length) = 0) := by
    rcases LendingLedger.applyBroker_cases l tx u hu with ⟨hi, b, hb, -, hc⟩ | ⟨b, b2, hb, hb2, -, hc⟩ |
      ⟨b, hb, hb2, hc⟩
    · rw [hi, if_neg (lt_irrefl _)]
      refine ⟨fun b' hb' => ?_, fun h => ?_⟩
      · rw [hb] at hb'; cases hb'; rw [hc, hinv.orphans _ (hnone _ le_rfl)]; rfl
      · rw [hb] at h; cases h
    · rw [if_pos (LendingLedger.broker?_lt hb)]
      refine ⟨fun b' hb' => ?_, fun h => ?_⟩
      · rw [hb2] at hb'; cases hb'; rw [hc]; exact hinv.counted _ b hb
      · rw [hb2] at h; cases h
    · rw [if_pos (LendingLedger.broker?_lt hb)]
      refine ⟨fun b' hb' => ?_, fun _ => ?_⟩
      · rw [hb2] at hb'; cases hb'
      · have := hinv.counted _ b hb; rw [hc] at this; exact this.symm
  refine ⟨fun j b' hb' => ?_, fun j hj => ?_⟩ <;> rw [hloans]
  · rw [LendingLedger.broker?_commitBroker] at hb'
    by_cases hj : j = (if u.index < l.brokers.length then u.index else l.brokers.length)
    · rw [if_pos hj] at hb'; rw [hj]; exact hk.1 b' hb'
    · rw [if_neg hj] at hb'; exact hinv.counted j b' hb'
  · rw [LendingLedger.broker?_commitBroker] at hj
    by_cases hjk : j = (if u.index < l.brokers.length then u.index else l.brokers.length)
    · rw [if_pos hjk] at hj; rw [hjk]; exact hk.2 hj
    · rw [if_neg hjk] at hj; exact hinv.orphans j hj

/-- Every transaction keeps the invariant. -/
lemma LendingLedger.LoanCountInv.step {l l' : LendingLedger} (hinv : l.LoanCountInv) {tx : LendingTx}
    (h : (l.apply tx).run = .ok (.ok l')) : l'.LoanCountInv := by
  have hpre := (LendingLedger.apply_checked h).1
  by_cases hv : tx.isVault = true
  · obtain ⟨u, -, rfl⟩ := LendingLedger.apply_vault hv h
    have hrest : (l.commitVault u).loans = l.loans ∧ (l.commitVault u).brokers = l.brokers := by
      unfold LendingLedger.commitVault; split <;> simp [LendingLedger.setShares]
    have hl : ∀ j, (l.commitVault u).loansOf j = l.loansOf j := fun j => by
      unfold LendingLedger.loansOf; rw [hrest.1]
    have hb : ∀ j, (l.commitVault u).broker? j = l.broker? j := fun j => by
      unfold LendingLedger.broker?; rw [hrest.2]
    exact ⟨fun j b hj => by rw [hl]; rw [hb] at hj; exact hinv.counted j b hj,
      fun j hj => by rw [hl]; rw [hb] at hj; exact hinv.orphans j hj⟩
  by_cases hb : tx.isBroker = true
  · obtain ⟨u, hu, rfl⟩ := LendingLedger.apply_broker hb h
    exact hinv.broker_step hu
  by_cases hl : tx.isLoan = true
  · obtain ⟨u, hu, rfl⟩ := LendingLedger.apply_loan hl h
    exact hinv.loan_step hpre hu
  have hc := (LendingLedger.apply_checked h).2
  cases tx <;> simp only [LendingTx.isVault, LendingTx.isBroker, LendingTx.isLoan, Bool.false_eq_true,
    not_false_eq_true, not_true_eq_false] at hv hb hl
  · -- vaultDelete only sets the deleted flag
    simp only [LendingLedger.applyChecked, LendingLedger.applyVaultDelete] at hc
    unfold_ter at hc
    walk_ok
    exact ⟨hinv.counted, hinv.orphans⟩
  · -- close only moves the close time
    simp only [LendingLedger.applyChecked] at hc
    cases hc
    exact ⟨hinv.counted, hinv.orphans⟩

/-- A genesis ledger has no brokers and no loans. -/
lemma LendingLedger.Genesis.loanCountInv {g : LendingLedger} (hg : g.Genesis) : g.LoanCountInv := by
  have hl : ∀ j, g.loansOf j = 0 := fun j => by unfold LendingLedger.loansOf; rw [hg.no_loans]; rfl
  refine ⟨fun j b hb => ?_, fun j _ => hl j⟩
  unfold LendingLedger.broker? at hb
  rw [hg.no_brokers] at hb
  cases hb

/-- A stored loan counts for its broker. -/
lemma LendingLedger.loansOf_pos {l : LendingLedger} {i : Nat} {e : LoanEntry} (he : l.loan? i = some e) :
    0 < l.loansOf e.brokerIndex := by
  obtain ⟨hi, hei⟩ := LendingLedger.loan?_getElem he
  unfold LendingLedger.loansOf
  exact List.countP_pos_iff.mpr ⟨l.loans[i], List.getElem_mem hi, by rw [hei]; simp⟩

/-- The broker of a stored loan counts it, so its LoanCount is not zero. -/
lemma LendingLedger.LoanCountInv.loanCount_ne_zero {l : LendingLedger} (hinv : l.LoanCountInv) {i : Nat}
    {e : LoanEntry} {b : LoanBroker} (he : l.loan? i = some e) (hb : l.broker? e.brokerIndex = some b) :
    b.loanCount ≠ 0 := by
  have hc' := hinv.counted _ b hb
  have hpos := LendingLedger.loansOf_pos he
  intro h0
  rw [h0] at hc'
  simp at hc'
  omega

/-- Every reachable ledger satisfies the invariant. -/
lemma LendingLedger.Reachable.loanCountInv {l : LendingLedger} (hr : l.Reachable) : l.LoanCountInv :=
  LendingLedger.Reachable.invariant (fun _ hg => hg.loanCountInv) (fun _ _ _ hi ha => hi.step ha) hr

/-- Proof body of the LoanCount line of `Lending.Reachable.ledger_sums`. -/
lemma LendingLedger.loanCount_proof (l : LendingLedger) (hr : l.Reachable) (j : Nat) (b : LoanBroker)
    (hb : l.broker? j = some b) : b.loanCount.toNat = l.loansOf j :=
  hr.loanCountInv.counted j b hb

end XRPL.Model.Lending
