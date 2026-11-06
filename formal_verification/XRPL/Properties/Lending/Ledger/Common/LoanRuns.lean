import XRPL.Properties.Lending.Ledger.Common.ClosedLoans
import XRPL.Properties.Lending.Ledger.Common.LoansInv
import XRPL.Properties.Lending.Ledger.Common.LoanTxResults
import XRPL.Properties.Lending.Ledger.Common.Scope
import XRPL.Properties.Lending.Loan.Common.ReachableProofs

/-! # The loan at one slot along a run of ledger transactions

Loan slots are never reused: LoanSet adds a slot at the end and LoanDelete leaves `none` in its place. So a loan at
`i` after a transaction was at `i` before it, and the transaction either ran an operation on that loan or left its
entry alone, changing at most the ledger's copy of its broker. Along a run from a reachable ledger the loan at `i`
is then reachable from the loan at `i` before the run, by `Loan.ReachableFrom`. -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault (Vault)

/-- Writing a slot never shortens the list. -/
private lemma storeSlot_length_ge {α : Type} (xs : List (Option α)) (k : Nat) (x : Option α) :
    xs.length ≤ (storeSlot xs k x).length := by
  unfold storeSlot
  split <;> simp

/-- A transaction never moves the close time back. -/
lemma LendingLedger.apply_now_le {l l' : LendingLedger} {tx : LendingTx} (h : (l.apply tx).run = .ok (.ok l')) :
    l.now ≤ l'.now := by
  have hrefl : l.now ≤ l.now := UInt32.le_iff_toNat_le.mpr (le_refl _)
  by_cases hv : tx.isVault = true
  · obtain ⟨u, -, rfl⟩ := LendingLedger.apply_vault hv h
    unfold LendingLedger.commitVault
    split <;> exact hrefl
  by_cases hb : tx.isBroker = true
  · obtain ⟨u, -, rfl⟩ := LendingLedger.apply_broker hb h
    exact hrefl
  by_cases hl : tx.isLoan = true
  · obtain ⟨u, -, rfl⟩ := LendingLedger.apply_loan hl h
    exact hrefl
  have hc := (LendingLedger.apply_checked h).2
  cases tx <;> simp only [LendingTx.isVault, LendingTx.isBroker, LendingTx.isLoan, Bool.false_eq_true,
    not_false_eq_true, not_true_eq_false] at hv hb hl
  · simp only [LendingLedger.applyChecked, LendingLedger.applyVaultDelete] at hc
    unfold_ter at hc
    walk_ok
    exact hrefl
  · simp only [LendingLedger.applyChecked] at hc
    cases hc
    show l.now ≤ max l.now _
    simp only [max, UInt32.le_iff_toNat_le]
    split <;> omega

/-- A transaction keeps every loan slot, and changes slot `i` only by a LoanDelete or an operation on loan `i`. -/
lemma LendingLedger.apply_loanSlot {l l' : LendingLedger} {tx : LendingTx} (h : (l.apply tx).run = .ok (.ok l'))
    {i : Nat} (hi : i < l.loans.length) :
    i < l'.loans.length ∧ (l'.loan? i = l.loan? i ∨ tx = .loanDelete i ∨ tx = .loanAccept i ∨
      (∃ action, tx = .loanManage i action) ∨ ∃ paymentType amount, tx = .loanPay i paymentType amount) := by
  have hsame : l'.loans = l.loans → i < l'.loans.length ∧ l'.loan? i = l.loan? i := fun hl =>
    ⟨by rw [hl]; exact hi, by unfold LendingLedger.loan?; rw [hl]⟩
  by_cases hv : tx.isVault = true
  · obtain ⟨h1, h2⟩ := hsame (LendingLedger.vault_ops_scope_proof l l' tx hv h).1
    exact ⟨h1, .inl h2⟩
  by_cases hb : tx.isBroker = true
  · obtain ⟨h1, h2⟩ := hsame (LendingLedger.broker_ops_scope_proof l l' tx hb h).1
    exact ⟨h1, .inl h2⟩
  by_cases hl : tx.isLoan = true
  · have hlen : i < l'.loans.length := by
      obtain ⟨u, -, rfl⟩ := LendingLedger.apply_loan hl h
      exact lt_of_lt_of_le hi (storeSlot_length_ge _ _ _)
    refine ⟨hlen, ?_⟩
    cases tx with
    | loanSet j principal rates fees pi pt gp sd twoStep ao =>
      obtain ⟨_, r, -, -, -, -, -, rfl, -⟩ := LendingLedger.loanSet_ok h
      left
      rw [LendingLedger.loan?_commitLoan]
      simp only [LoanEffect.ofCreate, lt_irrefl, ↓reduceIte]
      rw [if_neg (by omega)]
    | loanAccept j =>
      by_cases hij : j = i
      · subst hij; exact .inr (.inr (.inl rfl))
      obtain ⟨e, _, _, he, -, -, -, rfl, -⟩ := LendingLedger.loanAccept_ok h
      left
      rw [LendingLedger.loan?_commit_ofLoan l he, if_neg (Ne.symm hij)]
    | loanDelete j =>
      by_cases hij : j = i
      · subst hij; exact .inr (.inl rfl)
      obtain ⟨e, _, _, he, -, -, -, rfl, -⟩ := LendingLedger.loanDelete_ok h
      left
      rw [LendingLedger.loan?_commitLoan]
      simp only [LendingLedger.loan?_lt he, ↓reduceIte]
      rw [if_neg (Ne.symm hij)]
    | loanManage j action =>
      by_cases hij : j = i
      · subst hij; exact .inr (.inr (.inr (.inl ⟨action, rfl⟩)))
      obtain ⟨e, _, _, he, -, -, -, rfl, -⟩ := LendingLedger.loanManage_ok h
      left
      rw [LendingLedger.loan?_commit_ofLoan l he, if_neg (Ne.symm hij)]
    | loanPay j paymentType amount =>
      by_cases hij : j = i
      · subst hij; exact .inr (.inr (.inr (.inr ⟨paymentType, amount, rfl⟩)))
      obtain ⟨e, _, _, he, -, -, -, -, rfl, -⟩ := LendingLedger.loanPay_ok h
      left
      rw [LendingLedger.loan?_commit_ofLoan l he, if_neg (Ne.symm hij)]
    | _ => simp [LendingTx.isLoan] at hl
  cases tx <;> simp only [LendingTx.isVault, LendingTx.isBroker, LendingTx.isLoan, Bool.false_eq_true,
    not_false_eq_true, not_true_eq_false] at hv hb hl
  · obtain ⟨h1, h2⟩ := hsame (LendingLedger.vaultDelete_scope l l' h).1
    exact ⟨h1, .inl h2⟩
  · have hc := (LendingLedger.apply_checked h).2
    simp only [LendingLedger.applyChecked] at hc
    cases hc
    exact ⟨hi, .inl rfl⟩

/-- Two reachable ledgers with the same entry at `i` read the same loan there, up to the copy of its broker, which
has the same asset. -/
lemma LendingLedger.loanAt_refresh {l l' : LendingLedger} (hr : l.Reachable) (hr' : l'.Reachable) {i : Nat}
    (hs : l'.loan? i = l.loan? i) {loan' : Loan} (hat' : l'.LoanAt i loan') :
    ∃ loan b, l.LoanAt i loan ∧ b.numericType = loan.broker.numericType ∧ loan.withBroker b = .ok loan' := by
  obtain ⟨e, b', he', hb', hw'⟩ := hat'
  have he : l.loan? i = some e := hs ▸ he'
  obtain ⟨b, hb⟩ := hr.loanCountInv.broker_of_loan he
  obtain ⟨loan, hw⟩ := Loan.withBroker_ok e.loan b (hr.scaleInv.broker_asset he hb)
  have hraw := Loan.withBroker_eq hw
  refine ⟨loan, b', ⟨e, b, he, hb, hw⟩, ?_, ?_⟩
  · rw [show loan.broker = loan.toRawLoan.broker from rfl, hraw]
    exact (hr'.scaleInv.broker_asset he' hb').trans (hr.scaleInv.broker_asset he hb).symm
  · unfold Loan.withBroker at hw' ⊢
    rw [hraw]
    exact hw'

/-- A transaction on a reachable ledger, read at slot `i`. A loan at `i` afterwards was at `i` before, and the
transaction either ran an operation on it or changed at most its broker copy, to one of the same asset. -/
lemma LendingLedger.loanAt_apply {l l' : LendingLedger} (hr : l.Reachable) {tx : LendingTx}
    (h : (l.apply tx).run = .ok (.ok l')) {i : Nat} (hi : i < l.loans.length) {loan' : Loan}
    (hat' : l'.LoanAt i loan') :
    ∃ loan, l.LoanAt i loan ∧ ((∃ b, b.numericType = loan.broker.numericType ∧ loan.withBroker b = .ok loan') ∨
      tx = .loanAccept i ∨ (∃ action, tx = .loanManage i action) ∨
      ∃ paymentType amount, tx = .loanPay i paymentType amount) := by
  obtain ⟨-, hs⟩ := LendingLedger.apply_loanSlot h hi
  rcases hs with hs | rfl | rfl | ⟨action, rfl⟩ | ⟨paymentType, amount, rfl⟩
  · obtain ⟨loan, b, hat, hnt, hw⟩ := LendingLedger.loanAt_refresh hr (hr.apply h) hs hat'
    exact ⟨loan, hat, .inl ⟨b, hnt, hw⟩⟩
  · obtain ⟨_, _, _, -, -, -, -, -, -, hnone, -⟩ := LendingLedger.loanDelete_ok h
    obtain ⟨e, _, he, -⟩ := hat'
    rw [hnone] at he
    cases he
  · obtain ⟨_, loan, _, -, hat, -⟩ := LendingLedger.loanAccept_ok h
    exact ⟨loan, hat, .inr (.inl rfl)⟩
  · obtain ⟨_, loan, _, -, hat, -⟩ := LendingLedger.loanManage_ok h
    exact ⟨loan, hat, .inr (.inr (.inl ⟨action, rfl⟩))⟩
  · obtain ⟨_, loan, _, -, hat, -⟩ := LendingLedger.loanPay_ok h
    exact ⟨loan, hat, .inr (.inr (.inr ⟨paymentType, amount, rfl⟩))⟩

/-- An operation on the loan at `i` is a step of a run of that loan, at the ledger's close time. -/
lemma LendingLedger.op_reachableFrom {l l' : LendingLedger} {tx : LendingTx} (h : (l.apply tx).run = .ok (.ok l'))
    {i : Nat} (hop : tx = .loanAccept i ∨ (∃ action, tx = .loanManage i action) ∨
      ∃ paymentType amount, tx = .loanPay i paymentType amount)
    {loan loan' : Loan} (hat : l.LoanAt i loan) (hat' : l'.LoanAt i loan') {start : Loan} {t₀ t : UInt32}
    (ht : t ≤ l.now) (hfrom : Loan.ReachableFrom start t₀ loan t) : Loan.ReachableFrom start t₀ loan' l.now := by
  rcases hop with rfl | ⟨action, rfl⟩ | ⟨paymentType, amount, rfl⟩
  · obtain ⟨_, x, r, -, hx, hc, hok, -, -, hy, -⟩ := LendingLedger.loanAccept_ok h
    obtain rfl := hat.eq hx
    obtain rfl := hat'.eq hy
    exact .accept _ _ _ _ _ hfrom ht hc hok
  · cases action with
    | impair =>
      obtain ⟨_, x, r, -, hx, hc, hok, -, -, hy, -⟩ := LendingLedger.loanImpair_ok h
      obtain rfl := hat.eq hx
      obtain rfl := hat'.eq hy
      exact .impair _ _ _ _ _ hfrom ht hc hok
    | unimpair =>
      obtain ⟨_, x, r, -, hx, hc, hok, -, -, hy, -⟩ := LendingLedger.loanUnimpair_ok h
      obtain rfl := hat.eq hx
      obtain rfl := hat'.eq hy
      exact .unimpair _ _ _ _ _ hfrom ht hc hok
    | default =>
      obtain ⟨_, x, r, -, hx, hc, hok, -, -, hy, -⟩ := LendingLedger.loanDefault_ok h
      obtain rfl := hat.eq hx
      obtain rfl := hat'.eq hy
      exact .default _ _ _ _ _ hfrom ht hc hok
  · obtain ⟨_, x, r, -, hx, -, hc, hok, -, -, hy, -⟩ := LendingLedger.loanPay_ok h
    obtain rfl := hat.eq hx
    obtain rfl := hat'.eq hy
    exact Loan.ReachableFrom.pay_step hfrom ht hc hok

/-- An operation on the loan at `i` reads the stored entry `e` as `loan`, and writes `e` back with the loan `loan'`
it reads afterwards. -/
lemma LendingLedger.op_entry {l l' : LendingLedger} {tx : LendingTx} (h : (l.apply tx).run = .ok (.ok l')) {i : Nat}
    (hop : tx = .loanAccept i ∨ (∃ action, tx = .loanManage i action) ∨
      ∃ paymentType amount, tx = .loanPay i paymentType amount) :
    ∃ e loan loan', l.loan? i = some e ∧ l.LoanAt i loan ∧ l'.loan? i = some { e with loan := loan' } ∧
      l'.LoanAt i loan' := by
  rcases hop with rfl | ⟨action, rfl⟩ | ⟨paymentType, amount, rfl⟩
  · obtain ⟨e, x, r, he, hx, -, -, rfl, -, hy, -⟩ := LendingLedger.loanAccept_ok h
    exact ⟨e, x, r.loan', he, hx, by rw [LendingLedger.loan?_commit_ofLoan l he, if_pos rfl], hy⟩
  · obtain ⟨e, x, r, he, hx, -, -, rfl, -, hy, -⟩ := LendingLedger.loanManage_ok h
    exact ⟨e, x, r.loan', he, hx, by rw [LendingLedger.loan?_commit_ofLoan l he, if_pos rfl], hy⟩
  · obtain ⟨e, x, r, he, hx, -, -, -, rfl, -, hy, -⟩ := LendingLedger.loanPay_ok h
    exact ⟨e, x, r.loan', he, hx, by rw [LendingLedger.loan?_commit_ofLoan l he, if_pos rfl], hy⟩

/-- A relation between loans holds from the loan at `i` before a run to the loan at `i` after it, on any ledger. It
must chain, hold both ways between a loan and its copy with another broker, and hold across one operation. -/
lemma LendingLedger.Reaches.slot_rel {R : Loan → Loan → Prop} (htrans : ∀ x y z, R x y → R y z → R x z)
    (hbroker : ∀ (x y : Loan) (b : LoanBroker), x.withBroker b = .ok y → R x y ∧ R y x)
    (hop : ∀ (x y : Loan) (t : UInt32), Loan.ReachableFrom x t y t → R x y)
    {l l' : LendingLedger} {txs : List LendingTx} (hrun : LendingLedger.Reaches l txs l') {i : Nat}
    {loan loan' : Loan} (hat : l.LoanAt i loan) (hat' : l'.LoanAt i loan') : R loan loan' := by
  obtain ⟨e₀, b₀, he₀, -, hw₀⟩ := hat
  obtain ⟨e', b', he', -, hw'⟩ := hat'
  have key : i < l'.loans.length ∧ ∀ e, l'.loan? i = some e → R loan e.loan := by
    clear he' hw'
    induction hrun with
    | refl =>
      refine ⟨LendingLedger.loan?_lt he₀, fun e he => ?_⟩
      rw [he₀] at he
      obtain rfl := Option.some.inj he
      exact (hbroker _ _ _ hw₀).2
    | step tx _ h ih =>
      obtain ⟨hik, hR⟩ := ih
      obtain ⟨hik', hs⟩ := LendingLedger.apply_loanSlot h hik
      refine ⟨hik', fun e' he' => ?_⟩
      rcases hs with hs | rfl | hop'
      · rw [hs] at he'
        exact hR e' he'
      · obtain ⟨_, _, _, -, -, -, -, -, -, hnone, -⟩ := LendingLedger.loanDelete_ok h
        rw [hnone] at he'
        cases he'
      · obtain ⟨e, x, y, he, hx, hy₁, hy⟩ := LendingLedger.op_entry h hop'
        rw [hy₁] at he'
        obtain rfl := Option.some.inj he'
        obtain ⟨e₁, b, he₁, hb, hw⟩ := hx
        rw [he] at he₁
        obtain rfl := Option.some.inj he₁
        exact htrans _ _ _ (htrans _ _ _ (hR _ he) (hbroker _ _ _ hw).1)
          (hop _ _ _ (LendingLedger.op_reachableFrom h hop' ⟨e, b, he, hb, hw⟩ hy
            (UInt32.le_iff_toNat_le.mpr (le_refl _)) .refl))
  exact htrans _ _ _ (key.2 e' he') (hbroker _ _ _ hw').1

/-- Induction along a run from a reachable ledger, read at slot `i`. `P` holds for the loan at `i` after the run when
it holds before and every transaction of the run keeps it, the ones that only change the loan's broker copy included. -/
lemma LendingLedger.Reaches.loanAt_induction {P : LendingLedger → Loan → Prop} {l l' : LendingLedger}
    {txs : List LendingTx} (hr : l.Reachable) (hrun : LendingLedger.Reaches l txs l') {i : Nat} {loan loan' : Loan}
    (hat : l.LoanAt i loan) (hat' : l'.LoanAt i loan') (h0 : P l loan)
    (hstep : ∀ (pre : List LendingTx) (lk lk' : LendingLedger) (tx : LendingTx) (x y : Loan), pre ++ [tx] <+: txs →
      LendingLedger.Reaches l pre lk → lk.Reachable → (lk.apply tx).run = .ok (.ok lk') → lk.LoanAt i x →
      lk'.LoanAt i y → P lk x →
      ((∃ b, b.numericType = x.broker.numericType ∧ x.withBroker b = .ok y) ∨ tx = .loanAccept i ∨
        (∃ action, tx = .loanManage i action) ∨ ∃ paymentType amount, tx = .loanPay i paymentType amount) →
      P lk' y) :
    P l' loan' := by
  have hlt : i < l.loans.length := by
    obtain ⟨e, _, he, -⟩ := hat
    exact LendingLedger.loan?_lt he
  suffices key : ∀ (pre : List LendingTx) (lk : LendingLedger), LendingLedger.Reaches l pre lk → pre <+: txs →
      lk.Reachable ∧ i < lk.loans.length ∧ ∀ x, lk.LoanAt i x → P lk x from
    (key txs l' hrun (List.prefix_refl _)).2.2 loan' hat'
  intro pre lk hk
  induction hk with
  | refl =>
    intro _
    exact ⟨hr, hlt, fun x hx => hat.eq hx ▸ h0⟩
  | step tx hprev h ih =>
    intro hpre
    obtain ⟨hrk, hik, hP⟩ := ih ((List.prefix_append _ _).trans hpre)
    refine ⟨hrk.apply h, (LendingLedger.apply_loanSlot h hik).1, fun y hy => ?_⟩
    obtain ⟨x, hx, hcase⟩ := LendingLedger.loanAt_apply hrk h hik hy
    exact hstep _ _ _ tx x y hpre hprev hrk h hx hy (hP x hx) hcase

end XRPL.Model.Lending
