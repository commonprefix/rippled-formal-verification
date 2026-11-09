import XRPL.Properties.Lending.Ledger.Common.LoanSubsequenceDefs
import XRPL.Properties.Lending.Ledger.Common.Isolation
import XRPL.Properties.Lending.Ledger.Common.BrokerAccounting
import XRPL.Properties.Lending.Ledger.Common.LoanTxResults
import XRPL.Properties.Lending.Ledger.Common.ReservedInv
import XRPL.Properties.Lending.Loan.Common.AcceptExits
import XRPL.Properties.Lending.Loan.Common.ManageProofs
import XRPL.Properties.Lending.Loan.Common.GuardProofs

/-! # One loan in a sequence and in its subsequence

What a transaction keeps on the ledger: the close time, the vault's asset and scale, the brokers' management fee
rates and the other loans. A transaction on two twins of a loan, the same loan but for the copy of its broker,
leaves twins on both ledgers or deletes both. -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault (Vault)

open private LendingLedger.applyLoan_effect from XRPL.Properties.Lending.Ledger.Common.Isolation
open private LendingLedger.apply_other LendingLedger.apply_brokers LendingLedger.apply_brokers_length
  from XRPL.Properties.Lending.Ledger.Common.BrokerAccounting
open private Loan.manageUnimpair_ok_parts from XRPL.Properties.Lending.Loan.Common.ManageProofs

/-- Every transaction keeps the vault's scale. -/
private lemma LendingLedger.apply_scale {l l' : LendingLedger} {tx : LendingTx}
    (h : (l.apply tx).run = .ok (.ok l')) : l'.vault.scale = l.vault.scale := by
  by_cases hv : tx.isVault = true
  · obtain ⟨u, hu, rfl⟩ := LendingLedger.apply_vault hv h
    have hvault : (l.commitVault u).vault = u.vault := by
      unfold LendingLedger.commitVault; split <;> simp [LendingLedger.setShares]
    rw [hvault]; exact (l.applyVault_keepsLending tx u hu).scale
  by_cases hb : tx.isBroker = true
  · obtain ⟨u, -, rfl⟩ := LendingLedger.apply_broker hb h
    rfl
  by_cases hl : tx.isLoan = true
  · obtain ⟨u, hu, rfl⟩ := LendingLedger.apply_loan hl h
    exact (l.applyLoan_keepsSettings tx u hu).scale
  rw [(LendingLedger.apply_other hv hb hl h).1]

/-- Every transaction but a close keeps the close time. -/
private lemma LendingLedger.apply_now {l l' : LendingLedger} {tx : LendingTx}
    (h : (l.apply tx).run = .ok (.ok l')) (hc : ∀ t, tx ≠ .close t) : l'.now = l.now := by
  by_cases hv : tx.isVault = true
  · obtain ⟨u, -, rfl⟩ := LendingLedger.apply_vault hv h
    unfold LendingLedger.commitVault; split <;> simp [LendingLedger.setShares]
  by_cases hb : tx.isBroker = true
  · obtain ⟨u, -, rfl⟩ := LendingLedger.apply_broker hb h
    rfl
  by_cases hl : tx.isLoan = true
  · obtain ⟨u, -, rfl⟩ := LendingLedger.apply_loan hl h
    rfl
  have h := (LendingLedger.apply_checked h).2
  cases tx <;> simp only [LendingTx.isVault, LendingTx.isBroker, LendingTx.isLoan, Bool.false_eq_true,
    not_false_eq_true, not_true_eq_false] at hv hb hl
  · simp only [LendingLedger.applyChecked, LendingLedger.applyVaultDelete] at h
    unfold_ter at h
    walk_ok
    rfl
  · exact absurd rfl (hc _)

/-- A close moves only the close time. -/
private lemma LendingLedger.apply_close (l : LendingLedger) (t : UInt32) :
    (l.apply (.close t)).run = .ok (.ok { l with now := max l.now t }) := rfl

/-- A cover transaction keeps the broker's management fee rate. -/
private lemma LoanBroker.applyCoverTransaction_feeRate (lb : LoanBroker) (d : CoverDirection) (a : STAmount)
    (r : LoanBrokerCoverResult) (h : lb.applyCoverTransaction d a = .ok r) :
    r.loanBroker'.managementFeeRate = lb.managementFeeRate := by
  unfold LoanBroker.applyCoverTransaction at h
  obtain ⟨_, -, h⟩ := bind_ok_peel _ _ _ h
  dsimp only at h
  cases d <;>
  · obtain ⟨_, -, h⟩ := bind_ok_peel _ _ _ h
    obtain ⟨b, hb, h⟩ := bind_ok_peel _ _ _ h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    exact (congrArg RawLoanBroker.managementFeeRate (RawLoanBroker.to_lawful_ok hb).1 :)

/-- A broker transaction writes a new broker at the end of the list, or a broker of the same management fee rate. -/
private lemma LendingLedger.applyBroker_feeRate (l : LendingLedger) (tx : LendingTx) (u : BrokerEffect)
    (h : (l.applyBroker tx).run = .ok (.ok u)) (b' : LoanBroker) (hb' : u.broker = some b') :
    u.index = l.brokers.length ∨ ∃ b, l.broker? u.index = some b ∧ b'.managementFeeRate = b.managementFeeRate := by
  cases tx with
  | loanBrokerCreate ctx =>
    simp only [LendingLedger.applyBroker] at h
    unfold_ter at h
    walk_ok
    exact Or.inl rfl
  | loanBrokerUpdate i dm =>
    simp only [LendingLedger.applyBroker] at h
    unfold_ter at h
    walk_ok
    simp only [Option.some.injEq] at hb'
    subst hb'
    exact Or.inr ⟨_, ‹_›, (congrArg RawLoanBroker.managementFeeRate (RawLoanBroker.to_lawful_ok ‹_›).1 :)⟩
  | loanBrokerCoverDeposit i a =>
    simp only [LendingLedger.applyBroker, LoanBroker.coverDeposit] at h
    unfold_ter at h
    walk_ok
    simp only [Option.some.injEq] at hb'
    subst hb'
    exact Or.inr ⟨_, ‹_›, LoanBroker.applyCoverTransaction_feeRate _ _ _ _ ‹_›⟩
  | loanBrokerCoverWithdraw i a =>
    simp only [LendingLedger.applyBroker, LoanBroker.coverWithdraw] at h
    unfold_ter at h
    walk_ok
    simp only [Option.some.injEq] at hb'
    subst hb'
    exact Or.inr ⟨_, ‹_›, LoanBroker.applyCoverTransaction_feeRate _ _ _ _ ‹_›⟩
  | loanBrokerCoverClawback i a =>
    simp only [LendingLedger.applyBroker, LoanBroker.coverClawback] at h
    unfold_ter at h
    walk_ok
    simp only [Option.some.injEq] at hb'
    subst hb'
    exact Or.inr ⟨_, ‹_›, LoanBroker.applyCoverTransaction_feeRate _ _ _ _ ‹_›⟩
  | loanBrokerDelete i =>
    simp only [LendingLedger.applyBroker] at h
    unfold_ter at h
    walk_ok
    cases hb'
  | _ => simp only [LendingLedger.applyBroker] at h; cases h

/-- After any transaction, a broker on an old slot has the management fee rate of the broker that was there. -/
private lemma LendingLedger.apply_feeRate {l l' : LendingLedger} {tx : LendingTx}
    (h : (l.apply tx).run = .ok (.ok l')) {k : Nat} {b' : LoanBroker} (hb' : l'.broker? k = some b') :
    l.brokers.length ≤ k ∨ ∃ b, l.broker? k = some b ∧ b'.managementFeeRate = b.managementFeeRate := by
  by_cases hb : tx.isBroker = true
  · obtain ⟨u, hu, rfl⟩ := LendingLedger.apply_broker hb h
    rw [LendingLedger.broker?_commitBroker] at hb'
    by_cases hk : k = (if u.index < l.brokers.length then u.index else l.brokers.length)
    · rw [if_pos hk] at hb'
      by_cases hlt : u.index < l.brokers.length
      · rw [if_pos hlt] at hk
        subst hk
        rcases LendingLedger.applyBroker_feeRate l tx u hu b' hb' with hi | hold
        · exact Or.inl (le_of_eq hi.symm)
        · exact Or.inr hold
      · rw [if_neg hlt] at hk
        exact Or.inl (le_of_eq hk.symm)
    · rw [if_neg hk] at hb'
      exact Or.inr ⟨b', hb', rfl⟩
  by_cases hl : tx.isLoan = true
  · obtain ⟨u, hu, rfl⟩ := LendingLedger.apply_loan hl h
    obtain ⟨-, -, b0, hb0, hrate⟩ := LendingLedger.applyLoan_effect hu
    rw [LendingLedger.broker?_commitLoan l u b0 hb0] at hb'
    split at hb'
    · rename_i hk
      subst hk
      obtain rfl := Option.some.inj hb'
      exact Or.inr ⟨b0, hb0, hrate⟩
    · exact Or.inr ⟨b', hb', rfl⟩
  unfold LendingLedger.broker? at hb' ⊢
  rw [LendingLedger.apply_brokers hb hl h] at hb'
  exact Or.inr ⟨b', hb', rfl⟩

/-- A loan transaction or a close keeps the number of broker slots. -/
private lemma LendingLedger.apply_brokers_length_eq {l l' : LendingLedger} {tx : LendingTx}
    (h : (l.apply tx).run = .ok (.ok l')) (hk : tx.isLoan = true ∨ ∃ t, tx = .close t) :
    l'.brokers.length = l.brokers.length := by
  rcases hk with hl | ⟨t, rfl⟩
  · obtain ⟨u, -, rfl⟩ := LendingLedger.apply_loan hl h
    simp [LendingLedger.commitLoan]
  · rw [LendingLedger.apply_close] at h
    cases h
    rfl

/-- A loan transaction writes the slot of the stored loan it names, or a new slot at the end for a LoanSet. -/
private lemma LendingLedger.applyLoan_slot {l : LendingLedger} {tx : LendingTx} {u : LoanEffect}
    (hu : (l.applyLoan tx).run = .ok (.ok u)) :
    (u.loanIndex < l.loans.length ∧ tx.loanIndex? = some u.loanIndex) ∨
      (u.loanIndex = l.loans.length ∧ tx.loanIndex? = none) := by
  cases tx with
  | loanSet i principal rates fees pi pt gp sd twoStep ao =>
    simp only [LendingLedger.applyLoan] at hu
    obtain ⟨broker, r, -, -, -, rfl⟩ := l.applyLoanSet_inv _ _ _ _ _ _ _ _ hu
    exact Or.inr ⟨rfl, rfl⟩
  | loanAccept i =>
    obtain ⟨e, -, -, -, he, -, -, -, -, rfl⟩ := l.applyLoan_accept_inv u i hu
    exact Or.inl ⟨LendingLedger.loan?_lt he, rfl⟩
  | loanDelete i =>
    obtain ⟨e, -, -, -, he, -, -, -, -, rfl⟩ := l.applyLoan_delete_inv u i hu
    exact Or.inl ⟨LendingLedger.loan?_lt he, rfl⟩
  | loanManage i action =>
    obtain ⟨e, -, -, -, he, -, -, -, -, rfl⟩ := l.applyLoan_manage_inv u i action hu
    exact Or.inl ⟨LendingLedger.loan?_lt he, rfl⟩
  | loanPay i pt amount =>
    obtain ⟨e, -, -, -, he, -, -, -, -, rfl⟩ := l.applyLoan_pay_inv u i pt amount hu
    exact Or.inl ⟨LendingLedger.loan?_lt he, rfl⟩
  | _ => simp only [LendingLedger.applyLoan] at hu; cases hu

/-- A LoanSet adds a loan slot at the end, every other transaction keeps the number of slots, and only a
transaction naming a stored loan writes an old slot. -/
private lemma LendingLedger.apply_loans {l l' : LendingLedger} {tx : LendingTx}
    (h : (l.apply tx).run = .ok (.ok l')) :
    (l'.loans.length = l.loans.length ∨
      (l'.loans.length = l.loans.length + 1 ∧ tx.isLoan = true ∧ tx.loanIndex? = none)) ∧
    ∀ j, j < l.loans.length → tx.loanIndex? ≠ some j → l'.loan? j = l.loan? j := by
  by_cases hl : tx.isLoan = true
  · obtain ⟨u, hu, rfl⟩ := LendingLedger.apply_loan hl h
    have hlen : (l.commitLoan u).loans.length = (storeSlot l.loans u.loanIndex u.loan).length := rfl
    rcases LendingLedger.applyLoan_slot hu with ⟨hlt, hidx⟩ | ⟨heq, hidx⟩
    · refine ⟨Or.inl ?_, fun j hj hne => ?_⟩
      · rw [hlen]; unfold storeSlot; rw [if_pos hlt]; simp
      · have hji : ¬ j = u.loanIndex := fun hji => hne (by rw [hji, hidx])
        rw [LendingLedger.loan?_commitLoan, if_pos hlt, if_neg hji]
    · have hge : ¬ u.loanIndex < l.loans.length := by omega
      refine ⟨Or.inr ⟨?_, hl, hidx⟩, fun j hj _ => ?_⟩
      · rw [hlen]; unfold storeSlot; rw [if_neg hge]; simp
      · rw [LendingLedger.loan?_commitLoan, if_neg hge, if_neg (show ¬ j = l.loans.length by omega)]
  have hloans : l'.loans = l.loans := by
    by_cases hv : tx.isVault = true
    · obtain ⟨u, -, rfl⟩ := LendingLedger.apply_vault hv h
      unfold LendingLedger.commitVault; split <;> simp [LendingLedger.setShares]
    by_cases hb : tx.isBroker = true
    · obtain ⟨u, -, rfl⟩ := LendingLedger.apply_broker hb h
      rfl
    exact (LendingLedger.apply_other hv hb hl h).2.2
  refine ⟨Or.inl (by rw [hloans]), fun j _ _ => ?_⟩
  unfold LendingLedger.loan?
  rw [hloans]

/-- A transaction naming a loan succeeds only on a stored loan. -/
private lemma LendingLedger.apply_named_loan {l l' : LendingLedger} {tx : LendingTx} {j : Nat}
    (h : (l.apply tx).run = .ok (.ok l')) (htx : tx.loanIndex? = some j) : ∃ e, l.loan? j = some e := by
  cases tx <;> simp only [LendingTx.loanIndex?, Option.some.injEq, reduceCtorEq] at htx <;> subst htx
  · obtain ⟨e, -, -, he, -⟩ := LendingLedger.loanAccept_ok h
    exact ⟨e, he⟩
  · obtain ⟨e, -, -, he, -⟩ := LendingLedger.loanDelete_ok h
    exact ⟨e, he⟩
  · obtain ⟨e, -, -, he, -⟩ := LendingLedger.loanManage_ok h
    exact ⟨e, he⟩
  · obtain ⟨e, -, -, he, -⟩ := LendingLedger.loanPay_ok h
    exact ⟨e, he⟩

/-- Twin entries read with brokers of the same asset and management fee rate give twin loans. -/
private lemma Loan.twin_of_entries {e e' : LoanEntry} {b b' : LoanBroker} {loan loan' : Loan}
    (hraw : e'.loan.toRawLoan = { e.loan.toRawLoan with broker := e'.loan.toRawLoan.broker })
    (hw : e.loan.withBroker b = .ok loan) (hw' : e'.loan.withBroker b' = .ok loan')
    (hnt : b'.numericType = b.numericType) (hm : b'.managementFeeRate = b.managementFeeRate) :
    Loan.Twin loan loan' := by
  have h1 := Loan.withBroker_eq hw
  have h2 := Loan.withBroker_eq hw'
  have hb : loan.broker = b := by rw [show loan.broker = loan.toRawLoan.broker from rfl, h1]
  have hb' : loan'.broker = b' := by rw [show loan'.broker = loan'.toRawLoan.broker from rfl, h2]
  refine ⟨?_, by rw [hb, hb']; exact hnt, by rw [hb, hb']; exact hm⟩
  rw [h2, h1, hraw]

/-- Twin entries stored on two reachable ledgers of the same asset, on brokers of the same management fee rate,
read as twin loans. -/
private lemma LendingLedger.loanAt_twin {l L : LendingLedger} (hr : l.Reachable) (hR : L.Reachable) {j j' : Nat}
    {e e' : LoanEntry} (he : l.loan? j = some e) (he' : L.loan? j' = some e')
    (hraw : e'.loan.toRawLoan = { e.loan.toRawLoan with broker := e'.loan.toRawLoan.broker })
    (hnt : L.vault.numericType = l.vault.numericType)
    (hfee : ∀ b b', l.broker? e.brokerIndex = some b → L.broker? e'.brokerIndex = some b' →
      b'.managementFeeRate = b.managementFeeRate)
    {loan loan' : Loan} (hat : l.LoanAt j loan) (hat' : L.LoanAt j' loan') : Loan.Twin loan loan' := by
  obtain ⟨e0, b, he0, hb, hw⟩ := hat
  obtain ⟨e0', b', he0', hb', hw'⟩ := hat'
  rw [he] at he0
  rw [he'] at he0'
  obtain rfl := Option.some.inj he0
  obtain rfl := Option.some.inj he0'
  refine Loan.twin_of_entries hraw hw hw' ?_ (hfee b b' hb hb')
  rw [hR.scaleInv.brokers _ b' hb', hr.scaleInv.brokers _ b hb, hnt]

/-- Writing twin loans over twin entries leaves twin entries. -/
private lemma LendingLedger.commit_twin {l L : LendingLedger} {j j' : Nat} {e e' : LoanEntry}
    (he : l.loan? j = some e) (he' : L.loan? j' = some e')
    {r r' : Loan} (v v' : Vault) (hrr : r'.toRawLoan = { r.toRawLoan with broker := r'.toRawLoan.broker }) :
    ∃ f f', (l.commitLoan (LoanEffect.ofLoan j e r v)).loan? j = some f ∧
      (L.commitLoan (LoanEffect.ofLoan j' e' r' v')).loan? j' = some f' ∧ f.brokerIndex = e.brokerIndex ∧
      f'.brokerIndex = e'.brokerIndex ∧
      f'.loan.toRawLoan = { f.loan.toRawLoan with broker := f'.loan.toRawLoan.broker } := by
  refine ⟨{ e with loan := r }, { e' with loan := r' }, ?_, ?_, rfl, rfl, hrr⟩
  · rw [LendingLedger.loan?_commit_ofLoan l he]; simp
  · rw [LendingLedger.loan?_commit_ofLoan L he']; simp

/-- Twins paid the same way at the same close time leave twins. -/
private lemma Loan.pay_twin {loan loan' : Loan} (ht : Loan.Twin loan loan') (v v' : Vault) (pt : LoanPaymentType)
    (amount : Number) (now : UInt32) {r r' : LoanWithAmounts Vault}
    (h : (loan.pay v pt amount now).run = .ok (.ok r)) (h' : (loan'.pay v' pt amount now).run = .ok (.ok r')) :
    r'.loan'.toRawLoan = { r.loan'.toRawLoan with broker := r'.loan'.toRawLoan.broker } := by
  obtain ⟨p, hp, hs⟩ := Loan.pay_ok loan v pt amount now r h
  obtain ⟨q, hq, hs'⟩ := Loan.pay_ok loan' v' pt amount now r' h'
  obtain ⟨-, hu', -, -, -⟩ := Loan.payInstalments_ok loan' v' pt amount now q hq
  obtain ⟨q', hq', htw, -⟩ := Loan.payInstalments_twin ht v v' q.pool pt amount now p hu' hp
  rw [hq] at hq'
  obtain rfl : q = q' := by injection hq' with hq'; injection hq'
  obtain ⟨_, _, _, _, _, _, b1, -, -, -, -, hl1, -, -⟩ := UnsettledPayment.settle_ok p r hs
  obtain ⟨_, _, _, _, _, _, b2, -, -, -, -, hl2, -, -⟩ := UnsettledPayment.settle_ok q r' hs'
  rw [(RawLoan.to_lawful_ok hl2).1, (RawLoan.to_lawful_ok hl1).1, htw.raw]

/-- A LoanAccept, LoanDelete, LoanManage or LoanPay that succeeds on twins of a loan, stored at `j` and `j'` on
two reachable ledgers at the same close time, leaves twins at `j` and `j'` or deletes both. -/
private lemma LendingLedger.loanTx_twin {l L l₂ L₂ : LendingLedger} (hr : l.Reachable) (hR : L.Reachable)
    {j j' : Nat} {e e' : LoanEntry} (he : l.loan? j = some e) (he' : L.loan? j' = some e')
    (hraw : e'.loan.toRawLoan = { e.loan.toRawLoan with broker := e'.loan.toRawLoan.broker })
    (hnow : L.now = l.now) (hnt : L.vault.numericType = l.vault.numericType)
    (hfee : ∀ b b', l.broker? e.brokerIndex = some b → L.broker? e'.brokerIndex = some b' →
      b'.managementFeeRate = b.managementFeeRate)
    (tx : LendingTx) (htx : tx.loanIndex? = some j)
    (hb : (l.apply tx).run = .ok (.ok l₂)) (hb' : (L.apply (tx.withLoan j')).run = .ok (.ok L₂)) :
    (l₂.loan? j = none ∧ L₂.loan? j' = none) ∨
      ∃ f f', l₂.loan? j = some f ∧ L₂.loan? j' = some f' ∧ f.brokerIndex = e.brokerIndex ∧
        f'.brokerIndex = e'.brokerIndex ∧
        f'.loan.toRawLoan = { f.loan.toRawLoan with broker := f'.loan.toRawLoan.broker } := by
  have htwin : ∀ loan loan', l.LoanAt j loan → L.LoanAt j' loan' → Loan.Twin loan loan' :=
    fun _ _ hat hat' => LendingLedger.loanAt_twin hr hR he he' hraw hnt hfee hat hat'
  cases tx <;> simp only [LendingTx.loanIndex?, Option.some.injEq, reduceCtorEq] at htx <;> subst htx <;>
    dsimp only [LendingTx.withLoan] at hb'
  · obtain ⟨e0, loan, r, he0, hat, -, hok, rfl, -⟩ := LendingLedger.loanAccept_ok hb
    obtain ⟨e0', loan', r', he0', hat', -, hok', rfl, -⟩ := LendingLedger.loanAccept_ok hb'
    rw [he] at he0
    rw [he'] at he0'
    obtain rfl := Option.some.inj he0
    obtain rfl := Option.some.inj he0'
    refine Or.inr (LendingLedger.commit_twin he he' _ _ ?_)
    obtain ⟨i1, hi1⟩ := Loan.interestDue_ok loan
    obtain ⟨i2, hi2⟩ := Loan.interestDue_ok loan'
    obtain ⟨_, -, -, h1, -⟩ := Loan.accept_ok_inv loan _ i1 r hi1 hok
    obtain ⟨_, -, -, h2, -⟩ := Loan.accept_ok_inv loan' _ i2 r' hi2 hok'
    rw [(RawLoan.to_lawful_ok h2).1, (RawLoan.to_lawful_ok h1).1, (htwin _ _ hat hat').raw]
  · obtain ⟨-, -, -, -, -, -, -, -, -, hl2, -⟩ := LendingLedger.loanDelete_ok hb
    obtain ⟨-, -, -, -, -, -, -, -, -, hL2, -⟩ := LendingLedger.loanDelete_ok hb'
    exact Or.inl ⟨hl2, hL2⟩
  · rename_i action
    cases action with
    | impair =>
      obtain ⟨e0, loan, r, he0, hat, -, hok, rfl, -⟩ := LendingLedger.loanImpair_ok hb
      obtain ⟨e0', loan', r', he0', hat', -, hok', rfl, -⟩ := LendingLedger.loanImpair_ok hb'
      rw [he] at he0
      rw [he'] at he0'
      obtain rfl := Option.some.inj he0
      obtain rfl := Option.some.inj he0'
      refine Or.inr (LendingLedger.commit_twin he he' _ _ ?_)
      obtain ⟨-, -, -, -, h1⟩ := Loan.manageImpair_ok_parts loan _ _ r hok
      obtain ⟨-, -, -, -, h2⟩ := Loan.manageImpair_ok_parts loan' _ _ r' hok'
      rw [h2, h1, (htwin _ _ hat hat').raw]
    | unimpair =>
      obtain ⟨e0, loan, r, he0, hat, -, hok, rfl, -⟩ := LendingLedger.loanUnimpair_ok hb
      obtain ⟨e0', loan', r', he0', hat', -, hok', rfl, -⟩ := LendingLedger.loanUnimpair_ok hb'
      rw [he] at he0
      rw [he'] at he0'
      obtain rfl := Option.some.inj he0
      obtain rfl := Option.some.inj he0'
      refine Or.inr (LendingLedger.commit_twin he he' _ _ ?_)
      obtain ⟨-, -, -, h1⟩ := Loan.manageUnimpair_ok_parts loan _ r hok
      obtain ⟨-, -, -, h2⟩ := Loan.manageUnimpair_ok_parts loan' _ r' hok'
      rw [h2, h1, (htwin _ _ hat hat').raw]
    | default =>
      obtain ⟨e0, loan, r, he0, hat, -, hok, rfl, -⟩ := LendingLedger.loanDefault_ok hb
      obtain ⟨e0', loan', r', he0', hat', -, hok', rfl, -⟩ := LendingLedger.loanDefault_ok hb'
      rw [he] at he0
      rw [he'] at he0'
      obtain rfl := Option.some.inj he0
      obtain rfl := Option.some.inj he0'
      refine Or.inr (LendingLedger.commit_twin he he' _ _ ?_)
      obtain ⟨_, _, _, _, _, -, -, -, -, -, -, -, h1, -⟩ := Loan.manageDefault_ok_parts loan _ r hok
      obtain ⟨_, _, _, _, _, -, -, -, -, -, -, -, h2, -⟩ := Loan.manageDefault_ok_parts loan' _ r' hok'
      rw [h2, h1, Loan.defaultedLoan, Loan.defaultedLoan, (htwin _ _ hat hat').raw]
  · obtain ⟨e0, loan, r, he0, hat, -, -, hok, rfl, -⟩ := LendingLedger.loanPay_ok hb
    obtain ⟨e0', loan', r', he0', hat', -, -, hok', rfl, -⟩ := LendingLedger.loanPay_ok hb'
    rw [he] at he0
    rw [he'] at he0'
    obtain rfl := Option.some.inj he0
    obtain rfl := Option.some.inj he0'
    rw [hnow] at hok'
    exact Or.inr (LendingLedger.commit_twin he he' _ _ (Loan.pay_twin (htwin _ _ hat hat') _ _ _ _ _ hok hok'))

/-- The same LoanSet on two reachable ledgers at the same close time, with vaults of the same asset and scale and
brokers of the same management fee rate, stores twins at the end of both loan lists. -/
private lemma LendingLedger.loanSet_twin {l L l₂ L₂ : LendingLedger} (hr : l.Reachable) (hR : L.Reachable)
    (hnow : L.now = l.now) (hnt : L.vault.numericType = l.vault.numericType)
    (hscale : L.vault.scale = l.vault.scale)
    (hfee : ∀ k b b', l.broker? k = some b → L.broker? k = some b' → b'.managementFeeRate = b.managementFeeRate)
    {tx : LendingTx} (hset : tx.isLoan = true ∧ tx.loanIndex? = none)
    (hb : (l.apply tx).run = .ok (.ok l₂)) (hb' : (L.apply tx).run = .ok (.ok L₂)) :
    ∃ f f', l₂.loan? l.loans.length = some f ∧ L₂.loan? L.loans.length = some f' ∧
      f'.brokerIndex = f.brokerIndex ∧
      f'.loan.toRawLoan = { f.loan.toRawLoan with broker := f'.loan.toRawLoan.broker } := by
  cases tx <;> simp only [LendingTx.isLoan, LendingTx.loanIndex?, Bool.false_eq_true, reduceCtorEq, and_true,
    and_false] at hset
  rename_i k principal rates fees pi pt gp sd twoStep ao
  obtain ⟨b, r, hbk, -, -, -, hcr, rfl, -⟩ := LendingLedger.loanSet_ok hb
  obtain ⟨b', r', hbk', -, -, -, hcr', rfl, -⟩ := LendingLedger.loanSet_ok hb'
  rw [hnow] at hcr'
  have hbnt : b'.numericType = b.numericType := by
    rw [hR.scaleInv.brokers _ b' hbk', hr.scaleInv.brokers _ b hbk, hnt]
  have hbe : L.vault.baseExponent = l.vault.baseExponent := by
    unfold XRPL.Model.SingleAssetVault.Vault.baseExponent; rw [hnt, hscale]
  have ht := Loan.create_twin b b' l.vault L.vault principal rates fees _ ao twoStep r r' hbnt (hfee k b b' hbk hbk')
    hbe hcr hcr'
  refine ⟨{ brokerIndex := k, loan := r.loan' }, { brokerIndex := k, loan := r'.loan' }, ?_, ?_, rfl, ht.raw⟩
  · rw [LendingLedger.loan?_commitLoan]; simp [LoanEffect.ofCreate]
  · rw [LendingLedger.loan?_commitLoan]; simp [LoanEffect.ofCreate]

/-- The loan read at `j` is pending exactly when the stored one is. -/
private lemma LendingLedger.LoanAt.isPending_eq {l : LendingLedger} {j : Nat} {e : LoanEntry} {loan : Loan}
    (hat : l.LoanAt j loan) (he : l.loan? j = some e) : loan.isPending = e.loan.isPending := by
  obtain ⟨e1, b, he1, -, hw⟩ := hat
  rw [he] at he1
  obtain rfl := Option.some.inj he1
  exact (congrArg RawLoan.isPending (Loan.withBroker_eq hw) :)

/-- A LoanAccept succeeds only on a pending loan. -/
private lemma LendingLedger.accept_pending {l l' : LendingLedger} {j : Nat} {e : LoanEntry}
    (he : l.loan? j = some e) (h : (l.apply (.loanAccept j)).run = .ok (.ok l')) : e.loan.isPending = true := by
  obtain ⟨-, loan, -, -, hat, hc, -⟩ := LendingLedger.loanAccept_ok h
  cases hpe : e.loan.isPending
  · rw [Loan.canAccept_not_pending_proof loan _ _ (by rw [hat.isPending_eq he, hpe])] at hc
    injection hc with hc
    cases hc
  · rfl

/-- A LoanDelete, LoanManage or LoanPay on an active loan leaves no pending loan in its slot. -/
private lemma LendingLedger.apply_keeps_active {l l' : LendingLedger} {tx : LendingTx} {j : Nat}
    (h : (l.apply tx).run = .ok (.ok l')) (htx : tx.loanIndex? = some j) (hacc : ∀ k, tx ≠ .loanAccept k)
    (hact : ∀ e, l.loan? j = some e → e.loan.isPending = false) :
    ∀ e, l'.loan? j = some e → e.loan.isPending = false := by
  cases tx <;> simp only [LendingTx.loanIndex?, Option.some.injEq, reduceCtorEq] at htx <;> subst htx
  · exact absurd rfl (hacc _)
  · obtain ⟨-, -, -, -, -, -, -, -, -, hl2, -⟩ := LendingLedger.loanDelete_ok h
    intro e he
    rw [hl2] at he
    cases he
  · obtain ⟨e0, loan, r, he0, hat, -, hok, rfl, -⟩ := LendingLedger.loanManage_ok h
    intro f hf
    rw [LendingLedger.loan?_commit_ofLoan l he0, if_pos rfl] at hf
    obtain rfl := Option.some.inj hf
    show r.loan'.isPending = false
    rw [Loan.manage_isPending _ _ _ _ _ hok, hat.isPending_eq he0]
    exact hact e0 he0
  · obtain ⟨e0, loan, r, he0, hat, -, -, hok, rfl, -⟩ := LendingLedger.loanPay_ok h
    intro f hf
    rw [LendingLedger.loan?_commit_ofLoan l he0, if_pos rfl] at hf
    obtain rfl := Option.some.inj hf
    show r.loan'.isPending = false
    rw [Loan.pay_isPending _ _ _ _ _ _ hok, hat.isPending_eq he0]
    exact hact e0 he0

end XRPL.Model.Lending
