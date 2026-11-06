import XRPL.Properties.Lending.Ledger.Common.LoanSteps
import XRPL.Properties.Lending.Ledger.Common.BrokerSteps

/-! # What a successful loan transaction did to the ledger

Each lemma turns a successful `l.apply` of a loan transaction into the model operation it ran. The operation reads
the ledger before (`l.LoanAt i loan`, `l.vault`, `l.now`), and the ledger after holds its result (`l'.LoanAt i loan'`,
`l'.vault`). Headline theorems state loan transactions through `l.apply` and reach the operation with these. -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault (Vault)

/-- A loan read with its own broker is itself. -/
lemma Loan.withBroker_self (loan : Loan) : loan.withBroker loan.broker = .ok loan := by
  unfold Loan.withBroker RawLoan.to_lawful
  rw [dif_pos ⟨loan.wf, loan.valid⟩]

/-- The ledger reads at most one loan at `i`. -/
lemma LendingLedger.LoanAt.eq {l : LendingLedger} {i : Nat} {a b : Loan} (ha : l.LoanAt i a) (hb : l.LoanAt i b) :
    a = b := by
  obtain ⟨e₁, b₁, he₁, hb₁, hw₁⟩ := ha
  obtain ⟨e₂, b₂, he₂, hb₂, hw₂⟩ := hb
  rw [he₁] at he₂
  obtain rfl := Option.some.inj he₂
  rw [hb₁] at hb₂
  obtain rfl := Option.some.inj hb₂
  rw [hw₁] at hw₂
  exact Except.ok.inj hw₂

/-- After an operation on the stored loan at `i`, the ledger reads the operation's loan at `i`. -/
lemma LendingLedger.loanAt_commit_ofLoan (l : LendingLedger) {i : Nat} {e : LoanEntry} {b : LoanBroker}
    (he : l.loan? i = some e) (hb : l.broker? e.brokerIndex = some b) (loan' : Loan) (v' : Vault) :
    (l.commitLoan (LoanEffect.ofLoan i e loan' v')).LoanAt i loan' := by
  refine ⟨{ e with loan := loan' }, loan'.broker, ?_, ?_, Loan.withBroker_self loan'⟩
  · rw [LendingLedger.loan?_commit_ofLoan l he]
    simp
  · rw [LendingLedger.broker?_commitLoan l _ b hb]
    simp [LoanEffect.ofLoan]

/-- After an operation on the stored loan at `i`, its broker slot holds the operation's broker. -/
lemma LendingLedger.broker?_commit_ofLoan (l : LendingLedger) {i : Nat} {e : LoanEntry} {b : LoanBroker}
    (hb : l.broker? e.brokerIndex = some b) (loan' : Loan) (v' : Vault) (j : Nat) :
    (l.commitLoan (LoanEffect.ofLoan i e loan' v')).broker? j =
      if j = e.brokerIndex then some loan'.broker else l.broker? j := by
  rw [LendingLedger.broker?_commitLoan l _ b hb]
  rfl

/-- A successful loan transaction passed its preflight. -/
lemma LendingLedger.apply_preflight {l l' : LendingLedger} {tx : LendingTx} (h : (l.apply tx).run = .ok (.ok l')) :
    tx.preflight l = .tesSUCCESS :=
  (TER.isTesSuccess_iff _).mp (LendingLedger.apply_checked h).1

/-- A successful LoanPay: the loan at `i` passed `canPay` and `Loan.pay` returned `r`. The ledger after holds the
vault and the loan of `r`, and the broker of `r` in the loan's broker slot. -/
lemma LendingLedger.loanPay_ok {l l' : LendingLedger} {i : Nat} {paymentType : LoanPaymentType} {amount : Number}
    (h : (l.apply (.loanPay i paymentType amount)).run = .ok (.ok l')) :
    ∃ e loan r, l.loan? i = some e ∧ l.LoanAt i loan ∧
      (LendingTx.loanPay i paymentType amount).preflight l = .tesSUCCESS ∧
      loan.canPay paymentType = .tesSUCCESS ∧ (loan.pay l.vault paymentType amount l.now).run = .ok (.ok r) ∧
      l' = l.commitLoan (LoanEffect.ofLoan i e r.loan' r.pool') ∧
      l'.vault = r.pool' ∧ l'.LoanAt i r.loan' ∧ l'.now = l.now ∧
      ∀ j, l'.broker? j = if j = e.brokerIndex then some r.loan'.broker else l.broker? j := by
  have hpre := LendingLedger.apply_preflight h
  obtain ⟨u, hu, rfl⟩ := LendingLedger.apply_loan rfl h
  obtain ⟨e, b, loan, r, he, hb, hw, hc, hpay, rfl⟩ := l.applyLoan_pay_inv u i paymentType amount hu
  exact ⟨e, loan, r, he, ⟨e, b, he, hb, hw⟩, hpre, hc, hpay, rfl, rfl, l.loanAt_commit_ofLoan he hb _ _, rfl,
    l.broker?_commit_ofLoan hb _ _⟩

/-- A successful LoanManage: the loan at `i` passed `canManage` and `Loan.manage` returned `r`. The ledger after
holds the vault and the loan of `r`, and the broker of `r` in the loan's broker slot. -/
lemma LendingLedger.loanManage_ok {l l' : LendingLedger} {i : Nat} {action : LoanManageAction}
    (h : (l.apply (.loanManage i action)).run = .ok (.ok l')) :
    ∃ e loan r, l.loan? i = some e ∧ l.LoanAt i loan ∧ loan.canManage action l.now = .ok .tesSUCCESS ∧
      (loan.manage action l.vault l.now).run = .ok (.ok r) ∧
      l' = l.commitLoan (LoanEffect.ofLoan i e r.loan' r.pool') ∧
      l'.vault = r.pool' ∧ l'.LoanAt i r.loan' ∧ l'.now = l.now ∧
      ∀ j, l'.broker? j = if j = e.brokerIndex then some r.loan'.broker else l.broker? j := by
  obtain ⟨u, hu, rfl⟩ := LendingLedger.apply_loan rfl h
  obtain ⟨e, b, loan, r, he, hb, hw, hc, hm, rfl⟩ := l.applyLoan_manage_inv u i action hu
  exact ⟨e, loan, r, he, ⟨e, b, he, hb, hw⟩, hc, hm, rfl, rfl, l.loanAt_commit_ofLoan he hb _ _, rfl,
    l.broker?_commit_ofLoan hb _ _⟩

/-- A successful default ran `Loan.manageDefault`, whose loan and vault the ledger holds after. -/
lemma LendingLedger.loanDefault_ok {l l' : LendingLedger} {i : Nat}
    (h : (l.apply (.loanManage i .default)).run = .ok (.ok l')) :
    ∃ e loan r, l.loan? i = some e ∧ l.LoanAt i loan ∧ loan.canManage .default l.now = .ok .tesSUCCESS ∧
      (loan.manageDefault l.vault).run = .ok (.ok r) ∧
      l' = l.commitLoan (LoanEffect.ofLoan i e r.loan' r.pool') ∧
      l'.vault = r.pool' ∧ l'.LoanAt i r.loan' ∧ l'.now = l.now ∧
      ∀ j, l'.broker? j = if j = e.brokerIndex then some r.loan'.broker else l.broker? j := by
  obtain ⟨e, loan, r, he, hat, hc, hm, hl', hv, hat', hnow, hbr⟩ := LendingLedger.loanManage_ok h
  simp only [Loan.manage] at hm
  unfold_ter at hm
  walk_ok
  rename_i r₀ hdef
  exact ⟨e, loan, r₀, he, hat, hc, hdef, hl', hv, hat', hnow, hbr⟩

/-- A successful impairment ran `Loan.manageImpair`, whose loan and vault the ledger holds after. -/
lemma LendingLedger.loanImpair_ok {l l' : LendingLedger} {i : Nat}
    (h : (l.apply (.loanManage i .impair)).run = .ok (.ok l')) :
    ∃ e loan r, l.loan? i = some e ∧ l.LoanAt i loan ∧ loan.canManage .impair l.now = .ok .tesSUCCESS ∧
      (loan.manageImpair l.vault l.now).run = .ok (.ok r) ∧
      l' = l.commitLoan (LoanEffect.ofLoan i e r.loan' r.pool') ∧
      l'.vault = r.pool' ∧ l'.LoanAt i r.loan' ∧ l'.now = l.now ∧
      ∀ j, l'.broker? j = if j = e.brokerIndex then some r.loan'.broker else l.broker? j :=
  LendingLedger.loanManage_ok h

/-- A successful unimpairment ran `Loan.manageUnimpair`, whose loan and vault the ledger holds after. -/
lemma LendingLedger.loanUnimpair_ok {l l' : LendingLedger} {i : Nat}
    (h : (l.apply (.loanManage i .unimpair)).run = .ok (.ok l')) :
    ∃ e loan r, l.loan? i = some e ∧ l.LoanAt i loan ∧ loan.canManage .unimpair l.now = .ok .tesSUCCESS ∧
      (loan.manageUnimpair l.vault).run = .ok (.ok r) ∧
      l' = l.commitLoan (LoanEffect.ofLoan i e r.loan' r.pool') ∧
      l'.vault = r.pool' ∧ l'.LoanAt i r.loan' ∧ l'.now = l.now ∧
      ∀ j, l'.broker? j = if j = e.brokerIndex then some r.loan'.broker else l.broker? j :=
  LendingLedger.loanManage_ok h

/-- A successful LoanAccept: the loan at `i` passed `canAccept` and `Loan.accept` returned `r`. The ledger after
holds the vault and the loan of `r`, and the broker of `r` in the loan's broker slot. -/
lemma LendingLedger.loanAccept_ok {l l' : LendingLedger} {i : Nat}
    (h : (l.apply (.loanAccept i)).run = .ok (.ok l')) :
    ∃ e loan r, l.loan? i = some e ∧ l.LoanAt i loan ∧ loan.canAccept l.vault l.now = .ok .tesSUCCESS ∧
      (loan.accept l.vault).run = .ok (.ok r) ∧
      l' = l.commitLoan (LoanEffect.ofLoan i e r.loan' r.pool') ∧
      l'.vault = r.pool' ∧ l'.LoanAt i r.loan' ∧ l'.now = l.now ∧
      ∀ j, l'.broker? j = if j = e.brokerIndex then some r.loan'.broker else l.broker? j := by
  obtain ⟨u, hu, rfl⟩ := LendingLedger.apply_loan rfl h
  obtain ⟨e, b, loan, r, he, hb, hw, hc, ha, rfl⟩ := l.applyLoan_accept_inv u i hu
  exact ⟨e, loan, r, he, ⟨e, b, he, hb, hw⟩, hc, ha, rfl, rfl, l.loanAt_commit_ofLoan he hb _ _, rfl,
    l.broker?_commit_ofLoan hb _ _⟩

/-- A successful LoanDelete: the loan at `i` passed `canDelete` and `Loan.delete` returned `r`. The ledger after
holds the vault of `r`, no loan at `i`, and the broker of `r` in the loan's broker slot. -/
lemma LendingLedger.loanDelete_ok {l l' : LendingLedger} {i : Nat}
    (h : (l.apply (.loanDelete i)).run = .ok (.ok l')) :
    ∃ e loan r, l.loan? i = some e ∧ l.LoanAt i loan ∧ loan.canDelete = .tesSUCCESS ∧
      (loan.delete l.vault).run = .ok (.ok r) ∧
      l' = l.commitLoan
        { vault := r.pool', brokerIndex := e.brokerIndex, broker := r.broker', loanIndex := i, loan := none } ∧
      l'.vault = r.pool' ∧ l'.loan? i = none ∧ l'.now = l.now ∧
      ∀ j, l'.broker? j = if j = e.brokerIndex then some r.broker' else l.broker? j := by
  obtain ⟨u, hu, rfl⟩ := LendingLedger.apply_loan rfl h
  obtain ⟨e, b, loan, r, he, hb, hw, hc, hd, rfl⟩ := l.applyLoan_delete_inv u i hu
  refine ⟨e, loan, r, he, ⟨e, b, he, hb, hw⟩, hc, hd, rfl, rfl, ?_, rfl, ?_⟩
  · rw [LendingLedger.loan?_commitLoan]
    have hi := LendingLedger.loan?_lt he
    simp [hi]
  · intro j
    rw [LendingLedger.broker?_commitLoan l _ b hb]

/-- A successful LoanSet on broker `j`: the schedule its fields build fits, the broker and the vault passed
`canCreate`, and `Loan.create` returned `r`. The ledger after holds the vault of `r`, the new loan at the end of the
loan list, and the broker of `r` at `j`. -/
lemma LendingLedger.loanSet_ok {l l' : LendingLedger} {j : Nat} {principal : Number} {rates : LoanRates}
    {fees : LoanFees} {paymentInterval paymentTotal gracePeriod : Option UInt32} {startDate : UInt32}
    {twoStep allowsOverpayment : Bool}
    (h : (l.apply (.loanSet j principal rates fees paymentInterval paymentTotal gracePeriod startDate twoStep
      allowsOverpayment)).run = .ok (.ok l')) :
    ∃ broker r, l.broker? j = some broker ∧
      (LendingTx.loanSet j principal rates fees paymentInterval paymentTotal gracePeriod startDate twoStep
        allowsOverpayment).preflight l = .tesSUCCESS ∧
      (LoanSchedule.build paymentInterval paymentTotal gracePeriod startDate l.now twoStep).checkTimeAvailability =
        .ok .tesSUCCESS ∧
      Loan.canCreate broker l.vault principal fees
        (LoanSchedule.build paymentInterval paymentTotal gracePeriod startDate l.now twoStep) l.now twoStep =
        .ok .tesSUCCESS ∧
      (Loan.create broker l.vault principal rates fees
        (LoanSchedule.build paymentInterval paymentTotal gracePeriod startDate l.now twoStep) allowsOverpayment
        twoStep).run = .ok (.ok r) ∧
      l' = l.commitLoan (LoanEffect.ofCreate j l.loans.length r) ∧
      l'.vault = r.pool' ∧ l'.LoanAt l.loans.length r.loan' ∧ l'.now = l.now ∧
      ∀ k, l'.broker? k = if k = j then some r.loan'.broker else l.broker? k := by
  have hpre := LendingLedger.apply_preflight h
  obtain ⟨u, hu, rfl⟩ := LendingLedger.apply_loan rfl h
  have hsched : (LoanSchedule.build paymentInterval paymentTotal gracePeriod startDate l.now
      twoStep).checkTimeAvailability = .ok .tesSUCCESS := by
    simp only [LendingLedger.applyLoan, LendingLedger.applyLoanSet] at hu
    generalize (LoanSchedule.build paymentInterval paymentTotal gracePeriod startDate l.now
      twoStep).checkTimeAvailability = t at hu ⊢
    cases t with
    | error e => simp [ExceptT.run, ExceptT.mk] at hu
    | ok t =>
      dsimp only at hu
      cases ht : t.isTesSuccess
      · rw [ht, if_pos (by decide)] at hu
        cases hu
      · exact congrArg Except.ok ((TER.isTesSuccess_iff t).mp ht)
  obtain ⟨broker, r, hb, hc, hcr, rfl⟩ := l.applyLoanSet_inv u j principal rates fees _ twoStep allowsOverpayment hu
  refine ⟨broker, r, hb, hpre, hsched, hc, hcr, rfl, rfl, ?_, rfl, ?_⟩
  · refine ⟨{ brokerIndex := j, loan := r.loan' }, r.loan'.broker, ?_, ?_, Loan.withBroker_self r.loan'⟩
    · rw [LendingLedger.loan?_commitLoan]
      simp [LoanEffect.ofCreate]
    · rw [LendingLedger.broker?_commitLoan l _ broker hb]
      simp [LoanEffect.ofCreate]
  · intro k
    rw [LendingLedger.broker?_commitLoan l _ broker hb]
    rfl

end XRPL.Model.Lending
