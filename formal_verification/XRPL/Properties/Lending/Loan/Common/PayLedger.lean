import XRPL.Properties.Lending.Ledger.Common.LoanTxResults
import XRPL.Properties.Lending.Ledger.Common.Exits
import XRPL.Properties.Lending.Ledger.Common.PaymentTotal
import XRPL.Properties.Lending.Ledger.Common.ClosedLoans

/-! # A LoanPay transaction and the payment it runs

A successful LoanPay on the loan stored at `i` ran `Loan.pay` on the loan the ledger reads at `i`, on the ledger's
vault at its close time. The ledger after reads the payment's loan at `i` and holds the payment's vault. -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault (Vault)

/-- A successful LoanPay ran `Loan.pay` on the loan read at `i`, and the ledger after holds its loan and vault. -/
lemma LendingLedger.loanPay_pay {l l' : LendingLedger} {i : Nat} {pt : LoanPaymentType} {amount : Number}
    (h : (l.apply (.loanPay i pt amount)).run = .ok (.ok l')) {loan : Loan} (hat : l.LoanAt i loan) :
    ∃ r : LoanWithAmounts Vault, (loan.pay l.vault pt amount l.now).run = .ok (.ok r) ∧ l'.LoanAt i r.loan' ∧
      l'.vault = r.pool' := by
  obtain ⟨-, loan₀, r, -, hat₀, -, -, hok, -, hv, hat', -, -⟩ := LendingLedger.loanPay_ok h
  obtain rfl := LendingLedger.LoanAt.eq hat₀ hat
  exact ⟨r, hok, hat', hv⟩

/-- A successful LoanPay ran `Loan.pay` on the loan read at `i` before, whose loan the ledger reads at `i` after. -/
lemma LendingLedger.loanPay_loans {l l' : LendingLedger} {i : Nat} {pt : LoanPaymentType} {amount : Number}
    (h : (l.apply (.loanPay i pt amount)).run = .ok (.ok l')) {loan loan' : Loan} (hat : l.LoanAt i loan)
    (hat' : l'.LoanAt i loan') :
    ∃ r : LoanWithAmounts Vault, (loan.pay l.vault pt amount l.now).run = .ok (.ok r) ∧ r.loan' = loan' ∧
      l'.vault = r.pool' := by
  obtain ⟨r, hok, hat'', hv⟩ := LendingLedger.loanPay_pay h hat
  exact ⟨r, hok, LendingLedger.LoanAt.eq hat'' hat', hv⟩

/-- A successful LoanPay paid the instalments of the loan read at `i`, on the ledger's vault at its close time. -/
lemma LendingLedger.loanPay_instalments {l l' : LendingLedger} {i : Nat} {pt : LoanPaymentType} {amount : Number}
    (h : (l.apply (.loanPay i pt amount)).run = .ok (.ok l')) {loan : Loan} (hat : l.LoanAt i loan) :
    ∃ p, (loan.payInstalments l.vault pt amount l.now).run = .ok (.ok p) := by
  obtain ⟨r, hok, -, -⟩ := LendingLedger.loanPay_pay h hat
  obtain ⟨p, hp, -⟩ := Loan.pay_ok loan l.vault pt amount l.now r hok
  exact ⟨p, hp⟩

/-- The instalments a successful LoanPay paid are the ones `loan.payInstalments` names. -/
lemma LendingLedger.loanPay_instalments_eq {l l' : LendingLedger} {i : Nat} {pt : LoanPaymentType} {amount : Number}
    (h : (l.apply (.loanPay i pt amount)).run = .ok (.ok l')) {loan : Loan} (hat : l.LoanAt i loan)
    {p : UnsettledPayment Vault} (hp : (loan.payInstalments l.vault pt amount l.now).run = .ok (.ok p)) :
    ∃ q, (loan.payInstalments l.vault pt amount l.now).run = .ok (.ok q) ∧ q = p := by
  obtain ⟨q, hq⟩ := LendingLedger.loanPay_instalments h hat
  exact ⟨q, hq, Except.ok.inj (Except.ok.inj (hq.symm.trans hp))⟩

/-- A LoanPay that passes its preflight on a live vault returns the `canPay` rejection, or else what `Loan.pay`
returns, written into the ledger. -/
lemma LendingLedger.apply_loanPay_run {l : LendingLedger} {i : Nat} {e : LoanEntry} {b : LoanBroker} {loan : Loan}
    (he : l.loan? i = some e) (hb : l.broker? e.brokerIndex = some b) (hw : e.loan.withBroker b = .ok loan)
    {pt : LoanPaymentType} {amount : Number} (hpre : (LendingTx.loanPay i pt amount).preflight l = .tesSUCCESS)
    (hnd : l.vaultDeleted = false) :
    (l.apply (.loanPay i pt amount)).run =
      if (loan.canPay pt).isTesSuccess then
        ((fun r : LoanWithAmounts Vault => l.commitLoan (LoanEffect.ofLoan i e r.loan' r.pool')) <$>
          loan.pay l.vault pt amount l.now).run
      else .ok (.error (loan.canPay pt)) := by
  rw [LendingLedger.apply_of_preflight hpre]
  simp only [LendingLedger.applyChecked, hnd, LendingTx.isVault, LendingTx.isBroker, Bool.false_eq_true,
    ↓reduceIte, LendingLedger.applyLoan, he, hb, hw]
  unfold_ter
  cases hc : (loan.canPay pt).isTesSuccess
  · simp only [Bool.not_false, ↓reduceIte, Bool.false_eq_true]
    rfl
  · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    generalize (loan.pay l.vault pt amount l.now : Except Error (Except TER (LoanWithAmounts Vault))) = x
    rcases x with _ | _ | _ <;> rfl

/-- A LoanPay that passes its preflight and `canPay` on a live vault returns what `Loan.pay` returns, written
into the ledger. -/
lemma LendingLedger.apply_loanPay_eq {l : LendingLedger} {i : Nat} {e : LoanEntry} {b : LoanBroker} {loan : Loan}
    (he : l.loan? i = some e) (hb : l.broker? e.brokerIndex = some b) (hw : e.loan.withBroker b = .ok loan)
    {pt : LoanPaymentType} {amount : Number} (hpre : (LendingTx.loanPay i pt amount).preflight l = .tesSUCCESS)
    (hnd : l.vaultDeleted = false) (hc : loan.canPay pt = .tesSUCCESS) :
    (l.apply (.loanPay i pt amount)).run =
      ((fun r : LoanWithAmounts Vault => l.commitLoan (LoanEffect.ofLoan i e r.loan' r.pool')) <$>
        loan.pay l.vault pt amount l.now).run := by
  rw [LendingLedger.apply_loanPay_run he hb hw hpre hnd, hc]
  rfl

/-- Writing a result into the ledger keeps a rejection. -/
lemma TerExcept.run_map_error {α β : Type} (f : α → β) (x : TerExcept α) (t : TER) :
    (f <$> x).run = .ok (.error t) ↔ x.run = .ok (.error t) := by
  simp only [ExceptT.run, Functor.map, ExceptT.map, ExceptT.mk]
  generalize (x : Except Error (Except TER α)) = y
  rcases y with _ | _ | _ <;> simp [bind, Except.bind]

/-- `canPay` reads the payment type only for an overpayment. -/
lemma Loan.canPay_eq_regular (loan : Loan) {pt : LoanPaymentType} (hpt : pt ≠ .overpayment) :
    loan.canPay pt = loan.canPay .regular := by
  cases pt
  · rfl
  · rfl
  · rfl
  · exact absurd rfl hpt

/-- An overpayment whose payment equals the regular payment of the same amount leaves the same ledger as the
regular LoanPay. -/
lemma LendingLedger.apply_regular_of_overpayment {l l' : LendingLedger} {i : Nat} {amount : Number}
    (h : (l.apply (.loanPay i .overpayment amount)).run = .ok (.ok l')) {loan : Loan} (hat : l.LoanAt i loan)
    (heq : (loan.overpayment l.vault amount l.now).run = (loan.regularPayment l.vault amount l.now).run) :
    (l.apply (.loanPay i .regular amount)).run = .ok (.ok l') := by
  obtain ⟨-, loan₀, -, -, hat₀, hpre, hc, -, -, -, -, -, -⟩ := LendingLedger.loanPay_ok h
  obtain rfl := LendingLedger.LoanAt.eq hat₀ hat
  obtain ⟨e, b, he, hb, hw⟩ := hat₀
  have hnd := LendingLedger.apply_loan_live rfl h
  have hpre' : (LendingTx.loanPay i .regular amount).preflight l = .tesSUCCESS := hpre
  rw [← h, LendingLedger.apply_loanPay_eq he hb hw hpre' hnd (Loan.canPay_regular_of_overpayment hc),
    LendingLedger.apply_loanPay_eq he hb hw hpre hnd hc]
  have hx : (loan₀.regularPayment l.vault amount l.now : TerExcept (LoanWithAmounts Vault)) =
      loan₀.overpayment l.vault amount l.now := heq.symm
  show (_ <$> loan₀.regularPayment l.vault amount l.now).run = (_ <$> loan₀.overpayment l.vault amount l.now).run
  rw [hx]

/-- Writing a vault effect keeps the deleted flag. -/
private lemma LendingLedger.commitVault_vaultDeleted (l : LendingLedger) (u : VaultEffect) :
    (l.commitVault u).vaultDeleted = l.vaultDeleted := by
  unfold LendingLedger.commitVault
  split <;> rfl

/-- A deleted vault has no broker left: the delete needs every broker gone, and after it only a close succeeds. -/
private lemma LendingLedger.apply_deleted_empty {l l' : LendingLedger} {tx : LendingTx}
    (hinv : l.vaultDeleted = true → l.brokers.any Option.isSome = false)
    (h : (l.apply tx).run = .ok (.ok l')) : l'.vaultDeleted = true → l'.brokers.any Option.isSome = false := by
  have hc := (LendingLedger.apply_checked h).2
  intro hdel
  cases tx
  case close t =>
    cases hc
    exact hinv hdel
  case vaultDelete =>
    simp only [LendingLedger.applyChecked, LendingLedger.applyVaultDelete] at hc
    unfold_ter at hc
    walk_ok
    simpa using ‹¬l.brokers.any Option.isSome = true›
  all_goals
    simp only [LendingLedger.applyChecked] at hc
    split at hc
    · cases hc
    · rename_i hnd
      simp only [LendingTx.isVault, LendingTx.isBroker, Bool.false_eq_true, ↓reduceIte] at hc
      obtain ⟨u, -, rfl⟩ := TerExcept.map_ok hc
      first
        | (rw [LendingLedger.commitVault_vaultDeleted] at hdel; exact absurd hdel hnd)
        | exact absurd hdel hnd

/-- A reachable ledger that stores a loan still has its vault. -/
lemma LendingLedger.Reachable.live_of_loan {l : LendingLedger} (hr : l.Reachable) {i : Nat} {e : LoanEntry}
    (he : l.loan? i = some e) : l.vaultDeleted = false := by
  have hinv : l.vaultDeleted = true → l.brokers.any Option.isSome = false :=
    LendingLedger.Reachable.invariant (Inv := fun l => l.vaultDeleted = true → l.brokers.any Option.isSome = false)
      (fun g hg hd => by rw [hg.not_deleted] at hd; cases hd)
      (fun _ _ _ hi ha => LendingLedger.apply_deleted_empty hi ha) hr
  obtain ⟨b, hb⟩ := hr.loanCountInv.broker_of_loan he
  cases hd : l.vaultDeleted
  · rfl
  · have hany := hinv hd
    unfold LendingLedger.broker? at hb
    cases hj : l.brokers[e.brokerIndex]? with
    | none => rw [hj] at hb; cases hb
    | some x =>
      have hx : (some x).join = some b := by rw [← hj]; exact hb
      have hmem := List.mem_of_getElem? hj
      have : l.brokers.any Option.isSome = true := List.any_eq_true.mpr ⟨x, hmem, by cases x <;> simp_all⟩
      rw [hany] at this
      cases this

end XRPL.Model.Lending
