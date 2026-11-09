import XRPL.Properties.Lending.Ledger.Common.Exits
import XRPL.Properties.Lending.Ledger.Common.LoanCountInv
import XRPL.Properties.Lending.Ledger.Common.ScaleInv
import XRPL.Properties.Lending.Loan.Common.DeleteExits

/-! # Closed loans can always be deleted

A loan takes any broker of the same asset, every stored loan has a stored broker of the vault's asset,
so a paid-off or defaulted loan passes LoanDelete on every reachable ledger. -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault (Vault)

/-- A loan takes any broker of the same asset: its checks read the broker only through the asset. -/
lemma Loan.withBroker_ok (loan : Loan) (b : LoanBroker) (hnt : b.numericType = loan.broker.numericType) :
    ∃ loan', loan.withBroker b = .ok loan' := by
  unfold Loan.withBroker
  have hv := loan.valid
  have hvalid : ({ loan.toRawLoan with broker := b } : RawLoan).Valid := { hv with }
  have hw := loan.wf
  have hwf : ({ loan.toRawLoan with broker := b } : RawLoan).WF :=
    { hw with
      totalValueOutstanding_atExponent := by show _ = true; rw [hnt]; exact hw.totalValueOutstanding_atExponent
      principalOutstanding_atExponent := by show _ = true; rw [hnt]; exact hw.principalOutstanding_atExponent
      managementFeeOutstanding_atExponent := by
        show _ = true; rw [hnt]; exact hw.managementFeeOutstanding_atExponent
      originationFee_atExponent := by show _ = true; rw [hnt]; exact hw.originationFee_atExponent }
  obtain ⟨l', hl', -⟩ := RawLoan.to_lawful_ok_of hwf hvalid
  exact ⟨l', hl'⟩

/-- A stored loan's broker is stored. -/
lemma LendingLedger.LoanCountInv.broker_of_loan {l : LendingLedger} (hinv : l.LoanCountInv) {i : Nat}
    {e : LoanEntry} (he : l.loan? i = some e) : ∃ b, l.broker? e.brokerIndex = some b := by
  cases hb : l.broker? e.brokerIndex with
  | none => have := hinv.orphans _ hb; have := LendingLedger.loansOf_pos he; omega
  | some b => exact ⟨b, rfl⟩

/-- A closed loan on a reachable ledger can always be deleted. A paid-off or defaulted loan that is not
pending passes LoanDelete. -/
lemma LendingLedger.closed_loan_deletable (l : LendingLedger) (hr : l.Reachable) (hnd : l.vaultDeleted = false)
    (i : Nat) (e : LoanEntry) (he : l.loan? i = some e) (hpaid : e.loan.paymentRemaining = 0)
    (hnp : e.loan.isPending = false) : ∃ l', (l.apply (.loanDelete i)).run = .ok (.ok l') := by
  obtain ⟨b, hb⟩ := hr.loanCountInv.broker_of_loan he
  have hs := hr.scaleInv
  obtain ⟨loan, hw⟩ := Loan.withBroker_ok e.loan b (by rw [hs.brokers _ b hb, hs.loanBroker i e he])
  have hraw := Loan.withBroker_eq hw
  have hp' : loan.isPending = false := by rw [show loan.isPending = loan.toRawLoan.isPending from rfl, hraw]; exact hnp
  have hpr : loan.paymentRemaining = 0 := by
    rw [show loan.paymentRemaining = loan.toRawLoan.paymentRemaining from rfl, hraw]; exact hpaid
  have hc : loan.canDelete = .tesSUCCESS := by unfold Loan.canDelete; simp [hp', hpr]
  have hlb : loan.broker = b := by rw [show loan.broker = loan.toRawLoan.broker from rfl, hraw]
  obtain ⟨b', hb', -⟩ := Loan.deleteActive_ok loan.broker (by rw [hlb]; exact hr.loanCountInv.loanCount_ne_zero he hb)
  have hdel := Loan.delete_active_reduce loan l.vault hp'
  rw [hb'] at hdel
  let u : LoanEffect := { vault := l.vault, brokerIndex := e.brokerIndex, broker := b', loanIndex := i, loan := none }
  refine ⟨l.commitLoan u, ?_⟩
  rw [LendingLedger.apply_of_preflight rfl]
  simp only [LendingLedger.applyChecked, hnd, LendingTx.isVault, LendingTx.isBroker, Bool.false_eq_true,
    ↓reduceIte, LendingLedger.applyLoan, he, hb, hw]
  unfold_ter
  simp only [ExceptT.run] at hdel
  rw [hc, show TER.tesSUCCESS.isTesSuccess = true from rfl]
  simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, hdel]
  rfl

end XRPL.Model.Lending
