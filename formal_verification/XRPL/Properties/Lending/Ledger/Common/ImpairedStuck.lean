import XRPL.Properties.Lending.Ledger.Common.StuckLoan

/-! # A late loan no payment can pay

On the coarsened vault of `CoarsenedVault.lean` loan C is late, and its late payment of exactly totalDue rounds
to no credit, so the payment fails, impaired or not. Checked by `native_decide`. -/

set_option linter.style.nativeDecide false

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault (Vault)

/-- The coarsened run with loan C impaired after loan A's late payment. -/
private def cwImpairedTxs : List LendingTx := cwCoarsenedTxs ++ [.loanManage 2 .impair]

/-- After `txs`, loan C has the given impaired flag, and its late payment of exactly totalDue passes the payment
checks and is rejected with tecPRECISION_LOSS. -/
private def stuckCheck (txs : List LendingTx) (impaired : Bool) : Bool :=
  match cwGenesis.run txs with
  | .ok l =>
    match l.loan? 2 with
    | some e =>
      match l.broker? e.brokerIndex with
      | some b =>
        match e.loan.withBroker b with
        | .ok loan =>
          match loan.paymentComponents .late l.now with
          | .ok pc =>
            match pc.totalDue with
            | .ok td =>
              decide (e.loan.isImpaired = impaired) && decide (loan.canPay .late = .tesSUCCESS) &&
                (match (l.apply (.loanPay 2 .late td)).run with
                  | .ok (.error .tecPRECISION_LOSS) => true
                  | _ => false)
            | .error _ => false
          | .error _ => false
        | .error _ => false
      | none => false
    | none => false
  | .error _ => false

private lemma stuckCheck_impaired : stuckCheck cwImpairedTxs true = true := by native_decide

private lemma stuckCheck_late : stuckCheck cwCoarsenedTxs false = true := by native_decide

/-- A run whose check passes gives a reachable ledger with that stuck payment. -/
private lemma LendingLedger.stuck_of_check {txs : List LendingTx} {impaired : Bool}
    (h : stuckCheck txs impaired = true) :
    ∃ l : LendingLedger, l.Reachable ∧
      ∃ (e : LoanEntry) (b : LoanBroker) (loan : Loan) (pc : PaymentComponents) (td : Number),
        l.loan? 2 = some e ∧ e.loan.isImpaired = impaired ∧ l.broker? e.brokerIndex = some b ∧
        e.loan.withBroker b = .ok loan ∧ loan.canPay .late = .tesSUCCESS ∧
        loan.paymentComponents .late l.now = .ok pc ∧ pc.totalDue = .ok td ∧
        (l.apply (.loanPay 2 .late td)).run = .ok (.error .tecPRECISION_LOSS) := by
  unfold stuckCheck at h
  split at h
  case h_2 => cases h
  rename_i l hl
  split at h
  case h_2 => cases h
  rename_i e he
  split at h
  case h_2 => cases h
  rename_i b hb
  split at h
  case h_2 => cases h
  rename_i loan hw
  split at h
  case h_2 => cases h
  rename_i pc hpc
  split at h
  case h_2 => cases h
  rename_i td htd
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨himp, hc⟩, hpay⟩ := h
  refine ⟨l, LendingLedger.Reachable.of_run cwGenesis_genesis hl, e, b, loan, pc, td, he, himp, hb, hw, hc, hpc,
    htd, ?_⟩
  split at hpay
  · assumption
  · cases hpay

/-- **An impaired loan on a reachable ledger whose payment passes its checks and fails.** Loan C is impaired
and late, and its late payment of exactly totalDue is rejected with tecPRECISION_LOSS. -/
lemma LendingLedger.impaired_payment_stuck_reachable :
    ∃ l : LendingLedger, l.Reachable ∧
      ∃ (e : LoanEntry) (b : LoanBroker) (loan : Loan) (pc : PaymentComponents) (td : Number),
        l.loan? 2 = some e ∧ e.loan.isImpaired = true ∧ l.broker? e.brokerIndex = some b ∧
        e.loan.withBroker b = .ok loan ∧ loan.canPay .late = .tesSUCCESS ∧
        loan.paymentComponents .late l.now = .ok pc ∧ pc.totalDue = .ok td ∧
        (l.apply (.loanPay 2 .late td)).run = .ok (.error .tecPRECISION_LOSS) :=
  LendingLedger.stuck_of_check stuckCheck_impaired

/-- **A loan that is not impaired on a reachable ledger whose payment passes its checks and fails.** Loan C is
late, and its late payment of exactly totalDue is rejected with tecPRECISION_LOSS. -/
lemma LendingLedger.late_payment_stuck_reachable :
    ∃ l : LendingLedger, l.Reachable ∧
      ∃ (e : LoanEntry) (b : LoanBroker) (loan : Loan) (pc : PaymentComponents) (td : Number),
        l.loan? 2 = some e ∧ e.loan.isImpaired = false ∧ l.broker? e.brokerIndex = some b ∧
        e.loan.withBroker b = .ok loan ∧ loan.canPay .late = .tesSUCCESS ∧
        loan.paymentComponents .late l.now = .ok pc ∧ pc.totalDue = .ok td ∧
        (l.apply (.loanPay 2 .late td)).run = .ok (.error .tecPRECISION_LOSS) :=
  LendingLedger.stuck_of_check stuckCheck_late

end XRPL.Model.Lending
