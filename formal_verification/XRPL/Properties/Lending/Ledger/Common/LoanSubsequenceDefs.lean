import XRPL.Properties.Lending.Ledger.Common.IsolationDefs
import XRPL.Properties.Lending.Ledger.Common.VaultAccountingDefs

/-! # The transactions of one loan

A sequence of transactions and its subsequence of one loan's transactions, each at the same close time: the LoanSet
that creates the loan, every LoanAccept, LoanDelete, LoanManage and LoanPay on it, and every ledger close. Without
the other LoanSets the loan can get a lower number, so its transactions are renumbered. -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol

/-- The transaction with its loan number set to `i'`. Only LoanAccept, LoanDelete, LoanManage and LoanPay name a
loan, every other transaction stays as it is. -/
def LendingTx.withLoan (i' : Nat) : LendingTx → LendingTx
  | .loanAccept _ => .loanAccept i'
  | .loanDelete _ => .loanDelete i'
  | .loanManage _ action => .loanManage i' action
  | .loanPay _ paymentType amount => .loanPay i' paymentType amount
  | tx => tx

/-- The number loan `i` gets when only its own transactions run from `l`: its own number when it is already on `l`,
else the next free slot of `l`. -/
def LendingLedger.aloneIndex (l : LendingLedger) (i : Nat) : Nat := min i l.loans.length

/-- The transactions of loan `i` among `txs` run from `l`, renumbered to `i'`, with every ledger close. Its LoanSet is
the one run while the ledger holds `i` loans. After a failing transaction the rest is dropped. -/
def LendingLedger.loanTxsFrom (i i' : Nat) (l : LendingLedger) : List LendingTx → List LendingTx
  | [] => []
  | tx :: txs =>
    let kept : List LendingTx :=
      match tx with
      | .close _ => [tx]
      | .loanSet .. => if l.loans.length = i then [tx] else []
      | _ => if tx.loanIndex? = some i then [tx.withLoan i'] else []
    kept ++
      match (l.apply tx).run with
      | .ok (.ok l') => LendingLedger.loanTxsFrom i i' l' txs
      | _ => []

/-- The subsequence of loan `i`'s transactions among `txs` from `start`, each at the same close time, with the loan
renumbered to `start.aloneIndex i`. -/
def LendingLedger.loanSubsequence (start : LendingLedger) (i : Nat) (txs : List LendingTx) : List LendingTx :=
  start.loanTxsFrom i (start.aloneIndex i) txs

/-- The balances the model does not track fit before each transaction of `txs` from `start`: the cover of loan
`i`'s broker as an amount of the asset, and a LoanPay's credit to the vault and fee within the XRP or MPT supply. -/
def LendingLedger.UntrackedFitsAlong (start : LendingLedger) (i : Nat) (txs : List LendingTx) : Prop :=
  ∀ (pre : List LendingTx) (m : LendingLedger) (tx : LendingTx), pre ++ [tx] <+: txs →
    LendingLedger.Reaches start pre m →
    (∀ (e : LoanEntry) (b : LoanBroker), m.loan? i = some e → m.broker? e.brokerIndex = some b →
      b.coverAvailable.toRat < 10 ^ 96) ∧
    ∀ (paymentType : LoanPaymentType) (amount : Number), tx = .loanPay i paymentType amount →
      m.CreditFits i paymentType amount ∧ m.FeeFits i paymentType amount

end XRPL.Model.Lending
