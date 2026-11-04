import XRPL.Properties.Lending.Ledger.Common.LoanSubsequenceDefs

/-! # The transactions of one broker

A sequence of transactions and its subsequence of one broker's and its loans' transactions, each at the same close
time: the broker's own transactions, the LoanSets on it, every LoanAccept, LoanDelete, LoanManage and LoanPay on its
loans, and every ledger close. Without the other brokers and loans the broker and its new loans can get lower
numbers, so their transactions are renumbered. -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol

/-- The transaction with its broker number set to `k'`. Only the broker transactions after create and LoanSet name a
broker, every other transaction stays as it is. -/
def LendingTx.withBroker (k' : Nat) : LendingTx → LendingTx
  | .loanBrokerUpdate _ debtMaximum => .loanBrokerUpdate k' debtMaximum
  | .loanBrokerCoverDeposit _ amount => .loanBrokerCoverDeposit k' amount
  | .loanBrokerCoverWithdraw _ amount => .loanBrokerCoverWithdraw k' amount
  | .loanBrokerCoverClawback _ amount => .loanBrokerCoverClawback k' amount
  | .loanBrokerDelete _ => .loanBrokerDelete k'
  | .loanSet _ principal rates fees paymentInterval paymentTotal gracePeriod startDate twoStep allowsOverpayment =>
    .loanSet k' principal rates fees paymentInterval paymentTotal gracePeriod startDate twoStep allowsOverpayment
  | tx => tx

/-- A transaction that creates a broker or a loan, or accepts a loan. -/
def LendingTx.isOpening : LendingTx → Bool
  | .loanBrokerCreate _ | .loanSet .. | .loanAccept _ => true
  | _ => false

/-- The number broker `k` gets when only its own transactions run from `l`: its own number when it is already on
`l`, else the next free slot of `l`. -/
def LendingLedger.aloneBrokerIndex (l : LendingLedger) (k : Nat) : Nat := min k l.brokers.length

/-- The number of loan `i` in the subsequence. Loans on the start ledger keep their number, and the broker's new
loans `created`, listed in the order they were created, follow the `base` loans of the start ledger. -/
def subLoanIndex (base : Nat) (created : List Nat) (i : Nat) : Nat :=
  if i < base then i else base + created.idxOf i

/-- The transactions of broker `k` and its loans among `txs` run from `l`, renumbered to broker `k'`, with every
ledger close. `created` lists the loans of `k` created so far. After a failing transaction the rest is dropped. -/
def LendingLedger.brokerTxsFrom (k k' base : Nat) (created : List Nat) (l : LendingLedger) :
    List LendingTx → List LendingTx
  | [] => []
  | tx :: txs =>
    let step : List LendingTx × List Nat :=
      match tx with
      | .close _ => ([tx], created)
      | .loanSet .. =>
        if l.loanTxBroker? tx = some k then ([tx.withBroker k'], created ++ [l.loans.length]) else ([], created)
      | _ =>
        if l.txBroker? tx = some k then
          match tx.loanIndex? with
          | some i => ([tx.withLoan (subLoanIndex base created i)], created)
          | none => ([tx.withBroker k'], created)
        else ([], created)
    step.1 ++
      match (l.apply tx).run with
      | .ok (.ok l') => LendingLedger.brokerTxsFrom k k' base step.2 l' txs
      | _ => []

/-- The subsequence of broker `k`'s and its loans' transactions among `txs` from `start`, each at the same close
time, with the broker renumbered to `start.aloneBrokerIndex k`. -/
def LendingLedger.brokerSubsequence (start : LendingLedger) (k : Nat) (txs : List LendingTx) : List LendingTx :=
  start.brokerTxsFrom k (start.aloneBrokerIndex k) start.loans.length [] txs

/-- Every creation of a broker or a loan and every LoanAccept in `txs` succeeds on the ledger it runs on from
`start`. -/
def LendingLedger.OpeningsSucceedAlong (start : LendingLedger) (txs : List LendingTx) : Prop :=
  ∀ (pre : List LendingTx) (m : LendingLedger) (tx : LendingTx), pre ++ [tx] <+: txs →
    LendingLedger.Reaches start pre m → tx.isOpening = true → ∃ m', (m.apply tx).run = .ok (.ok m')

/-- The balances the model does not track fit before each transaction of `txs` from `start`: broker `k`'s cover as
an amount of the asset, and a LoanPay's credit to the vault and fee within the XRP or MPT supply. -/
def LendingLedger.BrokerUntrackedFitsAlong (start : LendingLedger) (k : Nat) (txs : List LendingTx) : Prop :=
  ∀ (pre : List LendingTx) (m : LendingLedger) (tx : LendingTx), pre ++ [tx] <+: txs →
    LendingLedger.Reaches start pre m →
    (∀ b : LoanBroker, m.broker? k = some b → b.coverAvailable.toRat < 10 ^ 96) ∧
    ∀ (i : Nat) (paymentType : LoanPaymentType) (amount : Number), tx = .loanPay i paymentType amount →
      m.CreditFits i paymentType amount ∧ m.FeeFits i paymentType amount

end XRPL.Model.Lending
