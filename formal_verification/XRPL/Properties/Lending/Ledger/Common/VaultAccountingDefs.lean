import XRPL.Properties.Lending.Ledger.Common.RunSums

/-! # What each transaction moves in or out of the vault's balances

Each `…Of` reads one amount off the operation a transaction runs on the ledger `l`, and is zero for every other
kind of transaction. The sum of the same name adds it up along a sequence of transactions, each read on the ledger
it runs on. -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault (Vault)

/-- The assets a VaultDeposit adds after rounding, donations included. -/
def LendingLedger.depositsOf (l : LendingLedger) : LendingTx → ℚ
  | .vaultDeposit _ amount isDonation => l.depositedAssets amount isDonation
  | _ => 0

/-- The assets a VaultWithdraw pays the holder after the early-exit fee. -/
def LendingLedger.withdrawalsOf (l : LendingLedger) : LendingTx → ℚ
  | .vaultWithdraw h amount => l.withdrawalPayout h amount
  | _ => 0

/-- The assets a VaultClawback takes from the holder. -/
def LendingLedger.clawbacksOf (l : LendingLedger) : LendingTx → ℚ
  | .vaultClawback h assets => l.clawedAssets h assets
  | _ => 0

/-- PrincipalRequested of a new loan. -/
def LendingLedger.lentOf (_l : LendingLedger) : LendingTx → ℚ
  | .loanSet _ principal .. => principal.toRat
  | _ => 0

/-- PrincipalRequested of a new pending loan, one that waits for a LoanAccept. -/
def LendingLedger.lentPendingOf (_l : LendingLedger) : LendingTx → ℚ
  | .loanSet _ principal _ _ _ _ _ _ twoStep _ => if twoStep then principal.toRat else 0
  | _ => 0

/-- PrincipalOutstanding of the loan a LoanAccept accepts. -/
def LendingLedger.acceptedOf (l : LendingLedger) : LendingTx → ℚ
  | .loanAccept i =>
    match l.loanRead i with
    | some loan => loan.principalOutstanding.toRat
    | none => 0
  | _ => 0

/-- PrincipalOutstanding of the loan a LoanDelete deletes while it is still pending. -/
def LendingLedger.deletedPendingOf (l : LendingLedger) : LendingTx → ℚ
  | .loanDelete i =>
    match l.loanRead i with
    | some loan => if loan.isPending then loan.principalOutstanding.toRat else 0
    | none => 0
  | _ => 0

/-- The principal a LoanPay pays. -/
def LendingLedger.principalPaidOf (l : LendingLedger) : LendingTx → ℚ
  | .loanPay i pt amount =>
    match l.loanRead i with
    | some loan =>
      match (loan.payInstalments l.vault pt amount l.now).run with
      | .ok (.ok p) => p.amounts.principalPaid.toRat
      | _ => 0
    | none => 0
  | _ => 0

/-- The interest a LoanPay pays. -/
def LendingLedger.interestPaidOf (l : LendingLedger) : LendingTx → ℚ
  | .loanPay i pt amount => l.paidInterest i pt amount
  | _ => 0

/-- amountToPool of a LoanPay: what the borrower sends the vault for the principal and the interest. -/
def LendingLedger.amountToPoolOf (l : LendingLedger) : LendingTx → ℚ
  | .loanPay i pt amount =>
    match l.loanRead i with
    | some loan =>
      match (loan.pay l.vault pt amount l.now).run with
      | .ok (.ok r) => r.amountToPool.toRat
      | _ => 0
    | none => 0
  | _ => 0

/-- PrincipalOutstanding of the loan a default writes off. -/
def LendingLedger.defaultedOf (l : LendingLedger) : LendingTx → ℚ
  | .loanManage i .default =>
    match l.loanRead i with
    | some loan => loan.principalOutstanding.toRat
    | none => 0
  | _ => 0

/-- The cover a default moves from the broker to the vault. -/
def LendingLedger.defaultCoveredOf (l : LendingLedger) : LendingTx → ℚ
  | .loanManage i .default =>
    match l.loanRead i with
    | some loan =>
      match (loan.manageDefault l.vault).run with
      | .ok (.ok r) => r.amountToPool.toRat
      | _ => 0
    | none => 0
  | _ => 0

/-- PrincipalOutstanding of the loan an impairment marks impaired. -/
def LendingLedger.impairedOf (l : LendingLedger) : LendingTx → ℚ
  | .loanManage i .impair =>
    match l.loanRead i with
    | some loan => loan.principalOutstanding.toRat
    | none => 0
  | _ => 0

/-- PrincipalOutstanding of an impaired loan that stops being impaired: by an unimpairment, a payment or a
default. -/
def LendingLedger.unimpairedOf (l : LendingLedger) : LendingTx → ℚ
  | .loanManage i .unimpair =>
    match l.loanRead i with
    | some loan => loan.principalOutstanding.toRat
    | none => 0
  | .loanManage i .default | .loanPay i .. =>
    match l.loanRead i with
    | some loan => if loan.isImpaired then loan.principalOutstanding.toRat else 0
    | none => 0
  | _ => 0

/-- interestDue of a loan that becomes active: a LoanSet that does not wait for a LoanAccept, or a LoanAccept. -/
def LendingLedger.interestBookedOf (l : LendingLedger) : LendingTx → ℚ
  | .loanSet j principal rates fees paymentInterval paymentTotal gracePeriod startDate twoStep allowsOverpayment =>
    if twoStep then 0
    else
      match l.broker? j with
      | some broker =>
        let schedule := LoanSchedule.build paymentInterval paymentTotal gracePeriod startDate l.now twoStep
        match (Loan.create broker l.vault principal rates fees schedule allowsOverpayment twoStep).run with
        | .ok (.ok r) => r.loan'.toExact.interestDue
        | _ => 0
      | none => 0
  | .loanAccept i =>
    match l.loanRead i with
    | some loan => loan.toExact.interestDue
    | none => 0
  | _ => 0

/-- What a LoanPay takes off the loan's interestDue: interestDue before the payment less interestDue after it. -/
def LendingLedger.interestRemovedOf (l : LendingLedger) : LendingTx → ℚ
  | .loanPay i pt amount =>
    match l.loanRead i with
    | some loan =>
      match (loan.pay l.vault pt amount l.now).run with
      | .ok (.ok r) => loan.toExact.interestDue - r.loan'.toExact.interestDue
      | _ => 0
    | none => 0
  | _ => 0

/-- interestDue of the loan a default writes off. -/
def LendingLedger.interestDefaultedOf (l : LendingLedger) : LendingTx → ℚ
  | .loanManage i .default =>
    match l.loanRead i with
    | some loan => loan.toExact.interestDue
    | none => 0
  | _ => 0

/-- Σ deposits over the transactions `txs` applied in order from `l`. -/
def LendingLedger.deposits (l : LendingLedger) (txs : List LendingTx) : ℚ := l.runSum LendingLedger.depositsOf txs

/-- Σ withdrawals over the transactions `txs` applied in order from `l`. -/
def LendingLedger.withdrawals (l : LendingLedger) (txs : List LendingTx) : ℚ := l.runSum LendingLedger.withdrawalsOf txs

/-- Σ clawbacks over the transactions `txs` applied in order from `l`. -/
def LendingLedger.clawbacks (l : LendingLedger) (txs : List LendingTx) : ℚ := l.runSum LendingLedger.clawbacksOf txs

/-- Σ lent over the transactions `txs` applied in order from `l`. -/
def LendingLedger.lent (l : LendingLedger) (txs : List LendingTx) : ℚ := l.runSum LendingLedger.lentOf txs

/-- Σ lentPending over the transactions `txs` applied in order from `l`. -/
def LendingLedger.lentPending (l : LendingLedger) (txs : List LendingTx) : ℚ :=
  l.runSum LendingLedger.lentPendingOf txs

/-- Σ accepted over the transactions `txs` applied in order from `l`. -/
def LendingLedger.accepted (l : LendingLedger) (txs : List LendingTx) : ℚ := l.runSum LendingLedger.acceptedOf txs

/-- Σ deletedPending over the transactions `txs` applied in order from `l`. -/
def LendingLedger.deletedPending (l : LendingLedger) (txs : List LendingTx) : ℚ :=
  l.runSum LendingLedger.deletedPendingOf txs

/-- Σ principalPaid over the transactions `txs` applied in order from `l`. -/
def LendingLedger.principalPaid (l : LendingLedger) (txs : List LendingTx) : ℚ :=
  l.runSum LendingLedger.principalPaidOf txs

/-- Σ interestPaid over the transactions `txs` applied in order from `l`. -/
def LendingLedger.interestPaid (l : LendingLedger) (txs : List LendingTx) : ℚ :=
  l.runSum LendingLedger.interestPaidOf txs

/-- Σ amountToPool over the transactions `txs` applied in order from `l`. -/
def LendingLedger.amountToPool (l : LendingLedger) (txs : List LendingTx) : ℚ :=
  l.runSum LendingLedger.amountToPoolOf txs

/-- Σ defaulted over the transactions `txs` applied in order from `l`. -/
def LendingLedger.defaulted (l : LendingLedger) (txs : List LendingTx) : ℚ := l.runSum LendingLedger.defaultedOf txs

/-- Σ defaultCovered over the transactions `txs` applied in order from `l`. -/
def LendingLedger.defaultCovered (l : LendingLedger) (txs : List LendingTx) : ℚ :=
  l.runSum LendingLedger.defaultCoveredOf txs

/-- Σ impaired over the transactions `txs` applied in order from `l`. -/
def LendingLedger.impaired (l : LendingLedger) (txs : List LendingTx) : ℚ := l.runSum LendingLedger.impairedOf txs

/-- Σ unimpaired over the transactions `txs` applied in order from `l`. -/
def LendingLedger.unimpaired (l : LendingLedger) (txs : List LendingTx) : ℚ :=
  l.runSum LendingLedger.unimpairedOf txs

/-- Σ interestBooked over the transactions `txs` applied in order from `l`. -/
def LendingLedger.interestBooked (l : LendingLedger) (txs : List LendingTx) : ℚ :=
  l.runSum LendingLedger.interestBookedOf txs

/-- Σ interestRemoved over the transactions `txs` applied in order from `l`. -/
def LendingLedger.interestRemoved (l : LendingLedger) (txs : List LendingTx) : ℚ :=
  l.runSum LendingLedger.interestRemovedOf txs

/-- Σ interestDefaulted over the transactions `txs` applied in order from `l`. -/
def LendingLedger.interestDefaulted (l : LendingLedger) (txs : List LendingTx) : ℚ :=
  l.runSum LendingLedger.interestDefaultedOf txs

/-- The vault is not coarsened on any ledger the transactions `txs` pass through from `start`, the first and the
last included. -/
def LendingLedger.NotCoarsenedAlong (start : LendingLedger) (txs : List LendingTx) : Prop :=
  ∀ (pre : List LendingTx) (l : LendingLedger), pre <+: txs → LendingLedger.Reaches start pre l → l.NotCoarsened

end XRPL.Model.Lending
