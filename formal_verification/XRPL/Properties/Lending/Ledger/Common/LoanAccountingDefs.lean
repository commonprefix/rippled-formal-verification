import XRPL.Properties.Lending.Ledger.Common.RunSums

/-! # What each transaction takes off one loan

Each `…Of` reads one amount off the operation a transaction runs on the loan at slot `i` of the ledger `l`, and is
zero for every other transaction. A payment pays scheduled instalments, each one taking its own value, management
fee and one payment off the loan. An overpayment then re-amortizes the loan, a full payment clears what is left and a
default writes it off. The sum of the same name adds the amount up along a sequence of transactions, each read on the
ledger it runs on. -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault (Vault)

open private Loan.scheduledComponents Loan.doPayment from XRPL.Model.Lending.Loan.LoanPay

/-- The scheduled instalments a payment of `amount` pays on `loan`, as its instalment loop walks them: at most `n`,
while payments are left and `amount` covers each one on top of `totalPaid`. Each carries LoanServiceFee. -/
def Loan.scheduledInstalments (loan : Loan) (totalPaid amount : Number) :
    Nat → Except Error (List PaymentComponents)
  | 0 => return []
  | n + 1 => do
    if loan.paymentRemaining == 0 then return []

    let pc ← Loan.scheduledComponents loan
    let pc' : PaymentComponents := { pc with untrackedManagementFee := loan.fees.serviceFee }
    let due ← pc'.totalDue
    if amount.operator_lt (← totalPaid.operator_add due .to_nearest) then return []

    let loan' ← Loan.doPayment loan pc'
    let totalPaid' ← totalPaid.operator_add due .to_nearest
    if pc.isFinal then return [pc']
    let rest ← loan'.scheduledInstalments totalPaid' amount n
    return pc' :: rest

/-- The scheduled instalments a LoanPay on the loan at `i` pays: the ones a regular payment or an overpayment pays
before any overpayment, or the one a late payment pays. A full payment pays none. -/
def LendingLedger.scheduledInstalmentsOf (l : LendingLedger) (i : Nat) : LendingTx → List PaymentComponents
  | .loanPay j pt amount =>
    if j = i then
      match l.loanRead i with
      | some loan =>
        match pt with
        | .regular | .overpayment =>
          match loan.unimpaired.scheduledInstalments Number.zero amount maxPaymentsPerTransaction with
          | .ok pcs => pcs
          | .error _ => []
        | .late =>
          match loan.paymentComponents .late l.now with
          | .ok pc => [pc]
          | .error _ => []
        | .full => []
      | none => []
    else []
  | _ => []

/-- The loan at `i` after the scheduled instalments of an overpayment of `amount`, and after its overpayment
re-amortizes it. -/
def LendingLedger.overpaymentLoans (l : LendingLedger) (i : Nat) (amount : Number) : Option (Loan × Loan) :=
  match l.loanRead i with
  | some loan =>
    match (loan.payInstalments l.vault .regular amount l.now).run,
      (loan.payInstalments l.vault .overpayment amount l.now).run with
    | .ok (.ok scheduled), .ok (.ok reamortized) => some (scheduled.loan, reamortized.loan)
    | _, _ => none
  | none => none

/-- `f` of the loan at `i`, the loan a LoanPay or a LoanManage on `i` reads. -/
def LendingLedger.loanField (l : LendingLedger) (i : Nat) (f : Loan → ℚ) : ℚ :=
  match l.loanRead i with
  | some loan => f loan
  | none => 0

/-- The principal a LoanPay on the loan at `i` pays. -/
def LendingLedger.loanPrincipalPaidOf (l : LendingLedger) (i : Nat) : LendingTx → ℚ
  | .loanPay j pt amount =>
    if j = i then
      match l.loanRead i with
      | some loan =>
        match (loan.payInstalments l.vault pt amount l.now).run with
        | .ok (.ok p) => p.amounts.principalPaid.toRat
        | _ => 0
      | none => 0
    else 0
  | _ => 0

/-- The value of the scheduled instalments a LoanPay on the loan at `i` pays. -/
def LendingLedger.scheduledValueOf (l : LendingLedger) (i : Nat) (tx : LendingTx) : ℚ :=
  ((l.scheduledInstalmentsOf i tx).map fun pc => pc.totalValueDelta.toRat).sum

/-- The management fee of the scheduled instalments a LoanPay on the loan at `i` pays. -/
def LendingLedger.scheduledFeeOf (l : LendingLedger) (i : Nat) (tx : LendingTx) : ℚ :=
  ((l.scheduledInstalmentsOf i tx).map fun pc => pc.managementFeeDelta.toRat).sum

/-- The number of scheduled instalments a LoanPay on the loan at `i` pays. -/
def LendingLedger.scheduledPaymentsOf (l : LendingLedger) (i : Nat) (tx : LendingTx) : ℚ :=
  (l.scheduledInstalmentsOf i tx).length

/-- What the overpayment of a LoanPay on the loan at `i` takes off TotalValueOutstanding: its extra principal and
what the re-amortized schedule drops, `0` when a guard drops it. -/
def LendingLedger.overpaymentValueOf (l : LendingLedger) (i : Nat) : LendingTx → ℚ
  | .loanPay j .overpayment amount =>
    if j = i then
      match l.overpaymentLoans i amount with
      | some (scheduled, reamortized) =>
        scheduled.totalValueOutstanding.toRat - reamortized.totalValueOutstanding.toRat
      | none => 0
    else 0
  | _ => 0

/-- What the overpayment of a LoanPay on the loan at `i` takes off ManagementFeeOutstanding, `0` when a guard drops
it. -/
def LendingLedger.overpaymentFeeOf (l : LendingLedger) (i : Nat) : LendingTx → ℚ
  | .loanPay j .overpayment amount =>
    if j = i then
      match l.overpaymentLoans i amount with
      | some (scheduled, reamortized) =>
        scheduled.managementFeeOutstanding.toRat - reamortized.managementFeeOutstanding.toRat
      | none => 0
    else 0
  | _ => 0

/-- TotalValueOutstanding of the loan at `i` that a full payment clears. -/
def LendingLedger.fullPaymentValueOf (l : LendingLedger) (i : Nat) : LendingTx → ℚ
  | .loanPay j .full _ => if j = i then l.loanField i fun loan => loan.totalValueOutstanding.toRat else 0
  | _ => 0

/-- ManagementFeeOutstanding of the loan at `i` that a full payment clears. -/
def LendingLedger.fullPaymentFeeOf (l : LendingLedger) (i : Nat) : LendingTx → ℚ
  | .loanPay j .full _ => if j = i then l.loanField i fun loan => loan.managementFeeOutstanding.toRat else 0
  | _ => 0

/-- PaymentRemaining of the loan at `i` that a full payment clears. -/
def LendingLedger.fullPaymentPaymentsOf (l : LendingLedger) (i : Nat) : LendingTx → ℚ
  | .loanPay j .full _ => if j = i then l.loanField i fun loan => loan.paymentRemaining.toNat else 0
  | _ => 0

/-- PrincipalOutstanding of the loan at `i` that a default writes off. -/
def LendingLedger.defaultPrincipalOf (l : LendingLedger) (i : Nat) : LendingTx → ℚ
  | .loanManage j .default => if j = i then l.loanField i fun loan => loan.principalOutstanding.toRat else 0
  | _ => 0

/-- TotalValueOutstanding of the loan at `i` that a default writes off. -/
def LendingLedger.defaultValueOf (l : LendingLedger) (i : Nat) : LendingTx → ℚ
  | .loanManage j .default => if j = i then l.loanField i fun loan => loan.totalValueOutstanding.toRat else 0
  | _ => 0

/-- ManagementFeeOutstanding of the loan at `i` that a default writes off. -/
def LendingLedger.defaultFeeOf (l : LendingLedger) (i : Nat) : LendingTx → ℚ
  | .loanManage j .default => if j = i then l.loanField i fun loan => loan.managementFeeOutstanding.toRat else 0
  | _ => 0

/-- PaymentRemaining of the loan at `i` that a default clears. -/
def LendingLedger.defaultPaymentsOf (l : LendingLedger) (i : Nat) : LendingTx → ℚ
  | .loanManage j .default => if j = i then l.loanField i fun loan => loan.paymentRemaining.toNat else 0
  | _ => 0

/-- Σ principal the payments on the loan at `i` pay. -/
def LendingLedger.loanPrincipalPaid (l : LendingLedger) (i : Nat) (txs : List LendingTx) : ℚ :=
  l.runSum (fun l₀ tx => l₀.loanPrincipalPaidOf i tx) txs

/-- Σ value of the scheduled instalments the payments on the loan at `i` pay. -/
def LendingLedger.scheduledValue (l : LendingLedger) (i : Nat) (txs : List LendingTx) : ℚ :=
  l.runSum (fun l₀ tx => l₀.scheduledValueOf i tx) txs

/-- Σ value the overpayments on the loan at `i` take off. -/
def LendingLedger.overpaymentValue (l : LendingLedger) (i : Nat) (txs : List LendingTx) : ℚ :=
  l.runSum (fun l₀ tx => l₀.overpaymentValueOf i tx) txs

/-- Σ management fee of the scheduled instalments the payments on the loan at `i` pay. -/
def LendingLedger.scheduledFee (l : LendingLedger) (i : Nat) (txs : List LendingTx) : ℚ :=
  l.runSum (fun l₀ tx => l₀.scheduledFeeOf i tx) txs

/-- Σ management fee the overpayments on the loan at `i` take off. -/
def LendingLedger.overpaymentFee (l : LendingLedger) (i : Nat) (txs : List LendingTx) : ℚ :=
  l.runSum (fun l₀ tx => l₀.overpaymentFeeOf i tx) txs

/-- The number of scheduled instalments the payments on the loan at `i` pay. -/
def LendingLedger.scheduledPayments (l : LendingLedger) (i : Nat) (txs : List LendingTx) : ℚ :=
  l.runSum (fun l₀ tx => l₀.scheduledPaymentsOf i tx) txs

/-- TotalValueOutstanding a full payment of the loan at `i` clears, `0` if none happens. -/
def LendingLedger.fullPaymentValue (l : LendingLedger) (i : Nat) (txs : List LendingTx) : ℚ :=
  l.runSum (fun l₀ tx => l₀.fullPaymentValueOf i tx) txs

/-- ManagementFeeOutstanding a full payment of the loan at `i` clears, `0` if none happens. -/
def LendingLedger.fullPaymentFee (l : LendingLedger) (i : Nat) (txs : List LendingTx) : ℚ :=
  l.runSum (fun l₀ tx => l₀.fullPaymentFeeOf i tx) txs

/-- PaymentRemaining a full payment of the loan at `i` clears, `0` if none happens. -/
def LendingLedger.fullPaymentPayments (l : LendingLedger) (i : Nat) (txs : List LendingTx) : ℚ :=
  l.runSum (fun l₀ tx => l₀.fullPaymentPaymentsOf i tx) txs

/-- PrincipalOutstanding a default of the loan at `i` writes off, `0` if none happens. -/
def LendingLedger.defaultPrincipal (l : LendingLedger) (i : Nat) (txs : List LendingTx) : ℚ :=
  l.runSum (fun l₀ tx => l₀.defaultPrincipalOf i tx) txs

/-- TotalValueOutstanding a default of the loan at `i` writes off, `0` if none happens. -/
def LendingLedger.defaultValue (l : LendingLedger) (i : Nat) (txs : List LendingTx) : ℚ :=
  l.runSum (fun l₀ tx => l₀.defaultValueOf i tx) txs

/-- ManagementFeeOutstanding a default of the loan at `i` writes off, `0` if none happens. -/
def LendingLedger.defaultFee (l : LendingLedger) (i : Nat) (txs : List LendingTx) : ℚ :=
  l.runSum (fun l₀ tx => l₀.defaultFeeOf i tx) txs

/-- PaymentRemaining a default of the loan at `i` clears, `0` if none happens. -/
def LendingLedger.defaultPayments (l : LendingLedger) (i : Nat) (txs : List LendingTx) : ℚ :=
  l.runSum (fun l₀ tx => l₀.defaultPaymentsOf i tx) txs

end XRPL.Model.Lending
