import XRPL.Model.Protocol.Number
import XRPL.Model.Protocol.STAmount
import XRPL.Model.Protocol.TER
import XRPL.Model.Lending.AssetPool
import XRPL.Model.Lending.Loan.Loan

namespace XRPL.Model.Lending

open XRPL.Model.Protocol

-- LoanDelete -> preclaim
def Loan.canDelete (loan : Loan) : TER :=
  if !loan.isPending && loan.paymentRemaining > 0 then .tecHAS_OBLIGATIONS
  else .tesSUCCESS

def LoanBroker.releaseLoan (lb : LoanBroker) (debtTotal : Number) : Except Error LoanBroker :=
  let loanCount' := lb.loanCount - 1
  let debtTotal' := if loanCount' == 0 then Number.zero else debtTotal
  let rawBroker' : RawLoanBroker := { lb.toRawLoanBroker with loanCount := loanCount', debtTotal := debtTotal' }
  rawBroker'.to_lawful

-- Undo the bookkeeping of a pending loan: the principal returns from reserved to available and leaves the debt.
def Loan.deletePending {α : Type} [AssetPool α] (loan : Loan) (pool : α) : TerExcept (LoanBrokerWithPool α) := do
  let broker := loan.broker
  let principal := loan.principalOutstanding

  let principal' ← STAmount.roundToNumericType broker.numericType principal .to_nearest
  let change : PoolBalanceChange := {
    cash := principal'
    deployed := principal.operator_neg
    reserved := principal'.operator_neg }
  let pool' ← AssetPool.adjustBalances pool change

  let debtTotal' ← broker.debtTotal.operator_sub principal .to_nearest
  let broker' ← broker.releaseLoan debtTotal'

  return { broker' := broker', pool' := pool' }

-- Delete a paid-off loan.
def Loan.deleteActive (broker : LoanBroker) : Except Error LoanBroker :=
  broker.releaseLoan broker.debtTotal

-- LoanDelete -> doApply. Deleting a paid-off loan leaves the pool untouched.
def Loan.delete {α : Type} [AssetPool α] (loan : Loan) (pool : α) : TerExcept (LoanBrokerWithPool α) :=
  if loan.isPending then loan.deletePending pool
  else do
    let broker' ← Loan.deleteActive loan.broker
    return { broker' := broker', pool' := pool }

end XRPL.Model.Lending
