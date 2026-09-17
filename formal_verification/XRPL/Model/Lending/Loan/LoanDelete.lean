import XRPL.Model.Protocol.Exponent
import XRPL.Model.Protocol.Number
import XRPL.Model.Protocol.Rounding
import XRPL.Model.Protocol.TER
import XRPL.Model.Lending.AssetPool
import XRPL.Model.Lending.Loan.Loan

namespace XRPL.Model.Lending

open XRPL.Model.Protocol

-- LoanDelete -> preclaim
def Loan.canDelete (loan : Loan) : TER :=
  if !loan.isPending && loan.paymentRemaining > 0 then .tecHAS_OBLIGATIONS
  else .tesSUCCESS

-- Undo the bookkeeping of a pending loan: the principal returns from reserved to available and leaves the debt.
def Loan.deletePending {α : Type} [AssetPool α] (loan : Loan) (pool : α)
    : Except Error (LoanBrokerWithPool α) := do
  let broker := loan.broker
  let nt := broker.numericType
  let poolAmounts := AssetPool.amounts pool

  let vaultExponent ← AssetPool.exponent pool nt
  let assetsAvailable' ← poolAmounts.assetsAvailable.operator_add loan.principalOutstanding .to_nearest
  let assetsReserved' ← poolAmounts.assetsReserved.operator_sub loan.principalOutstanding .to_nearest

  let pool' ← AssetPool.updateAmounts pool { poolAmounts with
    assetsAvailable := assetsAvailable', assetsReserved := assetsReserved' }

  let debtTotal' ← sumRoundAndClamp broker.debtTotal
    loan.principalOutstanding.operator_neg vaultExponent nt
  let rawBroker' : RawLoanBroker := { broker.toRawLoanBroker with
    debtTotal := debtTotal', loanCount := broker.loanCount - 1 }
  let broker' ← rawBroker'.to_lawful

  return { broker' := broker', pool' := pool' }

-- Delete a paid-off loan. With no loans left, any debt still on the broker is dust and is ignored.
def Loan.deleteActive (broker : LoanBroker) : Except Error LoanBroker :=
  let loanCount := broker.loanCount - 1
  let debtTotal' := if loanCount == 0 then Number.zero else broker.debtTotal

  let rawBroker' : RawLoanBroker := { broker.toRawLoanBroker with
    loanCount := loanCount, debtTotal := debtTotal' }
  rawBroker'.to_lawful

-- LoanDelete -> doApply. Deleting a paid-off loan leaves the pool untouched.
def Loan.delete {α : Type} [AssetPool α] (loan : Loan) (pool : α) : Except Error (LoanBrokerWithPool α) :=
  if loan.isPending then loan.deletePending pool
  else do
    let broker' ← Loan.deleteActive loan.broker
    return { broker' := broker', pool' := pool }

end XRPL.Model.Lending
