import XRPL.Model.Protocol.Number
import XRPL.Model.Protocol.Exponent
import XRPL.Model.Protocol.Rounding
import XRPL.Model.Protocol.STAmount
import XRPL.Model.Lending.AssetPool
import XRPL.Model.Lending.Loan.LoanState
import XRPL.Model.Lending.LoanBroker.BrokerCover
import XRPL.Model.Lending.LoanBroker.LoanBroker

namespace XRPL.Model.Lending

open XRPL.Model.Protocol

namespace CashBasis

-- Apply the amounts one payment moves to the broker and its pool. Also returns the amount the pool gets.
def applyPayment {α : Type} [AssetPool α] (broker : LoanBroker) (pool : α) (amounts : PaymentAmounts)
    : Except Error (LoanBrokerWithPool α × Number) := do
  let nt := broker.numericType
  let poolAmounts := AssetPool.amounts pool
  let vaultScale ← AssetPool.exponent pool nt
  let totalPaid ← amounts.principalPaid.operator_add amounts.interestPaid .to_nearest
  let totalPaid' ← STAmount.roundToNumericType nt totalPaid .downward (some vaultScale)

  -- interest raises AssetsTotal, principal repays DebtTotal
  let assetsAvailable ← poolAmounts.assetsAvailable.operator_add totalPaid' .to_nearest
  let assetsTotal ← poolAmounts.assetsTotal.operator_add amounts.interestPaid .to_nearest
  let debtTotal ← sumRoundAndClamp broker.debtTotal amounts.principalPaid.operator_neg vaultScale nt

  -- if cover already meets its minimum, pay the owner, else add the fee to cover
  let hasMinimumCover ← broker.hasMinimumCover vaultScale
  let coverAvailable' ← if hasMinimumCover then pure broker.coverAvailable
                        else broker.coverAvailable.operator_add amounts.feePaid .to_nearest

  let pool' ← AssetPool.updateAmounts pool { poolAmounts with
    assetsTotal := assetsTotal, assetsAvailable := assetsAvailable }

  let rawBroker' : RawLoanBroker := { broker.toRawLoanBroker with
    debtTotal := debtTotal, coverAvailable := coverAvailable' }
  let broker' ← rawBroker'.to_lawful

  return ({ broker' := broker', pool' := pool' }, totalPaid')

end CashBasis

end XRPL.Model.Lending
