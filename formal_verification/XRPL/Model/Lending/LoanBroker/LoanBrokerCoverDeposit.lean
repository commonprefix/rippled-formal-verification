import XRPL.Model.Protocol.STAmount
import XRPL.Model.Protocol.TER
import XRPL.Model.Lending.LoanBroker.BrokerCover

namespace XRPL.Model.Lending

open XRPL.Model.Protocol

-- LoanBrokerCoverDeposit -> doApply
def LoanBroker.coverDeposit (lb : LoanBroker) (amount : STAmount)
    : Except Error LoanBrokerCoverTerResult := do
  let amount ← match (← lb.roundedCoverAmount amount) with
    | .rejected _ => return .error .tecINTERNAL
    | .rounded amount => .pure amount
  return .ok (← lb.applyCoverTransaction .credit amount)

end XRPL.Model.Lending
