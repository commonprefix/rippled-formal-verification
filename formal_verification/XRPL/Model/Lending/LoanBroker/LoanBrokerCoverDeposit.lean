import XRPL.Model.Protocol.NumericType
import XRPL.Model.Protocol.STAmount
import XRPL.Model.Lending.Loan.LoanResult
import XRPL.Model.Lending.LoanBroker.BrokerCover

namespace XRPL.Model.Lending

open XRPL.Model.Protocol

def LoanBroker.coverDeposit (lb : LoanBroker) (numericType : NumericType) (amount : STAmount)
    : Except Error (LoanResult LoanBrokerCoverResult) := do
  let amount ← match (← lb.roundedCoverAmount numericType amount) with
    | .rejected _ => return .rejected .tecINTERNAL
    | .rounded amount => .pure amount
  return .ok (← lb.applyCoverTransaction .credit amount)

end XRPL.Model.Lending
