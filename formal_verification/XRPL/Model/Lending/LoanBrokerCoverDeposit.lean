import XRPL.Model.Protocol.NumericType
import XRPL.Model.Protocol.STAmount
import XRPL.Model.Lending.BrokerCover

namespace XRPL.Model.Lending

open XRPL.Model.Protocol

def LoanBroker.coverDeposit (lb : LoanBroker) (numericType : NumericType) (amount : STAmount)
    : Except Error LoanBrokerCoverResult := do
  let rounded ← lb.roundedCoverAmount numericType amount
  lb.applyCoverFlow numericType .inflow rounded

end XRPL.Model.Lending
