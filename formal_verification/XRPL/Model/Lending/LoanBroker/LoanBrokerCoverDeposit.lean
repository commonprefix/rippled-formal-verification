import XRPL.Model.Protocol.STAmount
import XRPL.Model.Protocol.TER
import XRPL.Model.Lending.LoanBroker.BrokerCover

namespace XRPL.Model.Lending

open XRPL.Model.Protocol

-- LoanBrokerCoverDeposit -> preclaim
def LoanBroker.canCoverDeposit {α : Type} [AssetPool α] (lb : LoanBroker) (pool : α) (amount : STAmount)
    : Except Error TER := do
  match ← (lb.roundedCoverAmount pool amount).run with
  | .error ter => return ter
  | .ok amount => lb.checkCoverOpenLimit pool amount

-- LoanBrokerCoverDeposit -> doApply
def LoanBroker.coverDeposit {α : Type} [AssetPool α] (lb : LoanBroker) (pool : α) (amount : STAmount)
    : TerExcept LoanBrokerCoverResult := do
  let amount ← try lb.roundedCoverAmount pool amount catch _ : TER => throw .tecINTERNAL
  lb.applyCoverTransaction .credit amount

end XRPL.Model.Lending
