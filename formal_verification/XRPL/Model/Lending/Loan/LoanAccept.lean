import XRPL.Model.Protocol.Number
import XRPL.Model.Protocol.TER
import XRPL.Model.Lending.AssetPool
import XRPL.Model.Lending.Loan.Loan

namespace XRPL.Model.Lending

open XRPL.Model.Protocol

-- LoanAccept -> preclaim
def Loan.canAccept (loan : Loan) (ledgerCloseTime : UInt32) : TER :=
  if !loan.isPending then .tecNO_PERMISSION
  else if hasExpired ledgerCloseTime loan.schedule.startDate then .tecEXPIRED
  else .tesSUCCESS

-- LoanAccept -> doApply. The principal leaves the reserved assets and the loan becomes active.
def Loan.accept {α : Type} [AssetPool α] (loan : Loan) (pool : α) : Except Error (LoanWithPool α) := do
  let poolAmounts := AssetPool.amounts pool
  let assetsReserved' ← poolAmounts.assetsReserved.operator_sub loan.principalOutstanding .to_nearest
  let pool' ← AssetPool.updateAmounts pool { poolAmounts with assetsReserved := assetsReserved' }

  let rawLoan' : RawLoan := { loan.toRawLoan with isPending := false }
  let loan' ← rawLoan'.to_lawful

  return { loan' := loan', pool' := pool' }

end XRPL.Model.Lending
