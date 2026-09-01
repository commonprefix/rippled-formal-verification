import XRPL.Model.Protocol.Number
import XRPL.Model.Protocol.TER
import XRPL.Model.Vault.Vault
import XRPL.Model.Lending.Loan
import XRPL.Model.Lending.LendingHelpers

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault

-- LoanAccept -> preclaim
def Loan.canAccept (loan : Loan) (ledgerCloseTime : UInt32) : TER :=
  if !loan.isPending then .tecNO_PERMISSION
  else if hasExpired ledgerCloseTime loan.schedule.startDate then .tecEXPIRED
  else .tesSUCCESS

-- LoanAccept -> doApply
def Loan.accept (loan : Loan) (vault : RawVault) : Except Error (Loan × RawVault) := do
  let reservedAfter ← vault.assetsReserved.operator_sub loan.principalOutstanding .to_nearest
  return ({ loan with isPending := false }, { vault with assetsReserved := reservedAfter })

end XRPL.Model.Lending
