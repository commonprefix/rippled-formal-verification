import XRPL.Model.Protocol.Number
import XRPL.Model.Protocol.TER
import XRPL.Model.Vault.Vault
import XRPL.Model.Lending.Loan.Loan

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault

-- LoanAccept -> preclaim
def Loan.canAccept (loan : Loan) (ledgerCloseTime : UInt32) : TER :=
  if !loan.isPending then .tecNO_PERMISSION
  else if hasExpired ledgerCloseTime loan.schedule.startDate then .tecEXPIRED
  else .tesSUCCESS

-- LoanAccept -> doApply. The principal leaves the reserved assets and the loan becomes active.
def Loan.accept (loan : Loan) : Except Error Loan := do
  let vault := loan.broker.vault
  let assetsReserved' ← vault.assetsReserved.operator_sub loan.principalOutstanding .to_nearest
  let rawVault' : RawVault := { vault.toRawVault with assetsReserved := assetsReserved' }
  let vault' ← rawVault'.to_lawful

  let rawBroker' : RawLoanBroker := { loan.broker.toRawLoanBroker with vault := vault' }
  let broker' ← rawBroker'.to_lawful

  let rawLoan' : RawLoan := { loan.toRawLoan with isPending := false, broker := broker' }
  rawLoan'.to_lawful

end XRPL.Model.Lending
