import XRPL.Model.Protocol.Exponent
import XRPL.Model.Protocol.Number
import XRPL.Model.Protocol.Rounding
import XRPL.Model.Protocol.TER
import XRPL.Model.Vault.Vault
import XRPL.Model.Lending.Loan.Loan
import XRPL.Model.Lending.Loan.LoanResult
import XRPL.Model.Lending.LoanBroker.LoanBroker

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault

-- LoanDelete -> preclaim
def Loan.canDelete (loan : Loan) : TER :=
  if !loan.isPending && loan.paymentRemaining > 0 then .tecHAS_OBLIGATIONS
  else .tesSUCCESS

-- Undo the bookkeeping of a pending loan: the principal returns from reserved to available and leaves the debt.
def Loan.deletePending (loan : Loan) (vault : Vault) (broker : LoanBroker) : Except Error (LoanResult BrokerVault) := do
  let vaultExponent ← numberExponent vault.assetsTotal vault.numericType
  let assetsAvailable' ← vault.assetsAvailable.operator_add loan.principalOutstanding .to_nearest
  let assetsReserved' ← vault.assetsReserved.operator_sub loan.principalOutstanding .to_nearest

  let rawVault' : RawVault := { vault.toRawVault with assetsAvailable := assetsAvailable', assetsReserved := assetsReserved' }
  let vault' ← rawVault'.to_lawful

  let debtTotal' ← adjustImpreciseNumber vault.numericType broker.debtTotal
    loan.principalOutstanding.operator_neg vaultExponent
  let broker' := { broker with debtTotal := debtTotal', loanCount := broker.loanCount - 1 }

  return .ok { vault := vault', broker := broker' }

-- Delete a paid-off loan. With no loans left, any debt still on the broker is dust and is ignored.
def Loan.deleteActive (vault : Vault) (broker : LoanBroker) : LoanResult BrokerVault :=
  let loanCount := broker.loanCount - 1
  let debtTotal' := if loanCount == 0 then Number.zero else broker.debtTotal

  let broker' := { broker with loanCount := loanCount, debtTotal := debtTotal' }
  .ok { vault := vault, broker := broker' }

-- LoanDelete -> doApply
def Loan.delete (loan : Loan) (vault : Vault) (broker : LoanBroker) : Except Error (LoanResult BrokerVault) :=
  if loan.isPending then loan.deletePending vault broker
  else .ok (Loan.deleteActive vault broker)

end XRPL.Model.Lending
