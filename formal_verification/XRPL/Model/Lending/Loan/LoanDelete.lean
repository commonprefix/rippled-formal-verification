import XRPL.Model.Protocol.Exponent
import XRPL.Model.Protocol.Number
import XRPL.Model.Protocol.Rounding
import XRPL.Model.Protocol.TER
import XRPL.Model.Vault.Vault
import XRPL.Model.Lending.Loan.Loan

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault

-- LoanDelete -> preclaim
def Loan.canDelete (loan : Loan) : TER :=
  if !loan.isPending && loan.paymentRemaining > 0 then .tecHAS_OBLIGATIONS
  else .tesSUCCESS

-- Undo the bookkeeping of a pending loan: the principal returns from reserved to available and leaves the debt.
def Loan.deletePending (loan : Loan) : Except Error LoanBroker := do
  let broker := loan.broker
  let vault := broker.vault

  let vaultExponent ← numberExponent vault.assetsTotal vault.numericType
  let assetsAvailable' ← vault.assetsAvailable.operator_add loan.principalOutstanding .to_nearest
  let assetsReserved' ← vault.assetsReserved.operator_sub loan.principalOutstanding .to_nearest

  let rawVault' : RawVault := { vault.toRawVault with
    assetsAvailable := assetsAvailable', assetsReserved := assetsReserved' }
  let vault' ← rawVault'.to_lawful

  let debtTotal' ← sumRoundAndClamp broker.debtTotal
    loan.principalOutstanding.operator_neg vaultExponent vault.numericType

  let rawBroker' : RawLoanBroker := { broker.toRawLoanBroker with
    debtTotal := debtTotal', loanCount := broker.loanCount - 1
    vault := vault' }
  rawBroker'.to_lawful

-- Delete a paid-off loan. With no loans left, any debt still on the broker is dust and is ignored.
def Loan.deleteActive (broker : LoanBroker) : Except Error LoanBroker :=
  let loanCount := broker.loanCount - 1
  let debtTotal' := if loanCount == 0 then Number.zero else broker.debtTotal

  let rawBroker' : RawLoanBroker := { broker.toRawLoanBroker with
    loanCount := loanCount, debtTotal := debtTotal' }
  rawBroker'.to_lawful

-- LoanDelete -> doApply
def Loan.delete (loan : Loan) : Except Error LoanBroker :=
  if loan.isPending then loan.deletePending
  else Loan.deleteActive loan.broker

end XRPL.Model.Lending
