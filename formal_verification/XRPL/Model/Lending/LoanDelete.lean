import XRPL.Model.Protocol.Exponent
import XRPL.Model.Protocol.Number
import XRPL.Model.Protocol.Rounding
import XRPL.Model.Protocol.TER
import XRPL.Model.Vault.Vault
import XRPL.Model.Lending.Loan
import XRPL.Model.Lending.LoanBroker

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault

-- LoanDelete -> preclaim
def Loan.canDelete (loan : Loan) : TER :=
  if !loan.isPending && loan.paymentRemaining > 0 then .tecHAS_OBLIGATIONS
  else .tesSUCCESS

-- bug: C++ hardcodes the accrual formula here, which is wrong for cash-basis vaults
def deletePendingLoan (loan : Loan) (vault : RawVault) (broker : LoanBroker)
    : Except Error (RawVault × LoanBroker) := do
  let vaultExponent ← numberExponent vault.assetsTotal vault.numericType
  let availableAfter ← vault.assetsAvailable.operator_add loan.principalOutstanding .to_nearest
  let reservedAfter ← vault.assetsReserved.operator_sub loan.principalOutstanding .to_nearest
  let vault' := { vault with assetsAvailable := availableAfter, assetsReserved := reservedAfter }

  let debtAfter ← adjustImpreciseNumber vault.numericType broker.debtTotal
    loan.principalOutstanding.operator_neg vaultExponent
  return (vault', { broker with debtTotal := debtAfter,
                                loanCount := broker.loanCount - 1 })

def deleteActiveLoan (vault : RawVault) (broker : LoanBroker) : Except Error (RawVault × LoanBroker) :=
  let loanCount := broker.loanCount - 1
  let newDebt := if loanCount == 0 then Number.zero else broker.debtTotal
  .ok (vault, { broker with loanCount := loanCount, debtTotal := newDebt })

-- LoanDelete -> doApply
def Loan.delete (loan : Loan) (vault : RawVault) (broker : LoanBroker)
    : Except Error (RawVault × LoanBroker) :=
  if loan.isPending then deletePendingLoan loan vault broker
  else deleteActiveLoan vault broker

end XRPL.Model.Lending
