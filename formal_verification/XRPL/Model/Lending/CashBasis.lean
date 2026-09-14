import XRPL.Model.Protocol.Number
import XRPL.Model.Protocol.Exponent
import XRPL.Model.Protocol.Rounding
import XRPL.Model.Protocol.STAmount
import XRPL.Model.Vault.Vault
import XRPL.Model.Lending.Loan.LoanResult
import XRPL.Model.Lending.Loan.LoanState
import XRPL.Model.Lending.LoanBroker.BrokerCover
import XRPL.Model.Lending.LoanBroker.LoanBroker

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault

namespace CashBasis

-- Apply the amounts one payment moves to the vault and broker
def applyPayment (vault : Vault) (broker : LoanBroker) (amounts : PaymentAmounts) : Except Error BrokerVault := do
  let vaultScale ← numberExponent vault.assetsTotal vault.numericType
  let cash ← amounts.principalPaid.operator_add amounts.interestPaid .to_nearest
  let cashRounded ← STAmount.roundToNumericType vault.numericType cash .downward (some vaultScale)

  -- interest raises AssetsTotal, principal repays DebtTotal
  let assetsAvailable ← vault.assetsAvailable.operator_add cashRounded .to_nearest
  let assetsTotal ← vault.assetsTotal.operator_add amounts.interestPaid .to_nearest
  let debtTotal ← adjustImpreciseNumber vault.numericType broker.debtTotal amounts.principalPaid.operator_neg vaultScale

  -- if cover already meets its minimum, pay the owner, else add the fee to cover
  let minimumCover ← minimumBrokerCover vault.numericType broker.debtTotal broker.coverRateMinimum vaultScale
  let sendFeeToOwner := minimumCover.operator_le broker.coverAvailable
  let coverAvailable' ← if sendFeeToOwner then pure broker.coverAvailable
                        else broker.coverAvailable.operator_add amounts.feePaid .to_nearest

  let rawVault' : RawVault := { vault.toRawVault with assetsTotal := assetsTotal, assetsAvailable := assetsAvailable }
  let vault' ← rawVault'.to_lawful
  let broker' := { broker with debtTotal := debtTotal, coverAvailable := coverAvailable' }

  return { vault := vault', broker := broker' }

end CashBasis

end XRPL.Model.Lending
