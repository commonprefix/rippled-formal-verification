import XRPL.Model.Protocol.Number
import XRPL.Model.Protocol.STAmount
import XRPL.Model.Protocol.TER
import XRPL.Model.Vault.Vault
import XRPL.Model.Lending.LoanBroker
import XRPL.Model.Lending.LendingHelpers

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault

def LoanBroker.canCoverWithdraw (lb : LoanBroker) (vault : Vault) (amount : STAmount)
    : Except Error TER := do
  let ter ← canApplyToBrokerCover vault.numericType lb.coverAvailable amount
  if ter.operator_bool then
    return ter

  let vaultScale ← getAssetsTotalScale vault.numericType vault.assetsTotal
  let minimumCover ← minimumBrokerCover vault.numericType lb.debtTotal lb.coverRateMinimum vaultScale
  let amountNumber ← amount.toNumber .to_nearest
  if lb.coverAvailable.operator_lt amountNumber then
    return .tecINSUFFICIENT_FUNDS
  let coverAvailable' ← lb.coverAvailable.operator_sub amountNumber .to_nearest
  if coverAvailable'.operator_lt minimumCover then
    return .tecINSUFFICIENT_FUNDS

  return .tesSUCCESS

-- result

def LoanBroker.coverWithdraw (lb : LoanBroker) (amount : STAmount) : Except Error LoanBroker := do
  let amountNumber ← amount.toNumber .to_nearest
  let coverAvailable' ← lb.coverAvailable.operator_sub amountNumber .to_nearest
  return { lb with coverAvailable := coverAvailable' }

end XRPL.Model.Lending
