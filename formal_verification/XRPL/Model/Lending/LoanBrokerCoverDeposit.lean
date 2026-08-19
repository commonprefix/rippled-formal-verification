import XRPL.Model.Protocol.Number
import XRPL.Model.Protocol.STAmount
import XRPL.Model.Protocol.TER
import XRPL.Model.Vault.Vault
import XRPL.Model.Lending.LoanBroker

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault

inductive RoundedCoverDepositResult where
  | rejected (ter : TER)
  | rounded (amount : STAmount)

def LoanBroker.roundedCoverDeposit (lb : LoanBroker) (vaultNumericType : NumericType) (amount : STAmount) : Except Error RoundedCoverDepositResult := do
  let exponent ← exponent lb.coverAvailable vaultNumericType
  let rounded ← STAmount.roundToExponent amount exponent .downward
  if rounded.signum == 0 then
    return .rejected .tecPRECISION_LOSS
  return .rounded rounded

structure LoanBrokerCoverDepositResult where
  status : TER
  amountDeposit' : STAmount
  loanBroker' : LoanBroker

def LoanBroker.coverDeposit (lb : LoanBroker) (vaultNumericType : NumericType) (amount : STAmount) : Except Error LoanBrokerCoverDepositResult := do
  let result : LoanBrokerCoverDepositResult := {
    status := .tesSUCCESS,
    amountDeposit' := STAmount.zero vaultNumericType,
    loanBroker' := lb
  }

  let rounded ← match (← lb.roundedCoverDeposit vaultNumericType amount) with
    | .rejected _ => return { result with status := .tecINTERNAL }
    | .rounded amount => .pure amount
  -- rounded cannot be 0 here, don't implement the CPP defensive 0 check

  let roundedNumber ← rounded.toNumber .to_nearest
  let coverAvailable' ← lb.coverAvailable.operator_add roundedNumber .to_nearest
  let lb' := { lb with coverAvailable := coverAvailable' }
  return { result with amountDeposit' := rounded, loanBroker' := lb' }

end XRPL.Model.Lending
