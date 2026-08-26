import XRPL.Model.Protocol.Exponent
import XRPL.Model.Protocol.Number
import XRPL.Model.Protocol.Result
import XRPL.Model.Protocol.STAmount
import XRPL.Model.Protocol.TER
import XRPL.Model.Lending.LoanBroker

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.Result

def LoanBroker.roundedCoverDeposit (lb : LoanBroker) (numericType : NumericType) (amount : STAmount) : Except Error RoundingResult := do
  let exponent ← numberExponent lb.coverAvailable numericType
  let rounded ← STAmount.roundToExponent amount exponent .downward
  if rounded.signum == 0 then
    return .rejected .tecPRECISION_LOSS
  return .rounded rounded

structure LoanBrokerCoverDepositResult where
  status : TER
  amountDeposit' : STAmount
  loanBroker' : LoanBroker

def LoanBroker.coverDeposit (lb : LoanBroker) (numericType : NumericType) (amount : STAmount) : Except Error LoanBrokerCoverDepositResult := do
  let result : LoanBrokerCoverDepositResult := {
    status := .tesSUCCESS,
    amountDeposit' := STAmount.zero numericType,
    loanBroker' := lb
  }

  let rounded ← match (← lb.roundedCoverDeposit numericType amount) with
    | .rejected _ => return { result with status := .tecINTERNAL }
    | .rounded amount => .pure amount
  -- rounded cannot be 0 here, don't implement the CPP defensive 0 check

  let roundedNumber ← rounded.toNumber .to_nearest
  let coverAvailable' ← lb.coverAvailable.operator_add roundedNumber .to_nearest
  let lb' := { lb with coverAvailable := coverAvailable' }
  return { result with amountDeposit' := rounded, loanBroker' := lb' }

end XRPL.Model.Lending
