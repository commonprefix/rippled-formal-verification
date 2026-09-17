import XRPL.Model.Protocol.Exponent
import XRPL.Model.Protocol.Number
import XRPL.Model.Protocol.STAmount
import XRPL.Model.Protocol.TER
import XRPL.Model.Lending.LoanBroker.LoanBroker

namespace XRPL.Model.Lending

open XRPL.Model.Protocol

def LoanBroker.canDelete (lb : LoanBroker) : Except Error TER := do
  if lb.loanCount != 0 then
    return .tecHAS_OBLIGATIONS

  if lb.debtTotal.signum != 0 then
    -- defensive check: in case debt is non-zero but rounds to zero
    let nt := lb.vault.numericType
    let vaultExponent ← numberExponent lb.vault.assetsTotal nt
    let rounded ← STAmount.roundToNumericType nt lb.debtTotal .towards_zero (.some vaultExponent)
    if rounded.signum != 0 then
      return .tecHAS_OBLIGATIONS

  return .tesSUCCESS

end XRPL.Model.Lending
