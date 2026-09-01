import XRPL.Model.Protocol.Number
import XRPL.Model.Protocol.STAmount
import XRPL.Model.Protocol.TER
import XRPL.Model.Vault.Vault
import XRPL.Model.Lending.LoanBroker

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault

def LoanBroker.canDelete (lb : LoanBroker) (vault : RawVault) : Except Error TER := do
  if lb.loanCount != 0 then
    return .tecHAS_OBLIGATIONS

  if lb.debtTotal.signum != 0 then
    -- defensive check: in case debt is non-zero but rounds to zero
    let scale ← exponent vault.assetsTotal vault.numericType
    let rounded ← STAmount.roundToNumericType vault.numericType lb.debtTotal .towards_zero (.some scale)
    if rounded.signum != 0 then
      return .tecHAS_OBLIGATIONS

  return .tesSUCCESS

end XRPL.Model.Lending
