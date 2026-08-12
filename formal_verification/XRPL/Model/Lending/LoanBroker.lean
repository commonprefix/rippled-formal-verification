import XRPL.Model.Protocol.Number
import XRPL.Model.Protocol.TenthBips

namespace XRPL.Model.Lending

open XRPL.Model.Protocol

structure LoanBroker where
  managementFeeRate : TenthBips16
  coverRateMinimum : TenthBips32
  coverRateLiquidation : TenthBips32
  -- amounts in the vault's asset
  debtTotal : Number
  debtMaximum : Number
  coverAvailable : Number
  loanCount : UInt32

end XRPL.Model.Lending
