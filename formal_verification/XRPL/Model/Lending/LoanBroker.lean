import XRPL.Model.Protocol.Number

namespace XRPL.Model.Lending

open XRPL.Model.Protocol

structure LoanBroker where
  -- all rates in 1/10 bips
  managementFeeRate : UInt16
  coverRateMinimum : UInt32
  coverRateLiquidation : UInt32
  -- amounts in the vault's asset
  debtTotal : Number
  debtMaximum : Number
  coverAvailable : Number
  loanCount : UInt32

end XRPL.Model.Lending
