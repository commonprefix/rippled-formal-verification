import XRPL.Model.Protocol.Number
import XRPL.Model.Protocol.NumericType
import XRPL.Model.Protocol.STAmount
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

-- XLS-66 (32): management fee on the interest, rounded down
def computeManagementFee (nt : NumericType) (value : Number) (feeRate : TenthBips16) (exponent : Int)
    : Except Error Number := do
  let raw ← tenthBipsOfValue value feeRate.toTenthBips32 .to_nearest
  STAmount.roundToNumericType nt raw .downward (some exponent)

end XRPL.Model.Lending
