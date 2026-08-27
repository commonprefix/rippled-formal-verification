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

/-- Debt cap `2^63 − 1` as a `Number` (C++ `kMaxMpTokenAmount`). -/
def debtMaxCap : Number := Number.ofInt64 (9223372036854775807 : Int64)

/-- Max management fee rate, in tenth-bips, so 10% (C++ `kMaxManagementFeeRate`). -/
def maxManagementFeeRate : ℕ := 10_000

/-- Max cover rate, in tenth-bips, so 100% (C++ `kMaxCoverRate`). -/
def maxCoverRate : ℕ := 100_000

end XRPL.Model.Lending
