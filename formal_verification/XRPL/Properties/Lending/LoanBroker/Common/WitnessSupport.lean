import XRPL.Model.Lending.LoanBroker.LoanBrokerCoverDeposit
import XRPL.Model.Lending.LoanBroker.LoanBrokerCoverWithdraw
import XRPL.Model.Lending.LoanBroker.LoanBrokerCoverClawback
import XRPL.Model.Lending1_1.AssetPool
import XRPL.Properties.Lending.LoanBroker.Defs

/-! # Shared fixtures for the cover witnesses

The vault, brokers and amounts the cover witnesses share. -/

set_option linter.style.nativeDecide false

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.Lending1_1
open XRPL.Model.SingleAssetVault (Vault RawVault)

/-- An IOU vault holding `10^6`, so the vault scale is `10^-9`. -/
def wvPool : RawVault :=
  { assetsTotal := ⟨false, 1000000000000000000, -12⟩
  , assetsAvailable := ⟨false, 1000000000000000000, -12⟩
  , assetsReserved := Number.zero, assetsMaximum := none, numericType := .fractional, scale := 0
  , sharesTotal := ⟨false, 1000000000000000000, -12⟩, lossUnrealized := Number.zero }

def wvPoolL : Vault := ⟨wvPool, by native_decide, by native_decide⟩

/-- An IOU broker holding `10^6` of cover, scale `10^-9`, with no debt. -/
def wbMillion : RawLoanBroker :=
  { numericType := .fractional, managementFeeRate := 0, coverRateMinimum := 0
  , coverRateLiquidation := 0, debtTotal := Number.zero, debtMaximum := Number.zero
  , coverAvailable := ⟨false, 1000000000000000000, -12⟩, loanCount := 0 }

def wbMillionL : LoanBroker := ⟨wbMillion, by native_decide, by native_decide⟩

/-- `7.6 * 10^-10`, below one unit at scale `10^-9`. It rounds to `10^-9`, so it
passes the scale check. -/
def waBelowUnit : STAmount := STAmount.unchecked .fractional 7600000000000000 (-25) false

/-- An IOU broker holding `10^18` of cover, with no debt. -/
def wbLargeCover : RawLoanBroker :=
  { numericType := .fractional, managementFeeRate := 0, coverRateMinimum := 0
  , coverRateLiquidation := 0, debtTotal := Number.zero, debtMaximum := Number.zero
  , coverAvailable := ⟨false, 1000000000000000000, 0⟩, loanCount := 0 }

def wbLargeCoverL : LoanBroker := ⟨wbLargeCover, by native_decide, by native_decide⟩

/-- The amount, `1234.567890123456`. -/
def waSmallAmount : STAmount := STAmount.unchecked .fractional 1234567890123456 (-12) false

/-- One part of a split, `1000.5`. -/
def waSplitPart : STAmount := STAmount.unchecked .fractional 1000500000000000 (-12) false

/-- The other amount of an either-order pair with `waSplitPart`, `1001.25`. -/
def waOrderPart : STAmount := STAmount.unchecked .fractional 1001250000000000 (-12) false

/-- Both parts at once, `2001`. -/
def waSplitWhole : STAmount := STAmount.unchecked .fractional 2001000000000000 (-12) false

end XRPL.Model.Lending
