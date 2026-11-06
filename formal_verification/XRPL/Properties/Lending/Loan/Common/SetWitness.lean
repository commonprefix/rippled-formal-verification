import XRPL.Model.Lending.Loan.LoanSet
import XRPL.Model.Lending1_1.AssetPool
import XRPL.Properties.Lending.Loan.Defs

/-! # Witnesses for the LoanSet theorems

Concrete creates on a closed-ended IOU vault, checked by `native_decide`, including one-payment creates for the
value bounds. -/

set_option linter.style.nativeDecide false

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault (Vault RawVault)

/-- No fees. -/
def lwFees : LoanFees :=
  { originationFee := Number.zero, serviceFee := Number.zero, latePaymentFee := Number.zero
  , closePaymentFee := Number.zero }

/-- The given InterestRate and no other rate. -/
def lwRates (interestRate : TenthBips32) : LoanRates :=
  { interestRate := interestRate, lateInterestRate := 0, closeInterestRate := 0, overpaymentInterestRate := 0
  , overpaymentFee := 0 }

end XRPL.Model.Lending
