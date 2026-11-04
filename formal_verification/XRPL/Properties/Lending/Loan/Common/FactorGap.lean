import XRPL.Model.Lending.Amortization
import XRPL.Properties.Lending.Loan.Common.RoundingError

/-! # A payment factor that falls with each payment

The payment factor of `k` payments is at least four roundings below the factor of `k − 1` payments. So the theoretical
principal never rises after a payment, and a re-amortization never schedules more principal than it re-amortized. -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol

/-- The payment factor of `k` payments, times four roundings, is at most the factor of `k − 1` payments. -/
def FactorGap (rate : Number) (k : UInt32) : Prop :=
  ∀ f f' : Number, computePaymentFactor rate (Number.ofInt64 k.toUInt64.toInt64) k = .ok f →
    computePaymentFactor rate (Number.ofInt64 (k - 1).toUInt64.toInt64) (k - 1) = .ok f' →
    f.toRat * (1 + Number.nearestError) ^ 4 ≤ f'.toRat

end XRPL.Model.Lending
