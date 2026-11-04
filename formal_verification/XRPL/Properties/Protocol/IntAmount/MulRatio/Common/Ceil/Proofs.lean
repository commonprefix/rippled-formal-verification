import XRPL.Properties.Protocol.IntAmount.MulRatio.Common.Proofs

/-! # `mulRatio` ceil direction (`roundUp = true`).

The `roundUp = true` case of `mulRatio_rounds_proof`: the result is saturated to `Int64.minValue` or is the
smallest representable value not below `amt · num / den`. -/

namespace XRPL.Model.Protocol

/-- `mulRatio` ceils when `roundUp = true`. -/
theorem IntAmount.mulRatio_rounds_ceil_proof (amt : IntAmount) (num den : UInt32)
    (result : IntAmount)
    (hok : IntAmount.mulRatio amt num den true = .ok result) :
    result.value = Int64.minValue ∨
      (amt.toRat * (num.toNat : ℚ) / (den.toNat : ℚ) ≤ result.toRat ∧
       result.toRat - 1 < amt.toRat * (num.toNat : ℚ) / (den.toNat : ℚ)) := by
  simpa using IntAmount.mulRatio_rounds_proof amt num den true result hok

end XRPL.Model.Protocol
