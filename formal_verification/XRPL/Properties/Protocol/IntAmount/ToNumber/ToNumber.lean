import XRPL.Properties.Protocol.IntAmount.ToNumber.Common.Proofs

/-! # Correctness of `IntAmount.toNumber` -/

namespace XRPL.Model.Protocol

/-- `toNumber` is exact for every value except `Int64.minValue`, whose magnitude `2^63` is one past
`maxRep = 2^63 - 1` and gets rounded. -/
theorem IntAmount.toNumber_exact (x : IntAmount) (mode : rounding_mode)
    (h_ne_min : x.value ≠ Int64.minValue) :
    ∃ xn : Number, x.toNumber mode = .ok xn ∧ xn.toRat = x.toRat ∧ xn.isNormalized :=
  IntAmount.toNumber_exact_proof x mode h_ne_min

end XRPL.Model.Protocol
