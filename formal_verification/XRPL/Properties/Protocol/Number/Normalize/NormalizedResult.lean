import XRPL.Properties.Protocol.Number.Normalize.Common.ResultFacts
import XRPL.Properties.Protocol.Number.Sub.ZeroShape
import XRPL.Properties.Protocol.Number.Common.Constants
import XRPL.Properties.Protocol.Number.Div.Common.Decompose

/-! # Every successful `normalize` result is normalized

A zero input or an underflow returns `Number.zero`, so every successful `normalize` and `from_rep` gives a normalized
`Number`. The same holds for `operator_mul` and `operator_div` of normalized operands. -/

namespace XRPL.Model.Protocol

/-- A mantissa-`0` `doNormalize` result is the literal `Number.zero`. -/
lemma doNormalize_zero_shape (neg : Bool) (m : UInt64) (e : Int) (minM maxM : UInt64)
    (mode : rounding_mode) (result : Number)
    (hok : doNormalize neg m e minM maxM mode = .ok result) (h0 : result.mantissa_ = 0) :
    result = Number.zero := by
  sorry

/-- Every successful `normalize` gives a normalized `Number`. -/
lemma Number.normalize_isNormalized (n result : Number) (mode : rounding_mode)
    (hok : n.normalize largeRange.min largeRange.max mode = .ok result) :
    result.isNormalized := by
  sorry

/-- Every successful `from_rep` gives a normalized `Number`. -/
lemma Number.from_rep_isNormalized (m : Int64) (e : Int) (mode : rounding_mode)
    (result : Number)
    (hok : Number.from_rep m e largeRange.min largeRange.max mode = .ok result) :
    result.isNormalized := by
  sorry

/-- A count converted to a `Number` is normalized. -/
lemma Number.ofInt64_isNormalized (m : Int64) (mode : rounding_mode := .to_nearest) :
    (Number.ofInt64 m mode).isNormalized := by
  sorry

/-- Every successful `operator_mul` of normalized `Number`s gives a normalized `Number`. A zero operand is
returned as it is, and every other product goes through `normalize`. -/
lemma Number.operator_mul_isNormalized (x y result : Number) (mode : rounding_mode)
    (hx : x.isNormalized) (hy : y.isNormalized)
    (hok : Number.operator_mul x y mode = .ok result) : result.isNormalized := by
  sorry

/-- Every successful `operator_div` of normalized `Number`s gives a normalized `Number`. A zero numerator is
returned as it is, and a zero quotient is the literal `Number.zero`. -/
lemma Number.operator_div_isNormalized (x y result : Number) (mode : rounding_mode)
    (hx : x.isNormalized) (hy : y.isNormalized)
    (hok : Number.operator_div x y mode = .ok result) : result.isNormalized := by
  sorry

end XRPL.Model.Protocol
