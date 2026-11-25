import XRPL.Properties.Protocol.Number.Common.NumberBridge
import XRPL.Properties.Protocol.Number.Add.Common.ToNearest.AlgorithmicFacts.SameSign
import XRPL.Properties.Protocol.Number.Add.Common.ToNearest.AlgorithmicFacts.DiffSignRepresents

/-! # A zero `to_nearest` sum or difference is `Number.zero`

On normalized operands, a `to_nearest` add or sub result with mantissa 0 is the literal `Number.zero`. So the result
is always normalized, and its `operator_eq Number.zero` test matches `mantissa_ = 0`. -/

namespace XRPL.Model.Protocol

/-- `bringIntoRange` output: the canonical zero record, or nonzero mantissa. -/
lemma Guard.bringIntoRange_cases_sz (neg : Bool) (m : UInt64) (e : Int) (minM : UInt64) :
    Guard.bringIntoRangeSpec neg m e minM
      = ({ negative_ := false, mantissa_ := 0, exponent_ := -2147483648 } : RoundResult) ∨
    (Guard.bringIntoRangeSpec neg m e minM).mantissa_ ≠ 0 := by
  sorry

/-- A mantissa-`0` `doRoundUp` result converts to the literal `Number.zero`. -/
lemma Guard.doRoundUp_zero_shape_sz (g : Guard) (neg : Bool) (m : UInt64) (e : Int)
    (minM maxM : UInt64) (mode : rounding_mode) (loc : Error) (res : RoundResult)
    (hok : g.doRoundUp neg m e minM maxM mode loc = .ok res)
    (h0 : res.mantissa_ = 0) : res.toNumber = Number.zero := by
  sorry

/-- A mantissa-`0` `doNormalize128` result is the literal `Number.zero`. -/
lemma doNormalize128_zero_shape_sz (zn : Bool) (M : UInt128) (e : Int) (sticky : Bool)
    (mode : rounding_mode) (result : Number)
    (hok : doNormalize128 zn M e largeRange.min largeRange.max mode sticky = .ok result)
    (h0 : result.mantissa_ = 0) : result = Number.zero := by
  sorry

/-- A mantissa-`0` `to_nearest` addition result of normalized operands is the
literal `Number.zero`. -/
lemma Number.operator_add_zero_shape_sz (x y result : Number)
    (hx : x.isNormalized) (hy : y.isNormalized)
    (hok : Number.operator_add x y .to_nearest = .ok result)
    (h0 : result.mantissa_ = 0) : result = Number.zero := by
  sorry

/-- A mantissa-`0` `to_nearest` subtraction result of normalized operands is the
literal `Number.zero`. -/
lemma Number.operator_sub_zero_shape_sz (x y result : Number)
    (hx : x.isNormalized) (hy : y.isNormalized)
    (hok : Number.operator_sub x y .to_nearest = .ok result)
    (h0 : result.mantissa_ = 0) : result = Number.zero := by
  sorry

/-- A successful `to_nearest` addition of normalized `Number`s gives a normalized `Number`. -/
lemma Number.operator_add_isNormalized_to_nearest_sz (x y result : Number)
    (hx : x.isNormalized) (hy : y.isNormalized)
    (hok : Number.operator_add x y .to_nearest = .ok result) :
    result.isNormalized := by
  sorry

/-- A successful `to_nearest` subtraction of normalized `Number`s gives a normalized `Number`. -/
lemma Number.operator_sub_isNormalized_to_nearest_sz (x y result : Number)
    (hx : x.isNormalized) (hy : y.isNormalized)
    (hok : Number.operator_sub x y .to_nearest = .ok result) :
    result.isNormalized := by
  sorry

/-- `divQuotient128` on a zero numerator yields a zero quotient (no remainder). -/
lemma divQuotient128_zero_sz (ym : UInt64) (xe ye : Int) :
    divQuotient128 0 ym xe ye = .ok (0, xe - ye - 17, false) := by
  sorry

/-- `doNormalize128` on a zero mantissa is the literal `Number.zero`, returned by the leading
`if mantissa == 0` check before the loop. -/
lemma doNormalize128_zero_num_sz (zn : Bool) (e : Int) (minM maxM : UInt64)
    (mode : rounding_mode) (s : Bool) :
    doNormalize128 zn 0 e minM maxM mode s = .ok Number.zero := by
  sorry

/-- A nonzero `operator_div` result forces a nonzero numerator, since a zero numerator is either returned as
it is or gives a zero quotient that `doNormalize128` turns into `Number.zero`. -/
lemma Number.operator_div_numerator_ne_zero_sz (x y result : Number) (mode : rounding_mode)
    (hyne : ¬ y.operator_eq Number.zero = true)
    (hok : Number.operator_div x y mode = .ok result) (hres : result.mantissa_ ≠ 0) :
    x.mantissa_ ≠ 0 := by
  sorry

end XRPL.Model.Protocol
