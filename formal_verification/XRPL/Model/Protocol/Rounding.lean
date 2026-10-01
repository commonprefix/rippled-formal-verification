import XRPL.Model.Protocol.Exponent
import XRPL.Model.Protocol.Number
import XRPL.Model.Protocol.NumericType
import XRPL.Model.Protocol.STAmount

namespace XRPL.Model.Protocol

-- exactly representable at scale (round-down == round-up)
def isRounded (value : Number) (scale : Int) (nt : NumericType) : Except Error Bool := do
  let down ← STAmount.roundToNumericType nt value .downward (some scale)
  let up ← STAmount.roundToNumericType nt value .upward (some scale)
  return down.operator_eq up

-- One past the largest unit count an STAmount of the type can carry
def NumericType.mantissaBound (nt : NumericType) : Nat :=
  match nt with
  | .fractional => 10 ^ 16
  | .integral maxValue _ _ _ => min maxValue.toNat maxRep.toNat + 1

-- The value is a whole number of units at the exponent and that count fits the type's STAmount
def Number.isAtExponent (value : Number) (exponent : Int) (nt : NumericType) : Bool :=
  let shift := exponent - value.exponent_
  let units := value.mantissa_.toNat / 10 ^ shift.toNat
  value == Number.zero ||
    (decide (0 ≤ shift) && value.mantissa_.toNat % 10 ^ shift.toNat == 0 && decide (units < nt.mantissaBound))

-- Round a value at the scale, then clamp it into [0, cap].
def roundAndClamp (value cap : Number) (mode : rounding_mode) (nt : NumericType) (scale : Int)
    : Except Error Number := do
  let rounded ← STAmount.roundToNumericType nt value mode (some scale)
  return Number.clamp rounded Number.zero cap

-- C++ `adjustImpreciseNumber`
def sumRoundAndClamp (amount amountDelta : Number) (scale : Int) (nt : NumericType)
    : Except Error Number := do
  let sum ← amount.operator_add amountDelta .to_nearest
  let sum' ← STAmount.roundToNumericType nt sum .to_nearest (some scale)
  if sum'.signum < 0 then return Number.zero else return sum'

private def sumAndRoundToExponent (amount : Number) (amountDelta : STAmount)
    (exponent : Int) (rounding : rounding_mode) : Except Error Number := do
  let numericType := amountDelta.numericType
  let amountDelta ← amountDelta.toNumber rounding
  let sum ← amount.operator_add amountDelta rounding
  let sum ← STAmount.ofNumber numericType sum rounding
  let sum ← STAmount.roundToExponent sum exponent rounding
  sum.toNumber rounding

def clampToSumExponent (amount : Number) (amountDelta : STAmount)
    : Except Error STAmount := do
  let amountDeltaAbs := if amountDelta.negative then amountDelta.operator_neg else amountDelta
  if amountDelta.integral then
    return amountDeltaAbs

  let postExponent ← postSumExponent amount amountDelta
  if amountDelta.negative then
    STAmount.roundToExponent amountDeltaAbs postExponent .downward
  else
    let sum ← sumAndRoundToExponent amount amountDeltaAbs postExponent .downward
    let amountDeltaAbs ← sum.operator_sub amount .to_nearest
    STAmount.ofNumber amountDelta.numericType amountDeltaAbs .to_nearest

end XRPL.Model.Protocol
