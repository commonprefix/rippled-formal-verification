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

-- C++ `isOnVaultBaseGrid`
def Number.isOnExponentGrid (value : Number) (exponent : Int) (nt : NumericType) : Except Error Bool := do
  if STAmount.isRounded nt value then
    return false

  let value' ← STAmount.roundToNumericType nt value .towards_zero (some exponent)
  return value'.operator_eq value

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

-- C++ `creditToPosteriorAvailableScale` and `creditToPosteriorBrokerCoverScale`
def sumRoundAndSubtract (amount amountDelta : Number) (exponent : Int) (nt : NumericType) (mode : rounding_mode)
    : Except Error STAmount := do
  if nt.isIntegral then
    return ← STAmount.ofNumber nt amountDelta mode

  let exponent ← postSumExponent amount amountDelta exponent nt
  let sum ← amount.operator_add amountDelta mode
  let sum' ← STAmount.roundToNumericType nt sum mode (some exponent)

  let amountDelta' ← sum'.operator_sub amount mode
  STAmount.ofNumber nt amountDelta' mode

-- C++ `clampToAssetsTotalScale` and `clampToAvailableScale`
def clampToSumExponent (amount : Number) (amountDelta : STAmount) (exponent : Int)
    : Except Error STAmount := do
  let amountDeltaAbs := if amountDelta.negative then amountDelta.operator_neg else amountDelta
  if amountDelta.integral then
    return amountDeltaAbs

  let amountDeltaNum ← amountDelta.toNumber .to_nearest
  let postExponent ← postSumExponent amount amountDeltaNum exponent amountDelta.numericType
  STAmount.roundToExponent amountDeltaAbs postExponent .towards_zero

end XRPL.Model.Protocol
