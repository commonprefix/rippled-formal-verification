import Mathlib.Tactic
import XRPL.Model.Protocol.STAmount

/-! # The values that round to an amount of a type

An IOU amount has 16 digits and an exponent up to 80, so the largest one is `9999999999999999 * 10^80`. An XRP or
MPT amount is a whole number up to the `maxValue` of its type. `STAmount.RoundsInRange` says that a value, rounded
once in the mode, is still such an amount. A value that is too small is in range, because it rounds to zero. -/

namespace XRPL.Model.Protocol

/-- The smallest int64, `-2^63` (`INT64_MIN`). Its size is one above `maxRep`, the largest int64. -/
def minInt64 : ℚ := -9223372036854775808

/-- The exact value `v`, rounded once in the mode, is an amount of the type. -/
def STAmount.RoundsInRange (nt : NumericType) (mode : rounding_mode) (v : ℚ) : Prop :=
  match nt with
  | .fractional =>
    match mode with
    | .to_nearest => |v| < 99999999999999995 * 10 ^ 79
    | .towards_zero => |v| < 10 ^ 96
    | .downward => -(9999999999999999 * 10 ^ 80) ≤ v ∧ v < 10 ^ 96
    | .upward => -(10 ^ 96) < v ∧ v ≤ 9999999999999999 * 10 ^ 80
  | .integral maxValue _ _ _ =>
    match mode with
    | .to_nearest =>
      |v| < (maxValue.toNat : ℚ) + 1 / 2 ∨ (|v| = (maxValue.toNat : ℚ) + 1 / 2 ∧ maxValue.toNat % 2 = 0)
    | .towards_zero => |v| < (maxValue.toNat : ℚ) + 1
    | .downward => -(maxValue.toNat : ℚ) ≤ v ∧ v < (maxValue.toNat : ℚ) + 1
    | .upward => -((maxValue.toNat : ℚ) + 1) < v ∧ v ≤ (maxValue.toNat : ℚ)

end XRPL.Model.Protocol
