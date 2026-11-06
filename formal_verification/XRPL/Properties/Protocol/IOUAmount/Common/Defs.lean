import Mathlib.Tactic
import XRPL.Model.Protocol.IOUAmount
import XRPL.Properties.Protocol.STAmount.Common.RoundToScaleHelpers

/-! # Shared definitions for the `IOUAmount` proof tree

The exactness precondition `ToNumberExact` and the add/sub error budgets. The canonical form `InRange16`
lives in the STAmount tree. -/

namespace XRPL.Model.Protocol

/-- Relative error bound of directed IOU add and sub, about `10⁻¹⁵`: the `Number` error `11/(2⁶³−18)` combined
with the 16-digit re-round error `10⁻¹⁵`. -/
abbrev IOUAmount.εDirected : ℚ :=
  11 / (2 ^ 63 - 18 : ℚ) + (10 : ℚ) ^ (-15 : ℤ) + 11 / (2 ^ 63 - 18 : ℚ) * (10 : ℚ) ^ (-15 : ℤ)

/-- Relative error bound of `to_nearest` IOU add and sub, about `½·10⁻¹⁵`: the `Number` error `6/(2⁶³−3)`
combined with the 16-digit re-round error `½·10⁻¹⁵`. -/
abbrev IOUAmount.εToNearest : ℚ :=
  6 / (2 ^ 63 - 3 : ℚ) + (1 / 2) * (10 : ℚ) ^ (-15 : ℤ)
    + 6 / (2 ^ 63 - 3 : ℚ) * ((1 / 2) * (10 : ℚ) ^ (-15 : ℤ))

/-- Precondition for an exact `IOUAmount.toNumber`: the mantissa is not `Int64.minValue` and the exponent
leaves room for the `largeRange` scale-up. Far weaker than `InRange16`. -/
structure IOUAmount.ToNumberExact (a : IOUAmount) : Prop where
  mant_ne_min : a.mantissa_ ≠ Int64.minValue
  exp_lo : minExponent + 18 ≤ a.exponent_
  exp_hi : a.exponent_ ≤ maxExponent - 1

/-- A canonical 16-digit amount satisfies `ToNumberExact` (with enormous margin). -/
lemma IOUAmount.InRange16.toNumberExact {a : IOUAmount} (h : a.InRange16) :
    a.ToNumberExact := by
  refine ⟨?_, ?_, ?_⟩
  · intro hmin
    have hh := h.mant_hi
    rw [hmin, show Int64.minValue.toInt.natAbs = 9223372036854775808 from by decide] at hh
    omega
  · have := h.exp_lo; have hm : minExponent = -32768 := rfl; omega
  · have := h.exp_hi; have hM : maxExponent = 32768 := rfl; omega

end XRPL.Model.Protocol
