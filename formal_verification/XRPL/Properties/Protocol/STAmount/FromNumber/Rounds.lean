import XRPL.Properties.Protocol.STAmount.FromNumber.Common.RoundsProofs

/-! # An amount made from a Number is rounded in the requested mode

`STAmount.ofNumber` rounds the magnitude and then restores the sign, so `downward` and `upward` round a negative
Number the wrong way. Those theorems assume `hnonneg`, and their `_attained` witnesses show the failure. -/

namespace XRPL.Model.Protocol

/-- For a Number that is not negative (`hnonneg`), `downward` conversion gives an amount at or below it, less
than one unit away. -/
theorem STAmount.ofNumber_rounds_downward (nt : NumericType) (n : Number) (result : STAmount)
    (hn : n.isNormalized) (hnonneg : 0 ≤ n.toRat)
    (hok : STAmount.ofNumber nt n .downward = .ok result) (hne : nt.isIntegral = true ∨ result.mValue ≠ 0) :
    result.toRat ≤ n.toRat ∧ n.toRat - result.toRat < (10 : ℚ) ^ result.mOffset := by
  sorry

/-- A negative Number that `downward` conversion rounds up: -1.5 XRP becomes -1. -/
theorem STAmount.ofNumber_rounds_downward_attained :
    ∃ (nt : NumericType) (n : Number) (result : STAmount),
      n.isNormalized ∧
      STAmount.ofNumber nt n .downward = .ok result ∧
      (nt.isIntegral = true ∨ result.mValue ≠ 0) ∧
      n.toRat < result.toRat := by
  sorry

/-- For a Number that is not negative (`hnonneg`), `upward` conversion gives an amount at or above it, less
than one unit away. -/
theorem STAmount.ofNumber_rounds_upward (nt : NumericType) (n : Number) (result : STAmount)
    (hn : n.isNormalized) (hnonneg : 0 ≤ n.toRat)
    (hok : STAmount.ofNumber nt n .upward = .ok result) (hne : nt.isIntegral = true ∨ result.mValue ≠ 0) :
    n.toRat ≤ result.toRat ∧ result.toRat - n.toRat < (10 : ℚ) ^ result.mOffset := by
  sorry

/-- A negative Number that `upward` conversion rounds down: -1.5 XRP becomes -2. -/
theorem STAmount.ofNumber_rounds_upward_attained :
    ∃ (nt : NumericType) (n : Number) (result : STAmount),
      n.isNormalized ∧
      STAmount.ofNumber nt n .upward = .ok result ∧
      (nt.isIntegral = true ∨ result.mValue ≠ 0) ∧
      result.toRat < n.toRat := by
  sorry

/-- `towards_zero` conversion gives an amount no larger in size than the Number, less than one unit away. -/
theorem STAmount.ofNumber_rounds_towards_zero (nt : NumericType) (n : Number) (result : STAmount)
    (hn : n.isNormalized)
    (hok : STAmount.ofNumber nt n .towards_zero = .ok result) (hne : nt.isIntegral = true ∨ result.mValue ≠ 0) :
    |result.toRat| ≤ |n.toRat| ∧ |n.toRat| - |result.toRat| < (10 : ℚ) ^ result.mOffset := by
  sorry

/-- `to_nearest` conversion gives an amount at most half a unit away from the Number. -/
theorem STAmount.ofNumber_rounds_to_nearest (nt : NumericType) (n : Number) (result : STAmount)
    (hn : n.isNormalized)
    (hok : STAmount.ofNumber nt n .to_nearest = .ok result) (hne : nt.isIntegral = true ∨ result.mValue ≠ 0) :
    |result.toRat - n.toRat| ≤ (10 : ℚ) ^ result.mOffset / 2 := by
  sorry

end XRPL.Model.Protocol
