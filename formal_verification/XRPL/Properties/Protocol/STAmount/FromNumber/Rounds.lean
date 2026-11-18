import XRPL.Properties.Protocol.STAmount.FromNumber.Common.RoundsProofs

/-! # An amount made from a Number is rounded in the requested mode

`STAmount.ofNumber` should return the amount just below the Number (`downward`), just above it (`upward`), the
one nearer zero (`towards_zero`) or the nearest one (`to_nearest`). The unit is `10 ^ result.mOffset`, which is 1
for XRP and MPT. The code drops the sign, rounds the size and puts the sign back, so `downward` and `upward` round
a negative Number the wrong way. Those two theorems assume a Number that is not negative (`hnonneg`), and their
`_attained` witnesses show a negative Number that breaks them. -/

namespace XRPL.Model.Protocol

/-- For a Number that is not negative (`hnonneg`), `downward` conversion gives an amount at or below it, less
than one unit away. -/
theorem STAmount.ofNumber_rounds_downward (nt : NumericType) (n : Number) (result : STAmount)
    (hn : n.isNormalized) (hnonneg : 0 ≤ n.toRat)
    (hok : STAmount.ofNumber nt n .downward = .ok result) (hne : nt.isIntegral = true ∨ result.mValue ≠ 0) :
    result.toRat ≤ n.toRat ∧ n.toRat - result.toRat < (10 : ℚ) ^ result.mOffset :=
  STAmount.ofNumber_rounds_downward_proof nt n result hn hnonneg hok hne

/-- A negative Number that `downward` conversion rounds up: -1.5 XRP becomes -1. -/
theorem STAmount.ofNumber_rounds_downward_attained :
    ∃ (nt : NumericType) (n : Number) (result : STAmount),
      n.isNormalized ∧
      STAmount.ofNumber nt n .downward = .ok result ∧
      (nt.isIntegral = true ∨ result.mValue ≠ 0) ∧
      n.toRat < result.toRat :=
  ⟨NumericType.native, ⟨true, 1500000000000000000, -18⟩, ⟨NumericType.native, 1, 0, true⟩,
    STAmount.ofNumber_negative_witness_normalized, STAmount.ofNumber_downward_negative_witness,
    Or.inl rfl, STAmount.ofNumber_downward_negative_witness_lt⟩

/-- For a Number that is not negative (`hnonneg`), `upward` conversion gives an amount at or above it, less
than one unit away. -/
theorem STAmount.ofNumber_rounds_upward (nt : NumericType) (n : Number) (result : STAmount)
    (hn : n.isNormalized) (hnonneg : 0 ≤ n.toRat)
    (hok : STAmount.ofNumber nt n .upward = .ok result) (hne : nt.isIntegral = true ∨ result.mValue ≠ 0) :
    n.toRat ≤ result.toRat ∧ result.toRat - n.toRat < (10 : ℚ) ^ result.mOffset :=
  STAmount.ofNumber_rounds_upward_proof nt n result hn hnonneg hok hne

/-- A negative Number that `upward` conversion rounds down: -1.5 XRP becomes -2. -/
theorem STAmount.ofNumber_rounds_upward_attained :
    ∃ (nt : NumericType) (n : Number) (result : STAmount),
      n.isNormalized ∧
      STAmount.ofNumber nt n .upward = .ok result ∧
      (nt.isIntegral = true ∨ result.mValue ≠ 0) ∧
      result.toRat < n.toRat :=
  ⟨NumericType.native, ⟨true, 1500000000000000000, -18⟩, ⟨NumericType.native, 2, 0, true⟩,
    STAmount.ofNumber_negative_witness_normalized, STAmount.ofNumber_upward_negative_witness,
    Or.inl rfl, STAmount.ofNumber_upward_negative_witness_lt⟩

/-- `towards_zero` conversion gives an amount no larger in size than the Number, less than one unit away. -/
theorem STAmount.ofNumber_rounds_towards_zero (nt : NumericType) (n : Number) (result : STAmount)
    (hn : n.isNormalized)
    (hok : STAmount.ofNumber nt n .towards_zero = .ok result) (hne : nt.isIntegral = true ∨ result.mValue ≠ 0) :
    |result.toRat| ≤ |n.toRat| ∧ |n.toRat| - |result.toRat| < (10 : ℚ) ^ result.mOffset :=
  STAmount.ofNumber_rounds_towards_zero_proof nt n result hn hok hne

/-- `to_nearest` conversion gives an amount at most half a unit away from the Number. -/
theorem STAmount.ofNumber_rounds_to_nearest (nt : NumericType) (n : Number) (result : STAmount)
    (hn : n.isNormalized)
    (hok : STAmount.ofNumber nt n .to_nearest = .ok result) (hne : nt.isIntegral = true ∨ result.mValue ≠ 0) :
    |result.toRat - n.toRat| ≤ (10 : ℚ) ^ result.mOffset / 2 :=
  STAmount.ofNumber_rounds_to_nearest_proof nt n result hn hok hne

end XRPL.Model.Protocol
