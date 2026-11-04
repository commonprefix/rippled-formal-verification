/-! Named numeric literals for the Number proofs. They expand to plain numerals, so `omega`, `linarith`, `norm_num`
and `decide` see through them in ℕ and ℚ, which an `abbrev` or `def` would block. -/

/-- `maxRep / 10`, the mantissa one digit shorter than `maxRep`. -/
notation "mantissaFloor" => 922337203685477580
notation "mantissaFloorSucc" => 922337203685477581

/-- `maxRep.toNat = 2^63 - 1`, the ℕ/ℚ literal form of `maxRep` (which as a
    `UInt64` `def` is opaque to `omega`). -/
notation "maxRepNat" => 9223372036854775807

/-- `maxRepUp.toNat = 2^63 + 2`, the ℕ/ℚ literal form of `maxRepUp` (the
    cusp round-up cap, numerically equal to `maxRepCuspTarget`). -/
notation "maxRepUpNat" => 9223372036854775810

/-- `2^63 + 2`, the maxRep-cusp round-up target (and the `10/(2^63+2)`
    same-sign directed bound denominator). -/
notation "maxRepCuspTarget" => 9223372036854775810

/-- `10^19 - 10`, the largest `%10=0` mantissa witness used in `Closest/`. -/
notation "maxMul10Witness" => 9999999999999999990

/-- The mantissa precision: `Int.log 10 largeRange.min = 18`. Used standalone in
    exponent arithmetic (NOT the `18` inside `10^18` or `2^63-18`). -/
notation "mantissaLog" => 18

/-- `10^19` (= `largeRange.max + 1`), the bound below every normalized mantissa. -/
notation "tenPow19" => 10000000000000000000

/-- `2^64`, the `UInt64` modulus, in `(2:ℕ)^64 = … := by decide` lemmas. -/
notation "twoPow64" => 18446744073709551616

/-- `maxRep + 93` (= 2^63+92), the mul-upward sharpness-witness mantissa. -/
notation "mulUpwardWitness" => 9223372036854775900

notation "twoPow63Add7"  => 9223372036854775815  -- 2^63+7 (to_nearest witness input)
notation "twoPow63Add12" => 9223372036854775820  -- 2^63+12 (to_nearest witness result)
