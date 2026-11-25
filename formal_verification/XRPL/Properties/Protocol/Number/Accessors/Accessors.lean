import XRPL.Properties.Protocol.Number.Accessors.Common.Proofs


namespace XRPL.Model.Protocol

/-- The public `mantissa()` and `exponent()` accessors give back the value: `mantissa · 10^exponent = toRat`. -/
theorem Number.mantissa_mul_exponent_eq_toRat (n : Number) (hn : n.isNormalized) :
    (n.mantissa.toInt : ℚ) * (10 : ℚ) ^ n.exponent = n.toRat := by
  sorry

/-- The public mantissa fits the signed rep: `|mantissa| ≤ maxRep = 2^63 - 1` -/
theorem Number.mantissa_natAbs_le_maxRep (n : Number) (_hn : n.isNormalized) :
    (n.mantissa).toInt.natAbs ≤ maxRep.toNat := by
  sorry

end XRPL.Model.Protocol
