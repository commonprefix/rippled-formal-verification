import XRPL.Properties.Protocol.STAmount.Constructors.Common.FromMantissaProofs

/-! # An XRP or MPT amount made from a mantissa and an exponent is rounded in the requested mode

An exponent of -20 or less gives zero before rounding, and a mantissa above the largest int64 loses its last digit.
The theorems assume `hexp` and `hm` against these, and the `_attained` witnesses show what happens without them. -/

namespace XRPL.Model.Protocol

/-- With an exponent above -20 (`hexp`) and a mantissa within int64 (`hm`), the XRP or MPT amount is less than
one away from `mantissa * 10 ^ exponent`, in every mode. -/
theorem STAmount.checked_integral_within_one (nt : NumericType) (m : UInt64) (e : Int) (neg : Bool)
    (mode : rounding_mode) (result : STAmount) (hint : nt.isIntegral = true)
    (hexp : -20 < e) (hm : m ≤ maxRep)
    (hok : STAmount.checked nt m e neg mode = .ok result) :
    |result.toRat - (STAmount.unchecked nt m e neg).toRat| < 1 :=
  STAmount.checked_integral_within_one_proof nt m e neg mode result hint hexp (UInt64.le_iff_toNat_le.mp hm) hok

/-- A mantissa above the largest int64 that ends 8 away: MPT `2^63` becomes `2^63 - 8`. -/
theorem STAmount.checked_integral_within_one_attained :
    ∃ (nt : NumericType) (m : UInt64) (e : Int) (neg : Bool) (mode : rounding_mode) (result : STAmount),
      nt.isIntegral = true ∧
      -20 < e ∧
      STAmount.checked nt m e neg mode = .ok result ∧
      1 ≤ |result.toRat - (STAmount.unchecked nt m e neg).toRat| :=
  ⟨NumericType.int64, 9223372036854775808, 0, false, .to_nearest,
    ⟨NumericType.int64, 9223372036854775800, 0, false⟩, rfl, by decide,
    STAmount.checked_integral_large_mantissa_witness, STAmount.checked_integral_large_mantissa_witness_gap⟩

/-- With an exponent above -20 (`hexp`) and a mantissa within int64 (`hm`), `upward` gives an XRP or MPT amount
at or above `mantissa * 10 ^ exponent`. -/
theorem STAmount.checked_integral_upward (nt : NumericType) (m : UInt64) (e : Int) (neg : Bool)
    (result : STAmount) (hint : nt.isIntegral = true)
    (hexp : -20 < e) (hm : m ≤ maxRep)
    (hok : STAmount.checked nt m e neg .upward = .ok result) :
    (STAmount.unchecked nt m e neg).toRat ≤ result.toRat :=
  STAmount.checked_integral_upward_proof nt m e neg result hint hexp (UInt64.le_iff_toNat_le.mp hm) hok

/-- An exponent of -20 where `upward` gives an amount below the value: XRP `10 * 10^-20` becomes 0. -/
theorem STAmount.checked_integral_upward_attained :
    ∃ (nt : NumericType) (m : UInt64) (e : Int) (neg : Bool) (result : STAmount),
      nt.isIntegral = true ∧
      m ≤ maxRep ∧
      STAmount.checked nt m e neg .upward = .ok result ∧
      result.toRat < (STAmount.unchecked nt m e neg).toRat :=
  ⟨NumericType.native, 10, -20, false, ⟨NumericType.native, 0, 0, false⟩, rfl, by decide,
    STAmount.checked_integral_small_exponent_witness, STAmount.checked_integral_small_exponent_witness_lt⟩

/-- With an exponent above -20 (`hexp`) and a mantissa within int64 (`hm`), `downward` gives an XRP or MPT
amount at or below `mantissa * 10 ^ exponent`. -/
theorem STAmount.checked_integral_downward (nt : NumericType) (m : UInt64) (e : Int) (neg : Bool)
    (result : STAmount) (hint : nt.isIntegral = true)
    (hexp : -20 < e) (hm : m ≤ maxRep)
    (hok : STAmount.checked nt m e neg .downward = .ok result) :
    result.toRat ≤ (STAmount.unchecked nt m e neg).toRat :=
  STAmount.checked_integral_downward_proof nt m e neg result hint hexp (UInt64.le_iff_toNat_le.mp hm) hok

end XRPL.Model.Protocol
