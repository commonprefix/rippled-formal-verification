import XRPL.Properties.Protocol.IOUAmount.Constructors.Common.Proofs
import XRPL.Properties.Protocol.IOUAmount.Common.Underflow

/-! # Correctness of the `IOUAmount` constructors -/

namespace XRPL.Model.Protocol

/-- `normalize` rounds a 17- or 18-digit mantissa to 16 digits with relative error about `10⁻¹⁵`. -/
theorem IOUAmount.normalize_rounds (m : Int64) (e : Int) (mode : rounding_mode) (result : IOUAmount)
    (hm_lo : 10 ^ 16 ≤ m.toInt.natAbs) (hm_hi : m.toInt.natAbs < 10 ^ 18)
    (he_hi : e + 4 ≤ maxExponent)
    (hok : IOUAmount.normalize ⟨m, e⟩ mode = .ok result) (hne : result.mantissa_ ≠ 0) :
    RoundsWithin result ((m.toInt : ℚ) * 10 ^ e) mode
      (10 / (2 ^ 63 + 2 : ℚ) + (10 : ℚ) ^ (-15 : ℤ) + 10 / (2 ^ 63 + 2 : ℚ) * (10 : ℚ) ^ (-15 : ℤ)) :=
  IOUAmount.normalize_rounds_proof m e mode result hm_lo hm_hi he_hi hok hne

/-- `normalize`'s output is canonical 16-digit (`InRange16`). -/
theorem IOUAmount.normalize_canonical (m : Int64) (e : Int) (mode : rounding_mode) (result : IOUAmount)
    (hm_lo : 10 ^ 16 ≤ m.toInt.natAbs) (hm_hi : m.toInt.natAbs < 10 ^ 18)
    (he_hi : e + 4 ≤ maxExponent)
    (hok : IOUAmount.normalize ⟨m, e⟩ mode = .ok result) (hne : result.mantissa_ ≠ 0) :
    result.InRange16 :=
  IOUAmount.normalize_InRange16_proof m e mode result hm_lo hm_hi he_hi hok hne

/-- `ofMantissaExp m e`, which is `normalize ⟨m, e⟩`, rounds a 17- or 18-digit mantissa to 16 digits with relative
error about `10⁻¹⁵`. -/
theorem IOUAmount.ofMantissaExp_rounds (m : Int64) (e : Int) (mode : rounding_mode)
    (result : IOUAmount)
    (hm_lo : 10 ^ 16 ≤ m.toInt.natAbs) (hm_hi : m.toInt.natAbs < 10 ^ 18)
    (he_hi : e + 4 ≤ maxExponent)
    (hok : IOUAmount.ofMantissaExp m e mode = .ok result) (hne : result.mantissa_ ≠ 0) :
    RoundsWithin result ((m.toInt : ℚ) * 10 ^ e) mode
      (10 / (2 ^ 63 + 2 : ℚ) + (10 : ℚ) ^ (-15 : ℤ) + 10 / (2 ^ 63 + 2 : ℚ) * (10 : ℚ) ^ (-15 : ℤ)) :=
  IOUAmount.ofMantissaExp_rounds_proof m e mode result hm_lo hm_hi he_hi hok hne

/-- `ofNumber` re-rounds a 19-digit-normalized `Number` to within a 16-digit ULP. -/
theorem IOUAmount.ofNumber_rounds (sum : Number) (mode : rounding_mode)
    (result : IOUAmount)
    (h_lo : 10 ^ 18 ≤ sum.mantissa_.toNat) (h_hi : sum.mantissa_.toNat < 10 ^ 19)
    (he_lo : minExponent ≤ sum.exponent_ + 3) (he_hi : sum.exponent_ + 4 ≤ maxExponent)
    (hok : IOUAmount.ofNumber sum mode = .ok result) (hne : result.mantissa_ ≠ 0) :
    |result.toRat - sum.toRat| ≤ (10 : ℚ) ^ (sum.exponent_ + 3) :=
  IOUAmount.ofNumber_within_ulp_proof sum mode result h_lo h_hi he_lo he_hi hok hne

/-- `normalize` returns zero for a 17- or 18-digit mantissa only when the exact value is below `10⁻⁸¹` in magnitude,
the smallest positive IOU amount. -/
theorem IOUAmount.normalize_underflow_truth_small (m : Int64) (e : Int) (mode : rounding_mode)
    (result : IOUAmount)
    (hm_lo : 10 ^ 16 ≤ m.toInt.natAbs) (hm_hi : m.toInt.natAbs < 10 ^ 18)
    (he_hi : e + 4 ≤ maxExponent)
    (hok : IOUAmount.normalize ⟨m, e⟩ mode = .ok result) (hres0 : result.mantissa_ = 0) :
    |(m.toInt : ℚ) * 10 ^ e| < (10 : ℚ) ^ (-81 : ℤ) :=
  IOUAmount.normalize_underflow_truth_small_proof m e mode result hm_lo hm_hi he_hi hok hres0

/-- `ofNumber` returns zero for a 19-digit-normalized `Number` only when its value is below `10⁻⁸¹` in magnitude,
the smallest positive IOU amount. -/
theorem IOUAmount.ofNumber_underflow_truth_small (sum : Number) (mode : rounding_mode) (result : IOUAmount)
    (h_lo : 10 ^ 18 ≤ sum.mantissa_.toNat) (h_hi : sum.mantissa_.toNat < 10 ^ 19)
    (he_lo : minExponent ≤ sum.exponent_ + 3) (he_hi : sum.exponent_ + 4 ≤ maxExponent)
    (hok : IOUAmount.ofNumber sum mode = .ok result) (hres0 : result.mantissa_ = 0) :
    |sum.toRat| < (10 : ℚ) ^ (-81 : ℤ) :=
  IOUAmount.ofNumber_underflow_truth_small_proof sum mode result h_lo h_hi he_lo he_hi hok hres0

end XRPL.Model.Protocol
