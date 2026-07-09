-- Multiplication rounding errors, denominated in computed-value ULP increments

import XRPL.Properties.Protocol.STAmount.Mul.Common.Integral
import XRPL.Properties.Protocol.STAmount.Mul.Common.RoundsToRepresentableProofs

namespace XRPL.Model.Protocol

/-! # Multiplication, discrete/ULP -/

/-- Integral (XRP/MPT) multiplication is exact. -/
theorem STAmount.operator_mul_repr_integral (v1 v2 result : STAmount) (nt : NumericType)
    (mode : rounding_mode)
    (hc1 : v1.IntegralCanonical) (hc2 : v2.IntegralCanonical)
    (hntint : nt.isIntegral = true) (hv1nt : v1.mNumericType = nt) (hv2nt : v2.mNumericType = nt)
    (hn1 : v1.mIsNegative = false) (hn2 : v2.mIsNegative = false)
    (hbound_val : nt.maxValue.toNat ≤ maxRep.toNat)
    (hbound : v1.mValue.toNat * v2.mValue.toNat ≤ nt.maxValue.toNat)
    (hok : STAmount.multiply v1 v2 nt mode = .ok result) :
    STAmount.RoundsToRepresentableWithin result (v1.toRat * v2.toRat) 0 mode :=
  RoundsToRepresentableWithin_of_eq result (v1.toRat * v2.toRat) mode
    (STAmount.operator_mul_integral_exact v1 v2 result nt mode hc1 hc2 hntint hv1nt hv2nt
      hn1 hn2 hbound_val hbound hok)

/-- **IOU multiplication lands within `1` ULP of `v1 · v2` (`to_nearest`).** -/
theorem STAmount.operator_mul_repr_iou (v1 v2 result : STAmount) (nt : NumericType)
    (hnt : nt = .fractional)
    (hc1 : v1.IOUCanonical) (hc2 : v2.IOUCanonical)
    (hok : STAmount.multiply v1 v2 nt .to_nearest = .ok result) (hresult : result.mValue ≠ 0) :
    STAmount.RoundsToRepresentableWithin result (v1.toRat * v2.toRat) 1 .to_nearest :=
  STAmount.operator_mul_repr_iou_proof v1 v2 result nt hnt hc1 hc2 hok hresult

/-- **IOU multiplication of non-negative operands lands within `1` ULP of `v1 · v2`
(directed modes), on the correct side.** -/
theorem STAmount.operator_mul_repr_iou_directed (v1 v2 result : STAmount) (nt : NumericType)
    (mode : rounding_mode)
    (hnt : nt = .fractional)
    (hc1 : v1.IOUCanonical) (hc2 : v2.IOUCanonical)
    (hn1 : v1.mIsNegative = false) (hn2 : v2.mIsNegative = false)
    (hok : STAmount.multiply v1 v2 nt mode = .ok result) (hresult : result.mValue ≠ 0) :
    STAmount.RoundsToRepresentableWithin result (v1.toRat * v2.toRat) 1 mode :=
  STAmount.operator_mul_repr_iou_directed_proof v1 v2 result nt mode hnt
    hc1 hc2 hn1 hn2 hok hresult

/-- **IOU multiplication is accurate to `1` ULP, for *any* operand signs and *any*
mode.** The pure accuracy (magnitude) guarantee `|result − v1·v2| ≤ 1·ULP`, with no
directional claim. `STAmount.ofNumber` rounds the *magnitude* `|·|`, so for a negative
product a directed mode rounds the magnitude one way at the `Number` stage and the other
way at the 16-digit snap; but because the 16-digit grid refines the 19-digit grid, even
that mixed double rounding stays within one ULP of the true product. (The *directional*
side-claim of `operator_mul_repr_iou_directed` still needs non-negativity; only the
magnitude/accuracy bound holds for every sign.) -/
theorem STAmount.operator_mul_iou_within_1ulp (v1 v2 result : STAmount) (nt : NumericType)
    (mode : rounding_mode)
    (hnt : nt = .fractional)
    (hc1 : v1.IOUCanonical) (hc2 : v2.IOUCanonical)
    (hok : STAmount.multiply v1 v2 nt mode = .ok result) (hresult : result.mValue ≠ 0) :
    |result.toRat - v1.toRat * v2.toRat| ≤ 1 * (10 : ℚ) ^ result.exponent :=
  STAmount.operator_mul_iou_within_1ulp_proof v1 v2 result nt mode hnt
    hc1 hc2 hok hresult

/-- **IOU multiplication lands within `1` ULP of `v1 · v2` (`towards_zero`), for operands
of *any* sign.** `towards_zero` truncates the *magnitude* at both rounding stages regardless
of sign, so — since the 16-digit grid embeds in the 19-digit `Number` grid — the composed
rounding is the single 16-digit truncation of `|v1·v2|`, hence within one ULP. (Its
side-clause is trivial, so no non-negativity is needed, unlike `operator_mul_repr_iou_directed`.) -/
theorem STAmount.operator_mul_repr_iou_towards_zero (v1 v2 result : STAmount) (nt : NumericType)
    (hnt : nt = .fractional)
    (hc1 : v1.IOUCanonical) (hc2 : v2.IOUCanonical)
    (hok : STAmount.multiply v1 v2 nt .towards_zero = .ok result) (hresult : result.mValue ≠ 0) :
    STAmount.RoundsToRepresentableWithin result (v1.toRat * v2.toRat) 1 .towards_zero :=
  ⟨trivial, by
    rw [Nat.cast_one, one_mul]
    exact STAmount.operator_mul_iou_towards_zero_one v1 v2 result nt hnt
      hc1 hc2 hok hresult⟩

/-- **IOU multiplication never increases magnitude (`towards_zero`), any sign.** The
faithful *directional* guarantee for the magnitude-rounding semantics: `|result| ≤ |v1·v2|`
regardless of sign. (`upward`/`downward` admit no such any-sign directional statement.) -/
theorem STAmount.operator_mul_iou_abs_le_towards_zero (v1 v2 result : STAmount) (nt : NumericType)
    (hnt : nt = .fractional)
    (hc1 : v1.IOUCanonical) (hc2 : v2.IOUCanonical)
    (hok : STAmount.multiply v1 v2 nt .towards_zero = .ok result) (hresult : result.mValue ≠ 0) :
    |result.toRat| ≤ |v1.toRat * v2.toRat| :=
  STAmount.operator_mul_iou_abs_le_towards_zero_proof v1 v2 result nt hnt
    hc1 hc2 hok hresult

end XRPL.Model.Protocol
