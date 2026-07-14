import XRPL.Properties.Protocol.STAmount.Mul.Common.Native
import XRPL.Properties.Protocol.STAmount.Mul.Common.MPT
import XRPL.Properties.Protocol.STAmount.Mul.Common.RoundsToRepresentableProofs

namespace XRPL.Model.Protocol

/-! # Multiplication, discrete/ULP -/

/-- Native (XRP) multiplication is exact. -/
theorem STAmount.operator_mul_repr_native (v1 v2 result : STAmount) (asset : Asset)
    (mode : rounding_mode)
    (hc1 : v1.NativeCanonical) (hc2 : v2.NativeCanonical)
    (hn1 : v1.mIsNegative = false) (hn2 : v2.mIsNegative = false)
    (hasset : asset.isNative = true)
    (hok : STAmount.multiply v1 v2 asset mode = .ok result) :
    STAmount.RoundsToRepresentableWithin result (v1.toRat * v2.toRat) 0 mode :=
  RoundsToRepresentableWithin_of_eq result (v1.toRat * v2.toRat) mode
    (STAmount.operator_mul_native_exact v1 v2 result asset mode hc1 hc2 hn1 hn2 hasset hok)

/-- MPT multiplication is exact. -/
theorem STAmount.operator_mul_repr_mpt (v1 v2 result : STAmount) (asset : Asset)
    (mode : rounding_mode)
    (hv1 : v1.mAsset.holdsMPTIssue = true) (hv2 : v2.mAsset.holdsMPTIssue = true)
    (hasset : asset.holdsMPTIssue = true)
    (hc1 : v1.MPTCanonical) (hc2 : v2.MPTCanonical)
    (hn1 : v1.mIsNegative = false) (hn2 : v2.mIsNegative = false)
    (hbound : v1.mValue.toNat * v2.mValue.toNat ≤ maxMPTokenAmount)
    (hok : STAmount.multiply v1 v2 asset mode = .ok result) :
    STAmount.RoundsToRepresentableWithin result (v1.toRat * v2.toRat) 0 mode :=
  RoundsToRepresentableWithin_of_eq result (v1.toRat * v2.toRat) mode
    (STAmount.operator_mul_mpt_exact v1 v2 result asset mode hv1 hv2 hasset hc1 hc2 hn1 hn2 hbound hok)

/-- **IOU multiplication lands within `1` ULP of `v1 · v2` (`to_nearest`).** -/
theorem STAmount.operator_mul_repr_iou (v1 v2 result : STAmount) (asset : Asset) (iss : Issue)
    (hv1 : v1.mAsset = .issue iss) (hv2 : v2.mAsset = .issue iss) (h_xrp : iss.isXRP = false)
    (ha_iou : asset.holdsIssue = true) (ha_not_xrp : asset.isNative = false)
    (hc1 : v1.IOUCanonical) (hc2 : v2.IOUCanonical)
    (hok : STAmount.multiply v1 v2 asset .to_nearest = .ok result) (hresult : result.mValue ≠ 0) :
    STAmount.RoundsToRepresentableWithin result (v1.toRat * v2.toRat) 1 .to_nearest :=
  STAmount.operator_mul_repr_iou_proof v1 v2 result asset iss hv1 hv2 h_xrp ha_iou ha_not_xrp
    hc1 hc2 hok hresult

/-- **IOU multiplication of non-negative operands lands within `1` ULP of `v1 · v2`
(directed modes), on the correct side.** -/
theorem STAmount.operator_mul_repr_iou_directed (v1 v2 result : STAmount) (asset : Asset)
    (iss : Issue) (mode : rounding_mode)
    (hv1 : v1.mAsset = .issue iss) (hv2 : v2.mAsset = .issue iss) (h_xrp : iss.isXRP = false)
    (ha_iou : asset.holdsIssue = true) (ha_not_xrp : asset.isNative = false)
    (hc1 : v1.IOUCanonical) (hc2 : v2.IOUCanonical)
    (hn1 : v1.mIsNegative = false) (hn2 : v2.mIsNegative = false)
    (hok : STAmount.multiply v1 v2 asset mode = .ok result) (hresult : result.mValue ≠ 0) :
    STAmount.RoundsToRepresentableWithin result (v1.toRat * v2.toRat) 1 mode :=
  STAmount.operator_mul_repr_iou_directed_proof v1 v2 result asset iss mode hv1 hv2 h_xrp ha_iou
    ha_not_xrp hc1 hc2 hn1 hn2 hok hresult

/-- **IOU multiplication is accurate to `1` ULP, for *any* operand signs and *any*
mode.** The pure accuracy (magnitude) guarantee `|result − v1·v2| ≤ 1·ULP`, with no
directional claim. `STAmount.ofNumber` rounds the *magnitude* `|·|`, so for a negative
product a directed mode rounds the magnitude one way at the `Number` stage and the other
way at the 16-digit snap; but because the 16-digit grid refines the 19-digit grid, even
that mixed double rounding stays within one ULP of the true product. (The *directional*
side-claim of `operator_mul_repr_iou_directed` still needs non-negativity; only the
magnitude/accuracy bound holds for every sign.) -/
theorem STAmount.operator_mul_iou_within_1ulp (v1 v2 result : STAmount) (asset : Asset)
    (iss : Issue) (mode : rounding_mode)
    (hv1 : v1.mAsset = .issue iss) (hv2 : v2.mAsset = .issue iss) (h_xrp : iss.isXRP = false)
    (ha_iou : asset.holdsIssue = true) (ha_not_xrp : asset.isNative = false)
    (hc1 : v1.IOUCanonical) (hc2 : v2.IOUCanonical)
    (hok : STAmount.multiply v1 v2 asset mode = .ok result) (hresult : result.mValue ≠ 0) :
    |result.toRat - v1.toRat * v2.toRat| ≤ 1 * (10 : ℚ) ^ result.exponent :=
  STAmount.operator_mul_iou_within_1ulp_proof v1 v2 result asset iss mode hv1 hv2 h_xrp ha_iou
    ha_not_xrp hc1 hc2 hok hresult

/-- **IOU multiplication lands within `1` ULP of `v1 · v2` (`towards_zero`), for operands
of *any* sign.** `towards_zero` truncates the *magnitude* at both rounding stages regardless
of sign, so — since the 16-digit grid embeds in the 19-digit `Number` grid — the composed
rounding is the single 16-digit truncation of `|v1·v2|`, hence within one ULP. (Its
side-clause is trivial, so no non-negativity is needed, unlike `operator_mul_repr_iou_directed`.) -/
theorem STAmount.operator_mul_repr_iou_towards_zero (v1 v2 result : STAmount) (asset : Asset)
    (iss : Issue)
    (hv1 : v1.mAsset = .issue iss) (hv2 : v2.mAsset = .issue iss) (h_xrp : iss.isXRP = false)
    (ha_iou : asset.holdsIssue = true) (ha_not_xrp : asset.isNative = false)
    (hc1 : v1.IOUCanonical) (hc2 : v2.IOUCanonical)
    (hok : STAmount.multiply v1 v2 asset .towards_zero = .ok result) (hresult : result.mValue ≠ 0) :
    STAmount.RoundsToRepresentableWithin result (v1.toRat * v2.toRat) 1 .towards_zero :=
  ⟨trivial, by
    rw [Nat.cast_one, one_mul]
    exact STAmount.operator_mul_iou_towards_zero_one v1 v2 result asset iss hv1 hv2 h_xrp ha_iou
      ha_not_xrp hc1 hc2 hok hresult⟩

/-- **IOU multiplication never increases magnitude (`towards_zero`), any sign.** The
faithful *directional* guarantee for the magnitude-rounding semantics: `|result| ≤ |v1·v2|`
regardless of sign. (`upward`/`downward` admit no such any-sign directional statement.) -/
theorem STAmount.operator_mul_iou_abs_le_towards_zero (v1 v2 result : STAmount) (asset : Asset)
    (iss : Issue)
    (hv1 : v1.mAsset = .issue iss) (hv2 : v2.mAsset = .issue iss) (h_xrp : iss.isXRP = false)
    (ha_iou : asset.holdsIssue = true) (ha_not_xrp : asset.isNative = false)
    (hc1 : v1.IOUCanonical) (hc2 : v2.IOUCanonical)
    (hok : STAmount.multiply v1 v2 asset .towards_zero = .ok result) (hresult : result.mValue ≠ 0) :
    |result.toRat| ≤ |v1.toRat * v2.toRat| :=
  STAmount.operator_mul_iou_abs_le_towards_zero_proof v1 v2 result asset iss hv1 hv2 h_xrp
    ha_iou ha_not_xrp hc1 hc2 hok hresult

end XRPL.Model.Protocol
