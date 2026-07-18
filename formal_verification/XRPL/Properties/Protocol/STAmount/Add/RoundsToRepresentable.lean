import XRPL.Properties.Protocol.STAmount.Add.Common.Integral
import XRPL.Properties.Protocol.STAmount.Add.Common.RoundsToRepresentableProofs

namespace XRPL.Model.Protocol

/-! # Addition, discrete/ULP -/

/-- Integral (XRP/MPT) addition is exact. -/
theorem STAmount.operator_add_repr_integral (v1 v2 result : STAmount) (mode : rounding_mode)
    (hc1 : v1.IntegralCanonical) (hc2 : v2.IntegralCanonical)
    (hbound_val : v1.mNumericType.maxValue.toNat ≤ maxRep.toNat)
    (hsum : (v1.signedDrops + v2.signedDrops).natAbs < 2 ^ 63)
    (hok : STAmount.operator_add v1 v2 mode = .ok result) :
    STAmount.RoundsToRepresentableWithin result (v1.toRat + v2.toRat) 0 mode :=
  RoundsToRepresentableWithin_of_eq result (v1.toRat + v2.toRat) mode
    (STAmount.operator_add_integral_exact v1 v2 result mode hc1 hc2 hbound_val hsum hok)

/-- **IOU addition lands within `1` ULP of `v1 + v2` (`to_nearest`).** -/
theorem STAmount.operator_add_repr_iou (v1 v2 result : STAmount)
    (hc1 : v1.IOUCanonical) (hc2 : v2.IOUCanonical)
    (h_truth_ne : v1.toRat + v2.toRat ≠ 0)
    (hok : STAmount.operator_add v1 v2 .to_nearest = .ok result) (hresult : result.mValue ≠ 0) :
    STAmount.RoundsToRepresentableWithin result (v1.toRat + v2.toRat) 1 .to_nearest :=
  STAmount.operator_add_repr_iou_proof v1 v2 result hc1 hc2 h_truth_ne hok hresult

/-- **IOU addition lands within `2` ULP of `v1 + v2` (directed modes)** -/
theorem STAmount.operator_add_repr_iou_directed (v1 v2 result : STAmount)
    (mode : rounding_mode)
    (hc1 : v1.IOUCanonical) (hc2 : v2.IOUCanonical)
    (h_truth_ne : v1.toRat + v2.toRat ≠ 0)
    (hok : STAmount.operator_add v1 v2 mode = .ok result) (hresult : result.mValue ≠ 0) :
    STAmount.RoundsToRepresentableWithin result (v1.toRat + v2.toRat) 2 mode :=
  STAmount.operator_add_repr_iou_directed_proof v1 v2 result mode hc1 hc2
    h_truth_ne hok hresult

end XRPL.Model.Protocol
