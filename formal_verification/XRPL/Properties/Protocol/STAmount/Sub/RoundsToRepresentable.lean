import XRPL.Properties.Protocol.STAmount.Sub.Common.RoundsToRepresentableProofs

/-! # STAmount subtraction lands within one ULP of the exact difference -/

namespace XRPL.Model.Protocol

/-- IOU subtraction lands within one ULP of `v1 − v2`, on the correct side for `downward` and `upward`. -/
theorem STAmount.operator_sub_repr_iou (v1 v2 result : STAmount)
    (mode : rounding_mode)
    (hc1 : v1.IOUCanonical) (hc2 : v2.IOUCanonical)
    (hok : STAmount.operator_sub v1 v2 mode = .ok result) (hresult : result.mValue ≠ 0) :
    STAmount.RoundsToRepresentableWithin result (v1.toRat - v2.toRat) mode 1 :=
  STAmount.operator_sub_repr_iou_proof v1 v2 result mode hc1 hc2
    hok hresult

end XRPL.Model.Protocol
