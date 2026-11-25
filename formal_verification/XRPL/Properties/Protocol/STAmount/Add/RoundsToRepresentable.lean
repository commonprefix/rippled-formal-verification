import XRPL.Properties.Protocol.STAmount.Add.Common.RoundsToRepresentableProofs

/-! # STAmount addition lands within one ULP of the exact sum -/

namespace XRPL.Model.Protocol

/-- IOU addition lands within one ULP of `v1 + v2`, on the correct side for `downward` and `upward`. -/
theorem STAmount.operator_add_repr_iou (v1 v2 result : STAmount)
    (mode : rounding_mode)
    (hc1 : v1.IOUCanonical) (hc2 : v2.IOUCanonical)
    (hok : STAmount.operator_add v1 v2 mode = .ok result) (hresult : result.mValue ≠ 0) :
    STAmount.RoundsToRepresentableWithin result (v1.toRat + v2.toRat) mode 1 := by
  sorry

end XRPL.Model.Protocol
