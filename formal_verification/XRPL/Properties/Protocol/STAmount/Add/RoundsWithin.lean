import XRPL.Properties.Protocol.STAmount.Add.Common.IOU
import XRPL.Properties.Protocol.STAmount.Add.Common.DirectedSupport
import XRPL.Properties.Protocol.STAmount.Add.Common.RoundsWithinProofs
import XRPL.Properties.Protocol.STAmount.Add.Common.Underflow
import XRPL.Properties.Protocol.STAmount.Common.IOUWitnessTraces
import XRPL.Properties.Protocol.STAmount.Common.IOUDirectedWitnesses
import XRPL.Properties.Protocol.IOUAmount.Common.Defs

namespace XRPL.Model.Protocol

/-- IOU addition rounds within `IOUAmount.εToNearest`. -/
theorem STAmount.operator_add_rounds_iou (v1 v2 result : STAmount)
    (hc1 : v1.IOUCanonical) (hc2 : v2.IOUCanonical)
    (hok : STAmount.operator_add v1 v2 .to_nearest = .ok result)
    (hresult : result.mValue ≠ 0) :
    RoundsWithin result (v1.toRat + v2.toRat) .to_nearest IOUAmount.εToNearest := by
  sorry

/-- IOU addition can err by more than `4/10¹⁶` of the exact sum, close to the `εToNearest` bound. -/
theorem STAmount.operator_add_rounds_iou_witness :
    ∃ (v1 v2 result : STAmount),
      v1.IOUCanonical ∧ v2.IOUCanonical ∧
      STAmount.operator_add v1 v2 .to_nearest = .ok result ∧ result.mValue ≠ 0 ∧
      RoundsWithinWitness result (v1.toRat + v2.toRat) (4 / 10 ^ 16 : ℚ) := by
  sorry

/-- IOU addition, `downward`: rounding within `IOUAmount.εDirected`. -/
theorem STAmount.operator_add_rounds_iou_downward (v1 v2 result : STAmount)
    (hc1 : v1.IOUCanonical) (hc2 : v2.IOUCanonical)
    (hok : STAmount.operator_add v1 v2 .downward = .ok result)
    (hresult : result.mValue ≠ 0) :
    RoundsWithin result (v1.toRat + v2.toRat) .downward IOUAmount.εDirected := by
  sorry

/-- IOU addition, `upward`: rounding within `IOUAmount.εDirected`. -/
theorem STAmount.operator_add_rounds_iou_upward (v1 v2 result : STAmount)
    (hc1 : v1.IOUCanonical) (hc2 : v2.IOUCanonical)
    (hok : STAmount.operator_add v1 v2 .upward = .ok result)
    (hresult : result.mValue ≠ 0) :
    RoundsWithin result (v1.toRat + v2.toRat) .upward IOUAmount.εDirected := by
  sorry

/-- IOU addition, `towards_zero`: rounding within `IOUAmount.εDirected`. -/
theorem STAmount.operator_add_rounds_iou_towards_zero (v1 v2 result : STAmount)
    (hc1 : v1.IOUCanonical) (hc2 : v2.IOUCanonical)
    (hok : STAmount.operator_add v1 v2 .towards_zero = .ok result)
    (hresult : result.mValue ≠ 0) :
    RoundsWithin result (v1.toRat + v2.toRat) .towards_zero IOUAmount.εDirected := by
  sorry

/-- IOU addition rounding `downward` can err by more than `4/10¹⁶` of the exact sum. -/
theorem STAmount.operator_add_rounds_iou_downward_witness :
    ∃ (v1 v2 result : STAmount),
      v1.IOUCanonical ∧ v2.IOUCanonical ∧
      STAmount.operator_add v1 v2 .downward = .ok result ∧ result.mValue ≠ 0 ∧
      RoundsWithinWitness result (v1.toRat + v2.toRat) (4 / 10 ^ 16 : ℚ) := by
  sorry

/-- IOU addition rounding `upward` can err by more than `4/10¹⁶` of the exact sum. -/
theorem STAmount.operator_add_rounds_iou_upward_witness :
    ∃ (v1 v2 result : STAmount),
      v1.IOUCanonical ∧ v2.IOUCanonical ∧
      STAmount.operator_add v1 v2 .upward = .ok result ∧ result.mValue ≠ 0 ∧
      RoundsWithinWitness result (v1.toRat + v2.toRat) (4 / 10 ^ 16 : ℚ) := by
  sorry

/-- IOU addition rounding `towards_zero` can err by more than `4/10¹⁶` of the exact sum. -/
theorem STAmount.operator_add_rounds_iou_towards_zero_witness :
    ∃ (v1 v2 result : STAmount),
      v1.IOUCanonical ∧ v2.IOUCanonical ∧
      STAmount.operator_add v1 v2 .towards_zero = .ok result ∧ result.mValue ≠ 0 ∧
      RoundsWithinWitness result (v1.toRat + v2.toRat) (4 / 10 ^ 16 : ℚ) := by
  sorry

/-- IOU addition returns zero only when the exact sum is below `10⁻⁸¹` in magnitude, the smallest positive IOU
amount. -/
theorem STAmount.operator_add_underflow_truth_small_iou (v1 v2 result : STAmount) (mode : rounding_mode)
    (hc1 : v1.IOUCanonical) (hc2 : v2.IOUCanonical)
    (hok : STAmount.operator_add v1 v2 mode = .ok result) (hres0 : result.mValue = 0) :
    |v1.toRat + v2.toRat| < (10 : ℚ) ^ (-81 : ℤ) := by
  sorry

end XRPL.Model.Protocol
