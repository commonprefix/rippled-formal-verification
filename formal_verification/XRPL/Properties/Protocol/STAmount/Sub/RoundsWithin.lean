import XRPL.Properties.Protocol.STAmount.Sub.Common.RoundsWithinProofs

namespace XRPL.Model.Protocol

/-- IOU subtraction rounds within `IOUAmount.εToNearest`. -/
theorem STAmount.operator_sub_rounds_iou (v1 v2 result : STAmount)
    (hc1 : v1.IOUCanonical) (hc2 : v2.IOUCanonical)
    (hok : STAmount.operator_sub v1 v2 .to_nearest = .ok result)
    (hresult : result.mValue ≠ 0) :
    RoundsWithin result (v1.toRat - v2.toRat) .to_nearest IOUAmount.εToNearest :=
  STAmount.operator_sub_rounds_iou_proof v1 v2 result hc1 hc2 hok hresult

/-- IOU subtraction can err by more than `4/10¹⁶` of the exact difference, close to the `εToNearest` bound. -/
theorem STAmount.operator_sub_rounds_iou_witness :
    ∃ (v1 v2 result : STAmount),
      v1.IOUCanonical ∧ v2.IOUCanonical ∧
      STAmount.operator_sub v1 v2 .to_nearest = .ok result ∧ result.mValue ≠ 0 ∧
      RoundsWithinWitness result (v1.toRat - v2.toRat) (4 / 10 ^ 16 : ℚ) :=
  STAmount.operator_sub_rounds_iou_witness_proof

/-- IOU subtraction, `downward` within `IOUAmount.εDirected`. -/
theorem STAmount.operator_sub_rounds_iou_downward (v1 v2 result : STAmount)
    (hc1 : v1.IOUCanonical) (hc2 : v2.IOUCanonical)
    (hok : STAmount.operator_sub v1 v2 .downward = .ok result)
    (hresult : result.mValue ≠ 0) :
    RoundsWithin result (v1.toRat - v2.toRat) .downward IOUAmount.εDirected :=
  STAmount.operator_sub_iou_rounds_directed v1 v2 result .downward hc1 hc2
    (STAmount.operator_sub_iou_truth_ne_of_result v1 v2 result _ hc1 hc2 hok hresult) hok hresult

/-- IOU subtraction, `upward` within `IOUAmount.εDirected`. -/
theorem STAmount.operator_sub_rounds_iou_upward (v1 v2 result : STAmount)
    (hc1 : v1.IOUCanonical) (hc2 : v2.IOUCanonical)
    (hok : STAmount.operator_sub v1 v2 .upward = .ok result)
    (hresult : result.mValue ≠ 0) :
    RoundsWithin result (v1.toRat - v2.toRat) .upward IOUAmount.εDirected :=
  STAmount.operator_sub_iou_rounds_directed v1 v2 result .upward hc1 hc2
    (STAmount.operator_sub_iou_truth_ne_of_result v1 v2 result _ hc1 hc2 hok hresult) hok hresult

/-- IOU subtraction, `towards_zero` within `IOUAmount.εDirected`. -/
theorem STAmount.operator_sub_rounds_iou_towards_zero (v1 v2 result : STAmount)
    (hc1 : v1.IOUCanonical) (hc2 : v2.IOUCanonical)
    (hok : STAmount.operator_sub v1 v2 .towards_zero = .ok result)
    (hresult : result.mValue ≠ 0) :
    RoundsWithin result (v1.toRat - v2.toRat) .towards_zero IOUAmount.εDirected :=
  STAmount.operator_sub_iou_rounds_directed v1 v2 result .towards_zero hc1 hc2
    (STAmount.operator_sub_iou_truth_ne_of_result v1 v2 result _ hc1 hc2 hok hresult) hok hresult

/-- IOU subtraction rounding `downward` can err by more than `4/10¹⁶` of the exact difference. -/
theorem STAmount.operator_sub_rounds_iou_downward_witness :
    ∃ (v1 v2 result : STAmount),
      v1.IOUCanonical ∧ v2.IOUCanonical ∧
      STAmount.operator_sub v1 v2 .downward = .ok result ∧ result.mValue ≠ 0 ∧
      RoundsWithinWitness result (v1.toRat - v2.toRat) (4 / 10 ^ 16 : ℚ) :=
  sub_dir_wit_core .downward 1000000000000000 (by decide) (Or.inl rfl)

/-- IOU subtraction rounding `upward` can err by more than `4/10¹⁶` of the exact difference. -/
theorem STAmount.operator_sub_rounds_iou_upward_witness :
    ∃ (v1 v2 result : STAmount),
      v1.IOUCanonical ∧ v2.IOUCanonical ∧
      STAmount.operator_sub v1 v2 .upward = .ok result ∧ result.mValue ≠ 0 ∧
      RoundsWithinWitness result (v1.toRat - v2.toRat) (4 / 10 ^ 16 : ℚ) :=
  sub_dir_wit_core .upward 1000000000000001 (by decide) (Or.inr (Or.inl rfl))

/-- IOU subtraction rounding `towards_zero` can err by more than `4/10¹⁶` of the exact difference. -/
theorem STAmount.operator_sub_rounds_iou_towards_zero_witness :
    ∃ (v1 v2 result : STAmount),
      v1.IOUCanonical ∧ v2.IOUCanonical ∧
      STAmount.operator_sub v1 v2 .towards_zero = .ok result ∧ result.mValue ≠ 0 ∧
      RoundsWithinWitness result (v1.toRat - v2.toRat) (4 / 10 ^ 16 : ℚ) :=
  sub_dir_wit_core .towards_zero 1000000000000000 (by decide) (Or.inr (Or.inr rfl))

end XRPL.Model.Protocol
