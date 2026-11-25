import XRPL.Properties.Protocol.STAmount.Sub.Common.Neg
import XRPL.Properties.Protocol.STAmount.Add.RoundsWithin
import XRPL.Properties.Protocol.STAmount.Common.IOUWitnessTraces
import XRPL.Properties.Protocol.STAmount.Common.IOUDirectedWitnesses

/-! # Proofs of the IOU subtraction `RoundsWithin` theorems

Subtraction reduces to addition via `v1 - v2 = v1 + (-v2)`. -/

namespace XRPL.Model.Protocol

/-- Proof of `operator_sub_rounds_iou` (IOU subtraction, `to_nearest`). -/
theorem STAmount.operator_sub_rounds_iou_proof (v1 v2 result : STAmount)
    (hc1 : v1.IOUCanonical) (hc2 : v2.IOUCanonical)
    (hok : STAmount.operator_sub v1 v2 .to_nearest = .ok result)
    (hresult : result.mValue ≠ 0) :
    RoundsWithin result (v1.toRat - v2.toRat) .to_nearest IOUAmount.εToNearest := by
  have htruth : v1.toRat + (v2.operator_neg).toRat = v1.toRat - v2.toRat := by
    rw [STAmount.operator_neg_toRat]; ring
  have hok' : STAmount.operator_add v1 v2.operator_neg .to_nearest = .ok result := hok
  rw [← htruth]
  exact STAmount.operator_add_rounds_iou v1 v2.operator_neg result hc1 hc2.operator_neg hok' hresult

/-- Proof of `operator_sub_rounds_iou_witness`. -/
theorem STAmount.operator_sub_rounds_iou_witness_proof :
    ∃ (v1 v2 result : STAmount),
      v1.IOUCanonical ∧ v2.IOUCanonical ∧
      STAmount.operator_sub v1 v2 .to_nearest = .ok result ∧ result.mValue ≠ 0 ∧
      RoundsWithinWitness result (v1.toRat - v2.toRat) (4 / 10 ^ 16 : ℚ) := by
  have h1 : (⟨.fractional, 5000000000000003, 0, false⟩ : STAmount).toRat = 5000000000000003 := by
    rw [STAmount.toRat_signed]
    norm_num [show ((5000000000000003 : UInt64).toNat : ℚ) = 5000000000000003 by norm_cast]
  have h2 : (⟨.fractional, 5000000000000002, 0, true⟩ : STAmount).toRat = -5000000000000002 := by
    rw [STAmount.toRat_signed]
    norm_num [show ((5000000000000002 : UInt64).toNat : ℚ) = 5000000000000002 by norm_cast]
  have hr : (⟨.fractional, 1000000000000000, 1, false⟩ : STAmount).toRat = 10000000000000000 := by
    rw [STAmount.toRat_signed]
    norm_num [show ((1000000000000000 : UInt64).toNat : ℚ) = 1000000000000000 by norm_cast]
  have hok : STAmount.operator_sub ⟨.fractional, 5000000000000003, 0, false⟩
      ⟨.fractional, 5000000000000002, 0, true⟩ .to_nearest
      = .ok ⟨.fractional, 1000000000000000, 1, false⟩ := STAmount.operator_add_iou_witness_eq
  refine ⟨⟨.fractional, 5000000000000003, 0, false⟩, ⟨.fractional, 5000000000000002, 0, true⟩,
          ⟨.fractional, 1000000000000000, 1, false⟩,
          ⟨by decide, by decide, by decide, by decide, by decide⟩,
          ⟨by decide, by decide, by decide, by decide, by decide⟩,
          hok, by decide, ?_⟩
  unfold RoundsWithinWitness
  rw [show RatValued.toRat (⟨.fractional, 1000000000000000, 1, false⟩ : STAmount)
        = (⟨.fractional, 1000000000000000, 1, false⟩ : STAmount).toRat from rfl, hr, h1, h2]
  norm_num

/-- IOU subtraction rounds within the directed addition bound in every mode, since `v1 − v2 = v1 + (−v2)` and
negating `v2` only flips its sign. -/
theorem STAmount.operator_sub_iou_rounds_directed (v1 v2 result : STAmount)
    (mode : rounding_mode)
    (hc1 : v1.IOUCanonical) (hc2 : v2.IOUCanonical)
    (h_truth_ne : v1.toRat - v2.toRat ≠ 0)
    (hok : STAmount.operator_sub v1 v2 mode = .ok result)
    (hresult : result.mValue ≠ 0) :
    RoundsWithin result (v1.toRat - v2.toRat) mode IOUAmount.εDirected := by
  have htruth : v1.toRat + (v2.operator_neg).toRat = v1.toRat - v2.toRat := by
    rw [STAmount.operator_neg_toRat]; ring
  have hok' : STAmount.operator_add v1 v2.operator_neg mode = .ok result := hok
  rw [← htruth]
  exact STAmount.operator_add_iou_rounds_directed v1 v2.operator_neg result mode hc1
    hc2.operator_neg (by rw [htruth]; exact h_truth_ne) hok' hresult

end XRPL.Model.Protocol
