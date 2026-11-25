import XRPL.Properties.Protocol.STAmount.Sub.Common.Neg
import XRPL.Properties.Protocol.STAmount.Add.Common.NearestProofs

/-! # Proofs that IOU subtraction rounds to nearest

Subtraction is addition of the negated amount, so the addition proofs carry over. -/

namespace XRPL.Model.Protocol

/-- Proof of `STAmount.operator_sub_nearest_iou`. -/
lemma STAmount.operator_sub_nearest_iou_proof (v1 v2 result : STAmount) (h1 : v1.IOUCanonical)
    (h2 : v2.IOUCanonical) (hfit : ∃ n : Number, n.isNormalized ∧ n.toRat = v1.toRat - v2.toRat)
    (hok : STAmount.operator_sub v1 v2 .to_nearest = .ok result) (hne : result.mValue ≠ 0) :
    |result.toRat - (v1.toRat - v2.toRat)| ≤ (10 : ℚ) ^ result.mOffset / 2 := by
  have htruth : v1.toRat + v2.operator_neg.toRat = v1.toRat - v2.toRat := by
    rw [STAmount.operator_neg_toRat]; ring
  have hok' : STAmount.operator_add v1 v2.operator_neg .to_nearest = .ok result := hok
  rw [← htruth] at hfit ⊢
  exact STAmount.operator_add_nearest_iou_proof v1 v2.operator_neg result h1 h2.operator_neg hfit hok' hne

/-- The exact difference `1000000000000000.5004` is rounded to `...000.500` and then to `...000`. -/
lemma STAmount.operator_sub_nearest_witness :
    STAmount.operator_sub ⟨.fractional, 1000000000000001, 0, false⟩
        ⟨.fractional, 4996000000000000, -16, false⟩ .to_nearest
      = .ok ⟨.fractional, 1000000000000000, 0, false⟩ := by
  decide +kernel

/-- The result is `0.5004` of a unit away from the exact difference. -/
lemma STAmount.operator_sub_nearest_witness_gap :
    (10 : ℚ) ^ (⟨.fractional, 1000000000000000, 0, false⟩ : STAmount).mOffset / 2 <
      |(⟨.fractional, 1000000000000000, 0, false⟩ : STAmount).toRat -
        ((⟨.fractional, 1000000000000001, 0, false⟩ : STAmount).toRat -
          (⟨.fractional, 4996000000000000, -16, false⟩ : STAmount).toRat)| := by
  have hr : (⟨.fractional, 1000000000000000, 0, false⟩ : STAmount).toRat = 1000000000000000 := by
    decide +kernel
  have h1 : (⟨.fractional, 1000000000000001, 0, false⟩ : STAmount).toRat = 1000000000000001 := by
    decide +kernel
  have h2 : (⟨.fractional, 4996000000000000, -16, false⟩ : STAmount).toRat = 4996 / 10000 := by
    decide +kernel
  rw [hr, h1, h2, zpow_zero]
  norm_num [abs_of_neg]

end XRPL.Model.Protocol
