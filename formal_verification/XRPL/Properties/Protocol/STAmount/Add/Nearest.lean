import XRPL.Properties.Protocol.STAmount.Add.Common.NearestProofs

/-! # IOU addition rounds to nearest

IOU addition rounds twice, to 19 digits and then to 16, and can miss the nearest amount. The theorem assumes an
exact sum that is a Number (`hfit`), and the `_attained` witness shows a sum that breaks it. -/

namespace XRPL.Model.Protocol

/-- When the exact sum is itself a Number (`hfit`), `to_nearest` IOU addition gives an amount at most half a
unit away from it. -/
theorem STAmount.operator_add_nearest_iou (v1 v2 result : STAmount) (h1 : v1.IOUCanonical)
    (h2 : v2.IOUCanonical) (hfit : ∃ n : Number, n.isNormalized ∧ n.toRat = v1.toRat + v2.toRat)
    (hok : STAmount.operator_add v1 v2 .to_nearest = .ok result) (hne : result.mValue ≠ 0) :
    |result.toRat - (v1.toRat + v2.toRat)| ≤ (10 : ℚ) ^ result.mOffset / 2 := by
  sorry

/-- A sum rounded twice that ends more than half a unit away: `1000000000000001 + (-0.4996)` gives
`1000000000000000`. -/
theorem STAmount.operator_add_nearest_iou_attained :
    ∃ v1 v2 result : STAmount,
      v1.IOUCanonical ∧
      v2.IOUCanonical ∧
      STAmount.operator_add v1 v2 .to_nearest = .ok result ∧
      result.mValue ≠ 0 ∧
      (10 : ℚ) ^ result.mOffset / 2 < |result.toRat - (v1.toRat + v2.toRat)| := by
  sorry

end XRPL.Model.Protocol
