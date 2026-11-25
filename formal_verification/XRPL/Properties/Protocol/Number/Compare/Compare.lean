import XRPL.Properties.Protocol.Number.Compare.Common.Proofs

/-! # `Number` comparisons

On normalized values each comparison operator decides the order of the exact values. -/

namespace XRPL.Model.Protocol

theorem Number.operator_lt_iff (x y : Number)
    (hx : x.isNormalized) (hy : y.isNormalized) :
    x.operator_lt y = true ↔ x.toRat < y.toRat := by
  sorry

/-- `operator_lt` is false exactly when the second value is at most the first. -/
lemma Number.operator_lt_eq_false_iff (x y : Number) (hx : x.isNormalized) (hy : y.isNormalized) :
    x.operator_lt y = false ↔ y.toRat ≤ x.toRat := by
  sorry

theorem Number.operator_le_iff (x y : Number)
    (hx : x.isNormalized) (hy : y.isNormalized) :
    x.operator_le y = true ↔ x.toRat ≤ y.toRat := by
  sorry

theorem Number.operator_gt_iff (x y : Number)
    (hx : x.isNormalized) (hy : y.isNormalized) :
    x.operator_gt y = true ↔ y.toRat < x.toRat := by
  sorry

theorem Number.operator_ge_iff (x y : Number)
    (hx : x.isNormalized) (hy : y.isNormalized) :
    x.operator_ge y = true ↔ y.toRat ≤ x.toRat := by
  sorry

theorem Number.operator_eq_iff (x y : Number)
    (hx : x.isNormalized) (hy : y.isNormalized) :
    x.operator_eq y = true ↔ x.toRat = y.toRat := by
  sorry

theorem Number.operator_ne_iff (x y : Number)
    (hx : x.isNormalized) (hy : y.isNormalized) :
    x.operator_ne y = true ↔ x.toRat ≠ y.toRat := by
  sorry

/-- `Number.operator_eq` decides structural record equality. -/
theorem Number.operator_eq_iff_eq (x y : Number) :
    x.operator_eq y = true ↔ x = y := by
  sorry

/-- `Number.operator_ne` decides structural record inequality. -/
theorem Number.operator_ne_iff_ne (x y : Number) :
    x.operator_ne y = true ↔ x ≠ y := by
  sorry

/-- On a normalized number, `operator_ne` against zero is false exactly at rational zero. -/
theorem Number.operator_ne_zero_eq_false_iff (x : Number) (hx : x.isNormalized) :
    x.operator_ne Number.zero = false ↔ x.toRat = 0 := by
  sorry

end XRPL.Model.Protocol
