import XRPL.Properties.Protocol.Number.Compare.Common.Proofs

/-! # `Number` comparisons

On normalized values each comparison operator decides the order of the exact values. -/

namespace XRPL.Model.Protocol

theorem operator_lt_iff (x y : Number)
    (hx : x.isNormalized) (hy : y.isNormalized) :
    x.operator_lt y = true ↔ x.toRat < y.toRat :=
  operator_lt_iff_proof x y hx hy

/-- `operator_lt` is false exactly when the second value is at most the first. -/
lemma operator_lt_eq_false_iff (x y : Number) (hx : x.isNormalized) (hy : y.isNormalized) :
    x.operator_lt y = false ↔ y.toRat ≤ x.toRat := by
  rw [← not_lt, ← operator_lt_iff x y hx hy]
  simp

theorem operator_le_iff (x y : Number)
    (hx : x.isNormalized) (hy : y.isNormalized) :
    x.operator_le y = true ↔ x.toRat ≤ y.toRat :=
  operator_le_iff_proof x y hx hy

theorem operator_gt_iff (x y : Number)
    (hx : x.isNormalized) (hy : y.isNormalized) :
    x.operator_gt y = true ↔ y.toRat < x.toRat :=
  operator_gt_iff_proof x y hx hy

theorem operator_ge_iff (x y : Number)
    (hx : x.isNormalized) (hy : y.isNormalized) :
    x.operator_ge y = true ↔ y.toRat ≤ x.toRat :=
  operator_ge_iff_proof x y hx hy

theorem operator_eq_iff (x y : Number)
    (hx : x.isNormalized) (hy : y.isNormalized) :
    x.operator_eq y = true ↔ x.toRat = y.toRat :=
  operator_eq_iff_proof x y hx hy

theorem operator_ne_iff (x y : Number)
    (hx : x.isNormalized) (hy : y.isNormalized) :
    x.operator_ne y = true ↔ x.toRat ≠ y.toRat :=
  operator_ne_iff_proof x y hx hy

/-- `Number.operator_eq` decides structural record equality. -/
theorem Number.operator_eq_iff_eq (x y : Number) :
    x.operator_eq y = true ↔ x = y := by
  unfold Number.operator_eq
  rw [Bool.and_eq_true, Bool.and_eq_true, beq_iff_eq, beq_iff_eq, beq_iff_eq]
  constructor
  · rintro ⟨⟨hn, hm⟩, he⟩
    obtain ⟨xn, xm, xe⟩ := x
    obtain ⟨yn, ym, ye⟩ := y
    simp only at hn hm he
    subst hn; subst hm; subst he; rfl
  · rintro rfl
    exact ⟨⟨rfl, rfl⟩, rfl⟩

/-- `Number.operator_ne` decides structural record inequality. -/
theorem Number.operator_ne_iff_ne (x y : Number) :
    x.operator_ne y = true ↔ x ≠ y := by
  rw [ne_eq, ← Number.operator_eq_iff_eq]
  unfold Number.operator_ne
  cases x.operator_eq y <;> simp

/-- On a normalized number, `operator_ne` against zero is false exactly at rational zero. -/
theorem Number.operator_ne_zero_eq_false_iff (x : Number) (hx : x.isNormalized) :
    x.operator_ne Number.zero = false ↔ x.toRat = 0 := by
  rw [Bool.eq_false_iff, ne_eq, operator_ne_iff x Number.zero hx Number.zero_isNormalized,
      Number.toRat_zero, not_not]

end XRPL.Model.Protocol
