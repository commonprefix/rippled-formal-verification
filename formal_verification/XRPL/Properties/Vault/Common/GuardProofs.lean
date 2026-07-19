import XRPL.Properties.Vault.Defs
import XRPL.Properties.Protocol.Number.Compare.Compare
import XRPL.Properties.Protocol.Number.Common.ToRatLemmas

/-! # Shared bridges for the pure vault guards

`canVaultSet` and `canVaultDelete` are boolean guards over `Number.operator_ne` /
`Number.operator_lt`. Their exit theorems need two bridges:

* a structural one, `operator_eq`/`operator_ne` decide record equality of the
  three `Number` fields, used where the statement compares against `Number.zero`
  with `=`/`≠`;
* the rational one from `Compare`, `operator_ne`/`operator_lt` agree with the
  order on `toRat` once both sides are normalized.
-/

namespace XRPL.Model.Protocol

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

/-- `Number.zero` is normalized. -/
theorem Number.zero_isNormalized : Number.zero.isNormalized := Or.inl rfl

/-- On a normalized number, `operator_ne` against zero is false exactly at
rational zero. -/
theorem Number.operator_ne_zero_eq_false_iff (x : Number) (hx : x.isNormalized) :
    x.operator_ne Number.zero = false ↔ x.toRat = 0 := by
  rw [Bool.eq_false_iff, ne_eq, operator_ne_iff x Number.zero hx Number.zero_isNormalized,
      Number.toRat_zero, not_not]

end XRPL.Model.Protocol
