import XRPL.Properties.Protocol.Number.Sub.ZeroShape
import XRPL.Properties.Protocol.Number.Add.Common.SameSignDecompose

/-! # A sum of normalized operands is normalized

In every rounding mode, a sum or difference of normalized `Number`s is normalized, and a zero sum is the literal
zero. -/

namespace XRPL.Model.Protocol

/-- A mantissa-zero sum of normalized operands is the literal zero, in every rounding mode. -/
private lemma Number.operator_add_zero_shape_any (x y result : Number) (mode : rounding_mode)
    (hx : x.isNormalized) (hy : y.isNormalized)
    (hok : Number.operator_add x y mode = .ok result)
    (h0 : result.mantissa_ = 0) : result = Number.zero := by
  by_cases hy_guard : y.operator_eq Number.zero = true
  · have h_result : result = x := by
      replace hok := Number.operator_add_ok_spec hok
      unfold Number.operator_addSpec at hok
      rw [if_pos hy_guard] at hok
      exact (Except.ok.inj (show (Except.ok x : Except Error Number) = .ok result from hok)).symm
    subst h_result
    exact Number.eq_zero_of_mantissa_zero result hx h0
  by_cases hx_guard : x.operator_eq Number.zero = true
  · have h_result : result = y := by
      replace hok := Number.operator_add_ok_spec hok
      unfold Number.operator_addSpec at hok
      rw [if_neg hy_guard, if_pos hx_guard] at hok
      exact (Except.ok.inj (show (Except.ok y : Except Error Number) = .ok result from hok)).symm
    subst h_result
    exact Number.eq_zero_of_mantissa_zero result hy h0
  by_cases heq_guard : x.operator_eq y.operator_neg = true
  · replace hok := Number.operator_add_ok_spec hok
    unfold Number.operator_addSpec at hok
    rw [if_neg hy_guard, if_neg hx_guard, if_pos heq_guard] at hok
    exact (Except.ok.inj (show (Except.ok Number.zero : Except Error Number) = .ok result from hok)).symm
  have hx_mant_ne : x.mantissa_ ≠ 0 := fun h => hx_guard (by rw [Number.eq_zero_of_mantissa_zero x hx h]; decide)
  have hy_mant_ne : y.mantissa_ ≠ 0 := fun h => hy_guard (by rw [Number.eq_zero_of_mantissa_zero y hy h]; decide)
  by_cases h_sign_eq : x.negative_ = y.negative_
  · obtain ⟨_, _, _, _, _, hspec⟩ := operator_add_algorithmic_facts_same_sign_anyMode x y result mode hx hy
      hx_mant_ne hy_mant_ne h_sign_eq heq_guard hok
    exact absurd h0 hspec.result_mant_ne
  · obtain ⟨M, ze', δ, zn, sticky, _, _, _, _, _, _, _, hok128, _, _, _⟩ :=
      operator_add_algorithmic_facts_diff_sign_represents x y result mode hx hy
        hx_mant_ne hy_mant_ne h_sign_eq heq_guard hok
    exact doNormalize128_zero_shape_sz zn M ze' sticky mode result hok128 h0

/-- A sum of normalized operands is normalized, in every rounding mode. -/
lemma Number.operator_add_isNormalized_any (x y result : Number) (mode : rounding_mode)
    (hx : x.isNormalized) (hy : y.isNormalized) (hok : Number.operator_add x y mode = .ok result) :
    result.isNormalized := by
  by_cases h0 : result.mantissa_ = 0
  · rw [Number.operator_add_zero_shape_any x y result mode hx hy hok h0]; exact Or.inl rfl
  · exact operator_add_isNormalized x y result mode hx hy hok h0

/-- A difference of normalized operands is normalized, in every rounding mode. -/
lemma Number.operator_sub_isNormalized_any (x y result : Number) (mode : rounding_mode)
    (hx : x.isNormalized) (hy : y.isNormalized) (hok : Number.operator_sub x y mode = .ok result) :
    result.isNormalized :=
  Number.operator_add_isNormalized_any x y.operator_neg result mode hx (Number.operator_neg_isNormalized y hy) hok

end XRPL.Model.Protocol
