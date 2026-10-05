import XRPL.Properties.Protocol.Number.Normalize.Common.ResultFacts
import XRPL.Properties.Protocol.Number.Sub.ZeroShape
import XRPL.Properties.Protocol.Number.Common.Constants
import XRPL.Properties.Protocol.Number.Div.Common.Decompose

/-! # Every successful `normalize` result is normalized

`normalize_result_isNormalized` covers a nonzero input with a nonzero result. A
zero input, or an underflow, returns the literal `Number.zero`. So every
successful `normalize`, and so every successful `from_rep`, gives a normalized
`Number`. The same holds for `operator_mul` and `operator_div` of normalized
operands. -/

namespace XRPL.Model.Protocol

/-- A mantissa-`0` `doNormalize` result is the literal `Number.zero`. -/
lemma doNormalize_zero_shape (neg : Bool) (m : UInt64) (e : Int) (minM maxM : UInt64)
    (mode : rounding_mode) (result : Number)
    (hok : doNormalize neg m e minM maxM mode = .ok result) (h0 : result.mantissa_ = 0) :
    result = Number.zero := by
  unfold doNormalize at hok
  by_cases hm : (m == 0) = true
  · rw [if_pos hm] at hok; exact (Except.ok.inj hok).symm
  rw [if_neg hm] at hok
  simp only [] at hok
  rcases hsu : doNormalize_scaleUp minM m e with ⟨m₁, e₁⟩
  rw [hsu] at hok
  simp only [] at hok
  cases hsd : doNormalize_scaleDown maxM m₁ e₁
      (if neg then Guard.new.set_negative else Guard.new) with
  | error err => rw [hsd] at hok; simp at hok
  | ok sd =>
    obtain ⟨m₂, e₂, g₂⟩ := sd
    rw [hsd] at hok
    simp only [] at hok
    by_cases hund : (e₂ < minExponent || m₂ < minM) = true
    · rw [if_pos hund] at hok; exact (Except.ok.inj hok).symm
    · rw [if_neg hund] at hok
      cases hcap : doNormalize_capAtMaxRep m₂ e₂ g₂ with
      | error err => rw [hcap] at hok; simp at hok
      | ok cp =>
        obtain ⟨m₃, e₃, g₃⟩ := cp
        rw [hcap] at hok
        simp only [] at hok
        cases hru : g₃.doRoundUp neg m₃ e₃ minM maxM mode .normalize2 with
        | error err => rw [hru] at hok; simp at hok
        | ok res =>
          rw [hru] at hok
          simp only [] at hok
          have hres : result = res.toNumber := (Except.ok.inj hok).symm
          rw [hres] at h0 ⊢
          exact Guard.doRoundUp_zero_shape_sz g₃ neg m₃ e₃ minM maxM mode .normalize2 res hru h0

/-- Every successful `normalize` gives a normalized `Number`. -/
lemma Number.normalize_isNormalized (n result : Number) (mode : rounding_mode)
    (hok : n.normalize largeRange.min largeRange.max mode = .ok result) :
    result.isNormalized := by
  by_cases hr : result.mantissa_ = 0
  · rw [doNormalize_zero_shape _ _ _ _ _ mode result hok hr]
    exact Number.zero_isNormalized
  · by_cases hn : n.mantissa_ = 0
    · exfalso
      unfold Number.normalize doNormalize at hok
      rw [if_pos (by simp [hn])] at hok
      exact hr (by rw [← Except.ok.inj hok]; rfl)
    · exact normalize_result_isNormalized n result mode hn hok hr

/-- Every successful `from_rep` gives a normalized `Number`. -/
lemma Number.from_rep_isNormalized (m : Int64) (e : Int) (mode : rounding_mode)
    (result : Number)
    (hok : Number.from_rep m e largeRange.min largeRange.max mode = .ok result) :
    result.isNormalized :=
  Number.normalize_isNormalized _ result mode hok

/-- Every successful `operator_mul` of normalized `Number`s gives a normalized
`Number`. A zero operand is returned as it is, and every other product goes
through `normalize`. -/
lemma Number.operator_mul_isNormalized (x y result : Number) (mode : rounding_mode)
    (hx : x.isNormalized) (hy : y.isNormalized)
    (hok : Number.operator_mul x y mode = .ok result) : result.isNormalized := by
  unfold Number.operator_mul at hok
  split_ifs at hok with hx0 hy0
  · rw [← Except.ok.inj (show (Except.ok x : Except Error Number) = .ok result from hok)]
    exact hx
  · rw [← Except.ok.inj (show (Except.ok y : Except Error Number) = .ok result from hok)]
    exact hy
  · simp only at hok
    split at hok
    · exact absurd hok (by simp)
    · exact Number.normalize_isNormalized _ result mode hok

/-- Every successful `operator_div` of normalized `Number`s gives a normalized
`Number`. A zero numerator is returned as it is, and a zero quotient is the
literal `Number.zero`. -/
lemma Number.operator_div_isNormalized (x y result : Number) (mode : rounding_mode)
    (hx : x.isNormalized) (hy : y.isNormalized)
    (hok : Number.operator_div x y mode = .ok result) : result.isNormalized := by
  by_cases h0 : result.mantissa_ = 0
  · unfold Number.operator_div at hok
    split_ifs at hok with hy0 hx0
    · rw [← Except.ok.inj (show (Except.ok x : Except Error Number) = .ok result from hok)]
      exact hx
    · rcases hq : divQuotient128 x.mantissa_ y.mantissa_ x.exponent_ y.exponent_ with
        ⟨zm, ze, dr⟩
      rw [hq] at hok
      rw [doNormalize128_zero_shape_sz _ _ _ _ mode result hok h0]
      exact Number.zero_isNormalized
  · obtain ⟨hxm, hym⟩ := operator_div_operands_ne_zero hx hy hok h0
    exact operator_div_result_isNormalized x y result mode hx hy hxm hym hok h0

end XRPL.Model.Protocol
