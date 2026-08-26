import XRPL.Properties.Vault.Common.SubZeroShape
import XRPL.Properties.Protocol.Number.Add.Common.Rounded

/-! # Unconditional downward subtraction lemmas (different-sign case)

This module lifts the `.downward` normalization to unconditional form for the
**different-sign** add (`x + y` with `x.negative_ ≠ y.negative_`), which is the
only shape a nonnegative subtraction `assetsTotal - assetsAvailable` produces.
The zero-mantissa output is the literal `Number.zero` (mode-general zero-shape
chain in `SubZeroShape`), so it is normalized; the nonzero output goes through the
mode-general `operator_add_result_isNormalized`. -/

namespace XRPL.Model.Protocol

/-- A mantissa-`0` `.downward` different-sign addition result of normalized
operands is the literal `Number.zero`. -/
lemma Number.operator_add_zero_shape_downward_diff (x y result : Number)
    (hx : x.isNormalized) (hy : y.isNormalized)
    (h_diff : x.negative_ ≠ y.negative_)
    (hok : Number.operator_add x y .downward = .ok result)
    (h0 : result.mantissa_ = 0) : result = Number.zero := by
  by_cases hy_guard : y.operator_eq Number.zero = true
  · have h_result : result = x := by
      unfold Number.operator_add at hok
      rw [if_pos hy_guard] at hok
      exact (Except.ok.inj (show (Except.ok x : Except Error Number) = .ok result from hok)).symm
    subst h_result
    exact Number.eq_zero_of_mantissa_zero result hx h0
  by_cases hx_guard : x.operator_eq Number.zero = true
  · have h_result : result = y := by
      unfold Number.operator_add at hok
      rw [if_neg hy_guard, if_pos hx_guard] at hok
      exact (Except.ok.inj (show (Except.ok y : Except Error Number) = .ok result from hok)).symm
    subst h_result
    exact Number.eq_zero_of_mantissa_zero result hy h0
  by_cases heq_guard : x.operator_eq y.operator_neg = true
  · unfold Number.operator_add at hok
    rw [if_neg hy_guard, if_neg hx_guard, if_pos heq_guard] at hok
    exact (Except.ok.inj
      (show (Except.ok Number.zero : Except Error Number) = .ok result from hok)).symm
  have hx_mant_ne : x.mantissa_ ≠ 0 := by
    intro h
    exact hx_guard (by rw [Number.eq_zero_of_mantissa_zero x hx h]; decide)
  have hy_mant_ne : y.mantissa_ ≠ 0 := by
    intro h
    exact hy_guard (by rw [Number.eq_zero_of_mantissa_zero y hy h]; decide)
  obtain ⟨M, ze', δ, zn, sticky, _, _, _, _, _, _, _, hok128, _, _, _⟩ :=
    operator_add_algorithmic_facts_diff_sign_represents x y result .downward hx hy
      hx_mant_ne hy_mant_ne h_diff heq_guard hok
  exact doNormalize128_zero_shape_sz zn M ze' sticky .downward result hok128 h0

/-- **Unconditional downward normalization (different-sign add).** -/
lemma operator_add_isNormalized_downward_diff (x y result : Number)
    (hx : x.isNormalized) (hy : y.isNormalized)
    (h_diff : x.negative_ ≠ y.negative_)
    (hok : Number.operator_add x y .downward = .ok result) :
    result.isNormalized := by
  by_cases h0 : result.mantissa_ = 0
  · rw [Number.operator_add_zero_shape_downward_diff x y result hx hy h_diff hok h0]
    exact Or.inl rfl
  by_cases hy_guard : y.operator_eq Number.zero = true
  · have h_result : result = x := by
      unfold Number.operator_add at hok
      rw [if_pos hy_guard] at hok
      exact (Except.ok.inj (show (Except.ok x : Except Error Number) = .ok result from hok)).symm
    rw [h_result]; exact hx
  by_cases hx_guard : x.operator_eq Number.zero = true
  · have h_result : result = y := by
      unfold Number.operator_add at hok
      rw [if_neg hy_guard, if_pos hx_guard] at hok
      exact (Except.ok.inj (show (Except.ok y : Except Error Number) = .ok result from hok)).symm
    rw [h_result]; exact hy
  by_cases heq_guard : x.operator_eq y.operator_neg = true
  · have h_result : result = Number.zero := by
      unfold Number.operator_add at hok
      rw [if_neg hy_guard, if_neg hx_guard, if_pos heq_guard] at hok
      exact (Except.ok.inj
        (show (Except.ok Number.zero : Except Error Number) = .ok result from hok)).symm
    exact absurd (show result.mantissa_ = 0 by rw [h_result]; rfl) h0
  have hx_mant_ne : x.mantissa_ ≠ 0 := by
    intro h
    exact hx_guard (by rw [Number.eq_zero_of_mantissa_zero x hx h]; decide)
  have hy_mant_ne : y.mantissa_ ≠ 0 := by
    intro h
    exact hy_guard (by rw [Number.eq_zero_of_mantissa_zero y hy h]; decide)
  exact operator_add_result_isNormalized x y result .downward hx hy hx_mant_ne hy_mant_ne
    h_diff heq_guard hok h0

/-- **Unconditional downward subtraction normalization.** When `x` and `-y` have
opposite signs (`x - y` with both nonnegative), the result is normalized, zero
mantissa included. -/
lemma operator_sub_isNormalized_downward (x y result : Number)
    (hx : x.isNormalized) (hy : y.isNormalized)
    (h_diff : x.negative_ ≠ y.operator_neg.negative_)
    (hok : Number.operator_sub x y .downward = .ok result) :
    result.isNormalized := by
  unfold Number.operator_sub at hok
  exact operator_add_isNormalized_downward_diff x y.operator_neg result hx
    (Number.operator_neg_isNormalized y hy) h_diff hok

/-- **Different-sign downward underflow.** When `x + y`, with `x` and `y` nonzero
and of opposite sign, rounds down to a zero mantissa, the true sum is below the
smallest positive representable magnitude. -/
lemma operator_add_underflow_truth_small_diff (x y result : Number)
    (hx : x.isNormalized) (hy : y.isNormalized)
    (hx_mant_ne : x.mantissa_ ≠ 0) (hy_mant_ne : y.mantissa_ ≠ 0)
    (h_diff : x.negative_ ≠ y.negative_)
    (h_not_zero : ¬ x.operator_eq y.operator_neg)
    (hok : Number.operator_add x y .downward = .ok result)
    (h0 : result.mantissa_ = 0) :
    |x.toRat + y.toRat| < (10 : ℚ) ^ (18 : ℕ) * (10 : ℚ) ^ (minExponent : ℤ) := by
  obtain ⟨M, ze', δ, zn, sticky, hδ_low, _hδ_le1, hsticky_zero, _hM_pos, hM_lt, hM_big,
      htruth, hok128, _hsign, hδ_lt, _hsticky_pos⟩ :=
    operator_add_algorithmic_facts_diff_sign_represents x y result .downward hx hy
      hx_mant_ne hy_mant_ne h_diff h_not_zero hok
  rw [htruth]
  exact doNormalize128_underflow_value_small zn M ze' δ sticky .downward hδ_low hδ_lt
    hsticky_zero _hM_pos (lt_trans hM_lt (by norm_num))
    (fun hst => by
      have h2 : (10 : ℚ) ^ 20 ≤ (M.toNat : ℚ) := by exact_mod_cast hM_big hst
      nlinarith [h2, hδ_lt, hδ_low]) result hok128 h0

/-- A nonzero-mantissa `Number` with nonnegative value is stored nonnegative. -/
lemma Number.negative_eq_false_of_nonneg (n : Number) (hm : n.mantissa_ ≠ 0)
    (hnn : 0 ≤ n.toRat) : n.negative_ = false := by
  by_contra h
  have hneg : n.negative_ = true := by
    cases hc : n.negative_ with
    | false => exact absurd hc h
    | true => rfl
  have hpos : 0 < n.toRat := lt_of_le_of_ne hnn (Ne.symm (Number.mantissa_ne_zero_iff.mp hm))
  exact absurd (Number.toRat_nonpos_of_negative n hneg) (not_le.mpr hpos)

/-- **Nonnegative-difference downward underflow.** A zero-mantissa `.downward`
result of `x - y` (with `x` and `-y` of opposite sign and `x ≠ y`) certifies the
true difference is below the smallest positive representable magnitude. -/
lemma operator_sub_underflow_small_diff (x y result : Number)
    (hx : x.isNormalized) (hy : y.isNormalized)
    (hx_mant_ne : x.mantissa_ ≠ 0) (hy_mant_ne : y.mantissa_ ≠ 0)
    (h_diff : x.negative_ ≠ y.operator_neg.negative_)
    (h_not_cancel : ¬ x.operator_eq y = true)
    (hok : Number.operator_sub x y .downward = .ok result)
    (h0 : result.mantissa_ = 0) :
    |x.toRat - y.toRat| < (10 : ℚ) ^ (18 : ℕ) * (10 : ℚ) ^ (minExponent : ℤ) := by
  have hny_norm := Number.operator_neg_isNormalized y hy
  have hny_mant_ne : y.operator_neg.mantissa_ ≠ 0 := by
    unfold Number.operator_neg
    rw [if_neg (by simp [hy_mant_ne])]; exact hy_mant_ne
  have h_not_zero : ¬ x.operator_eq y.operator_neg.operator_neg := by
    rw [neg_neg_of_mant_ne hy_mant_ne]; exact h_not_cancel
  unfold Number.operator_sub at hok
  have hkey := operator_add_underflow_truth_small_diff x y.operator_neg result hx hny_norm
    hx_mant_ne hny_mant_ne h_diff h_not_zero hok h0
  rw [Number.toRat_neg] at hkey
  rwa [sub_eq_add_neg]

end XRPL.Model.Protocol
