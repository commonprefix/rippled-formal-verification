import XRPL.Properties.Protocol.Number.Common.Rounding.SuccessCondition
import XRPL.Properties.Protocol.Number.Add.Common.NoWrap
import XRPL.Properties.Protocol.Number.Add.Common.Rounded
import XRPL.Properties.Protocol.Number.Add.Common.SameSignDecompose

/-! # Exact success condition for `operator_add`

`x + y` succeeds exactly when the exact sum is below `(maxRepUp + 1) * 10^maxExponent` in size. Both signs end in
`doNormalize128`, so the sum can fail only there. -/

namespace XRPL.Model.Protocol

/-- A same-sign addition succeeds exactly when the exact sum is below `(maxRepUp + 1) * 10^maxExponent` in size. -/
lemma Number.operator_addSpec_sameSign_ok_iff (x y : Number) (mode : rounding_mode)
    (hx : x.isNormalized) (hy : y.isNormalized)
    (hx0 : x.mantissa_ ≠ 0) (hy0 : y.mantissa_ ≠ 0)
    (hsign : x.negative_ = y.negative_) (hc : ¬ x.operator_eq y.operator_neg = true) :
    (∃ result, x.operator_addSpec y mode = .ok result) ↔
      |x.toRat + y.toRat| < 9223372036854775811 * (10 : ℚ) ^ (maxExponent : ℤ) := by
  obtain ⟨M, E, δ, sticky, hδ0, hδ1, -, -, -, -, -, htruth, -, hE, hspec⟩ :=
    Number.operator_addSpec_same_sign_sum x y mode hx hy hx0 hy0 hsign hc
  rw [hspec, htruth, scaled_lt_top_iff _ δ _ hδ0 hδ1 hE]
  exact doNormalize128_ok_iff _ _ _ mode _ hE

/-- An opposite-sign addition succeeds exactly when the exact sum is below `(maxRepUp + 1) * 10^maxExponent` in
size. -/
lemma Number.operator_addSpec_diffSign_ok_iff (x y : Number) (mode : rounding_mode)
    (hx : x.isNormalized) (hy : y.isNormalized)
    (hx0 : x.mantissa_ ≠ 0) (hy0 : y.mantissa_ ≠ 0)
    (hsign : x.negative_ ≠ y.negative_) (hc : ¬ x.operator_eq y.operator_neg = true) :
    (∃ result, x.operator_addSpec y mode = .ok result) ↔
      |x.toRat + y.toRat| < 9223372036854775811 * (10 : ℚ) ^ (maxExponent : ℤ) := by
  obtain ⟨zn, zm_pre, E, g_aln, f_aln, hrep, hzm_pos, hzm_lt, hxbit_big, htruth, hE, -, hspec⟩ :=
    Number.operator_addSpec_diff_sign_subtract x y mode hx hy hx0 hy0 hsign hc
  obtain ⟨δ, hδ0, hδ1, -, -, -, -, -, hval⟩ :=
    Number.operator_add_post_subtract_value zm_pre E g_aln f_aln hrep hzm_pos hzm_lt hxbit_big _ htruth
  have hRe : (recoverSpec (toUInt128 largeRange.min * 1000) zm_pre E g_aln 40).2.1 ≤ maxExponent :=
    le_trans (recover_exponent_le _ _ _ _ _) hE
  rw [hspec, hval, scaled_lt_top_iff _ δ _ hδ0 hδ1 hRe]
  exact doNormalize128_ok_iff zn _ _ mode _ hRe

/-- `x + y` succeeds exactly when the exact sum is below `(maxRepUp + 1) * 10^maxExponent` in size, in every
rounding mode. -/
lemma Number.operator_add_ok_iff_proof (x y : Number) (mode : rounding_mode)
    (hx : x.isNormalized) (hy : y.isNormalized)
    (hx0 : x.mantissa_ ≠ 0) (hy0 : y.mantissa_ ≠ 0) :
    (∃ result, x.operator_add y mode = .ok result) ↔
      |x.toRat + y.toRat| < 9223372036854775811 * (10 : ℚ) ^ (maxExponent : ℤ) := by
  rw [Number.operator_add_eq_spec mode hx hy]
  by_cases hc : x.operator_eq y.operator_neg = true
  · have hx_ne_zero : ¬ x.operator_eq Number.zero = true := fun h =>
      hx0 (Number.mantissa_eq_zero_of_operator_eq_zero h)
    have hy_ne_zero : ¬ y.operator_eq Number.zero = true := fun h =>
      hy0 (Number.mantissa_eq_zero_of_operator_eq_zero h)
    rw [add_truth_zero_of_eq_neg x y hc, abs_zero]
    refine iff_of_true ⟨Number.zero, ?_⟩ (mul_pos (by norm_num) (zpow_pos (by norm_num) _))
    unfold Number.operator_addSpec
    rw [ite_eq_right hy_ne_zero, ite_eq_right hx_ne_zero, ite_eq_left hc]
  by_cases hs : x.negative_ = y.negative_
  · exact Number.operator_addSpec_sameSign_ok_iff x y mode hx hy hx0 hy0 hs hc
  · exact Number.operator_addSpec_diffSign_ok_iff x y mode hx hy hx0 hy0 hs hc

/-- `x - y` succeeds exactly when the exact difference is below `(maxRepUp + 1) * 10^maxExponent` in size, in every
rounding mode. -/
lemma Number.operator_sub_ok_iff_proof (x y : Number) (mode : rounding_mode)
    (hx : x.isNormalized) (hy : y.isNormalized)
    (hx0 : x.mantissa_ ≠ 0) (hy0 : y.mantissa_ ≠ 0) :
    (∃ result, x.operator_sub y mode = .ok result) ↔
      |x.toRat - y.toRat| < 9223372036854775811 * (10 : ℚ) ^ (maxExponent : ℤ) := by
  have h := Number.operator_add_ok_iff_proof x y.operator_neg mode hx (Number.operator_neg_isNormalized y hy)
    hx0 (by rw [Number.operator_neg_mantissa_of_ne y hy0]; exact hy0)
  rw [Number.toRat_neg, ← sub_eq_add_neg] at h
  exact h

/-- Every `operator_add` error on normalized operands is an overflow error. -/
lemma Number.operator_add_error_isOverflow {x y : Number} {mode : rounding_mode} {err : Error}
    (hx : x.isNormalized) (hy : y.isNormalized) (h : x.operator_add y mode = .error err) :
    isOverflow err = true := by
  rw [Number.operator_add_eq_spec mode hx hy] at h
  unfold Number.operator_addSpec at h
  split at h
  · cases h
  split at h
  · cases h
  split at h
  · cases h
  dsimp only at h
  split at h
  · exact doNormalize128_error_isOverflow largeRange_min_toNat_le h
  · exact doNormalize128_error_isOverflow largeRange_min_toNat_le h

/-- `x + y` fails with an overflow error when the exact sum is at or above `(maxRepUp + 1) * 10^maxExponent` in
size. -/
lemma Number.operator_add_overflow_proof (x y : Number) (mode : rounding_mode)
    (hx : x.isNormalized) (hy : y.isNormalized)
    (hx0 : x.mantissa_ ≠ 0) (hy0 : y.mantissa_ ≠ 0)
    (h : 9223372036854775811 * (10 : ℚ) ^ (maxExponent : ℤ) ≤ |x.toRat + y.toRat|) :
    ∃ err, x.operator_add y mode = .error err ∧ isOverflow err = true :=
  overflow_of_not_ok
    (fun hok => absurd ((Number.operator_add_ok_iff_proof x y mode hx hy hx0 hy0).mp hok) (not_lt.mpr h))
    (fun _ herr => Number.operator_add_error_isOverflow hx hy herr)

/-- `x - y` fails with an overflow error when the exact difference is at or above
`(maxRepUp + 1) * 10^maxExponent` in size. -/
lemma Number.operator_sub_overflow_proof (x y : Number) (mode : rounding_mode)
    (hx : x.isNormalized) (hy : y.isNormalized)
    (hx0 : x.mantissa_ ≠ 0) (hy0 : y.mantissa_ ≠ 0)
    (h : 9223372036854775811 * (10 : ℚ) ^ (maxExponent : ℤ) ≤ |x.toRat - y.toRat|) :
    ∃ err, x.operator_sub y mode = .error err ∧ isOverflow err = true := by
  have h' := Number.operator_add_overflow_proof x y.operator_neg mode hx (Number.operator_neg_isNormalized y hy)
    hx0 (by rw [Number.operator_neg_mantissa_of_ne y hy0]; exact hy0)
  rw [Number.toRat_neg, ← sub_eq_add_neg] at h'
  exact h' h

end XRPL.Model.Protocol
