import XRPL.Properties.Lending.Loan.Common.DefaultCoverTotal
import XRPL.Properties.Lending.Loan.Common.MulTotal
import XRPL.Properties.Lending.Loan.Common.RoundingError

/-! # Number arithmetic below `10^200` never fails

A sum, difference or product of normalized numbers below `10^200` in size computes, and so does a quotient by a
divisor at least `10^-200` in size. The exponents stay far from the top of the range. -/

namespace XRPL.Model.Protocol

/-- A normalized number below `10^200` in size has its exponent at most `182`. -/
lemma Number.exponent_le_of_abs_lt_big (x : Number) (hx : x.isNormalized) (h : |x.toRat| < 10 ^ 200) :
    x.exponent_ ≤ 182 := by
  by_cases h0 : x.mantissa_ = 0
  · rw [Number.eq_zero_of_mantissa_zero x hx h0]; decide
  · have := Number.exponent_lt_of_abs_lt x hx h0 182 (by norm_num; exact h)
    omega

/-- A sum of normalized numbers below `10^200` computes, in every mode. -/
lemma Number.operator_add_ok_of_abs (x y : Number) (mode : rounding_mode) (hx : x.isNormalized)
    (hy : y.isNormalized) (hxl : |x.toRat| < 10 ^ 200) (hyl : |y.toRat| < 10 ^ 200) :
    ∃ r, x.operator_add y mode = .ok r := by
  have := Number.exponent_le_of_abs_lt_big x hx hxl
  have := Number.exponent_le_of_abs_lt_big y hy hyl
  exact Number.operator_add_ok_of_exp x y mode hx hy (by unfold maxExponent; omega) (by unfold maxExponent; omega)

/-- A difference of normalized numbers below `10^200` computes, in every mode. -/
lemma Number.operator_sub_ok_of_abs (x y : Number) (mode : rounding_mode) (hx : x.isNormalized)
    (hy : y.isNormalized) (hxl : |x.toRat| < 10 ^ 200) (hyl : |y.toRat| < 10 ^ 200) :
    ∃ r, x.operator_sub y mode = .ok r := by
  have := Number.exponent_le_of_abs_lt_big x hx hxl
  have := Number.exponent_le_of_abs_lt_big y hy hyl
  exact Number.operator_sub_ok_of_exp x y mode hx hy (by unfold maxExponent; omega) (by unfold maxExponent; omega)

/-- A product of normalized numbers below `10^200` computes, in every mode. -/
lemma Number.operator_mul_ok_of_abs (x y : Number) (mode : rounding_mode) (hx : x.isNormalized)
    (hy : y.isNormalized) (hxl : |x.toRat| < 10 ^ 200) (hyl : |y.toRat| < 10 ^ 200) :
    ∃ r, x.operator_mul y mode = .ok r := by
  have := Number.exponent_le_of_abs_lt_big x hx hxl
  have := Number.exponent_le_of_abs_lt_big y hy hyl
  exact Number.operator_mul_ok_of_exp_le x y mode hx hy (by unfold maxExponent; omega)

/-- A quotient of a normalized number below `10^200` by one at least `10^-200` in size computes. -/
lemma Number.operator_div_ok_of_abs (x y : Number) (mode : rounding_mode) (hx : x.isNormalized)
    (hy : y.isNormalized) (hxl : |x.toRat| < 10 ^ 200) (hyl : (10 : ℚ) ^ (-200 : ℤ) ≤ |y.toRat|) :
    ∃ r, x.operator_div y mode = .ok r := by
  have hy0 : y.mantissa_ ≠ 0 := by
    intro h0
    rw [Number.toRat_eq_zero_of_mantissa_zero y h0, abs_zero] at hyl
    exact absurd hyl (not_le.mpr (zpow_pos (by norm_num) _))
  by_cases hx0 : x.mantissa_ = 0
  · refine ⟨x, ?_⟩
    have := Number.eq_zero_of_mantissa_zero x hx hx0
    subst this
    unfold Number.operator_div
    rw [Number.operator_eq_zero_false_of_mantissa_ne y hy0]
    simp only [Bool.false_eq_true, if_false]
    rw [if_pos (by decide)]
    rfl
  have h1 := Number.exponent_le_of_abs_lt_big x hx hxl
  have h2 := Number.exponent_gt_of_abs_ge y hy hy0 (-219) (by
    have : ((-219 : ℤ) + 19) = -200 := by norm_num
    rw [this]; exact hyl)
  exact Number.operator_div_ok_of_normalized x y mode hx hy hx0 hy0 (by unfold maxExponent; omega)

/-- A near value is at most `1 + ε` times its target in size. -/
lemma Number.Near.abs_le {r : Number} {t : ℚ} (h : r.Near t) : |r.toRat| ≤ |t| * (1 + Number.nearestError) := by
  have he := Number.nearestError_pos
  rcases h with h | h
  · rw [h, abs_zero]; positivity
  · have := abs_sub_abs_le_abs_sub r.toRat t
    nlinarith [abs_nonneg t]

/-- A rate of a normalized value below `10^190` computes to nearest, and its size is at most `(1 + ε)^2` times the
exact rate. -/
lemma tenthBipsOfValue_ok_of_abs (x : Number) (bips : TenthBips32) (hx : x.isNormalized)
    (hxl : |x.toRat| < 10 ^ 190) :
    ∃ r, tenthBipsOfValue x bips .to_nearest = .ok r ∧ r.isNormalized ∧
      |r.toRat| ≤ |x.toRat| * bips.toNat / 100000 * (1 + Number.nearestError) ^ 2 := by
  have he := Number.nearestError_pos
  have he' := Number.nearestError_le
  obtain ⟨hbn, hbv⟩ := TenthBips32.toNumber_facts bips
  obtain ⟨hun, huv⟩ := TenthBips32.toNumber_facts kTenthBipsPerUnity
  have hu : (kTenthBipsPerUnity.toNat : ℚ) = 100000 := by decide
  rw [hu] at huv
  have hb32 : (bips.toNat : ℚ) < 2 ^ 32 := by exact_mod_cast bips.toNat_lt
  have hbl : |bips.toNumber.toRat| < 10 ^ 200 := by
    rw [hbv, abs_of_nonneg (by positivity)]; linarith [show (2 : ℚ) ^ 32 < 10 ^ 200 by norm_num]
  obtain ⟨m, hm⟩ := Number.operator_mul_ok_of_abs x bips.toNumber .to_nearest hx hbn
    (lt_trans hxl (by norm_num)) hbl
  have hmn := Number.operator_mul_isNormalized _ _ _ _ hx hbn hm
  have hma := (Number.mul_near _ _ _ hx hbn hm).abs_le
  rw [hbv, abs_mul, abs_of_nonneg (by positivity : (0 : ℚ) ≤ bips.toNat)] at hma
  have hml : |m.toRat| < 10 ^ 200 := by
    calc |m.toRat| ≤ |x.toRat| * bips.toNat * (1 + Number.nearestError) := hma
      _ ≤ 10 ^ 190 * 2 ^ 32 * 2 := by gcongr; linarith
      _ < 10 ^ 200 := by norm_num
  obtain ⟨r, hr⟩ := Number.operator_div_ok_of_abs m kTenthBipsPerUnity.toNumber .to_nearest hmn hun hml
    (by rw [huv]; norm_num)
  refine ⟨r, ?_, Number.operator_div_isNormalized _ _ _ _ hmn hun hr, ?_⟩
  · simp only [tenthBipsOfValue, bind, Except.bind, hm, hr]
  · have hra := (Number.div_near _ _ _ hmn hun hr).abs_le
    rw [huv, abs_div, abs_of_pos (by norm_num : (0 : ℚ) < 100000)] at hra
    calc |r.toRat| ≤ |m.toRat| / 100000 * (1 + Number.nearestError) := hra
      _ ≤ |x.toRat| * bips.toNat * (1 + Number.nearestError) / 100000 * (1 + Number.nearestError) := by
          gcongr
      _ = |x.toRat| * bips.toNat / 100000 * (1 + Number.nearestError) ^ 2 := by ring

end XRPL.Model.Protocol
