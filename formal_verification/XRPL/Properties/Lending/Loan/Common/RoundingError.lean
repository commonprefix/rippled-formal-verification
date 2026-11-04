import XRPL.Properties.Protocol.Number.Div.RoundsWithin
import XRPL.Properties.Protocol.Number.Mul.RoundsWithin
import XRPL.Properties.Protocol.Number.Sub.RoundsWithin
import XRPL.Properties.Protocol.Common.Reduction
import XRPL.Properties.Vault.Proofs.Support.NumberFacts

/-! # Relative rounding error of the `Number` operators

A to-nearest `Number` addition, subtraction, multiplication or division returns zero or a value within the
relative error `6 / (2^63 − 3)` of the exact result. These lemmas turn that into upper and lower bounds. -/

namespace XRPL.Model.Protocol

/-- The relative error of a to-nearest `Number` operation. -/
def Number.nearestError : ℚ := 6 / (2 ^ 63 - 3)

lemma Number.nearestError_pos : 0 < Number.nearestError := by unfold Number.nearestError; norm_num

lemma Number.nearestError_le : Number.nearestError ≤ 1 / 10 ^ 18 := by unfold Number.nearestError; norm_num

/-- `r` is zero or within the relative error of `t`. -/
def Number.Near (r : Number) (t : ℚ) : Prop :=
  r.toRat = 0 ∨ |r.toRat - t| ≤ |t| * Number.nearestError

/-- A near value of a value at least zero is at most `1 + ε` times it. -/
lemma Number.Near.le {r : Number} {t : ℚ} (h : r.Near t) (ht : 0 ≤ t) :
    r.toRat ≤ t * (1 + Number.nearestError) := by
  have he := Number.nearestError_pos
  rcases h with h | h
  · rw [h]; positivity
  · rw [abs_of_nonneg ht] at h
    have := (abs_le.mp h).2
    linarith

/-- A near value of a value at most zero is at most zero. -/
lemma Number.Near.nonpos {r : Number} {t : ℚ} (h : r.Near t) (ht : t ≤ 0) : r.toRat ≤ 0 := by
  have he := Number.nearestError_le
  rcases h with h | h
  · rw [h]
  · rw [abs_of_nonpos ht] at h
    have := (abs_le.mp h).2
    nlinarith [Number.nearestError_pos]

/-- A nonzero near value of a value at least zero is at least `1 − ε` times it. -/
lemma Number.Near.ge {r : Number} {t : ℚ} (h : r.Near t) (hr : r.toRat ≠ 0) (ht : 0 ≤ t) :
    t * (1 - Number.nearestError) ≤ r.toRat := by
  rcases h with h | h
  · exact absurd h hr
  · rw [abs_of_nonneg ht] at h
    have := (abs_le.mp h).1
    linarith

/-- A near value is at most `1 + ε` times the truth or zero, whichever is larger. -/
lemma Number.Near.le_max {r : Number} {t : ℚ} (h : r.Near t) :
    r.toRat ≤ Max.max t 0 * (1 + Number.nearestError) := by
  have he := Number.nearestError_pos
  rcases le_total 0 t with ht | ht
  · rw [max_eq_left ht]; exact h.le ht
  · rw [max_eq_right ht, zero_mul]; exact h.nonpos ht

/-- A value equal to the truth is near it. -/
lemma Number.Near.of_eq {r : Number} {t : ℚ} (h : r.toRat = t) : r.Near t := by
  right
  rw [h, sub_self, abs_zero]
  exact mul_nonneg (abs_nonneg _) Number.nearestError_pos.le

private lemma Number.near_of_within {r : Number} {t e : ℚ} (h : RoundsWithin r t .to_nearest e)
    (he : e ≤ Number.nearestError) : r.Near t := by
  right
  simp only [RoundsWithin] at h
  exact le_trans h (mul_le_mul_of_nonneg_left he (abs_nonneg _))

/-- A to-nearest product is near the exact product. -/
lemma Number.mul_near (x y r : Number) (hx : x.isNormalized) (hy : y.isNormalized)
    (h : x.operator_mul y .to_nearest = .ok r) : r.Near (x.toRat * y.toRat) := by
  by_cases hm : r.mantissa_ = 0
  · exact Or.inl (Number.toRat_eq_zero_of_mantissa_zero _ hm)
  · exact Number.near_of_within (operator_mul_rounds_to_nearest x y r hx hy h hm)
      (by unfold Number.nearestError; norm_num)

/-- A to-nearest quotient is near the exact quotient. -/
lemma Number.div_near (x y r : Number) (hx : x.isNormalized) (hy : y.isNormalized)
    (h : x.operator_div y .to_nearest = .ok r) : r.Near (x.toRat / y.toRat) := by
  by_cases hm : r.mantissa_ = 0
  · exact Or.inl (Number.toRat_eq_zero_of_mantissa_zero _ hm)
  · exact Number.near_of_within (operator_div_rounds_to_nearest x y r hx hy h hm) le_rfl

/-- A to-nearest sum is near the exact sum. -/
lemma Number.add_near (x y r : Number) (hx : x.isNormalized) (hy : y.isNormalized)
    (h : x.operator_add y .to_nearest = .ok r) : r.Near (x.toRat + y.toRat) := by
  by_cases hym : y.mantissa_ = 0
  · have hy0 : y = Number.zero := Number.eq_zero_of_mantissa_zero y hy hym
    have hres : r = x := by
      unfold Number.operator_add at h
      rw [if_pos (by rw [hy0]; decide)] at h
      exact (Except.ok.inj h).symm
    exact Number.Near.of_eq (by rw [hres, hy0, Number.toRat_zero, add_zero])
  by_cases hxm : x.mantissa_ = 0
  · have hx0 : x = Number.zero := Number.eq_zero_of_mantissa_zero x hx hxm
    have hres : r = y := by
      unfold Number.operator_add at h
      rw [if_neg (Number.not_operator_eq_zero_of_mantissa_ne hym), if_pos (by rw [hx0]; decide)] at h
      exact (Except.ok.inj h).symm
    exact Number.Near.of_eq (by rw [hres, hx0, Number.toRat_zero, zero_add])
  by_cases hc : x.operator_eq y.operator_neg = true
  · have hres : r = Number.zero := by
      unfold Number.operator_add at h
      rw [if_neg (Number.not_operator_eq_zero_of_mantissa_ne hym),
        if_neg (Number.not_operator_eq_zero_of_mantissa_ne hxm), if_pos hc] at h
      exact (Except.ok.inj h).symm
    exact Or.inl (by rw [hres, Number.toRat_zero])
  by_cases hm : r.mantissa_ = 0
  · exact Or.inl (Number.toRat_eq_zero_of_mantissa_zero _ hm)
  · exact Number.near_of_within (operator_add_rounds_to_nearest x y r hx hy hxm hym hc h hm) le_rfl

/-- A to-nearest difference is near the exact difference. -/
lemma Number.sub_near (x y r : Number) (hx : x.isNormalized) (hy : y.isNormalized)
    (h : x.operator_sub y .to_nearest = .ok r) : r.Near (x.toRat - y.toRat) := by
  unfold Number.operator_sub at h
  have := Number.add_near x y.operator_neg r hx (Number.operator_neg_isNormalized y hy) h
  rwa [Number.toRat_neg, ← sub_eq_add_neg] at this

/-- `(1 + e)^k ≤ 1 / (1 − k·e)` while `k·e < 1`. -/
lemma one_add_pow_le_inv (e : ℚ) (k : ℕ) (he : 0 ≤ e) (hk : (k : ℚ) * e < 1) :
    (1 + e) ^ k ≤ 1 / (1 - k * e) := by
  rcases Nat.eq_zero_or_pos k with hk0 | hk0
  · subst hk0; simp
  have hk1 : (1 : ℚ) ≤ k := by exact_mod_cast hk0
  have he1 : e < 1 := by nlinarith
  have h1 : 1 - (k : ℚ) * e ≤ (1 - e) ^ k := by
    have := one_add_mul_le_pow (a := -e) (by linarith) k
    have h' : (1 : ℚ) + k * -e = 1 - k * e := by ring
    rw [h', ← sub_eq_add_neg] at this
    exact this
  have hpos : 0 < 1 - (k : ℚ) * e := by linarith
  have hprod : (1 + e) ^ k * (1 - e) ^ k ≤ 1 := by
    rw [← mul_pow]
    exact pow_le_one₀ (by nlinarith) (by nlinarith)
  rw [le_div_iff₀ hpos]
  calc (1 + e) ^ k * (1 - k * e) ≤ (1 + e) ^ k * (1 - e) ^ k :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ ≤ 1 := hprod

/-- `(1 + ε)^k ≤ 1 + 2·k·ε` while `k·ε ≤ 1/2`. -/
lemma one_add_pow_le_lin (e : ℚ) (k : ℕ) (he : 0 ≤ e) (hk : (k : ℚ) * e ≤ 1 / 2) :
    (1 + e) ^ k ≤ 1 + 2 * k * e := by
  have h := one_add_pow_le_inv e k he (by linarith)
  have hpos : 0 < 1 - (k : ℚ) * e := by linarith
  refine le_trans h ?_
  rw [div_le_iff₀ hpos]
  nlinarith [show (0 : ℚ) ≤ k * e from by positivity]

end XRPL.Model.Protocol
