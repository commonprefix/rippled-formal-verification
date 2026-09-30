import XRPL.Properties.Protocol.Number.Mul.RoundsWithin
import XRPL.Properties.Protocol.Number.Div.RoundsWithin
import XRPL.Properties.Vault.Common.SubZeroShape
import XRPL.Properties.Vault.Common.ClawbackDefs
import XRPL.Properties.Vault.Proofs.Support.Integral
import XRPL.Properties.Vault.Proofs.DepositTight.DivSharp

/-! # The two-stage `mul`/`div` pricing pipeline -/

namespace XRPL.Model.SingleAssetVault.ClwTight

open XRPL.Model.Protocol

lemma stage_const : (5 / (2 ^ 63 + 7) : ℚ) + 6 / (2 ^ 63 - 3) + 5 / (2 ^ 63 + 7) * (6 / (2 ^ 63 - 3))
    ≤ depositε := by
  unfold depositε; norm_num

lemma pipe_q (T Z P Q a b ε : ℚ) (hT : 0 < T) (hZ : 0 < Z) (ha : a ≤ 1 / 4) (hb0 : 0 ≤ b) (h1 : |P - T| ≤ T * a) (h2 : |Q - P / Z| ≤ |P / Z| * b)
    (hc : a + b + a * b ≤ ε) : |Q - T / Z| ≤ T / Z * ε := by
  have h3 := (abs_le.mp h1).1
  have h4 : T * a ≤ T * (1 / 4) := mul_le_mul_of_nonneg_left ha hT.le
  have hP0 : 0 ≤ P := by linarith
  rw [abs_of_nonneg (div_nonneg hP0 hZ.le)] at h2
  have hTZ : 0 < T / Z := div_pos hT hZ
  have e1 : |P / Z - T / Z| ≤ T / Z * a := by
    rw [← sub_div, abs_div, abs_of_pos hZ, div_le_iff₀ hZ]
    calc |P - T| ≤ T * a := h1
      _ = T / Z * a * Z := by field_simp
  have e2 : P / Z ≤ T / Z * (1 + a) := by
    have := (abs_le.mp e1).2; nlinarith
  calc |Q - T / Z| ≤ |Q - P / Z| + |P / Z - T / Z| := abs_sub_le _ _ _
    _ ≤ P / Z * b + T / Z * a := add_le_add h2 e1
    _ ≤ T / Z * (1 + a) * b + T / Z * a := by nlinarith
    _ = T / Z * (a + b + a * b) := by ring
    _ ≤ T / Z * ε := mul_le_mul_of_nonneg_left hc hTZ.le

/-- `x * y / z`, rounded twice to nearest, stays within `depositε` of the exact quotient. -/
lemma pipe (x y z p q : Number) (hx : x.isNormalized) (hy : y.isNormalized)
    (hz : z.isNormalized) (hx0 : 0 ≤ x.toRat) (hy0 : 0 ≤ y.toRat) (hz0 : 0 < z.toRat)
    (hmul : x.operator_mul y .to_nearest = .ok p) (hdiv : p.operator_div z .to_nearest = .ok q)
    (hq : q.mantissa_ ≠ 0) :
    q.isNormalized ∧ 0 < x.toRat * y.toRat / z.toRat ∧
      |q.toRat - x.toRat * y.toRat / z.toRat| ≤ x.toRat * y.toRat / z.toRat * depositε := by
  have hzne : ¬ z.operator_eq Number.zero = true := fun h => by
    simp [Number.operator_div, h] at hdiv
  have hpm := operator_div_numerator_ne_zero_sz _ _ _ _ hzne hdiv hq
  obtain ⟨hxm, hym⟩ := operator_mul_operands_ne_zero hx hy hmul hpm
  have hpn := operator_mul_result_isNormalized _ _ _ _ hx hy hxm hym hmul hpm
  obtain ⟨-, hzm⟩ := operator_div_operands_ne_zero hpn hz hdiv hq
  have hqn := operator_div_result_isNormalized _ _ _ _ hpn hz hpm hzm hdiv hq
  have hw1 := operator_mul_rounds_to_nearest x y p hx hy hmul hpm
  have hw2 := operator_div_rounds_to_nearest p z q hpn hz hdiv hq
  simp only [RoundsWithin, RatValued.toRat] at hw1 hw2
  change |p.toRat - x.toRat * y.toRat| ≤ |x.toRat * y.toRat| * (5 / (2 ^ 63 + 7)) at hw1
  change |q.toRat - p.toRat / z.toRat| ≤ |p.toRat / z.toRat| * (6 / (2 ^ 63 - 3)) at hw2
  have hxy0 : 0 ≤ x.toRat * y.toRat := mul_nonneg hx0 hy0
  rw [abs_of_nonneg hxy0] at hw1
  have hxy : 0 < x.toRat * y.toRat := by
    rcases lt_or_eq_of_le hxy0 with h | h
    · exact h
    · exfalso
      rcases mul_eq_zero.mp h.symm with h1 | h1
      · exact absurd h1 (Number.toRat_ne_zero_of_mantissa_ne_zero x hxm)
      · exact absurd h1 (Number.toRat_ne_zero_of_mantissa_ne_zero y hym)
  refine ⟨hqn, div_pos hxy hz0, ?_⟩
  exact pipe_q _ _ _ _ _ _ _ hxy hz0 (by norm_num) (by norm_num) hw1 hw2
    stage_const

lemma stage_const_sharp :
    (5 / (2 ^ 63 + 7) : ℚ) + DepTight.divSharpε + 5 / (2 ^ 63 + 7) * DepTight.divSharpε
      ≤ sharesε := by
  unfold DepTight.divSharpε sharesε; norm_num

/-- `x * y / z`, rounded twice to nearest, stays within `sharesε` of the exact quotient. -/
lemma pipe_sharp (x y z p q : Number) (hx : x.isNormalized) (hy : y.isNormalized)
    (hz : z.isNormalized) (hx0 : 0 ≤ x.toRat) (hy0 : 0 ≤ y.toRat) (hz0 : 0 < z.toRat)
    (hmul : x.operator_mul y .to_nearest = .ok p) (hdiv : p.operator_div z .to_nearest = .ok q)
    (hq : q.mantissa_ ≠ 0) :
    q.isNormalized ∧ 0 < x.toRat * y.toRat / z.toRat ∧
      |q.toRat - x.toRat * y.toRat / z.toRat| ≤ x.toRat * y.toRat / z.toRat * sharesε := by
  have hzne : ¬ z.operator_eq Number.zero = true := fun h => by
    simp [Number.operator_div, h] at hdiv
  have hpm := operator_div_numerator_ne_zero_sz _ _ _ _ hzne hdiv hq
  obtain ⟨hxm, hym⟩ := operator_mul_operands_ne_zero hx hy hmul hpm
  have hpn := operator_mul_result_isNormalized _ _ _ _ hx hy hxm hym hmul hpm
  obtain ⟨-, hzm⟩ := operator_div_operands_ne_zero hpn hz hdiv hq
  have hqn := operator_div_result_isNormalized _ _ _ _ hpn hz hpm hzm hdiv hq
  have hw1 := operator_mul_rounds_to_nearest x y p hx hy hmul hpm
  have hw2 := DepTight.operator_div_rounds_to_nearest_sharp p z q hpn hz hdiv hq
  simp only [RoundsWithin, RatValued.toRat] at hw1
  change |p.toRat - x.toRat * y.toRat| ≤ |x.toRat * y.toRat| * (5 / (2 ^ 63 + 7)) at hw1
  have hxy0 : 0 ≤ x.toRat * y.toRat := mul_nonneg hx0 hy0
  rw [abs_of_nonneg hxy0] at hw1
  have hxy : 0 < x.toRat * y.toRat := by
    rcases lt_or_eq_of_le hxy0 with h | h
    · exact h
    · exfalso
      rcases mul_eq_zero.mp h.symm with h1 | h1
      · exact absurd h1 (Number.toRat_ne_zero_of_mantissa_ne_zero x hxm)
      · exact absurd h1 (Number.toRat_ne_zero_of_mantissa_ne_zero y hym)
  refine ⟨hqn, div_pos hxy hz0, ?_⟩
  exact pipe_q _ _ _ _ _ _ _ hxy hz0 (by norm_num) (by unfold DepTight.divSharpε; norm_num) hw1 hw2
    stage_const_sharp

end XRPL.Model.SingleAssetVault.ClwTight
