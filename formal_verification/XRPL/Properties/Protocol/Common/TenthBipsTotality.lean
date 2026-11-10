import XRPL.Properties.Protocol.Common.TenthBips
import XRPL.Properties.Protocol.Number.Totality
import XRPL.Properties.Protocol.Number.AtExponent
import XRPL.Properties.Protocol.Number.Mul.RoundsToRepresentable
import XRPL.Properties.Protocol.Number.Div.RoundsToRepresentable
import XRPL.Properties.Protocol.Number.Normalize.NormalizedResult

/-! # An early-exit or service rate never fails within range

A value below `10^20` times a rate of at most 100% computes rounding up. A normalized `Number`'s exponent is bounded
by its size. -/

namespace XRPL.Model.Protocol

/-- A nonzero normalized `Number` below `10^(k + 18)` in size has its exponent below `k`. -/
lemma Number.exponent_lt_of_abs_lt (n : Number) (hn : n.isNormalized) (h0 : n.mantissa_ ≠ 0) (k : Int)
    (hlt : |n.toRat| < (10 : ℚ) ^ (k + 18)) : n.exponent_ < k := by
  obtain ⟨hlo, -⟩ := hn.mantissaBounds_nat h0
  rw [abs_toRat_eq n] at hlt
  have hm : (10 : ℚ) ^ (18 : ℕ) ≤ (n.mantissa_.toNat : ℚ) := by exact_mod_cast hlo
  have h1 : (10 : ℚ) ^ (18 : ℕ) * 10 ^ n.exponent_ < 10 ^ (k + 18) :=
    lt_of_le_of_lt (mul_le_mul_of_nonneg_right hm (zpow_pos (by norm_num) _).le) hlt
  rw [zpow_add₀ (by norm_num : (10 : ℚ) ≠ 0), mul_comm ((10 : ℚ) ^ k)] at h1
  have h2 : (10 : ℚ) ^ n.exponent_ < 10 ^ k := by
    have : (10 : ℚ) ^ (18 : ℤ) = 10 ^ (18 : ℕ) := zpow_natCast 10 18
    rw [this] at h1
    exact lt_of_mul_lt_mul_left h1 (by positivity)
  exact (zpow_lt_zpow_iff_right₀ (by norm_num : (1 : ℚ) < 10)).mp h2

/-- A nonzero normalized `Number` at least `10^(k + 19)` in size has its exponent above `k`. -/
lemma Number.exponent_gt_of_abs_ge (n : Number) (hn : n.isNormalized) (h0 : n.mantissa_ ≠ 0) (k : Int)
    (hge : (10 : ℚ) ^ (k + 19) ≤ |n.toRat|) : k < n.exponent_ := by
  obtain ⟨-, hhi⟩ := hn.mantissaBounds_nat h0
  rw [abs_toRat_eq n] at hge
  have hm : (n.mantissa_.toNat : ℚ) < (10 : ℚ) ^ (19 : ℕ) := by exact_mod_cast hhi
  have h1 : (10 : ℚ) ^ (k + 19) < (10 : ℚ) ^ (19 : ℕ) * 10 ^ n.exponent_ :=
    lt_of_le_of_lt hge (mul_lt_mul_of_pos_right hm (zpow_pos (by norm_num) _))
  rw [zpow_add₀ (by norm_num : (10 : ℚ) ≠ 0), mul_comm ((10 : ℚ) ^ k)] at h1
  have h2 : (10 : ℚ) ^ k < 10 ^ n.exponent_ := by
    have : (10 : ℚ) ^ (19 : ℤ) = 10 ^ (19 : ℕ) := zpow_natCast 10 19
    rw [this] at h1
    exact lt_of_mul_lt_mul_left h1 (by positivity)
  exact (zpow_lt_zpow_iff_right₀ (by norm_num : (1 : ℚ) < 10)).mp h2

/-- An upward rate of a value never throws, for a value below `10^20`, at least `10^L` when nonzero, and a
rate of at most 100%. The result is at most the value, and at least `10^(L - 5)` when nonzero. -/
lemma tenthBipsOfValue_upward_ok (d : Number) (rate : TenthBips32) (L : Int) (hd : d.isNormalized)
    (h0 : 0 ≤ d.toRat) (hlt : d.toRat < 10 ^ 20) (hL : -100 ≤ L) (hlo : d.mantissa_ ≠ 0 → (10 : ℚ) ^ L ≤ d.toRat)
    (hrate : rate.toNat ≤ 100000) :
    ∃ r, tenthBipsOfValue d rate .upward = .ok r ∧ r.isNormalized ∧ 0 ≤ r.toRat ∧ r.toRat ≤ d.toRat ∧
      (r.mantissa_ ≠ 0 → (10 : ℚ) ^ (L - 5) ≤ r.toRat) := by
  obtain ⟨hrn, hrv⟩ := TenthBips32.toNumber_facts rate
  obtain ⟨hun, huv⟩ := TenthBips32.toNumber_facts kTenthBipsPerUnity
  have hu5 : kTenthBipsPerUnity.toNumber.toRat = 100000 := by rw [huv]; rfl
  have hr5 : rate.toNumber.toRat ≤ 100000 := by rw [hrv]; exact_mod_cast hrate
  have hr0 : 0 ≤ rate.toNumber.toRat := by rw [hrv]; positivity
  have hu0 : kTenthBipsPerUnity.toNumber.mantissa_ ≠ 0 := by
    intro h; rw [Number.toRat_eq_zero_of_mantissa_zero _ h] at hu5; norm_num at hu5
  have huz : kTenthBipsPerUnity.toNumber.operator_eq Number.zero = false :=
    Number.operator_eq_zero_false_of_mantissa_ne _ hu0
  -- a zero value or a zero rate gives zero
  by_cases hd0 : d.mantissa_ = 0
  · rw [Number.eq_zero_of_mantissa_zero d hd hd0]
    exact ⟨Number.zero, tenthBipsOfValue_zero rate, Number.zero_isNormalized, by rw [Number.toRat_zero],
      by rw [Number.toRat_zero], fun h => absurd rfl h⟩
  have hdz : d.operator_eq Number.zero = false := Number.operator_eq_zero_false_of_mantissa_ne _ hd0
  by_cases hrz : rate.toNumber.mantissa_ = 0
  · have hrzero : rate.toNumber = Number.zero := Number.eq_zero_of_mantissa_zero _ hrn hrz
    have hzz : Number.zero.operator_eq Number.zero = true :=
      (operator_eq_iff _ _ Number.zero_isNormalized Number.zero_isNormalized).mpr rfl
    refine ⟨Number.zero, ?_, Number.zero_isNormalized, by rw [Number.toRat_zero], by rw [Number.toRat_zero]; exact h0,
      fun h => absurd rfl h⟩
    unfold tenthBipsOfValue
    dsimp only
    rw [hrzero]
    simp [Number.operator_mul, Number.operator_div, hdz, hzz, huz, bind, Except.bind, pure, Except.pure]
  have hd' : (10 : ℚ) ^ L ≤ d.toRat := hlo hd0
  have hrate1 : (1 : ℚ) ≤ rate.toNumber.toRat := by
    rw [hrv]
    have : rate.toNat ≠ 0 := by
      intro h; apply hrz
      by_contra hne
      have := Number.toRat_ne_zero_of_mantissa_ne_zero _ hne
      rw [hrv, h] at this; exact this rfl
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr this
  have hde1 := Number.exponent_gt_of_abs_ge d hd hd0 (L - 19) (by rw [abs_of_nonneg h0]; simpa using hd')
  have hde2 := Number.exponent_lt_of_abs_lt d hd hd0 2 (by rw [abs_of_nonneg h0]; norm_num; exact hlt)
  have hre1 := Number.exponent_gt_of_abs_ge _ hrn hrz (-19) (by
    rw [abs_of_nonneg hr0]; norm_num; exact hrate1)
  have hre2 := Number.exponent_lt_of_abs_lt _ hrn hrz (-8) (by rw [abs_of_nonneg hr0]; norm_num; linarith)
  obtain ⟨pr, hpr⟩ := Number.operator_mul_ok_of_normalized d rate.toNumber .upward hd hrn hd0 hrz
    (by unfold minExponent; omega) (by unfold maxExponent; omega)
  have hprn := Number.operator_mul_isNormalized _ _ _ _ hd hrn hpr
  have hneg : d.negative_ = false := Number.negative_false_of_nonneg d hd h0
  set W : Number := ⟨d.negative_, d.mantissa_, d.exponent_ + 5⟩ with hW
  have hWn : W.isNormalized := by
    rcases hd with hz | ⟨h1, h2, h3, h4, h5⟩
    · exact absurd (by rw [hz]; rfl) hd0
    · exact Or.inr ⟨h1, h2, h3, by show minExponent ≤ d.exponent_ + 5; omega,
        by show d.exponent_ + 5 ≤ maxExponent; unfold maxExponent; omega⟩
  have hWv : W.toRat = d.toRat * 100000 := by
    rw [Number.toRat_of_nonneg W hneg, Number.toRat_of_nonneg d hneg]
    show (d.mantissa_.toNat : ℚ) * 10 ^ (d.exponent_ + 5) = _
    rw [zpow_add₀ (by norm_num : (10 : ℚ) ≠ 0)]; norm_num; ring
  have hprle : pr.toRat ≤ W.toRat := by
    by_cases hp0 : pr.mantissa_ = 0
    · rw [Number.toRat_eq_zero_of_mantissa_zero pr hp0, hWv]; positivity
    obtain ⟨n, hn, hv⟩ := operator_mul_rounded_upward _ _ _ hd hrn hpr hp0
    rw [hv]; exact Number.upper_tight _ n hn W hWn (by rw [hWv]; nlinarith)
  by_cases hp0 : pr.mantissa_ = 0
  · have hpz : pr = Number.zero := Number.eq_zero_of_mantissa_zero _ hprn hp0
    have hzz : Number.zero.operator_eq Number.zero = true :=
      (operator_eq_iff _ _ Number.zero_isNormalized Number.zero_isNormalized).mpr rfl
    refine ⟨Number.zero, ?_, Number.zero_isNormalized, by rw [Number.toRat_zero], by rw [Number.toRat_zero]; exact h0,
      fun h => absurd rfl h⟩
    unfold tenthBipsOfValue
    dsimp only
    rw [hpr, ok_bind, hpz]
    simp [Number.operator_div, hzz, huz, pure, Except.pure]
  have hpr0 : 0 ≤ pr.toRat := by
    obtain ⟨n, hn, hv⟩ := operator_mul_rounded_upward _ _ _ hd hrn hpr hp0
    rw [hv]; exact le_trans (mul_nonneg h0 hr0) (Number.le_upper _ n hn)
  have hpe2 := Number.exponent_lt_of_abs_lt pr hprn hp0 7 (by
    rw [abs_of_nonneg hpr0]; norm_num; rw [hWv] at hprle; nlinarith)
  have hue1 := Number.exponent_gt_of_abs_ge _ hun hu0 (-14) (by rw [hu5]; norm_num)
  obtain ⟨r, hr⟩ := Number.operator_div_ok_of_normalized pr _ .upward hprn hun hp0 hu0
    (by unfold maxExponent; omega)
  have hok : tenthBipsOfValue d rate .upward = .ok r := by
    unfold tenthBipsOfValue
    dsimp only
    rw [hpr, ok_bind]
    exact hr
  have hrn' := Number.operator_div_isNormalized _ _ _ _ hprn hun hr
  obtain ⟨-, hr0'⟩ := tenthBipsOfValue_upward_facts d rate r hd h0 hok
  refine ⟨r, hok, hrn', hr0', ?_, ?_⟩
  · by_cases hrr : r.mantissa_ = 0
    · rw [Number.toRat_eq_zero_of_mantissa_zero r hrr]; exact h0
    obtain ⟨n, hn, hv⟩ := operator_div_rounded_upward _ _ _ hprn hun hr hrr
    rw [hv]
    exact Number.upper_tight _ n hn d hd (by rw [hu5, div_le_iff₀ (by norm_num)]; linarith)
  · intro hrr
    obtain ⟨n, hn, hv⟩ := operator_div_rounded_upward _ _ _ hprn hun hr hrr
    obtain ⟨n', hn', hv'⟩ := operator_mul_rounded_upward _ _ _ hd hrn hpr hp0
    have h1 : d.toRat * rate.toNumber.toRat ≤ pr.toRat := by rw [hv']; exact Number.le_upper _ n' hn'
    have h2 : pr.toRat / 100000 ≤ r.toRat := by rw [hv, ← hu5]; exact Number.le_upper _ n hn
    have h3 : (10 : ℚ) ^ (L - 5) = 10 ^ L / 100000 := by
      rw [zpow_sub₀ (by norm_num : (10 : ℚ) ≠ 0)]; norm_num
    rw [h3]
    have : (10 : ℚ) ^ L ≤ pr.toRat := by nlinarith
    calc (10 : ℚ) ^ L / 100000 ≤ pr.toRat / 100000 := by linarith
      _ ≤ r.toRat := h2

end XRPL.Model.Protocol
