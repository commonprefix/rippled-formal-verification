import XRPL.Properties.Protocol.Number.Common.Notation
import XRPL.Properties.Protocol.Number.Common.ToRatLemmas
import XRPL.Properties.Protocol.Number.Common.Rounding.Spec
import XRPL.Properties.Protocol.Number.Add.Common.AlignDown

/-! # The alignment of `operator_add`

`operator_add` brings both mantissas onto one exponent like C++ `adjust`. The larger-exponent mantissa grows by
factors of ten up to `10^21`, and the other one sheds trailing zeros and then drops digits into the guard. -/

namespace XRPL.Model.Protocol

/-- Shedding trailing zeros divides the mantissa by `10^k` for some `k` with no remainder and raises the exponent by
`k` up to the target. A guard of zero digits stays as it is. -/
lemma adjustShrinkZeros_eq (g : Guard) (m : UInt64) (e target : Int) (hg : g.digits_ = 0)
    (m' : UInt64) (e' : Int) (g' : Guard) (h : adjustShrinkZeros g m e target = (m', e', g')) :
    ∃ k : ℕ, m'.toNat = m.toNat / 10 ^ k ∧ m.toNat % 10 ^ k = 0 ∧ e' = e + k ∧ g' = g ∧
      (e ≤ target → e' ≤ target) := by
  by_cases hc : e < target ∧ m % 10 = 0
  · rw [adjustShrinkZeros, ite_eq_left hc] at h
    have hm10 : m.toNat % 10 = 0 := by
      have h2 := congrArg UInt64.toNat hc.2
      simpa [UInt64.toNat_mod] using h2
    rw [hc.2, push_zero_fixed g hg] at h
    obtain ⟨k, h1, h2, h3, h4, h5⟩ := adjustShrinkZeros_eq g (m / 10) (e + 1) target hg m' e' g' h
    have hdiv : (m / 10).toNat = m.toNat / 10 := by simp [UInt64.toNat_div]
    refine ⟨k + 1, ?_, ?_, ?_, h4, fun _ => h5 (by omega)⟩
    · rw [h1, hdiv, Nat.div_div_eq_div_mul, pow_succ, mul_comm]
    · rw [hdiv] at h2
      obtain ⟨q, hq⟩ : 10 ∣ m.toNat := Nat.dvd_of_mod_eq_zero hm10
      rw [hq, Nat.mul_div_cancel_left _ (by norm_num)] at h2
      rw [hq, pow_succ, mul_comm (10 ^ k) 10, Nat.mul_mod_mul_left, h2]
    · rw [h3]; push_cast; ring
  · rw [adjustShrinkZeros, ite_eq_right hc] at h
    simp only [Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact ⟨0, by simp, Nat.mod_one _, by simp, rfl, id⟩
termination_by (target - e).toNat

/-- Growing the mantissa multiplies it by `10^j` and lowers the exponent by `j`. It stops at the other exponent, at
`minExponent`, or once the mantissa reaches `u`, and a mantissa below `u` never passes `10 u`. -/
lemma adjustExpandSpec_eq (u m : UInt128) (ee se : Int) (hu : u.toNat * 10 < 2 ^ 128) (m' : UInt128) (ee' : Int)
    (h : adjustExpandSpec u m ee se = (m', ee')) :
    ∃ j : ℕ, m'.toNat = m.toNat * 10 ^ j ∧ ee' = ee - j ∧
      (se ≤ ee → se ≤ ee') ∧ (minExponent ≤ ee → minExponent ≤ ee') ∧
      (0 < j → m'.toNat < u.toNat * 10) ∧
      (se < ee' → minExponent < ee' → u.toNat ≤ m'.toNat) := by
  by_cases hc : se < ee ∧ minExponent < ee ∧ m < u
  · rw [adjustExpandSpec, ite_eq_left hc] at h
    have hlt : m.toNat < u.toNat := BitVec.lt_def.mp hc.2.2
    have hmul : (m * 10).toNat = m.toNat * 10 := by
      rw [BitVec.toNat_mul, show (10 : BitVec 128).toNat = 10 from rfl, Nat.mod_eq_of_lt (by omega)]
    obtain ⟨j, h1, h2, h3, h4, h5, h6⟩ := adjustExpandSpec_eq u (m * 10) (ee - 1) se hu m' ee' h
    rw [hmul] at h1
    refine ⟨j + 1, by rw [h1]; ring, by rw [h2]; push_cast; ring, fun _ => h3 (by omega),
      fun _ => h4 (by omega), fun _ => ?_, h6⟩
    rcases Nat.eq_zero_or_pos j with hj | hj
    · subst hj; rw [h1]; omega
    · exact h5 hj
  · rw [adjustExpandSpec, ite_eq_right hc] at h
    simp only [Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    refine ⟨0, by simp, by simp, id, id, fun h => absurd h (lt_irrefl 0), fun h7 h8 => ?_⟩
    have hmu : ¬ m < u := fun hmu => hc ⟨h7, h8, hmu⟩
    exact BitVec.le_def.mp (BitVec.not_lt.mp hmu)
termination_by (ee - se).toNat
decreasing_by omega

/-- Dropping digits down to `target` splits the value into the kept mantissa and the dropped fraction. -/
lemma alignDownSpec_value (m : UInt64) (e target : Int) (g : Guard) (h : e ≤ target) :
    (m.toNat : ℚ) * 10 ^ e = ((alignDownSpec m e g target).1.toNat +
      ((m.toNat % 10 ^ (target - e).toNat : ℕ) : ℚ) / 10 ^ (target - e).toNat) * 10 ^ target := by
  have h_me := alignDownSpec_mantissa_eq m e g target
  rw [max_eq_right h] at h_me
  rw [h_me]
  set K : ℕ := (target - e).toNat with hK_def
  have hK_eq : (target : ℤ) = e + K := by rw [hK_def, Int.toNat_of_nonneg (by linarith)]; ring
  have h10K_ne : (10 : ℚ) ^ K ≠ 0 := by positivity
  have h_pow_split : (10 : ℚ) ^ target = 10 ^ e * 10 ^ K := by
    rw [hK_eq, zpow_add₀ (by norm_num : (10 : ℚ) ≠ 0), zpow_natCast]
  rw [h_pow_split]
  have hsplit : (m.toNat : ℚ) = ((m.toNat / 10 ^ K : ℕ) : ℚ) * (10 ^ K : ℚ) + ((m.toNat % 10 ^ K : ℕ) : ℚ) := by
    have h' : m.toNat = (m.toNat / 10 ^ K) * 10 ^ K + m.toNat % 10 ^ K := (Nat.div_add_mod' m.toNat (10 ^ K)).symm
    have : ((m.toNat : ℕ) : ℚ) = (((m.toNat / 10 ^ K) * 10 ^ K + m.toNat % 10 ^ K : ℕ) : ℚ) := by
      exact_mod_cast h'
    push_cast at this; linarith
  rw [hsplit]
  field_simp

/-- The fresh guard of the alignment holds no digit. -/
lemma alignGuard_digits (neg : Bool) :
    (if neg then Guard.new.set_negative else Guard.new).digits_ = 0 := by
  cases neg <;> rfl

/-- The fresh guard of the alignment is empty. -/
lemma alignGuard_empty (neg : Bool) :
    (if neg then Guard.new.set_negative else Guard.new).empty = true := by
  cases neg <;> rfl

/-- `adjust` of a 19-digit mantissa `em` and a smaller-exponent `sm`: `em'` below `10^22` on the common exponent, the
kept digits `sm'` and the guard's fraction `f`, nonzero only when `em'` reached `10^21`. -/
lemma adjustSpec_facts (em : UInt128) (ee : Int) (sm : UInt64) (se : Int) (neg : Bool)
    (em' : UInt128) (e : Int) (sm' : UInt64) (g' : Guard)
    (ha : adjustSpec (toUInt128 largeRange.min * 1000) em ee sm se
      (if neg then Guard.new.set_negative else Guard.new) = (em', e, sm', g'))
    (hlt : se < ee) (hmin : minExponent ≤ se) (hem : em.toNat < 10 ^ 19) (hem' : 10 ^ 18 ≤ em.toNat) :
    ∃ f : ℚ, represents g' f ∧ (em.toNat : ℚ) * 10 ^ ee = (em'.toNat : ℚ) * 10 ^ e ∧
      (sm.toNat : ℚ) * 10 ^ se = ((sm'.toNat : ℚ) + f) * 10 ^ e ∧
      em'.toNat < 10 ^ 22 ∧ 10 ^ 18 ≤ em'.toNat ∧ sm'.toNat ≤ sm.toNat ∧
      minExponent ≤ e ∧ e ≤ ee ∧ (g'.empty = false → 10 ^ 21 ≤ em'.toNat) := by
  have hu : (toUInt128 largeRange.min * 1000).toNat * 10 < 2 ^ 128 := by decide
  have huv : (toUInt128 largeRange.min * 1000).toNat = 10 ^ 21 := by decide
  set g := if neg then Guard.new.set_negative else Guard.new with hg_def
  rcases hs : adjustShrinkZeros g sm se ee with ⟨sm1, se1, g1⟩
  rcases hx : adjustExpandSpec (toUInt128 largeRange.min * 1000) em ee se1 with ⟨em1, e1⟩
  rcases hd : alignDownSpec sm1 se1 g1 e1 with ⟨sm2, se2, g2⟩
  unfold adjustSpec at ha
  rw [hs] at ha
  dsimp only at ha
  rw [hx] at ha
  dsimp only at ha
  rw [hd] at ha
  obtain ⟨rfl, rfl, rfl, rfl⟩ : em1 = em' ∧ e1 = e ∧ sm2 = sm' ∧ g2 = g' := by
    simpa only [Prod.mk.injEq] using ha
  obtain ⟨k, hk1, hk2, hk3, rfl, hk5⟩ := adjustShrinkZeros_eq g sm se ee (alignGuard_digits neg) _ _ _ hs
  obtain ⟨j, hj1, hj2, hj3, hj4, hj5, hj6⟩ := adjustExpandSpec_eq _ em ee se1 hu _ _ hx
  rw [huv] at hj5 hj6
  have hle : se1 ≤ e1 := hj3 (hk5 hlt.le)
  have hdrop := alignDownSpec_represents sm1 se1 g e1 0 (g0_represents_zero neg)
  rw [max_eq_right hle, zero_add, hd] at hdrop
  refine ⟨_, hdrop, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- the larger operand keeps its value
    have hj_eq : (ee : ℤ) = e1 + j := by omega
    rw [hj1, hj_eq, zpow_add₀ (by norm_num : (10 : ℚ) ≠ 0), zpow_natCast]
    push_cast
    ring
  · -- the smaller operand: trailing zeros, then the drop
    have hv := alignDownSpec_value sm1 se1 e1 g hle
    rw [hd] at hv
    rw [← hv, hk1, hk3]
    have hdvd : 10 ^ k ∣ sm.toNat := Nat.dvd_of_mod_eq_zero hk2
    have hcast : ((sm.toNat / 10 ^ k : ℕ) : ℚ) = (sm.toNat : ℚ) / 10 ^ k := by
      rw [Nat.cast_div hdvd (by positivity)]; push_cast; ring
    rw [hcast, zpow_add₀ (by norm_num : (10 : ℚ) ≠ 0), zpow_natCast]
    field_simp
  · -- below 10^22
    rcases Nat.eq_zero_or_pos j with hj | hj
    · subst hj; rw [hj1]; simp only [pow_zero, mul_one]; omega
    · have := hj5 hj; omega
  · -- at least 10^18
    rw [hj1]
    calc 10 ^ 18 ≤ em.toNat := hem'
      _ ≤ em.toNat * 10 ^ j := Nat.le_mul_of_pos_right _ (by positivity)
  · -- the kept digits of the smaller one
    have hm := alignDownSpec_mantissa_le sm1 se1 g e1
    rw [hd] at hm
    calc sm2.toNat ≤ sm1.toNat := hm
      _ = sm.toNat / 10 ^ k := hk1
      _ ≤ sm.toNat := Nat.div_le_self _ _
  · exact hj4 (le_trans hmin (by omega : se ≤ ee))
  · omega
  · -- a guard with digits came from a drop, which happens only once the larger mantissa reached 10^21
    intro hne
    by_cases hgap : se1 < e1
    · exact hj6 hgap (by omega)
    · rw [alignDownSpec_noop hgap] at hd
      obtain ⟨-, -, rfl⟩ : sm1 = sm2 ∧ se1 = se2 ∧ g = g2 := by simpa only [Prod.mk.injEq] using hd
      rw [alignGuard_empty neg] at hne
      exact absurd hne (by decide)

/-- A normalized nonzero Number has a mantissa of 19 digits and an exponent in range. -/
lemma Number.normal_bounds {x : Number} (hx : x.isNormalized) (hx0 : x.mantissa_ ≠ 0) :
    10 ^ 18 ≤ x.mantissa_.toNat ∧ x.mantissa_.toNat < 10 ^ 19 ∧ minExponent ≤ x.exponent_ ∧
      x.exponent_ ≤ maxExponent := by
  rcases hx with hz | ⟨hlo, hhi, -, hemin, hemax⟩
  · exact absurd (by rw [hz]; rfl) hx0
  · exact ⟨(mantissaBounds_nat_of ⟨hlo, hhi⟩).1, (mantissaBounds_nat_of ⟨hlo, hhi⟩).2, hemin, hemax⟩

/-- Of two normalized nonzero Numbers, the one with the smaller exponent is the smaller in magnitude. -/
lemma Number.abs_lt_of_exponent_lt {x y : Number} (hx : x.isNormalized) (hy : y.isNormalized)
    (hx0 : x.mantissa_ ≠ 0) (hy0 : y.mantissa_ ≠ 0) (h : x.exponent_ < y.exponent_) :
    |x.toRat| < |y.toRat| := by
  obtain ⟨-, hx19, -, -⟩ := Number.normal_bounds hx hx0
  obtain ⟨hy18, -, -, -⟩ := Number.normal_bounds hy hy0
  rw [abs_toRat_eq, abs_toRat_eq]
  have hxq : (x.mantissa_.toNat : ℚ) < 10 ^ 19 := by exact_mod_cast hx19
  have hyq : (10 : ℚ) ^ 18 ≤ (y.mantissa_.toNat : ℚ) := by exact_mod_cast hy18
  have hsplit : (10 : ℚ) ^ y.exponent_ = 10 ^ x.exponent_ * 10 ^ (y.exponent_ - x.exponent_) := by
    rw [← zpow_add₀ (by norm_num : (10 : ℚ) ≠ 0)]; ring_nf
  have h10 : (10 : ℚ) ≤ 10 ^ (y.exponent_ - x.exponent_) := by
    calc (10 : ℚ) = 10 ^ (1 : ℤ) := by norm_num
      _ ≤ 10 ^ (y.exponent_ - x.exponent_) := zpow_le_zpow_right₀ (by norm_num) (by omega)
  have hpos : (0 : ℚ) < 10 ^ x.exponent_ := zpow_pos (by norm_num) _
  rw [hsplit]
  calc (x.mantissa_.toNat : ℚ) * 10 ^ x.exponent_ < 10 ^ 19 * 10 ^ x.exponent_ :=
        mul_lt_mul_of_pos_right hxq hpos
    _ = 10 ^ 18 * 10 * 10 ^ x.exponent_ := by norm_num
    _ ≤ (y.mantissa_.toNat : ℚ) * 10 ^ (y.exponent_ - x.exponent_) * 10 ^ x.exponent_ := by
        apply mul_le_mul_of_nonneg_right _ hpos.le
        exact mul_le_mul hyq h10 (by norm_num) (by positivity)
    _ = (y.mantissa_.toNat : ℚ) * (10 ^ x.exponent_ * 10 ^ (y.exponent_ - x.exponent_)) := by ring

/-- Alignment of two normalized nonzero operands: mantissas `xa`, `ya` on exponent `E` and a guard fraction `f` that
the smaller-exponent operand adds, nonzero only when the other mantissa reached `10^21`. -/
theorem Number.addAlignSpec_facts (x y : Number) (hx : x.isNormalized) (hy : y.isNormalized)
    (hx0 : x.mantissa_ ≠ 0) (hy0 : y.mantissa_ ≠ 0) (xa ya : UInt128) (E : Int) (g : Guard)
    (ha : Number.addAlignSpec x y = (xa, ya, E, g)) :
    ∃ f : ℚ, represents g f ∧ minExponent ≤ E ∧ E ≤ maxExponent ∧ xa.toNat < 10 ^ 22 ∧ ya.toNat < 10 ^ 22 ∧
      (x.exponent_ < y.exponent_ → |x.toRat| = (xa.toNat + f) * 10 ^ E ∧ |y.toRat| = ya.toNat * 10 ^ E ∧
        xa.toNat < 10 ^ 19 ∧ 10 ^ 18 ≤ ya.toNat ∧ (g.empty = false → 10 ^ 21 ≤ ya.toNat)) ∧
      (y.exponent_ < x.exponent_ → |y.toRat| = (ya.toNat + f) * 10 ^ E ∧ |x.toRat| = xa.toNat * 10 ^ E ∧
        ya.toNat < 10 ^ 19 ∧ 10 ^ 18 ≤ xa.toNat ∧ (g.empty = false → 10 ^ 21 ≤ xa.toNat)) ∧
      (x.exponent_ = y.exponent_ → f = 0 ∧ g.empty = true ∧ |x.toRat| = xa.toNat * 10 ^ E ∧
        |y.toRat| = ya.toNat * 10 ^ E ∧ 10 ^ 18 ≤ xa.toNat ∧ xa.toNat < 10 ^ 19 ∧ 10 ^ 18 ≤ ya.toNat ∧
        ya.toNat < 10 ^ 19) := by
  obtain ⟨hx18, hx19, hxmin, hxmax⟩ := Number.normal_bounds hx hx0
  obtain ⟨hy18, hy19, hymin, hymax⟩ := Number.normal_bounds hy hy0
  rcases lt_trichotomy x.exponent_ y.exponent_ with h | h | h
  · unfold Number.addAlignSpec at ha
    rw [ite_eq_left h] at ha
    rcases hA : adjustSpec (toUInt128 largeRange.min * 1000) (toUInt128 y.mantissa_) y.exponent_ x.mantissa_
      x.exponent_ (if x.negative_ then Guard.new.set_negative else Guard.new) with ⟨ya', E', xm', g'⟩
    dsimp only at ha
    rw [hA] at ha
    obtain ⟨rfl, rfl, rfl, rfl⟩ : toUInt128 xm' = xa ∧ ya' = ya ∧ E' = E ∧ g' = g := by
      simpa only [Prod.mk.injEq] using ha
    obtain ⟨f, hrep, hv1, hv2, hb1, hb2, hb3, hb4, hb5, hb6⟩ :=
      adjustSpec_facts (toUInt128 y.mantissa_) y.exponent_ x.mantissa_ x.exponent_ x.negative_ _ _ _ _ hA h hxmin
        (by rw [toNat_toUInt128]; exact hy19) (by rw [toNat_toUInt128]; exact hy18)
    rw [toNat_toUInt128] at hv1
    refine ⟨f, hrep, hb4, by omega, ?_, hb1, fun _ => ?_, fun h' => absurd h' (by omega),
      fun h' => absurd h' (by omega)⟩
    · rw [toNat_toUInt128]; omega
    · refine ⟨?_, ?_, ?_, hb2, hb6⟩
      · rw [abs_toRat_eq, hv2, toNat_toUInt128]
      · rw [abs_toRat_eq, hv1]
      · rw [toNat_toUInt128]; omega
  · unfold Number.addAlignSpec at ha
    rw [ite_eq_right (by omega : ¬ x.exponent_ < y.exponent_),
      ite_eq_right (by omega : ¬ x.exponent_ > y.exponent_)] at ha
    simp only [Prod.mk.injEq] at ha
    obtain ⟨rfl, rfl, rfl, rfl⟩ := ha
    have hg := g0_represents_zero
      ((decide (x.mantissa_ < y.mantissa_) && x.negative_ || decide (y.mantissa_ < x.mantissa_) && y.negative_))
    refine ⟨0, ?_, hxmin, hxmax, ?_, ?_, fun h' => absurd h' (by omega), fun h' => absurd h' (by omega),
      fun _ => ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
    · convert hg using 2
    · rw [toNat_toUInt128]; omega
    · rw [toNat_toUInt128]; omega
    · split_ifs <;> rfl
    · rw [abs_toRat_eq, toNat_toUInt128]
    · rw [abs_toRat_eq, toNat_toUInt128, h]
    all_goals rw [toNat_toUInt128]; omega
  · unfold Number.addAlignSpec at ha
    rw [ite_eq_right (by omega : ¬ x.exponent_ < y.exponent_),
      ite_eq_left (show x.exponent_ > y.exponent_ from h)] at ha
    rcases hA : adjustSpec (toUInt128 largeRange.min * 1000) (toUInt128 x.mantissa_) x.exponent_ y.mantissa_
      y.exponent_ (if y.negative_ then Guard.new.set_negative else Guard.new) with ⟨xa', E', ym', g'⟩
    dsimp only at ha
    rw [hA] at ha
    obtain ⟨rfl, rfl, rfl, rfl⟩ : xa' = xa ∧ toUInt128 ym' = ya ∧ E' = E ∧ g' = g := by
      simpa only [Prod.mk.injEq] using ha
    obtain ⟨f, hrep, hv1, hv2, hb1, hb2, hb3, hb4, hb5, hb6⟩ :=
      adjustSpec_facts (toUInt128 x.mantissa_) x.exponent_ y.mantissa_ y.exponent_ y.negative_ _ _ _ _ hA h hymin
        (by rw [toNat_toUInt128]; exact hx19) (by rw [toNat_toUInt128]; exact hx18)
    rw [toNat_toUInt128] at hv1
    refine ⟨f, hrep, hb4, by omega, hb1, ?_, fun h' => absurd h' (by omega), fun _ => ?_,
      fun h' => absurd h' (by omega)⟩
    · rw [toNat_toUInt128]; omega
    · refine ⟨?_, ?_, ?_, hb2, hb6⟩
      · rw [abs_toRat_eq, hv2, toNat_toUInt128]
      · rw [abs_toRat_eq, hv1]
      · rw [toNat_toUInt128]; omega

end XRPL.Model.Protocol
