import XRPL.Properties.Protocol.Number.Common.Notation
import XRPL.Properties.Protocol.Number.Add.Common.Decompose
import XRPL.Properties.Protocol.Number.Add.Common.ToNearest.AlgorithmicFacts.DiffSignStructural
import XRPL.Properties.Protocol.Number.Common.Helpers
import XRPL.Properties.Protocol.Number.Common.Rounding.DoRoundUp
import XRPL.Properties.Protocol.Number.Common.Rounding.Normalize


namespace XRPL.Model.Protocol

/-- The model's recover upper limit, in ℕ: `10^21`. -/
private lemma diffSign_UL_val : (toUInt128 largeRange.min * 1000).toNat = 10 ^ 21 := by
  have h1000n : (1000 : UInt64).toNat = 1000 := rfl
  rw [show (1000 : UInt128) = toUInt128 (1000 : UInt64) from rfl,
      uint128_of_uint64_mul_toNat largeRange.min 1000
        (by rw [largeRange_min_toNat, h1000n]; norm_num),
      largeRange_min_toNat, h1000n]
  norm_num

private lemma diffSign_UL_bound : (toUInt128 largeRange.min * 1000).toNat * 10 < 2 ^ 128 := by
  rw [diffSign_UL_val]; norm_num

set_option maxHeartbeats 3200000 in
-- Three-leg recover analysis over large UInt128 terms needs a raised budget.
/-- After the opposite-sign subtraction, `recover` and the borrow leave a mantissa `M`, an exponent `e` and a `δ` in
`[0, 1)` with `|truth| = (M + δ)·10^e`. The guard is left empty exactly when `δ = 0`. -/
lemma Number.operator_add_post_subtract_value
    (zm_pre : UInt128) (E : Int) (g_aln : Guard) (f_aln : ℚ)
    (hrep : represents g_aln f_aln)
    (hzm_pos : 1 ≤ zm_pre.toNat)
    (hzm_lt : zm_pre.toNat < 10 ^ 22)
    (hxbit_big : g_aln.xbit_ = true → 10 ^ 18 - 101 ≤ zm_pre.toNat)
    (truth : ℚ)
    (htruth : |truth| = ((zm_pre.toNat : ℚ) - f_aln) * 10 ^ E) :
    let R := recoverSpec (toUInt128 largeRange.min * 1000) zm_pre E g_aln 40
    let M := if R.2.2.empty = true then R.1 else R.1 - 1
    ∃ δ : ℚ,
      0 ≤ δ ∧ δ < 1 ∧
      (R.2.2.empty = true → δ = 0) ∧ (R.2.2.empty = false → 0 < δ) ∧
      1 ≤ M.toNat ∧ M.toNat < 10 ^ 22 ∧ (R.2.2.empty = false → 10 ^ 20 ≤ M.toNat) ∧
      |truth| = ((M.toNat : ℚ) + δ) * 10 ^ R.2.1 := by
  dsimp only
  have hUL := diffSign_UL_bound
  have hall : allNibblesAtMost9 g_aln.digits_ := by
    obtain ⟨_, _, _, _, _, h⟩ := hrep; exact h
  have hf_nn : 0 ≤ f_aln := represents_nonneg hrep
  have hf_lt : f_aln < 1 := represents_lt_one hrep
  set R := recoverSpec (toUInt128 largeRange.min * 1000) zm_pre E g_aln 40
    with hR_def
  have hzm_pos_q : (1 : ℚ) ≤ (zm_pre.toNat : ℚ) := by exact_mod_cast hzm_pos
  have h10E_pos : (0 : ℚ) < (10 : ℚ) ^ E := zpow_pos (by norm_num) _
  have hupper : R.1.toNat < 10 ^ 22 := by
    have h := recover_mantissa_lt (toUInt128 largeRange.min * 1000) zm_pre hUL E g_aln 40
      hzm_pos hall (by rw [diffSign_UL_val]; omega)
    rw [diffSign_UL_val] at h
    calc R.1.toNat < 10 ^ 21 * 10 := h
      _ = 10 ^ 22 := by norm_num
  have hexit := recover_40_exits zm_pre E g_aln hzm_pos hall
  have hcases := recover_exit_cases hexit
  by_cases hemp : R.2.2.empty = true
  · -- EMPTY leg: the value is exact.
    have hexact := recover_exact_of_empty (toUInt128 largeRange.min * 1000) zm_pre hUL
      E g_aln 40 hzm_pos hrep hemp
    rw [← hR_def] at hexact
    have hL_pos : (0 : ℚ) < ((zm_pre.toNat : ℚ) - f_aln) * 10 ^ E := by
      apply mul_pos _ h10E_pos
      linarith
    rw [hexact] at hL_pos
    have hR1_pos : 1 ≤ R.1.toNat := by
      by_contra h0
      push Not at h0
      have h : R.1.toNat = 0 := by omega
      rw [h] at hL_pos
      norm_num at hL_pos
    rw [ite_eq_left hemp]
    refine ⟨0, le_refl _, by norm_num, fun _ => rfl, fun h => ?_, hR1_pos, hupper, fun h => ?_, ?_⟩
    · rw [hemp] at h; exact Bool.noConfusion h
    · rw [hemp] at h; exact Bool.noConfusion h
    · rw [htruth, hexact, add_zero]
  · -- NON-EMPTY legs: the mantissa is huge, so borrow and pass the sticky tail.
    have hUL_le : (toUInt128 largeRange.min * 1000).toNat ≤ R.1.toNat :=
      hcases.resolve_right hemp
    rw [diffSign_UL_val] at hUL_le
    have hR1_ge1 : (1 : UInt128) ≤ R.1 := by
      rw [BitVec.le_def]
      have h1 : ((1 : UInt128)).toNat = 1 := by decide
      rw [h1]; omega
    have hM_toNat : (R.1 - 1).toNat = R.1.toNat - 1 := by
      rw [BitVec.toNat_sub_of_le hR1_ge1]
      have h1 : ((1 : UInt128)).toNat = 1 := by decide
      rw [h1]
    have hM_cast : ((R.1 - 1).toNat : ℚ) = (R.1.toNat : ℚ) - 1 := by
      rw [hM_toNat, Nat.cast_sub (by omega : 1 ≤ R.1.toNat)]
      norm_num
    -- In both cases the leftover fraction is in (0, 1).
    have hresidue : ∃ f' : ℚ, 0 ≤ f' ∧ f' < 1 ∧ 0 < f' ∧
        ((zm_pre.toNat : ℚ) - f_aln) * 10 ^ E
          = ((R.1.toNat : ℚ) - f') * 10 ^ R.2.1 := by
      by_cases hxbit : g_aln.xbit_ = true
      · -- xbit set: the mantissa is at least 10^18 - 101, so at most 4 digits come back from the guard
        -- and the fraction stays below 1.
        have hzm_big := hxbit_big hxbit
        obtain ⟨f', k, hk_le, hk_eq, hf'_nn, hf'_slack, hstrict, hf'_pos, hval, _⟩ :=
          recover_value_in_unit_interval_at_exit (toUInt128 largeRange.min * 1000) zm_pre hUL
            E g_aln f_aln 40 hf_nn hf_lt hrep hzm_pos
        rw [← hR_def] at hk_eq hval
        -- Extract the per-pop factor: (zm_pre - f_aln) * 10^k = R.1 - f'.
        have hk_pow : (10 : ℚ) ^ E = (10 : ℚ) ^ (E - (k : ℤ)) * (10 : ℚ) ^ (k : ℕ) := by
          rw [← zpow_natCast (10 : ℚ) k, ← zpow_add₀ (by norm_num : (10 : ℚ) ≠ 0)]
          congr 1; ring
        have hcore : ((zm_pre.toNat : ℚ) - f_aln) * (10 : ℚ) ^ (k : ℕ)
            = (R.1.toNat : ℚ) - f' := by
          have hpow_ne : ((10 : ℚ) ^ (E - (k : ℤ))) ≠ 0 :=
            ne_of_gt (zpow_pos (by norm_num) _)
          have h := hval
          rw [hk_eq, hk_pow] at h
          field_simp at h
          -- field_simp cancels the common 10^(E-k) factor
          exact h
        -- k ≤ 4 from the magnitudes.
        have hZ_low : (10 : ℚ) ^ 18 - 102 ≤ (zm_pre.toNat : ℚ) - f_aln := by
          have : ((10 : ℕ) ^ 18 - 101 : ℕ) ≤ zm_pre.toNat := hzm_big
          have hq : (((10 : ℕ) ^ 18 - 101 : ℕ) : ℚ) ≤ (zm_pre.toNat : ℚ) := by
            exact_mod_cast this
          have hcast : (((10 : ℕ) ^ 18 - 101 : ℕ) : ℚ) = (10 : ℚ) ^ 18 - 101 := by
            rw [Nat.cast_sub (by norm_num)]
            push_cast; norm_num
          rw [hcast] at hq
          linarith
        have hR_hi : (R.1.toNat : ℚ) - f' ≤ (10 : ℚ) ^ 22 := by
          have hq : (R.1.toNat : ℚ) ≤ ((10 : ℕ) ^ 22 : ℕ) := by
            exact_mod_cast le_of_lt hupper
          have : (((10 : ℕ) ^ 22 : ℕ) : ℚ) = (10 : ℚ) ^ 22 := by push_cast; norm_num
          linarith [this ▸ hq, hf'_nn]
        have hk4 : k ≤ 4 := by
          by_contra hk
          push Not at hk
          have h5 : (10 : ℚ) ^ 5 ≤ (10 : ℚ) ^ (k : ℕ) :=
            pow_le_pow_right₀ (by norm_num) hk
          nlinarith [hcore, hZ_low, hR_hi, h5]
        exact ⟨f', hf'_nn, hstrict (by omega), hf'_pos hxbit, hval⟩
      · -- xbit clear: the guard keeps the exact fraction, which is positive because the guard is not empty.
        have hdich : g_aln.xbit_ = true →
            ¬ (zm_pre < toUInt128 largeRange.min * 1000 ∧ ¬ g_aln.empty) :=
          fun hxt => absurd hxt hxbit
        obtain ⟨f', hrep', hval⟩ :=
          recover_preserves_represents (toUInt128 largeRange.min * 1000) zm_pre hUL
            E g_aln 40 hzm_pos hrep hdich
        have hxbit_exit : R.2.2.xbit_ = false := by
          have h := recover_xbit (toUInt128 largeRange.min * 1000) zm_pre E g_aln 40
          rw [← hR_def] at h
          rw [h]
          exact Bool.not_eq_true _ |>.mp hxbit
        have hdig_ne : R.2.2.digits_ ≠ 0 := by
          intro hd0
          apply hemp
          unfold Guard.empty Guard.unrecoverable
          rw [hd0, hxbit_exit]
          decide
        have hf'_pos : 0 < f' := by
          obtain ⟨x', hx'_nn, _, hf'_eq, _, _⟩ := hrep'
          have hdv_pos : 0 < decimalValue R.2.2.digits_ :=
            decimalValue_pos_of_ne_zero _ hdig_ne
          have hdv_q : (0 : ℚ) < (decimalValue R.2.2.digits_ : ℚ) / 10 ^ 16 := by
            apply div_pos _ (by positivity)
            exact_mod_cast hdv_pos
          rw [hf'_eq]
          linarith
        exact ⟨f', represents_nonneg hrep', represents_lt_one hrep', hf'_pos, hval⟩
    obtain ⟨f', hf'_nn, hf'_lt, hf'_pos, hval⟩ := hresidue
    rw [ite_eq_right hemp]
    refine ⟨1 - f', by linarith, by linarith, fun h => absurd h hemp, fun _ => by linarith, ?_, ?_,
      fun _ => ?_, ?_⟩
    · rw [hM_toNat]; omega
    · rw [hM_toNat]; omega
    · rw [hM_toNat]
      have : (10 : ℕ) ^ 21 - 1 ≥ 10 ^ 20 := by norm_num
      omega
    · rw [htruth, hval, hM_cast]
      ring

/-- After the opposite-sign subtraction, `recover` and the borrow give `M` and `δ` in `[0, 1)` with
`|truth| = (M + δ)·10^ze'`, and `doNormalize128` on `M` returns `result`. -/
theorem Number.operator_add_post_subtract
    (zn : Bool) (zm_pre : UInt128) (E : Int) (g_aln : Guard) (f_aln : ℚ)
    (mode : rounding_mode)
    (hrep : represents g_aln f_aln)
    (hzm_pos : 1 ≤ zm_pre.toNat)
    (hzm_lt : zm_pre.toNat < 10 ^ 22)
    (hxbit_big : g_aln.xbit_ = true → 10 ^ 18 - 101 ≤ zm_pre.toNat)
    (truth : ℚ)
    (htruth : |truth| = ((zm_pre.toNat : ℚ) - f_aln) * 10 ^ E)
    (result : Number)
    (hok : doNormalize128 zn
        (if (recoverSpec (toUInt128 largeRange.min * 1000) zm_pre E g_aln 40).2.2.empty = true
          then (recoverSpec (toUInt128 largeRange.min * 1000) zm_pre E g_aln 40).1
          else (recoverSpec (toUInt128 largeRange.min * 1000) zm_pre E g_aln 40).1 - 1)
        (recoverSpec (toUInt128 largeRange.min * 1000) zm_pre E g_aln 40).2.1
        largeRange.min largeRange.max mode
        (!(recoverSpec (toUInt128 largeRange.min * 1000) zm_pre E g_aln 40).2.2.empty)
        = .ok result) :
    ∃ (M : UInt128) (ze' : Int) (δ : ℚ) (sticky : Bool),
      (0 ≤ δ) ∧ δ ≤ 1 ∧
      (sticky = false → δ = 0) ∧
      1 ≤ M.toNat ∧ M.toNat < 10 ^ 22 ∧
      (sticky = true → 10 ^ 20 ≤ M.toNat) ∧
      |truth| = ((M.toNat : ℚ) + δ) * 10 ^ ze' ∧
      doNormalize128 zn M ze' largeRange.min largeRange.max mode sticky = .ok result ∧
      δ < 1 ∧
      (sticky = true → 0 < δ) := by
  obtain ⟨δ, hδ0, hδ1, hδ_empty, hδ_pos, hM_pos, hM_lt, hM_big, hval⟩ :=
    Number.operator_add_post_subtract_value zm_pre E g_aln f_aln hrep hzm_pos hzm_lt hxbit_big truth htruth
  exact ⟨_, _, δ, _, hδ0, le_of_lt hδ1, fun h => hδ_empty (by simpa using h), hM_pos, hM_lt,
    fun h => hM_big (by simpa using h), hval, hok, hδ1, fun h => hδ_pos (by simpa using h)⟩

/-- For diff-sign Numbers with `|x.toRat| < |y.toRat|`, the sum `x.toRat + y.toRat`
takes the sign of the dominant operand `y`. -/
lemma diff_sign_sum_sign_of_dominant {x y : Number}
    (h_diff_xy : x.negative_ ≠ y.negative_)
    (h_dom : |x.toRat| < |y.toRat|) :
    (y.negative_ = true → x.toRat + y.toRat ≤ 0) ∧
    (y.negative_ = false → 0 ≤ x.toRat + y.toRat) := by
  constructor
  · intro hyn
    have hxn : x.negative_ = false := by
      cases hh : x.negative_
      · rfl
      · rw [hh, hyn] at h_diff_xy; exact absurd rfl h_diff_xy
    have hx_nn : 0 ≤ x.toRat := Number.toRat_nonneg_of_nonnegative x hxn
    have hy_np : y.toRat ≤ 0 := Number.toRat_nonpos_of_negative y hyn
    rw [abs_of_nonneg hx_nn, abs_of_nonpos hy_np] at h_dom
    linarith
  · intro hyn
    have hxn : x.negative_ = true := by
      cases hh : x.negative_
      · rw [hh, hyn] at h_diff_xy; exact absurd rfl h_diff_xy
      · rfl
    have hx_np : x.toRat ≤ 0 := Number.toRat_nonpos_of_negative x hxn
    have hy_nn : 0 ≤ y.toRat := Number.toRat_nonneg_of_nonnegative y hyn
    rw [abs_of_nonpos hx_np, abs_of_nonneg hy_nn] at h_dom
    linarith

/-- Opposite-sign addition up to the subtraction of the aligned mantissas. The rest is `recover`, the borrow and
`doNormalize128` on the difference `zm_pre`, and `|x + y| = (zm_pre - f)·10^E` for the guard fraction `f`. -/
lemma Number.operator_addSpec_diff_sign_subtract
    (x y : Number) (mode : rounding_mode)
    (hx : x.isNormalized) (hy : y.isNormalized)
    (hx_mant_ne : x.mantissa_ ≠ 0) (hy_mant_ne : y.mantissa_ ≠ 0)
    (h_diff_sign : x.negative_ ≠ y.negative_)
    (h_not_zero : ¬ x.operator_eq y.operator_neg) :
    ∃ (zn : Bool) (zm_pre : UInt128) (E : Int) (g_aln : Guard) (f_aln : ℚ),
      represents g_aln f_aln ∧
      1 ≤ zm_pre.toNat ∧ zm_pre.toNat < 10 ^ 22 ∧
      (g_aln.xbit_ = true → 10 ^ 18 - 101 ≤ zm_pre.toNat) ∧
      |x.toRat + y.toRat| = ((zm_pre.toNat : ℚ) - f_aln) * 10 ^ E ∧
      E ≤ maxExponent ∧
      ((zn = true → x.toRat + y.toRat ≤ 0) ∧ (zn = false → 0 ≤ x.toRat + y.toRat)) ∧
      x.operator_addSpec y mode = doNormalize128 zn
        (if (recoverSpec (toUInt128 largeRange.min * 1000) zm_pre E g_aln 40).2.2.empty = true
          then (recoverSpec (toUInt128 largeRange.min * 1000) zm_pre E g_aln 40).1
          else (recoverSpec (toUInt128 largeRange.min * 1000) zm_pre E g_aln 40).1 - 1)
        (recoverSpec (toUInt128 largeRange.min * 1000) zm_pre E g_aln 40).2.1
        largeRange.min largeRange.max mode
        (!(recoverSpec (toUInt128 largeRange.min * 1000) zm_pre E g_aln 40).2.2.empty) := by
  have hy0 : ¬ y.operator_eq Number.zero = true := by
    simp [Number.operator_eq, Number.zero, hy_mant_ne]
  have hx0 : ¬ x.operator_eq Number.zero = true := by
    simp [Number.operator_eq, Number.zero, hx_mant_ne]
  have hsgn : (x.negative_ == y.negative_) = false := by
    cases hxn : x.negative_ <;> cases hyn : y.negative_ <;> simp_all
  generalize ha : Number.addAlignSpec x y = a
  obtain ⟨xa, ya, E, g⟩ := a
  obtain ⟨f, hrep, -, hEmax, hxa, hya, hlt, hgt, heq⟩ :=
    Number.addAlignSpec_facts x y hx hy hx_mant_ne hy_mant_ne xa ya E g ha
  have hspec : ∀ zm zn, (if xa > ya then (xa - ya, x.negative_) else (ya - xa, y.negative_)) = (zm, zn) →
      x.operator_addSpec y mode = doNormalize128 zn
        (if (recoverSpec (toUInt128 largeRange.min * 1000) zm E g 40).2.2.empty = true
          then (recoverSpec (toUInt128 largeRange.min * 1000) zm E g 40).1
          else (recoverSpec (toUInt128 largeRange.min * 1000) zm E g 40).1 - 1)
        (recoverSpec (toUInt128 largeRange.min * 1000) zm E g 40).2.1
        largeRange.min largeRange.max mode
        (!(recoverSpec (toUInt128 largeRange.min * 1000) zm E g 40).2.2.empty) := by
    intro zm zn hd
    unfold Number.operator_addSpec
    rw [ite_eq_right hy0, ite_eq_right hx0, ite_eq_right h_not_zero]
    dsimp only
    rw [ha]
    dsimp only
    rw [hsgn]
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [hd]
  have hf0 : 0 ≤ f := represents_nonneg hrep
  have hf1 : f < 1 := represents_lt_one hrep
  have hE : (0 : ℚ) < 10 ^ E := zpow_pos (by norm_num) _
  have hsub : ∀ a b : UInt128, b.toNat ≤ a.toNat → (a - b).toNat = a.toNat - b.toNat := fun a b h =>
    BitVec.toNat_sub_of_le (BitVec.le_def.mpr h)
  have habs := abs_add_eq_of_diff_sign h_diff_sign
  have hxbit_empty : g.xbit_ = true → g.empty = false := by
    intro hxb; unfold Guard.empty; simp [hxb]
  rcases lt_trichotomy x.exponent_ y.exponent_ with h | h | h
  · -- y has the larger exponent, so it dominates and the subtraction is ya - xa
    obtain ⟨hxv, hyv, hxa19, hya18, hbig⟩ := hlt h
    have hdom0 := Number.abs_lt_of_exponent_lt hx hy hx_mant_ne hy_mant_ne h
    have hdom := hdom0
    rw [hxv, hyv] at hdom
    have hlt' : xa.toNat < ya.toNat := by
      have : (xa.toNat : ℚ) < ya.toNat := by nlinarith
      exact_mod_cast this
    have hng : ¬ xa > ya := fun hg' => by have := BitVec.lt_def.mp hg'; omega
    refine ⟨y.negative_, ya - xa, E, g, f, hrep, ?_, ?_, ?_, ?_, hEmax, ?_, hspec _ _ (by rw [ite_eq_right hng])⟩
    · rw [hsub _ _ hlt'.le]; omega
    · rw [hsub _ _ hlt'.le]; omega
    · intro hxb; have := hbig (hxbit_empty hxb); rw [hsub _ _ hlt'.le]; omega
    · rw [habs, hxv, hyv, hsub _ _ hlt'.le, Nat.cast_sub hlt'.le, abs_of_neg (by nlinarith)]; ring
    · exact diff_sign_sum_sign_of_dominant h_diff_sign hdom0
  · -- equal exponents: no guard, the larger mantissa dominates
    obtain ⟨rfl, hgemp, hxv, hyv, -, -, -, -⟩ := heq h
    have hne : xa.toNat ≠ ya.toNat := by
      intro hxy
      apply h_not_zero
      have hm : x.mantissa_.toNat = y.mantissa_.toNat := by
        have h1 : (x.mantissa_.toNat : ℚ) * 10 ^ x.exponent_ = (y.mantissa_.toNat : ℚ) * 10 ^ y.exponent_ := by
          rw [← abs_toRat_eq, ← abs_toRat_eq, hxv, hyv, hxy]
        rw [h] at h1
        have h2 := mul_right_cancel₀ (ne_of_gt (zpow_pos (by norm_num : (0 : ℚ) < 10) y.exponent_)) h1
        exact_mod_cast h2
      have hneg : x.negative_ = !y.negative_ := by
        cases hxn : x.negative_ <;> cases hyn : y.negative_ <;> simp_all
      simp [Number.operator_eq, Number.operator_neg, hneg, UInt64.toNat_inj.mp hm, h, hy_mant_ne]
    have hrep0 : represents g 0 := hrep
    have hxb : g.xbit_ = false := by
      cases hx : g.xbit_
      · rfl
      · exact absurd (hxbit_empty hx) (by rw [hgemp]; decide)
    rcases Nat.lt_or_gt_of_ne hne with hlt' | hgt'
    · have hng : ¬ xa > ya := fun hg' => by have := BitVec.lt_def.mp hg'; omega
      have hdom : |x.toRat| < |y.toRat| := by
        rw [hxv, hyv]
        have : (xa.toNat : ℚ) < ya.toNat := by exact_mod_cast hlt'
        nlinarith
      refine ⟨y.negative_, ya - xa, E, g, 0, hrep0, ?_, ?_, fun h' => by rw [hxb] at h'; exact absurd h' (by decide),
        ?_, hEmax, ?_, hspec _ _ (by rw [ite_eq_right hng])⟩
      · rw [hsub _ _ hlt'.le]; omega
      · rw [hsub _ _ hlt'.le]; omega
      · rw [habs, hxv, hyv, hsub _ _ hlt'.le, Nat.cast_sub hlt'.le, abs_of_neg (by
          have : (xa.toNat : ℚ) < ya.toNat := by exact_mod_cast hlt'
          nlinarith)]
        ring
      · exact diff_sign_sum_sign_of_dominant h_diff_sign hdom
    · have hg' : xa > ya := BitVec.lt_def.mpr hgt'
      have hdom : |y.toRat| < |x.toRat| := by
        rw [hxv, hyv]
        have : (ya.toNat : ℚ) < xa.toNat := by exact_mod_cast hgt'
        nlinarith
      refine ⟨x.negative_, xa - ya, E, g, 0, hrep0, ?_, ?_, fun h' => by rw [hxb] at h'; exact absurd h' (by decide),
        ?_, hEmax, ?_, hspec _ _ (by rw [ite_eq_left hg'])⟩
      · rw [hsub _ _ hgt'.le]; omega
      · rw [hsub _ _ hgt'.le]; omega
      · rw [habs, hxv, hyv, hsub _ _ hgt'.le, Nat.cast_sub hgt'.le, abs_of_pos (by
          have : (ya.toNat : ℚ) < xa.toNat := by exact_mod_cast hgt'
          nlinarith)]
        ring
      · have := diff_sign_sum_sign_of_dominant (Ne.symm h_diff_sign) hdom
        rw [add_comm] at this
        exact this
  · -- x has the larger exponent, so it dominates and the subtraction is xa - ya
    obtain ⟨hyv, hxv, hya19, hxa18, hbig⟩ := hgt h
    have hdom := Number.abs_lt_of_exponent_lt hy hx hy_mant_ne hx_mant_ne h
    have hdom' := hdom
    rw [hxv, hyv] at hdom'
    have hgt' : ya.toNat < xa.toNat := by
      have : (ya.toNat : ℚ) < xa.toNat := by nlinarith
      exact_mod_cast this
    have hg' : xa > ya := BitVec.lt_def.mpr hgt'
    refine ⟨x.negative_, xa - ya, E, g, f, hrep, ?_, ?_, ?_, ?_, hEmax, ?_, hspec _ _ (by rw [ite_eq_left hg'])⟩
    · rw [hsub _ _ hgt'.le]; omega
    · rw [hsub _ _ hgt'.le]; omega
    · intro hxb; have := hbig (hxbit_empty hxb); rw [hsub _ _ hgt'.le]; omega
    · rw [habs, hxv, hyv, hsub _ _ hgt'.le, Nat.cast_sub hgt'.le, abs_of_pos (by nlinarith)]; ring
    · have := diff_sign_sum_sign_of_dominant (Ne.symm h_diff_sign) hdom
      rw [add_comm] at this
      exact this

/-- A successful opposite-sign addition gives `M`, `δ` in `[0, 1)` and a sign `zn` with
`|x + y| = (M + δ)·10^ze'`, and `doNormalize128` on `M` returns `result`. -/
theorem Number.operator_add_algorithmic_facts_diff_sign_represents
    (x y result : Number) (mode : rounding_mode)
    (hx : x.isNormalized) (hy : y.isNormalized)
    (hx_mant_ne : x.mantissa_ ≠ 0) (hy_mant_ne : y.mantissa_ ≠ 0)
    (h_diff_sign : x.negative_ ≠ y.negative_)
    (h_not_zero : ¬ x.operator_eq y.operator_neg)
    (hok : Number.operator_add x y mode = .ok result) :
    ∃ (M : UInt128) (ze' : Int) (δ : ℚ) (zn sticky : Bool),
      (0 ≤ δ) ∧ δ ≤ 1 ∧
      (sticky = false → δ = 0) ∧
      1 ≤ M.toNat ∧ M.toNat < 10 ^ 22 ∧
      (sticky = true → 10 ^ 20 ≤ M.toNat) ∧
      |x.toRat + y.toRat| = ((M.toNat : ℚ) + δ) * 10 ^ ze' ∧
      doNormalize128 zn M ze' largeRange.min largeRange.max mode sticky = .ok result ∧
      ((zn = true → x.toRat + y.toRat ≤ 0) ∧ (zn = false → 0 ≤ x.toRat + y.toRat)) ∧
      δ < 1 ∧
      (sticky = true → 0 < δ) := by
  obtain ⟨zn, zm_pre, E, g_aln, f_aln, hrep, hzm_pos, hzm_lt, hxbit_big, htruth, -, h_sign, hspec⟩ :=
    Number.operator_addSpec_diff_sign_subtract x y mode hx hy hx_mant_ne hy_mant_ne h_diff_sign h_not_zero
  obtain ⟨M, ze', δ, sticky, hδ_low, hδ_le, hsticky_zero, hM_pos, hM_lt, hM_big,
      htruth_out, hok_out, hδ_lt, hsticky_pos⟩ :=
    Number.operator_add_post_subtract zn zm_pre E g_aln f_aln mode hrep hzm_pos hzm_lt hxbit_big
      (x.toRat + y.toRat) htruth result (hspec ▸ Number.operator_add_ok_spec hok)
  exact ⟨M, ze', δ, zn, sticky, hδ_low, hδ_le, hsticky_zero, hM_pos, hM_lt,
    hM_big, htruth_out, hok_out, h_sign, hδ_lt, hsticky_pos⟩

end XRPL.Model.Protocol
