import XRPL.Properties.Protocol.Number.Common.Rounding.SuccessCondition
import XRPL.Properties.Protocol.Number.Add.Common.NoWrap
import XRPL.Properties.Protocol.Number.Add.Common.Rounded
import XRPL.Properties.Protocol.Number.Add.Common.SameSignHelpers

/-! # Exact success condition for `operator_add`

`x + y` succeeds exactly when the exact sum is below `(maxRepUp + 1) * 10^maxExponent` in size. A same-sign sum can
fail only at the top-exponent check, and an opposite-sign sum only inside `doNormalize128`. -/

namespace XRPL.Model.Protocol

/-- The same-sign top-exponent check passes exactly when the mantissa sum is below
`(maxRepUp + 1) * 10^(maxExponent - e)`. -/
lemma checkSumAtTop_ok_iff (z : UInt128) (e : Int) (he : e ≤ maxExponent) (hz : z.toNat < 2 * 10 ^ 19) :
    checkSumAtTop z e = .ok () ↔ z.toNat < 9223372036854775811 * 10 ^ (maxExponent - e).toNat := by
  have hmru : (toUInt128 maxRepUp).toNat = 9223372036854775810 := by rw [toNat_toUInt128]; rfl
  have hlrm : (toUInt128 largeRange.max).toNat = 9999999999999999999 := by
    rw [toNat_toUInt128]; exact largeRange_max_val
  unfold checkSumAtTop
  by_cases hlt : e < maxExponent
  · rw [if_pos hlt]
    refine iff_of_true rfl ?_
    have hP : 10 ^ 1 ≤ 10 ^ (maxExponent - e).toNat := Nat.pow_le_pow_right (by norm_num) (by omega)
    set P := 10 ^ (maxExponent - e).toNat
    omega
  · rw [if_neg hlt]
    have hd : (maxExponent - e).toNat = 0 := by omega
    rw [hd, pow_zero]
    by_cases h1 : z > toUInt128 largeRange.max
    · rw [if_pos h1]
      have := BitVec.lt_def.mp h1
      exact iff_of_false (by simp) (by omega)
    · rw [if_neg h1]
      by_cases h2 : z > toUInt128 maxRepUp
      · rw [if_pos h2]
        have := BitVec.lt_def.mp h2
        exact iff_of_false (by simp) (by omega)
      · rw [if_neg h2]
        have : ¬ (toUInt128 maxRepUp).toNat < z.toNat := fun h => h2 (BitVec.lt_def.mpr h)
        exact iff_of_true rfl (by omega)

/-- Two aligned mantissas at a common exponent `e` add and round without error exactly when their sum is below
`(maxRepUp + 1) * 10^(maxExponent - e)`. -/
lemma Number.sameSign_add_tail_ok_iff (xn : Bool) (xm_a ym_a : UInt64) (e : Int) (g : Guard)
    (mode : rounding_mode) (hxm : xm_a.toNat < 10 ^ 19) (hym : ym_a.toNat < 10 ^ 19) (he : e ≤ maxExponent) :
    (∃ result, (do
      checkSumAtTop (toUInt128 xm_a + toUInt128 ym_a) e
      let zm128 : UInt128 := toUInt128 xm_a + toUInt128 ym_a
      let p : UInt64 × Int × Guard :=
        if zm128 > toUInt128 largeRange.max || zm128 > toUInt128 maxRepUp then
          (toUInt64 (g.doDropDigit128Spec zm128 e).2.1, (g.doDropDigit128Spec zm128 e).2.2,
           (g.doDropDigit128Spec zm128 e).1)
        else (toUInt64 zm128, e, g)
      match p.2.2.doRoundUp xn p.1 p.2.1 largeRange.min largeRange.max mode .overflow with
      | .error err => Except.error err
      | .ok res => .ok res.toNumber) = .ok result) ↔
      xm_a.toNat + ym_a.toNat < 9223372036854775811 * 10 ^ (maxExponent - e).toNat := by
  have hxm_tu : (toUInt128 xm_a).toNat = xm_a.toNat := toNat_toUInt128 xm_a
  have hym_tu : (toUInt128 ym_a).toNat = ym_a.toNat := toNat_toUInt128 ym_a
  set zm128 : UInt128 := toUInt128 xm_a + toUInt128 ym_a with hzm128_def
  have hzm128 : zm128.toNat = xm_a.toNat + ym_a.toNat := by
    rw [hzm128_def, BitVec.toNat_add, hxm_tu, hym_tu]
    apply Nat.mod_eq_of_lt
    have : 2 * 10 ^ 19 < 2 ^ 128 := by norm_num
    omega
  have hcheck := checkSumAtTop_ok_iff zm128 e he (by omega)
  rw [← hzm128, ← hcheck]
  constructor
  · rintro ⟨r, hr⟩
    cases hcs : checkSumAtTop zm128 e with
    | error err => rw [hcs, err_bind] at hr; cases hr
    | ok u => rfl
  · intro hcs
    -- the check passed, so a sum above `maxRepUp` sits below the top exponent
    have htop : e < maxExponent ∨ zm128.toNat ≤ 9223372036854775810 := by
      by_cases hlt : e < maxExponent
      · exact Or.inl hlt
      · right
        have h := hcheck.mp hcs
        have hd : (maxExponent - e).toNat = 0 := by omega
        rw [hd, pow_zero] at h
        omega
    have hmru : (toUInt128 maxRepUp).toNat = 9223372036854775810 := by
      rw [toNat_toUInt128]; rfl
    have hlrm : (toUInt128 largeRange.max).toNat = 9999999999999999999 := by
      rw [toNat_toUInt128]; exact largeRange_max_val
    have hmru' : maxRepUp.toNat = 9223372036854775810 := rfl
    rw [hcs, ok_bind]
    set p : UInt64 × Int × Guard :=
      if zm128 > toUInt128 largeRange.max || zm128 > toUInt128 maxRepUp then
        (toUInt64 (g.doDropDigit128Spec zm128 e).2.1, (g.doDropDigit128Spec zm128 e).2.2,
         (g.doDropDigit128Spec zm128 e).1)
      else (toUInt64 zm128, e, g) with hp_def
    -- the rounding input: mantissa at most `maxRepUp`, exponent at most `maxExponent`
    have hp : p.1 ≤ maxRepUp ∧ p.2.1 ≤ maxExponent := by
      by_cases hc : (zm128 > toUInt128 largeRange.max || zm128 > toUInt128 maxRepUp) = true
      · rw [hp_def, if_pos hc]
        have hgt : 9223372036854775810 < zm128.toNat := by
          rw [Bool.or_eq_true, decide_eq_true_eq, decide_eq_true_eq] at hc
          rcases hc with h | h
          · have := BitVec.lt_def.mp h; rw [hlrm] at this; omega
          · have := BitVec.lt_def.mp h; rw [hmru] at this; omega
        have h10 : (10 : UInt128).toNat = 10 := by decide
        have hdiv : (zm128 / 10).toNat = zm128.toNat / 10 := by rw [BitVec.toNat_udiv, h10]
        have hfit : (zm128 / 10).toNat < 2 ^ 64 := by
          rw [hdiv, hzm128]
          have : 2 * 10 ^ 18 < 2 ^ 64 := by norm_num
          omega
        simp only [Guard.doDropDigit128Spec]
        refine ⟨?_, by omega⟩
        rw [UInt64.le_iff_toNat_le, toNat_toUInt64 hfit, hdiv, hmru']
        omega
      · rw [hp_def, if_neg hc]
        rw [Bool.or_eq_true, decide_eq_true_eq, decide_eq_true_eq, not_or] at hc
        have hle : zm128.toNat ≤ 9223372036854775810 := by
          have h' : ¬ (toUInt128 maxRepUp).toNat < zm128.toNat := fun h => hc.2 (BitVec.lt_def.mpr h)
          rw [hmru] at h'
          omega
        have hfit : zm128.toNat < 2 ^ 64 := by omega
        simp only []
        refine ⟨?_, he⟩
        rw [UInt64.le_iff_toNat_le, toNat_toUInt64 hfit, hmru']
        exact hle
    obtain ⟨res, hres, -⟩ := Guard.doRoundUp_ok_of_le_maxRepUp p.2.2 xn p.1 p.2.1 mode .overflow hp.1 hp.2
    show ∃ result, (match p.2.2.doRoundUp xn p.1 p.2.1 largeRange.min largeRange.max mode
        .overflow with
      | .error err => Except.error err
      | .ok res => .ok res.toNumber) = .ok result
    rw [hres]
    exact ⟨res.toNumber, rfl⟩

/-- An operand aligned up to `target` keeps its size: the aligned mantissa plus a dropped fraction in `[0, 1)`,
at exponent `target`. -/
lemma alignDown_abs_value_frac (n : Number) (g₀ : Guard) (target : Int) (h_le : n.exponent_ ≤ target) :
    ∃ f : ℚ, 0 ≤ f ∧ f < 1 ∧ |n.toRat| =
      (((Number.operator_add.alignDown n.mantissa_ n.exponent_ g₀ target).1.toNat : ℚ) + f) * 10 ^ target := by
  have h := alignDown_abs_value n g₀ target h_le 0
  simp only [zero_mul, add_zero, zero_add] at h
  refine ⟨_, ?_, ?_, h⟩
  · positivity
  · rw [div_lt_one (by positivity)]
    exact_mod_cast Nat.mod_lt _ (by positivity)

/-- The exponent of a nonzero normalized `Number` is at most `maxExponent`. -/
lemma Number.exponent_le_max (n : Number) (hn : n.isNormalized) (hn0 : n.mantissa_ ≠ 0) :
    n.exponent_ ≤ maxExponent := by
  rcases hn with hz | ⟨_, _, _, _, hemax⟩
  · exfalso; apply hn0; rw [hz]; rfl
  · exact hemax

/-- A same-sign addition succeeds exactly when the exact sum is below `(maxRepUp + 1) * 10^maxExponent` in size. -/
lemma Number.operator_addSpec_sameSign_ok_iff (x y : Number) (mode : rounding_mode)
    (hx : x.isNormalized) (hy : y.isNormalized)
    (hx0 : x.mantissa_ ≠ 0) (hy0 : y.mantissa_ ≠ 0)
    (hsign : x.negative_ = y.negative_) (hc : ¬ x.operator_eq y.operator_neg = true) :
    (∃ result, x.operator_addSpec y mode = .ok result) ↔
      |x.toRat + y.toRat| < 9223372036854775811 * (10 : ℚ) ^ (maxExponent : ℤ) := by
  have hx_b := mantissaBounds_nat_of (hx.mantissaBounds hx0)
  have hy_b := mantissaBounds_nat_of (hy.mantissaBounds hy0)
  have hxe_max := Number.exponent_le_max x hx hx0
  have hye_max := Number.exponent_le_max y hy hy0
  have hx_ne_zero : ¬ x.operator_eq Number.zero = true := fun h =>
    hx0 (Number.mantissa_eq_zero_of_operator_eq_zero h)
  have hy_ne_zero : ¬ y.operator_eq Number.zero = true := fun h =>
    hy0 (Number.mantissa_eq_zero_of_operator_eq_zero h)
  have hsn : (x.negative_ == y.negative_) = true := by rw [beq_iff_eq]; exact hsign
  rw [abs_add_eq_of_same_sign hsign, abs_toRat_eq x, abs_toRat_eq y]
  unfold Number.operator_addSpec
  simp only [hy_ne_zero, hx_ne_zero, hc, Bool.false_eq_true, if_false]
  by_cases hlt : x.exponent_ < y.exponent_
  · rw [if_pos hlt]
    set g₀ : Guard := if x.negative_ then Guard.new.set_negative else Guard.new
    set aln := Number.operator_add.alignDown x.mantissa_ x.exponent_ g₀ y.exponent_ with haln
    obtain ⟨f, hf0, hf1, hxval⟩ := alignDown_abs_value_frac x g₀ y.exponent_ (le_of_lt hlt)
    have he : aln.2.1 = y.exponent_ := by
      rw [haln, alignDown_e_eq]; exact max_eq_right (le_of_lt hlt)
    have hm : aln.1.toNat ≤ x.mantissa_.toNat := alignDown_mantissa_le _ _ _ _
    have hE : aln.2.1 ≤ maxExponent := by rw [he]; exact hye_max
    have hval : (x.mantissa_.toNat : ℚ) * 10 ^ x.exponent_ + (y.mantissa_.toNat : ℚ) * 10 ^ y.exponent_
        = (((aln.1.toNat + y.mantissa_.toNat : ℕ) : ℚ) + f) * 10 ^ aln.2.1 := by
      rw [he, ← abs_toRat_eq x, hxval]; push_cast; ring
    rw [hval, scaled_lt_top_iff _ f _ hf0 hf1 hE]
    simpa only [hsn, if_true] using
      Number.sameSign_add_tail_ok_iff x.negative_ aln.1 y.mantissa_ aln.2.1 aln.2.2 mode (by omega) hy_b.2 hE
  by_cases hgt : x.exponent_ > y.exponent_
  · rw [if_neg hlt, if_pos hgt]
    set g₀ : Guard := if y.negative_ then Guard.new.set_negative else Guard.new
    set aln := Number.operator_add.alignDown y.mantissa_ y.exponent_ g₀ x.exponent_ with haln
    obtain ⟨f, hf0, hf1, hyval⟩ := alignDown_abs_value_frac y g₀ x.exponent_ (le_of_lt hgt)
    have hm : aln.1.toNat ≤ y.mantissa_.toNat := alignDown_mantissa_le _ _ _ _
    have hval : (x.mantissa_.toNat : ℚ) * 10 ^ x.exponent_ + (y.mantissa_.toNat : ℚ) * 10 ^ y.exponent_
        = (((x.mantissa_.toNat + aln.1.toNat : ℕ) : ℚ) + f) * 10 ^ x.exponent_ := by
      rw [← abs_toRat_eq y, hyval]; push_cast; ring
    rw [hval, scaled_lt_top_iff _ f _ hf0 hf1 hxe_max]
    simpa only [hsn, if_true] using
      Number.sameSign_add_tail_ok_iff x.negative_ x.mantissa_ aln.1 x.exponent_ aln.2.2 mode hx_b.2 (by omega)
        hxe_max
  · rw [if_neg hlt, if_neg hgt]
    have hval : (x.mantissa_.toNat : ℚ) * 10 ^ x.exponent_ + (y.mantissa_.toNat : ℚ) * 10 ^ y.exponent_
        = (((x.mantissa_.toNat + y.mantissa_.toNat : ℕ) : ℚ) + 0) * 10 ^ x.exponent_ := by
      rw [show y.exponent_ = x.exponent_ from by omega]; push_cast; ring
    rw [hval, scaled_lt_top_iff _ 0 _ (le_refl _) (by norm_num) hxe_max]
    simpa only [hsn, if_true] using
      Number.sameSign_add_tail_ok_iff x.negative_ x.mantissa_ y.mantissa_ x.exponent_
        (if x.negative_ then Guard.new.set_negative else Guard.new) mode hx_b.2 hy_b.2 hxe_max

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
    rw [if_neg hy_ne_zero, if_neg hx_ne_zero, if_pos hc]
    rfl
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
  dsimp (config := { iota := false, proj := false, etaStruct := .none }) only at h
  generalize (if x.exponent_ < y.exponent_ then _ else _ : UInt64 × Int × UInt64 × Int × Guard) = t at h
  obtain ⟨xm, xe, ym, ye, g⟩ := t
  dsimp only at h
  split at h
  · cases hcs : checkSumAtTop (toUInt128 xm + toUInt128 ym) xe with
    | error e =>
      rw [hcs, err_bind] at h
      cases h
      unfold checkSumAtTop at hcs
      split_ifs at hcs <;> cases hcs <;> rfl
    | ok u =>
      rw [hcs, ok_bind] at h
      split at h
      · rename_i err' herr
        cases h
        exact Guard.doRoundUp_error_isOverflow largeRange_min_toNat_le rfl herr
      · cases h
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
