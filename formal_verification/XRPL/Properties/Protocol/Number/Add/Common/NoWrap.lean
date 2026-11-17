import XRPL.Properties.Protocol.Number.Add.Common.RecoverBasic
import XRPL.Properties.Protocol.Number.Common.ToRatLemmas

/-! # `operator_add` never wraps on normalized operands

The `recover` loop multiplies a positive mantissa by ten and subtracts a guard digit below ten, so it stays positive
and below `2^128`. The subtraction gives a positive mantissa: the operand with the larger exponent has 19 digits, the
aligned one at most 18, and equal exponents leave the guard empty. -/

namespace XRPL.Model.Protocol

/-- `recover` never wraps while its mantissa is positive or its guard empty, and the guard holds decimal digits. The
result keeps the first fact. -/
lemma recover_eq_spec_of (u m : UInt128) (e : Int) (g : Guard) (fuel : Nat) (hu : u.toNat * 10 < 2 ^ 128)
    (hm : g.empty = true ∨ 1 ≤ m.toNat) (hg : allNibblesAtMost9 g.digits_) :
    Number.operator_add.recover u m e g fuel = .ok (recoverSpec u m e g fuel) ∧
      ((recoverSpec u m e g fuel).2.2.empty = true ∨ 1 ≤ (recoverSpec u m e g fuel).1.toNat) := by
  induction fuel generalizing m e g with
  | zero =>
    unfold Number.operator_add.recover recoverSpec
    exact ⟨rfl, hm⟩
  | succ n ih =>
    by_cases hc : m < u ∧ ¬ g.empty
    · have hm1 : 1 ≤ m.toNat := by
        rcases hm with h | h
        · exact absurd h hc.2
        · exact h
      have hd := pop_digit_le_9 g hg
      have hle := pop_digit_le_mul_ten_of_pos128 hu hm1 hc.1 hd
      have hmul := mul_ten_no_overflow_of_lt_upperLimit hu hc.1
      have hstep := recover_step_mantissa_nat128 hu hc.1 hle
      have hlt : m.toNat < u.toNat := BitVec.lt_def.mp hc.1
      unfold Number.operator_add.recover
      rw [if_pos hc]
      dsimp only
      rw [BitVec.mulChecked_of_lt (by rw [show (10 : BitVec 128).toNat = 10 from rfl]; omega), ok_bind,
        BitVec.subChecked_of_le (BitVec.le_def.mp hle), ok_bind, recover_step hc.1 hc.2]
      have hpd : g.pop.2.toNat ≤ 9 := hd
      exact ih _ _ _ (Or.inr (by rw [hstep]; omega)) (allNibblesAtMost9_pop g hg)
    · unfold Number.operator_add.recover
      rw [if_neg hc, recover_noop_exit hc]
      exact ⟨rfl, hm⟩

/-- The steps of `operator_add` after the alignment never wrap when the guard holds decimal digits and a subtraction
is either of different mantissas or comes with an empty guard. -/
lemma Number.operator_add_tail_ne_wrap (xn yn : Bool) (xm ym : UInt64) (xe : Int) (g : Guard)
    (mode : rounding_mode) (hg : allNibblesAtMost9 g.digits_) (hpos : xn ≠ yn → g.empty = true ∨ xm ≠ ym) :
    (if xn == yn then do
      let zm128 ← (toUInt128 xm).addChecked (toUInt128 ym)
      checkSumAtTop zm128 xe
      let (zm, xe, g) ←
        (if zm128 > toUInt128 largeRange.max || zm128 > toUInt128 maxRepUp then do
          let (g', zm128', xe') ← g.doDropDigit128 zm128 xe
          let zm ← toUInt64Checked zm128'
          pure (zm, xe', g')
        else do
          let zm ← toUInt64Checked zm128
          pure (zm, xe, g))
      match g.doRoundUp xn zm xe largeRange.min largeRange.max mode .overflow with
      | .error err => .error err
      | .ok res => res.toNumber.normalize largeRange.min largeRange.max mode
    else do
      let (zm128, zn, ze) ←
        (if xm > ym then do
          let zm128 ← (toUInt128 xm).subChecked (toUInt128 ym)
          pure (zm128, xn, xe)
        else do
          let zm128 ← (toUInt128 ym).subChecked (toUInt128 xm)
          pure (zm128, yn, xe))
      let (zm128, ze, g) ← Number.operator_add.recover (toUInt128 largeRange.min * 1000) zm128 ze g 40
      let zm128 ← (if g.empty then pure zm128 else zm128.subChecked 1)
      doNormalize128 zn zm128 ze largeRange.min largeRange.max mode (!g.empty)) ≠ .error .wrap := by
  have hx := xm.toNat_lt
  have hy := ym.toNat_lt
  have hup : maxRepUp.toNat = 2 ^ 63 + 2 := by decide
  split
  · rw [BitVec.addChecked_of_lt (by rw [toNat_toUInt128, toNat_toUInt128]; omega), ok_bind]
    have hs : (toUInt128 xm + toUInt128 ym).toNat = xm.toNat + ym.toNat := by
      rw [BitVec.toNat_add, toNat_toUInt128, toNat_toUInt128, Nat.mod_eq_of_lt (by omega)]
    refine bind_ne_error (by unfold checkSumAtTop; split_ifs <;> exact nofun) fun _ => ?_
    refine bind_ne_error ?_ fun p => ?_
    · split
      · rw [Guard.doDropDigit128_eq_spec, ok_bind]
        dsimp only [Guard.doDropDigit128Spec]
        rw [toUInt64Checked_of_lt (by
          rw [BitVec.toNat_udiv, hs, show (10 : BitVec 128).toNat = 10 from rfl]; omega), ok_bind]
        exact nofun
      · rename_i hc
        have hle : (toUInt128 xm + toUInt128 ym).toNat ≤ maxRepUp.toNat := by
          have : ¬ toUInt128 maxRepUp < toUInt128 xm + toUInt128 ym := by
            intro h'; apply hc; simp [h']
          rw [← toNat_toUInt128 maxRepUp]
          exact BitVec.not_lt.mp this
        rw [toUInt64Checked_of_lt (by omega), ok_bind]
        exact nofun
    · obtain ⟨zm, xe', g'⟩ := p
      dsimp only
      split
      · rename_i err herr
        intro h; cases h
        exact Guard.doRoundUp_ne_wrap _ _ _ _ _ _ largeRange_min_toNat_le (by decide) herr
      · exact doNormalize_ne_wrap _ _ _ _ _ largeRange_min_toNat_le
  · rename_i hxy
    have hne : xn ≠ yn := by simpa using hxy
    have hulim : (toUInt128 largeRange.min * 1000).toNat * 10 < 2 ^ 128 := by decide
    have htail : ∀ (zm128 : UInt128) (zn : Bool), (g.empty = true ∨ 1 ≤ zm128.toNat) →
        (do
          let (zm128, ze, g) ← Number.operator_add.recover (toUInt128 largeRange.min * 1000) zm128 xe g 40
          let zm128 ← (if g.empty then pure zm128 else zm128.subChecked 1)
          doNormalize128 zn zm128 ze largeRange.min largeRange.max mode (!g.empty)) ≠ .error .wrap := by
      intro zm128 zn hm
      obtain ⟨hrec, hpost⟩ := recover_eq_spec_of _ zm128 xe g 40 hulim hm hg
      rw [hrec, ok_bind]
      dsimp only
      refine bind_ne_error ?_ fun _ => doNormalize128_ne_wrap _ _ _ _ _ _ largeRange_min_toNat_le
      split
      · exact nofun
      · rename_i hemp
        have h1 : 1 ≤ (recoverSpec (toUInt128 largeRange.min * 1000) zm128 xe g 40).1.toNat := by
          rcases hpost with h | h
          · exact absurd h hemp
          · exact h
        rw [BitVec.subChecked_of_le (by rw [show (1 : BitVec 128).toNat = 1 from rfl]; exact h1)]
        exact nofun
    split
    · rename_i hgt
      have hlt : ym.toNat < xm.toNat := UInt64.lt_iff_toNat_lt.mp hgt
      rw [BitVec.subChecked_of_le (by rw [toNat_toUInt128, toNat_toUInt128]; omega), ok_bind]
      apply htail
      rcases hpos hne with h | _
      · exact Or.inl h
      · right
        rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, toNat_toUInt128, toNat_toUInt128]; omega),
          toNat_toUInt128, toNat_toUInt128]
        omega
    · rename_i hgt
      have hle : xm.toNat ≤ ym.toNat := by
        have := UInt64.not_lt.mp hgt
        exact UInt64.le_iff_toNat_le.mp this
      rw [BitVec.subChecked_of_le (by rw [toNat_toUInt128, toNat_toUInt128]; omega), ok_bind]
      apply htail
      rcases hpos hne with h | h
      · exact Or.inl h
      · right
        have hne' : xm.toNat ≠ ym.toNat := fun h' => h (UInt64.toNat_inj.mp h')
        rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, toNat_toUInt128, toNat_toUInt128]; omega),
          toNat_toUInt128, toNat_toUInt128]
        omega

/-- A normalized nonzero mantissa has 19 digits. -/
private lemma mantissa_bounds_of_ne_zero {x : Number} (hx : x.isNormalized) (h0 : ¬ x.operator_eq Number.zero = true) :
    10 ^ 18 ≤ x.mantissa_.toNat ∧ x.mantissa_.toNat < 10 ^ 19 := by
  rcases hx with hz | hb
  · exact absurd (by rw [hz]; decide) h0
  · exact mantissaBounds_nat_of ⟨hb.1, hb.2.1⟩

/-- Aligning to a larger exponent leaves at most 18 digits, and a guard of decimal digits. -/
private lemma alignDown_facts (m : UInt64) (e target : Int) (neg : Bool) (hlt : e < target)
    (hm : m.toNat < 10 ^ 19) :
    (Number.operator_add.alignDown m e (if neg then Guard.new.set_negative else Guard.new) target).1.toNat
        < 10 ^ 18 ∧
      allNibblesAtMost9
        (Number.operator_add.alignDown m e (if neg then Guard.new.set_negative else Guard.new) target).2.2.digits_ := by
  refine ⟨?_, ?_⟩
  · rw [alignDown_mantissa_eq, max_eq_right hlt.le]
    have hk : 1 ≤ (target - e).toNat := by omega
    calc m.toNat / 10 ^ (target - e).toNat ≤ m.toNat / 10 ^ 1 :=
          Nat.div_le_div_left (Nat.pow_le_pow_right (by norm_num) hk) (by positivity)
      _ < 10 ^ 18 := by omega
  · obtain ⟨_, _, _, _, _, h⟩ := alignDown_represents m e _ target 0 (g0_represents_zero neg)
    exact h

/-- `operator_add` on normalized operands never wraps. -/
theorem Number.operator_add_ne_wrap (x y : Number) (mode : rounding_mode) (hx : x.isNormalized)
    (hy : y.isNormalized) : x.operator_add y mode ≠ .error .wrap := by
  unfold Number.operator_add
  split
  · exact nofun
  rename_i hy0
  split
  · exact nofun
  rename_i hx0
  split
  · exact nofun
  have hxb := mantissa_bounds_of_ne_zero hx hx0
  have hyb := mantissa_bounds_of_ne_zero hy hy0
  dsimp (config := { iota := false, proj := false, etaStruct := .none }) only
  by_cases h1 : x.exponent_ < y.exponent_
  · rw [if_pos h1]
    obtain ⟨ha, hc⟩ := alignDown_facts x.mantissa_ x.exponent_ y.exponent_ x.negative_ h1 hxb.2
    generalize Number.operator_add.alignDown x.mantissa_ x.exponent_ _ y.exponent_ = A at ha hc
    obtain ⟨a, b, c⟩ := A
    dsimp only at ha hc ⊢
    refine Number.operator_add_tail_ne_wrap _ _ _ _ _ _ _ hc fun _ => Or.inr fun h => ?_
    rw [h] at ha; omega
  by_cases h2 : x.exponent_ > y.exponent_
  · rw [if_neg h1, if_pos h2]
    obtain ⟨ha, hc⟩ := alignDown_facts y.mantissa_ y.exponent_ x.exponent_ y.negative_ h2 hyb.2
    generalize Number.operator_add.alignDown y.mantissa_ y.exponent_ _ x.exponent_ = A at ha hc
    obtain ⟨a, b, c⟩ := A
    dsimp only at ha hc ⊢
    refine Number.operator_add_tail_ne_wrap _ _ _ _ _ _ _ hc fun _ => Or.inr fun h => ?_
    rw [← h] at ha; omega
  · rw [if_neg h1, if_neg h2]
    dsimp only
    refine Number.operator_add_tail_ne_wrap _ _ _ _ _ _ _ ?_ fun _ => Or.inl ?_
    · obtain ⟨_, _, _, _, _, h⟩ := g0_represents_zero x.negative_
      exact h
    · cases x.negative_ <;> decide

/-- On normalized operands `operator_add` gives the result of its raw twin. -/
theorem Number.operator_add_eq_spec {x y : Number} (mode : rounding_mode) (hx : x.isNormalized)
    (hy : y.isNormalized) : x.operator_add y mode = x.operator_addSpec y mode :=
  (Number.operator_add_refines x y mode).eq_of_ne (Number.operator_add_ne_wrap x y mode hx hy)

end XRPL.Model.Protocol
