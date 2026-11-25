import XRPL.Properties.Protocol.Number.Add.Common.RecoverBasic
import XRPL.Properties.Protocol.Number.Common.ToRatLemmas
import XRPL.Properties.Protocol.Number.Add.Common.Align

/-! # `operator_add` never wraps on normalized operands

The alignment multiplies only a mantissa below `10^21` and leaves both mantissas below `10^22`. The `recover` loop
keeps the mantissa positive and below `2^128`. -/

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
      rw [ite_eq_left hc]
      dsimp only
      rw [BitVec.mulChecked_of_lt (by rw [show (10 : BitVec 128).toNat = 10 from rfl]; omega), ok_bind,
        BitVec.subChecked_of_le (BitVec.le_def.mp hle), ok_bind, recover_step hc.1 hc.2]
      have hpd : g.pop.2.toNat ≤ 9 := hd
      exact ih _ _ _ (Or.inr (by rw [hstep]; omega)) (allNibblesAtMost9_pop g hg)
    · unfold Number.operator_add.recover
      rw [ite_eq_right hc, recover_noop_exit hc]
      exact ⟨rfl, hm⟩

/-- A bind whose first step gives `b` is the rest of the block on `b`. -/
private lemma bind_eq_of_ok {ε α β : Type} {A : Except ε α} {b : α} {K : α → Except ε β} {R : Except ε β}
    (hA : A = .ok b) (hK : K b = R) : (A >>= K) = R := by
  rw [hA, ok_bind, hK]

/-- On normalized operands `operator_add` gives the result of its raw twin. -/
theorem Number.operator_add_eq_spec {x y : Number} (mode : rounding_mode) (hx : x.isNormalized)
    (hy : y.isNormalized) : x.operator_add y mode = x.operator_addSpec y mode := by
  have hu : (toUInt128 largeRange.min * 1000).toNat * 10 < 2 ^ 128 := by decide
  unfold Number.operator_add Number.operator_addSpec
  split
  · rfl
  rename_i hy0
  split
  · rfl
  rename_i hx0
  split
  · rfl
  have hxm : x.mantissa_ ≠ 0 := fun h => hx0 (by
    rw [Number.eq_zero_of_mantissa_zero x hx h]; decide)
  have hym : y.mantissa_ ≠ 0 := fun h => hy0 (by
    rw [Number.eq_zero_of_mantissa_zero y hy h]; decide)
  dsimp only
  refine bind_eq_of_ok (b := Number.addAlignSpec x y) ?_ ?_
  · unfold Number.addAlignSpec
    split
    · rw [adjust_eq_spec _ _ _ _ _ _ hu, ok_bind]; rfl
    split
    · rw [adjust_eq_spec _ _ _ _ _ _ hu, ok_bind]; rfl
    · rfl
  generalize ha : Number.addAlignSpec x y = a
  obtain ⟨xa, ya, E, g⟩ := a
  obtain ⟨f, hrep, -, -, hxa, hya, hlt, hgt, heq⟩ :=
    Number.addAlignSpec_facts x y hx hy hxm hym xa ya E g ha
  dsimp only
  have hg : allNibblesAtMost9 g.digits_ := by obtain ⟨_, _, _, _, _, h⟩ := hrep; exact h
  split
  · rw [BitVec.addChecked_of_lt (by omega), ok_bind]
  · -- a guard with digits comes with mantissas at least 10^21 - 10^19 apart
    have hsep : g.empty = false → xa.toNat + 1 ≤ ya.toNat ∨ ya.toNat + 1 ≤ xa.toNat := by
      intro hne
      rcases lt_trichotomy x.exponent_ y.exponent_ with h | h | h
      · have := (hlt h).2.2.2.2 hne; have := (hlt h).2.2.1; omega
      · rw [(heq h).2.1] at hne; exact absurd hne (by decide)
      · have := (hgt h).2.2.2.2 hne; have := (hgt h).2.2.1; omega
    have hulim : (toUInt128 largeRange.min * 1000).toNat * 10 < 2 ^ 128 := hu
    have htail : ∀ (zm128 : UInt128) (zn : Bool), (g.empty = true ∨ 1 ≤ zm128.toNat) →
        (do
          let __discr ← Number.operator_add.recover (toUInt128 largeRange.min * 1000) zm128 E g 40
          match __discr with
          | (zm128, ze, g) => do
            let zm128 ← (if g.empty then pure zm128 else zm128.subChecked 1)
            doNormalize128 zn zm128 ze largeRange.min largeRange.max mode (!g.empty)) =
        (doNormalize128 zn
          (if (recoverSpec (toUInt128 largeRange.min * 1000) zm128 E g 40).2.2.empty then
            (recoverSpec (toUInt128 largeRange.min * 1000) zm128 E g 40).1
          else (recoverSpec (toUInt128 largeRange.min * 1000) zm128 E g 40).1 - 1)
          (recoverSpec (toUInt128 largeRange.min * 1000) zm128 E g 40).2.1 largeRange.min largeRange.max mode
          (!(recoverSpec (toUInt128 largeRange.min * 1000) zm128 E g 40).2.2.empty)) := by
      intro zm128 zn hm
      obtain ⟨hrec, hpost⟩ := recover_eq_spec_of _ zm128 E g 40 hulim hm hg
      rw [hrec, ok_bind]
      generalize recoverSpec (toUInt128 largeRange.min * 1000) zm128 E g 40 = r at hpost
      obtain ⟨r1, r2, r3⟩ := r
      dsimp only at hpost ⊢
      split
      · rename_i hemp
        rw [show (pure r1 : Except Error UInt128) = .ok r1 from rfl, ok_bind]
      · rename_i hemp
        have h1 : 1 ≤ r1.toNat := by
          rcases hpost with h | h
          · exact absurd h hemp
          · exact h
        rw [BitVec.subChecked_of_le (by rw [show (1 : BitVec 128).toNat = 1 from rfl]; exact h1), ok_bind]
    split
    · rename_i hgt'
      have hlt' : ya.toNat < xa.toNat := BitVec.lt_def.mp hgt'
      rw [BitVec.subChecked_of_le (BitVec.le_def.mpr (by omega)), ok_bind]
      dsimp only
      refine htail _ _ ?_
      cases hge : g.empty
      · right
        rw [BitVec.toNat_sub_of_le (BitVec.le_def.mpr (by omega))]
        omega
      · exact Or.inl rfl
    · rename_i hgt'
      have hle : xa.toNat ≤ ya.toNat := by
        have := BitVec.not_lt.mp hgt'
        exact BitVec.le_def.mp this
      rw [BitVec.subChecked_of_le (BitVec.le_def.mpr hle), ok_bind]
      dsimp only
      refine htail _ _ ?_
      cases hge : g.empty
      · right
        rw [BitVec.toNat_sub_of_le (BitVec.le_def.mpr hle)]
        have := hsep hge
        omega
      · exact Or.inl rfl

/-- `operator_add` on normalized operands never wraps: its raw twin errs only where normalizing does. -/
theorem Number.operator_add_ne_wrap (x y : Number) (mode : rounding_mode) (hx : x.isNormalized)
    (hy : y.isNormalized) : x.operator_add y mode ≠ .error .wrap := by
  rw [Number.operator_add_eq_spec mode hx hy]
  unfold Number.operator_addSpec
  split
  · exact nofun
  split
  · exact nofun
  split
  · exact nofun
  dsimp only
  split
  · exact doNormalize128_ne_wrap _ _ _ _ _ _ largeRange_min_toNat_le
  · exact doNormalize128_ne_wrap _ _ _ _ _ _ largeRange_min_toNat_le

end XRPL.Model.Protocol
