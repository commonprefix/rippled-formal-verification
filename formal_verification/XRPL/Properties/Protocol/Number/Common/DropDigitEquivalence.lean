import Mathlib.Tactic

import XRPL.Model.Protocol.Number
import XRPL.Properties.Protocol.Common.FixedWidth

/-! # The digit-dropping loops with and without the early exit

C++ `doDropDigitWithTarget` (Number.cpp:428) jumps to the target once the mantissa and the guard digits are zero.
The loops without that exit, `alignDownSpec` and `shiftSpec`, return the same result on every input. -/

namespace XRPL.Model.Protocol

/-- The alignment loop written without the early exit: one digit dropped per step. -/
def alignDownSpec (m : UInt64) (e : Int) (g : Guard) (target : Int) : UInt64 × Int × Guard :=
  if e < target then alignDownSpec (m / 10) (e + 1) (g.push (m % 10)) target
  else (m, e, g)
termination_by (target - e).toNat

lemma push_zero_fixed (g : Guard) (h : g.digits_ = 0) : g.push 0 = g := by
  obtain ⟨d, x, s⟩ := g
  subst h
  simp only [Guard.push]
  rw [Guard.mk.injEq]
  refine ⟨by decide, ?_, rfl⟩
  rw [show ((0 : UInt64) &&& 0xF) = 0 from by decide]
  simp

private lemma alignDownSpec_fixed_aux : ∀ (n : Nat) (e : Int) (g : Guard) (target : Int),
    g.digits_ = 0 → (target - e).toNat = n →
    alignDownSpec 0 e g target = (0, (if e < target then target else e), g) := by
  intro n
  induction n with
  | zero =>
    intro e g target _ hn
    have hge : ¬ e < target := by omega
    rw [alignDownSpec, ite_eq_right hge, ite_eq_right hge]
  | succ k ih =>
    intro e g target h hn
    rw [alignDownSpec]
    by_cases hlt : e < target
    · rw [ite_eq_left hlt, show (0 : UInt64) % 10 = 0 from by decide, show (0 : UInt64) / 10 = 0 from by decide,
        push_zero_fixed g h, ih (e + 1) g target h (by omega)]
      rw [ite_eq_left hlt]
      by_cases h2 : e + 1 < target
      · rw [ite_eq_left h2]
      · have heq : e + 1 = target := by omega
        rw [ite_eq_right h2, heq]
    · rw [ite_eq_right hlt, ite_eq_right hlt]

lemma alignDownSpec_fixed (e : Int) (g : Guard) (target : Int) (h : g.digits_ = 0) :
    alignDownSpec 0 e g target = (0, (if e < target then target else e), g) :=
  alignDownSpec_fixed_aux (target - e).toNat e g target h rfl

/-- `doDropDigitWithTargetU64` returns the same result as `alignDownSpec`. When it exits early, the steps it skips
would leave the mantissa and guard unchanged. -/
private lemma doDropDigitWithTargetU64_eq_spec_aux :
    ∀ (n : Nat) (g : Guard) (m : UInt64) (e target : Int),
    (target - e).toNat = n →
    g.doDropDigitWithTargetU64 m e target = alignDownSpec m e g target := by
  intro n
  induction n with
  | zero =>
    intro g m e target hn
    have hge : ¬ e < target := by omega
    rw [Guard.doDropDigitWithTargetU64, alignDownSpec, ite_eq_right hge, ite_eq_right hge]
  | succ k ih =>
    intro g m e target hn
    by_cases hlt : e < target
    · by_cases hsc : (m == 0 && g.unrecoverable) = true
      · rw [Guard.doDropDigitWithTargetU64, ite_eq_left hlt, ite_eq_left hsc]
        have hm : m = 0 := by
          simp only [Bool.and_eq_true, beq_iff_eq] at hsc; exact hsc.1
        have hd : g.digits_ = 0 := by
          simp only [Bool.and_eq_true, beq_iff_eq, Guard.unrecoverable] at hsc
          exact hsc.2
        subst hm
        rw [alignDownSpec_fixed e g target hd, ite_eq_left hlt]
      · rw [Guard.doDropDigitWithTargetU64, alignDownSpec, ite_eq_left hlt, ite_eq_left hlt, ite_eq_right hsc]
        exact ih (g.push (m % 10)) (m / 10) (e + 1) target (by omega)
    · rw [Guard.doDropDigitWithTargetU64, alignDownSpec, ite_eq_right hlt, ite_eq_right hlt]

theorem doDropDigitWithTargetU64_eq_spec (g : Guard) (m : UInt64) (e target : Int) :
    g.doDropDigitWithTargetU64 m e target = alignDownSpec m e g target :=
  doDropDigitWithTargetU64_eq_spec_aux (target - e).toNat g m e target rfl

/-- The `shift` loop written without the early exit: one digit dropped per step. -/
def shiftSpec (drops : rep) (offset : Int) (g : Guard) : rep × Guard :=
  if offset < 0 then shiftSpec (drops / 10) (offset + 1) (g.push (drops % 10).toUInt64)
  else (drops, g)
termination_by (-offset).toNat
decreasing_by omega

/-- With value `0` and an unrecoverable guard, each further step pushes a `0` digit and
leaves both the value and the guard unchanged. -/
private lemma shiftSpec_fixed_aux : ∀ (n : Nat) (offset : Int) (g : Guard),
    g.digits_ = 0 → (-offset).toNat = n → shiftSpec 0 offset g = (0, g) := by
  intro n
  induction n with
  | zero =>
    intro offset g _ hn
    have hge : ¬ offset < 0 := by omega
    rw [shiftSpec, ite_eq_right hge]
  | succ k ih =>
    intro offset g h hn
    rw [shiftSpec]
    by_cases hlt : offset < 0
    · rw [ite_eq_left hlt]
      have hpush : g.push ((0 : rep) % 10).toUInt64 = g := by
        rw [show ((0 : rep) % 10).toUInt64 = 0 from by decide]
        exact push_zero_fixed g h
      rw [show (0 : rep) / 10 = 0 from by decide, hpush]
      exact ih (offset + 1) g h (by omega)
    · rw [ite_eq_right hlt]

lemma shiftSpec_fixed (offset : Int) (g : Guard) (h : g.digits_ = 0) :
    shiftSpec 0 offset g = (0, g) :=
  shiftSpec_fixed_aux (-offset).toNat offset g h rfl

/-- The digit and the quotient of a non-negative `Int64` divided by `10` are non-negative. -/
private lemma mod_div_ten_nonneg {drops : rep} (h0 : 0 ≤ drops.toInt) :
    0 ≤ drops % 10 ∧ 0 ≤ (drops / 10).toInt := by
  have ha2 := Int64.toInt_lt drops
  have hten : (10 : Int64).toInt = 10 := by decide
  refine ⟨?_, ?_⟩
  · rw [Int64.le_iff_toInt_le, Int64.toInt_mod, hten, Int.tmod_eq_emod_of_nonneg h0]
    exact Int.emod_nonneg _ (by norm_num)
  · have hdiv_nonneg : 0 ≤ drops.toInt / 10 := Int.ediv_nonneg h0 (by norm_num)
    have hdiv_le : drops.toInt / 10 ≤ drops.toInt := Int.ediv_le_self _ h0
    have heq : (drops / 10).toInt = drops.toInt / 10 := by
      rw [Int64.toInt_div, hten, Int.bmod_eq_iff (by norm_num), Int.tdiv_eq_ediv_of_nonneg h0]
      omega
    omega

private lemma doDropDigitWithTargetI64_eq_shiftSpec_aux :
    ∀ (n : Nat) (g : Guard) (drops : rep) (offset : Int),
    (-offset).toNat = n → 0 ≤ drops.toInt →
    g.doDropDigitWithTargetI64 drops offset 0 = .ok (shiftSpec drops offset g) := by
  intro n
  induction n with
  | zero =>
    intro g drops offset hn _
    have hge : ¬ offset < 0 := by omega
    rw [Guard.doDropDigitWithTargetI64, shiftSpec, ite_eq_right hge, ite_eq_right hge]
  | succ k ih =>
    intro g drops offset hn h0
    by_cases hlt : offset < 0
    · by_cases hsc : (drops == 0 && g.unrecoverable) = true
      · rw [Guard.doDropDigitWithTargetI64, ite_eq_left hlt, ite_eq_left hsc]
        have hm : drops = 0 := by simp only [Bool.and_eq_true, beq_iff_eq] at hsc; exact hsc.1
        have hd : g.digits_ = 0 := by
          simp only [Bool.and_eq_true, beq_iff_eq, Guard.unrecoverable] at hsc; exact hsc.2
        subst hm
        rw [shiftSpec_fixed offset g hd]
      · obtain ⟨hmod, hdiv⟩ := mod_div_ten_nonneg h0
        rw [Guard.doDropDigitWithTargetI64, shiftSpec, ite_eq_left hlt, ite_eq_left hlt, ite_eq_right hsc,
          Int64.toUInt64Checked_of_nonneg hmod]
        exact ih (g.push (drops % 10).toUInt64) (drops / 10) (offset + 1) (by omega) hdiv
    · rw [Guard.doDropDigitWithTargetI64, shiftSpec, ite_eq_right hlt, ite_eq_right hlt]

/-- On a non-negative value the digit-dropping loop never wraps, and it equals `shiftSpec`. -/
lemma doDropDigitWithTargetI64_eq_shiftSpec (g : Guard) (drops : rep) (offset : Int) (h0 : 0 ≤ drops.toInt) :
    g.doDropDigitWithTargetI64 drops offset 0 = .ok (shiftSpec drops offset g) :=
  doDropDigitWithTargetI64_eq_shiftSpec_aux (-offset).toNat g drops offset rfl h0

/-- `Number.to_rep.shift` calls `doDropDigitWithTargetI64`, so it equals `shiftSpec`. -/
lemma shift_eq_spec (drops : rep) (offset : Int) (g : Guard) (h0 : 0 ≤ drops.toInt) :
    Number.to_rep.shift drops offset g = .ok (shiftSpec drops offset g) := by
  rw [Number.to_rep.shift.eq_def]
  exact doDropDigitWithTargetI64_eq_shiftSpec g drops offset h0

end XRPL.Model.Protocol
