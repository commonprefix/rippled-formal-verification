import XRPL.Properties.Protocol.Number.Common.Notation
import Mathlib.Tactic

import XRPL.Model.Protocol.Number
import XRPL.Properties.Protocol.Number.Add.Common.AlignDown
import XRPL.Properties.Protocol.Number.Common.Rounding.Guard
import XRPL.Properties.Protocol.Number.Common.Rounding.ScaleDown


namespace XRPL.Model.Protocol

/-- No-op case: `recover` with no fuel returns its inputs. -/
lemma recover_noop_zero (upperLimit m : UInt128) (e : Int) (g : Guard) :
    recoverSpec upperLimit m e g 0 = (m, e, g) := by
  rw [recoverSpec.eq_def]

/-- No-op case: when the exit condition holds, `recover` returns its inputs
regardless of remaining fuel. -/
lemma recover_noop_exit {upperLimit m : UInt128} {e : Int} {g : Guard} {fuel : ℕ}
    (h : ¬ (m < upperLimit ∧ ¬ g.empty)) :
    recoverSpec upperLimit m e g (fuel + 1) = (m, e, g) := by
  rw [recoverSpec.eq_def]
  simp only [ite_eq_right h]

/-- Step case: when fuel > 0 and the loop condition holds, `recover` unrolls
one `Guard.pop` step. -/
lemma recover_step {upperLimit m : UInt128} {e : Int} {g : Guard} {fuel : ℕ}
    (h1 : m < upperLimit) (h2 : ¬ g.empty) :
    recoverSpec upperLimit m e g (fuel + 1)
      = recoverSpec upperLimit (m * 10 - toUInt128 g.pop.2) (e - 1) g.pop.1 fuel := by
  rw [recoverSpec.eq_def]
  simp only [ite_eq_left (And.intro h1 h2)]

/-- `recover` keeps the guard's sticky bit `xbit_`, since `Guard.pop` does not change it. -/
theorem recover_xbit (upperLimit m : UInt128) (e : Int) (g : Guard) (fuel : ℕ) :
    (recoverSpec upperLimit m e g fuel).2.2.xbit_ = g.xbit_ := by
  induction m, e, g, fuel using recoverSpec.induct (upperLimit := upperLimit) with
  | case1 m e g => rw [recover_noop_zero]
  | case2 m e g fuel hcond g' d hpop IH =>
    obtain ⟨h1, h2⟩ := hcond
    rw [recover_step h1 h2]
    have hpop1 : g.pop.1 = g' := by rw [hpop]
    have hpop2 : g.pop.2 = d := by rw [hpop]
    rw [hpop1, hpop2, IH, ← hpop1]
    rfl
  | case3 m e g fuel hcond =>
    rw [recover_noop_exit hcond]

/-- If all nibbles of `g.digits_` are valid decimal digits (≤ 9), then
the popped digit is at most 9. -/
lemma pop_digit_le_9 (g : Guard) (hall : allNibblesAtMost9 g.digits_) :
    g.pop.2.toNat ≤ 9 := by
  rw [pop_digit_eq_nibble_15]
  exact hall ⟨15, by omega⟩

/-- `largeRange.min` in `ℕ` is `10^18`. -/
lemma largeRange_min_toNat : largeRange.min.toNat = 10 ^ 18 := by decide

/-- When `m < upperLimit` and `upperLimit.toNat * 10 < 2^128`, the product
`m * 10` does not overflow `UInt128`. -/
lemma mul_ten_no_overflow_of_lt_upperLimit {upperLimit m : UInt128}
    (hUL : upperLimit.toNat * 10 < 2 ^ 128) (h : m < upperLimit) :
    (m * 10 : UInt128).toNat = m.toNat * 10 := by
  have hlt : m.toNat < upperLimit.toNat := BitVec.lt_def.mp h
  have h10 : ((10 : UInt128)).toNat = 10 := by decide
  rw [BitVec.toNat_mul, h10]
  apply Nat.mod_eq_of_lt
  omega

/-- No-underflow: the popped digit (≤ 9) is at most `m * 10` when `1 ≤ m.toNat`. -/
lemma pop_digit_le_mul_ten_of_pos128 {upperLimit m : UInt128} {d : UInt64}
    (hUL : upperLimit.toNat * 10 < 2 ^ 128)
    (hm_pos : 1 ≤ m.toNat) (hm_lt : m < upperLimit) (hd : d.toNat ≤ 9) :
    toUInt128 d ≤ m * 10 := by
  rw [BitVec.le_def, toNat_toUInt128, mul_ten_no_overflow_of_lt_upperLimit hUL hm_lt]
  omega

/-- Nat-level identity for the `UInt128` loop body's mantissa update:
`(m * 10 - toUInt128 d).toNat = m.toNat * 10 - d.toNat` when nothing overflows or underflows. -/
lemma recover_step_mantissa_nat128 {upperLimit m : UInt128} {d : UInt64}
    (hUL : upperLimit.toNat * 10 < 2 ^ 128)
    (hm : m < upperLimit) (hd : toUInt128 d ≤ m * 10) :
    (m * 10 - toUInt128 d).toNat = m.toNat * 10 - d.toNat := by
  rw [BitVec.toNat_sub_of_le hd, mul_ten_no_overflow_of_lt_upperLimit hUL hm,
      toNat_toUInt128]

/-- Output exponent is at most the input exponent: each step decrements `e`. -/
theorem recover_exponent_le (upperLimit m : UInt128) (e : Int) (g : Guard) (fuel : ℕ) :
    (recoverSpec upperLimit m e g fuel).2.1 ≤ e := by
  induction m, e, g, fuel using recoverSpec.induct (upperLimit := upperLimit) with
  | case1 m e g => rw [recover_noop_zero]
  | case2 m e g fuel hcond g' d hpop IH =>
    obtain ⟨h1, h2⟩ := hcond
    rw [recover_step h1 h2, show g.pop = (g', d) from hpop]
    linarith [IH]
  | case3 m e g fuel hcond =>
    rw [recover_noop_exit hcond]

/-- Either the `recover` output meets the loop-exit condition, or the fuel ran out and the exponent dropped by
exactly `fuel`. -/
theorem recover_output_exits_or_fuel_exhausted
    (upperLimit m : UInt128) (e : Int) (g : Guard) (fuel : ℕ) :
    let r := recoverSpec upperLimit m e g fuel
    (¬ (r.1 < upperLimit ∧ ¬ r.2.2.empty))
    ∨ r.2.1 = e - fuel := by
  induction m, e, g, fuel using recoverSpec.induct (upperLimit := upperLimit) with
  | case1 m e g => rw [recover_noop_zero]; right; simp
  | case2 m e g fuel hcond g' d hpop IH =>
    obtain ⟨h1, h2⟩ := hcond
    rw [recover_step h1 h2, show g.pop = (g', d) from hpop]
    rcases IH with hexit | heq
    · left; exact hexit
    · right; rw [heq]; push_cast; ring
  | case3 m e g fuel hcond =>
    rw [recover_noop_exit hcond]
    left; exact hcond

end XRPL.Model.Protocol
