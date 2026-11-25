import Mathlib.Tactic

import XRPL.Model.Protocol.Number
import XRPL.Properties.Protocol.Number.Common.Constants
import XRPL.Properties.Protocol.Number.Common.Rounding.Guard
import XRPL.Properties.Protocol.Number.Common.Rounding.ScaleDown
import XRPL.Properties.Protocol.Number.Common.DropDigitEquivalence


namespace XRPL.Model.Protocol


/-- No-op case: when `e ≥ target`, `alignDown` returns its inputs. -/
lemma alignDownSpec_noop {m : UInt64} {e : Int} {g : Guard} {target : Int}
    (h : ¬ e < target) :
    alignDownSpec m e g target = (m, e, g) := by
  rw [alignDownSpec.eq_def]
  rw [ite_eq_right h]

/-- When `e < target`, `alignDown` drops one digit. -/
lemma alignDownSpec_step {m : UInt64} {e : Int} {g : Guard} {target : Int}
    (h : e < target) :
    alignDownSpec m e g target =
      alignDownSpec (m / 10) (e + 1) (g.push (m % 10)) target := by
  rw [alignDownSpec.eq_def]
  rw [ite_eq_left h]

/-- The output mantissa of `alignDown` is at most the input mantissa.
Each step divides by 10, so the value can only shrink. -/
theorem alignDownSpec_mantissa_le (m : UInt64) (e : Int) (g : Guard) (target : Int) :
    (alignDownSpec m e g target).1.toNat ≤ m.toNat := by
  induction m, e, g using alignDownSpec.induct target with
  | case1 m e g hlt IH =>
    rw [alignDownSpec_step hlt]
    have hstep : (m / 10).toNat ≤ m.toNat := by
      rw [UInt64.toNat_div]
      exact Nat.div_le_self _ _
    exact le_trans IH hstep
  | case2 m e g hnlt =>
    rw [alignDownSpec_noop hnlt]

/-- Output mantissa is `m / 10 ^ k` for `k = (max e target - e).toNat`. -/
theorem alignDownSpec_mantissa_eq (m : UInt64) (e : Int) (g : Guard) (target : Int) :
    (alignDownSpec m e g target).1.toNat
      = m.toNat / 10 ^ (Max.max e target - e).toNat := by
  induction m, e, g using alignDownSpec.induct target with
  | case1 m e g hlt IH =>
    rw [alignDownSpec_step hlt]
    rw [IH]
    have hm10 : ((m / 10 : UInt64)).toNat = m.toNat / 10 := by
      rw [UInt64.toNat_div]; rfl
    rw [hm10]
    -- max (e+1) target - (e+1) = max e target - e - 1 when e < target.
    have hmax_le : e ≤ Max.max e target := le_max_left _ _
    have htarget_le_max : target ≤ Max.max e target := le_max_right _ _
    have hmax_e1 : Max.max (e + 1) target = Max.max e target := by
      have hmax_r : Max.max e target = target := max_eq_right (le_of_lt hlt)
      rw [hmax_r]
      by_cases h2 : e + 1 ≤ target
      · exact max_eq_right h2
      · push Not at h2
        rw [max_eq_left (le_of_lt h2)]; omega
    rw [hmax_e1]
    have hpos : 0 < (Max.max e target - e).toNat := by
      have : 0 < Max.max e target - e := by
        have : e < Max.max e target := lt_of_lt_of_le hlt htarget_le_max
        omega
      omega
    set K := (Max.max e target - e).toNat with hK_def
    have hK1 : (Max.max e target - (e + 1)).toNat = K - 1 := by
      rw [hK_def]
      have : Max.max e target - (e + 1) = Max.max e target - e - 1 := by ring
      rw [this]
      omega
    rw [hK1]
    rw [Nat.div_div_eq_div_mul]
    have hKform : 10 * 10 ^ (K - 1) = 10 ^ K := by
      have hKsucc : K = (K - 1) + 1 := by omega
      conv_rhs => rw [hKsucc]
      ring
    rw [hKform]
  | case2 m e g hnlt =>
    rw [alignDownSpec_noop hnlt]
    push Not at hnlt
    have hmax : Max.max e target = e := max_eq_left hnlt
    rw [hmax]
    simp

/-- If `g0` represents `f0`, the guard after `alignDown m e g0 target` represents the truncated tail
`(f0 + m % 10^k) / 10^k`, where `k = (max e target - e).toNat`. -/
theorem alignDownSpec_represents
    (m : UInt64) (e : Int) (g0 : Guard) (target : Int)
    (f0 : ℚ) (hrep0 : represents g0 f0) :
    represents (alignDownSpec m e g0 target).2.2
      ((f0 + ((m.toNat % 10 ^ (Max.max e target - e).toNat : ℕ) : ℚ))
         / 10 ^ (Max.max e target - e).toNat) := by
  induction m, e, g0 using alignDownSpec.induct target
    generalizing f0 with
  | case1 m e g0 hlt IH =>
    have h10_uval : (10 : UInt64).toNat = 10 := uint64_ten_toNat
    have hd_lt : (m % 10).toNat < 10 := by
      rw [UInt64.toNat_mod, h10_uval]
      omega
    have hpush := represents_push hrep0 hd_lt
    have hd_eq : ((m % 10 : UInt64).toNat : ℚ) = ((m.toNat % 10 : ℕ) : ℚ) := by
      rw [UInt64.toNat_mod, h10_uval]
    have hstep := alignDownSpec_step (m := m) (e := e) (g := g0) (target := target) hlt
    rw [hstep]
    set f1 : ℚ := (f0 + ((m % 10 : UInt64).toNat : ℚ)) / 10 with hf1_def
    have hIH := IH (f0 := f1) hpush
    have hmax_e1 : Max.max (e + 1) target = Max.max e target := by
      have hmax_r : Max.max e target = target := max_eq_right (le_of_lt hlt)
      rw [hmax_r]
      by_cases h2 : e + 1 ≤ target
      · exact max_eq_right h2
      · push Not at h2
        rw [max_eq_left (le_of_lt h2)]; omega
    set K : ℕ := (Max.max e target - e).toNat with hK_def
    have hK_pos : 0 < K := by
      rw [hK_def]
      have hlt' : e < Max.max e target := lt_of_lt_of_le hlt (le_max_right _ _)
      omega
    have hKstep : (Max.max (e + 1) target - (e + 1)).toNat = K - 1 := by
      rw [hmax_e1, hK_def]
      have heq : Max.max e target - (e + 1) = Max.max e target - e - 1 := by ring
      rw [heq]; omega
    have hm10 : ((m / 10 : UInt64)).toNat = m.toNat / 10 := by
      rw [UInt64.toNat_div]; rfl
    have hKsucc : K = (K - 1) + 1 := by omega
    have hstep_nat : m.toNat % 10 ^ K
        = 10 * ((m / 10 : UInt64).toNat % 10 ^ (K - 1)) + m.toNat % 10 := by
      rw [hm10]
      conv_lhs => rw [hKsucc]
      exact nat_mod_pow_step _ _
    have hstep_q : ((m.toNat % 10 ^ K : ℕ) : ℚ)
        = 10 * (((m / 10 : UInt64).toNat % 10 ^ (K - 1) : ℕ) : ℚ)
            + ((m.toNat % 10 : ℕ) : ℚ) := by
      exact_mod_cast hstep_nat
    have target_eq :
        (f0 + ((m.toNat % 10 ^ K : ℕ) : ℚ)) / 10 ^ K
          = (f1 + (((m / 10 : UInt64).toNat % 10 ^ (K - 1) : ℕ) : ℚ)) / 10 ^ (K - 1) := by
      have hKK : (10 : ℚ) ^ K = 10 * 10 ^ (K - 1) := by
        conv_lhs => rw [hKsucc]
        rw [pow_succ]; ring
      rw [hstep_q, hKK]
      have hf1_q : f1 = (f0 + ((m.toNat % 10 : ℕ) : ℚ)) / 10 := by
        rw [hf1_def, hd_eq]
      rw [hf1_q]
      have hK1_ne : (10 : ℚ) ^ (K - 1) ≠ 0 := by positivity
      field_simp
      ring
    change represents
      (alignDownSpec (m / 10) (e + 1) (g0.push (m % 10)) target).2.2
      ((f0 + ((m.toNat % 10 ^ K : ℕ) : ℚ)) / 10 ^ K)
    rw [target_eq]
    rw [hKstep] at hIH
    exact hIH
  | case2 m e g0 hnlt =>
    rw [alignDownSpec_noop hnlt]
    push Not at hnlt
    have hmax : Max.max e target = e := max_eq_left hnlt
    have hk0 : (Max.max e target - e).toNat = 0 := by rw [hmax]; simp
    rw [hk0]
    simp only [pow_zero, Nat.mod_one, Nat.cast_zero, add_zero, div_one]
    exact hrep0

end XRPL.Model.Protocol
