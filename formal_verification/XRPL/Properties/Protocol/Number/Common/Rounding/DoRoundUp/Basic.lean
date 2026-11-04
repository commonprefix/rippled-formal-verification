import XRPL.Properties.Protocol.Number.Common.Notation
import Mathlib.Tactic

import XRPL.Properties.Protocol.Number.Common.Constants
import XRPL.Properties.Protocol.Number.Common.ToRatLemmas
import XRPL.Properties.Protocol.Number.Common.Rounding.ScaleDown

set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false

/-! # Basic facts for `Guard.doRoundUp`

No-overflow facts for the mantissa steps, the range of a guard's dropped fraction, when `pushOverflow` changes
nothing, and the two outcomes of `bringIntoRange`. -/

namespace XRPL.Model.Protocol

/-- `RoundResult` value as a rational. -/
noncomputable def RoundResult.toRat (r : RoundResult) : ℚ := r.toNumber.toRat

/-- `m + 1` does not overflow UInt64 when `m ≤ maxRep`. -/
lemma m_add_one_no_overflow {m : UInt64} (h : m.toNat ≤ maxRep.toNat) :
    (m + 1).toNat = m.toNat + 1 := by
  rw [UInt64.toNat_add]
  have h1 : (1 : UInt64).toNat = 1 := rfl
  rw [h1]
  have : m.toNat + 1 < 2 ^ 64 := by
    rw [maxRep_val] at h; omega
  exact Nat.mod_eq_of_lt this

/-- `m * 10` does not overflow UInt64 when `m < largeRange.min`. -/
lemma m_mul_ten_no_overflow {m : UInt64}
    (h : m.toNat < largeRange.min.toNat) :
    (m * 10).toNat = m.toNat * 10 := by
  rw [UInt64.toNat_mul]
  have h10 : (10 : UInt64).toNat = 10 := uint64_ten_toNat
  rw [h10]
  have : m.toNat * 10 < 2 ^ 64 := by
    rw [largeRange_min_val] at h
    calc m.toNat * 10 < 1000000000000000000 * 10 := by
          exact (Nat.mul_lt_mul_right (by norm_num : 0 < 10)).mpr h
      _ = tenPow19 := by norm_num
      _ < 2 ^ 64 := by norm_num
  exact Nat.mod_eq_of_lt this

/-- The `×1000` mantissa lift does not overflow for a 16-digit mantissa
(`m.toNat < 10^16`): `(m*10*10*10).toNat = m.toNat * 1000`. -/
lemma m_mul_thousand_no_overflow {m : UInt64} (h : m.toNat < 10 ^ 16) :
    (m * 10 * 10 * 10).toNat = m.toNat * 1000 := by
  have hmin : largeRange.min.toNat = 1000000000000000000 := largeRange_min_val
  have hb : m.toNat < 10000000000000000 := by
    have h16 : (10 : ℕ) ^ 16 = 10000000000000000 := by norm_num
    omega
  have h1 : (m * 10).toNat = m.toNat * 10 := m_mul_ten_no_overflow (by rw [hmin]; omega)
  have h2 : (m * 10 * 10).toNat = m.toNat * 100 := by
    rw [m_mul_ten_no_overflow (by rw [hmin, h1]; omega), h1]; ring
  rw [m_mul_ten_no_overflow (by rw [hmin, h2]; omega), h2]; ring

/-- The `÷1000` mantissa drop: `(m/10/10/10).toNat = m.toNat / 1000` (no wrap). -/
lemma m_div_thousand_toNat (m : UInt64) :
    (m / 10 / 10 / 10).toNat = m.toNat / 1000 := by
  rw [UInt64.toNat_div, UInt64.toNat_div, UInt64.toNat_div, uint64_ten_toNat,
      Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul]

/-- `represents g f` implies `0 ≤ f`. -/
lemma represents_nonneg {g : Guard} {f : ℚ} (hrep : represents g f) : 0 ≤ f := by
  obtain ⟨x, hx_nn, _, hf_eq, _, _⟩ := hrep
  rw [hf_eq]
  have : (0 : ℚ) ≤ (decimalValue g.digits_ : ℚ) / 10 ^ 16 := by positivity
  linarith

/-- `represents g f` implies `f < 1`. -/
lemma represents_lt_one {g : Guard} {f : ℚ} (hrep : represents g f) : f < 1 := by
  obtain ⟨x, hx_nn, hx_lt, hf_eq, _, hall⟩ := hrep
  have hdv_lt : decimalValue g.digits_ < 10 ^ 16 := by
    unfold decimalValue
    have hbound : ∀ p ∈ Finset.range 16, nibble g.digits_ p * 10 ^ p ≤ 9 * 10 ^ p := by
      intro p hp
      have : nibble g.digits_ p ≤ 9 := hall ⟨p, Finset.mem_range.mp hp⟩
      exact Nat.mul_le_mul_right _ this
    calc ∑ p ∈ Finset.range 16, nibble g.digits_ p * 10 ^ p
        ≤ ∑ p ∈ Finset.range 16, 9 * 10 ^ p := Finset.sum_le_sum hbound
      _ < 10 ^ 16 := by decide
  rw [hf_eq]
  have hdv_q : (decimalValue g.digits_ : ℚ) < 10 ^ 16 := by exact_mod_cast hdv_lt
  have h16_pos : (0 : ℚ) < 10 ^ 16 := by positivity
  have h_top : (decimalValue g.digits_ : ℚ) / 10 ^ 16 < 1 := by
    rw [div_lt_iff₀ h16_pos]; linarith
  have hx_lt_q : x < 1 / 10 ^ 16 := hx_lt
  have : (decimalValue g.digits_ : ℚ) / 10 ^ 16 + x < 1 / 10 ^ 16 + (1 - 1 / 10 ^ 16) := by
    have hdv_lt' : (decimalValue g.digits_ : ℚ) / 10 ^ 16 ≤ 1 - 1 / 10 ^ 16 := by
      have hdv_le : decimalValue g.digits_ + 1 ≤ 10 ^ 16 := by omega
      have hdv_q' : ((decimalValue g.digits_ + 1 : ℕ) : ℚ) ≤ ((10 ^ 16 : ℕ) : ℚ) := by
        exact_mod_cast hdv_le
      push_cast at hdv_q'
      have : (decimalValue g.digits_ : ℚ) ≤ 10 ^ 16 - 1 := by linarith
      rw [div_le_iff₀ h16_pos]
      have : (10 : ℚ) ^ 16 * (1 - 1 / 10 ^ 16) = 10 ^ 16 - 1 := by
        field_simp
      linarith
    linarith
  linarith

/-- `Guard.pushOverflow` is a no-op when `mantissa < maxRep` (strictly below the cusp). -/
lemma pushOverflow_noop_of_lt_maxRep {m : UInt64} (hlt : m.toNat < maxRep.toNat)
    (g : Guard) (mode : rounding_mode) :
    g.pushOverflow m mode = g := by
  unfold Guard.pushOverflow
  rw [if_neg]
  intro ⟨h_ge, _⟩
  have : maxRep.toNat ≤ m.toNat := UInt64.le_iff_toNat_le.mp h_ge
  omega

/-- Pushing a `0` digit onto an empty guard leaves it unchanged. -/
lemma Guard.push_zero_of_empty (g : Guard) (h : g.empty = true) : g.push 0 = g := by
  unfold Guard.empty Guard.unrecoverable at h
  simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_eq_eq_not, Bool.not_true] at h
  obtain ⟨hd, hx⟩ := h
  cases g with
  | mk d x s =>
    simp only at hd hx
    subst hd; subst hx
    unfold Guard.push
    simp

/-- Pushing a `0` digit keeps a guard empty or non-empty. -/
lemma Guard.push_zero_empty_eq (g : Guard) : (g.push 0).empty = g.empty := by
  cases g with
  | mk d x s =>
    unfold Guard.push Guard.empty Guard.unrecoverable
    simp only
    have key : ((d >>> 4) == 0 && !((d &&& 15) != 0)) = (d == 0) := by
      have h1 : (d >>> 4).toNat = d.toNat / 16 := by
        rw [UInt64.toNat_shiftRight]; simp [Nat.shiftRight_eq_div_pow]
      have h2 : (d &&& 15).toNat = d.toNat % 16 := by
        rw [UInt64.toNat_and]; exact Nat.and_two_pow_sub_one_eq_mod d.toNat 4
      rw [Bool.eq_iff_iff]
      simp only [bne, Bool.not_not, Bool.and_eq_true, beq_iff_eq]
      constructor
      · rintro ⟨ha, hb⟩
        have ha' := congrArg UInt64.toNat ha
        have hb' := congrArg UInt64.toNat hb
        rw [h1] at ha'; rw [h2] at hb'
        apply UInt64.toNat_inj.mp
        simp only [UInt64.toNat_zero] at ha' hb' ⊢
        omega
      · rintro rfl; decide
    cases x <;> simp [key]

/-- In a directed mode the rounding decision depends only on whether the guard is empty and on its sign bit. -/
lemma Guard.round_directed_eq (g : Guard) (mode : rounding_mode) (hm : mode ≠ .to_nearest) :
    g.round mode = if g.empty then -2 else
      match mode with
      | .downward => if g.sbit_ then 1 else -1
      | .upward => if g.sbit_ then -1 else 1
      | _ => -1 := by
  unfold Guard.round
  by_cases he : g.empty = true
  · simp [he]
  · have hne : (g.digits_ > 0 || g.xbit_) = true := by
      cases g with
      | mk d x s =>
        unfold Guard.empty Guard.unrecoverable at he
        simp only at he ⊢
        have key : (d > 0) = ¬ (d = 0) := by
          apply propext; constructor
          · intro h h0; subst h0; exact absurd h (by decide)
          · intro h; exact UInt64.pos_iff_ne_zero.mpr h
        cases x <;> simp_all
    cases mode
    · exact absurd rfl hm
    all_goals simp_all

/-- In a directed mode pushing a `0` digit does not change the rounding decision. -/
lemma Guard.push_zero_round_directed (g : Guard) (mode : rounding_mode) (hm : mode ≠ .to_nearest) :
    (g.push 0).round mode = g.round mode := by
  rw [Guard.round_directed_eq _ mode hm, Guard.round_directed_eq g mode hm, Guard.push_zero_empty_eq]
  rfl

/-- At `mantissa = maxRep`, when the guard does not round up, `pushOverflow` pushes the digit `0`. -/
lemma pushOverflow_maxRep_of_round_ne_one (g : Guard) (mode : rounding_mode) (hr : g.round mode ≠ 1) :
    g.pushOverflow maxRep mode = g.push 0 := by
  unfold Guard.pushOverflow
  rw [if_pos (by decide : maxRep ≤ maxRep ∧ maxRep < maxRepUp)]
  have hr_ne : (g.round mode == 1) = false := beq_eq_false_iff_ne.mpr hr
  have hmid : maxRep + (maxRepUp - maxRep) / 2 = (maxRep + 1 : UInt64) := by decide
  have hne : (maxRep == (maxRep + 1 : UInt64)) = false := by decide
  simp only [show maxRep % (10 : UInt64) < 9 from by decide, hmid, hr_ne, hne, Bool.false_or, Bool.and_false,
    ite_true, Bool.false_eq_true, ite_false]
  rfl

/-- At `mantissa = maxRep`, when the guard rounds up, `pushOverflow` moves to `maxRep + 1` and pushes the digit
`3`. -/
lemma pushOverflow_maxRep_of_round_eq_one (g : Guard) (mode : rounding_mode) (hr : g.round mode = 1) :
    g.pushOverflow maxRep mode = g.push 3 := by
  unfold Guard.pushOverflow
  rw [if_pos (by decide : maxRep ≤ maxRep ∧ maxRep < maxRepUp)]
  have hbump : (g.round mode == 1 || (g.round mode == 0 && maxRep == maxRep + 1)) = true := by simp [hr]
  simp only [show (maxRep : UInt64) % 10 < 9 from by decide, if_true,
             show (maxRepUp - maxRep : UInt64) / 2 = 1 from by decide, hbump,
             show ((maxRep + 1 : UInt64) - maxRep) = 1 from by decide,
             show (1 * 10 : UInt64) / (maxRepUp - maxRep) = 3 from by decide]

/-- A guard whose top digit is below `5` does not round up in `to_nearest`: it rounds down, or reports an empty
guard. -/
lemma Guard.round_to_nearest_of_top_lt_five (g : Guard) (h : g.digits_.toNat < 5764607523034234880) :
    g.round .to_nearest = -1 ∨ g.round .to_nearest = -2 := by
  by_cases hemp : g.empty = true
  · right; unfold Guard.round; rw [if_pos hemp]
  · left
    rw [round_to_nearest_def hemp]
    have hlt : g.digits_ < 0x5000_0000_0000_0000 := by
      rw [UInt64.lt_iff_toNat_lt, show (0x5000_0000_0000_0000 : UInt64).toNat = 5764607523034234880 from by decide]
      exact h
    have hgt : ¬ g.digits_ > 0x5000_0000_0000_0000 := by
      simp only [UInt64.lt_iff_toNat_lt] at *; omega
    simp only [if_neg hgt, if_pos hlt]

/-- At `mantissa = maxRep`, the guard left by `to_nearest` `pushOverflow` never rounds up: its top digit is `0` or
`3`. -/
lemma pushOverflow_maxRep_round_to_nearest (g : Guard) :
    (g.pushOverflow maxRep .to_nearest).round .to_nearest ≠ 1 ∧
      (g.pushOverflow maxRep .to_nearest).round .to_nearest ≠ 0 := by
  have hsize : g.digits_.toNat ≤ 2 ^ 64 - 1 := by
    have := UInt64.toNat_lt_size g.digits_; simp only [UInt64.size] at this; omega
  have hcases : ∃ d : UInt64, d.toNat ≤ 3 ∧ g.pushOverflow maxRep .to_nearest = g.push d := by
    by_cases hr : g.round .to_nearest = 1
    · exact ⟨3, by decide, pushOverflow_maxRep_of_round_eq_one g .to_nearest hr⟩
    · exact ⟨0, by decide, pushOverflow_maxRep_of_round_ne_one g .to_nearest hr⟩
  obtain ⟨d, hd, heq⟩ := hcases
  have htop : (g.push d).digits_.toNat < 5764607523034234880 := by
    rw [toNat_push_digits]; omega
  rw [heq]
  rcases Guard.round_to_nearest_of_top_lt_five _ htop with h | h <;> rw [h] <;> decide

/-- In `to_nearest`, `doRoundUp` at `mantissa = maxRep` keeps `maxRep`. -/
lemma doRoundUp_to_nearest_maxRep (g : Guard) (neg : Bool) (e : Int) (minM maxM : UInt64) (loc : Error)
    (res : RoundResult) (hok : g.doRoundUp neg maxRep e minM maxM .to_nearest loc = .ok res) :
    res = Guard.bringIntoRange neg maxRep e minM := by
  obtain ⟨h1, h0⟩ := pushOverflow_maxRep_round_to_nearest g
  have h_ru_false : (((g.pushOverflow maxRep .to_nearest).round .to_nearest == 1) ||
      (((g.pushOverflow maxRep .to_nearest).round .to_nearest == 0) && (maxRep % 2 == 1))) = false := by
    simp [h1, h0]
  have h_not_cusp : ¬ (maxRep < maxRep ∧ maxRep < maxRepUp) := by decide
  unfold Guard.doRoundUp at hok
  dsimp only [Guard.doDropDigit] at hok
  rw [h_ru_false] at hok
  simp only [Bool.false_eq_true, ite_false] at hok
  rw [if_neg h_not_cusp] at hok
  by_cases h_ovf : (Guard.bringIntoRange neg maxRep e minM).exponent_ > maxExponent
  · rw [if_pos h_ovf] at hok; simp at hok
  · rw [if_neg h_ovf] at hok; exact (Except.ok.inj hok).symm

/-- With an empty guard `pushOverflow` is a no-op for any `mantissa ≤ maxRep`. -/
lemma pushOverflow_noop_of_le_maxRep_of_empty {m : UInt64} (hle : m.toNat ≤ maxRep.toNat)
    (g : Guard) (mode : rounding_mode) (hempty : g.empty = true) :
    g.pushOverflow m mode = g := by
  rcases Nat.lt_or_ge m.toNat maxRep.toNat with hlt | hge
  · exact pushOverflow_noop_of_lt_maxRep hlt g mode
  · have hm : m = maxRep := UInt64.toNat_inj.mp (by omega)
    subst hm
    have hround : g.round mode = -2 := by unfold Guard.round; rw [if_pos hempty]
    rw [pushOverflow_maxRep_of_round_ne_one g mode (by rw [hround]; decide)]
    exact Guard.push_zero_of_empty g hempty

/-- In a directed mode, for `mantissa ≤ maxRep` and a guard that does not round up, `pushOverflow` keeps the
rounding decision. -/
lemma pushOverflow_round_of_le_maxRep_of_round_ne_one {m : UInt64} (hle : m.toNat ≤ maxRep.toNat)
    (g : Guard) (mode : rounding_mode) (hm : mode ≠ .to_nearest) (hr : g.round mode ≠ 1) :
    (g.pushOverflow m mode).round mode = g.round mode := by
  rcases Nat.lt_or_ge m.toNat maxRep.toNat with hlt | hge
  · rw [pushOverflow_noop_of_lt_maxRep hlt g mode]
  · have hm' : m = maxRep := UInt64.toNat_inj.mp (by omega)
    subst hm'
    rw [pushOverflow_maxRep_of_round_ne_one g mode hr]
    exact Guard.push_zero_round_directed g mode hm

/-- For an empty guard `pushOverflow` is a no-op whenever `mantissa` is NOT strictly in
the cusp interior `(maxRep, maxRepUp)`. -/
lemma pushOverflow_noop_of_empty {m : UInt64} (g : Guard) (mode : rounding_mode)
    (hempty : g.empty = true) (h_no_push : ¬ (maxRep < m ∧ m < maxRepUp)) :
    g.pushOverflow m mode = g := by
  by_cases hc : maxRep ≤ m ∧ m < maxRepUp
  · have hm_eq : m = maxRep := by
      have h1 : ¬ (maxRep.toNat < m.toNat) :=
        fun h => h_no_push ⟨UInt64.lt_iff_toNat_lt.mpr h, hc.2⟩
      have h2 : maxRep.toNat ≤ m.toNat := UInt64.le_iff_toNat_le.mp hc.1
      exact UInt64.toNat_inj.mp (by omega)
    subst hm_eq
    exact pushOverflow_noop_of_le_maxRep_of_empty (le_refl _) g mode hempty
  · unfold Guard.pushOverflow
    rw [if_neg hc]

/-- When `m < minM ∧ m ≠ 0`, `bringIntoRange` rescales once: result uses `m*10` and `e-1`. -/
lemma bringIntoRange_rescale_result {m : UInt64} {e : Int} {neg : Bool} {minM : UInt64}
    (hresc : m < minM) (hm_ne : m ≠ 0) :
    Guard.bringIntoRange neg m e minM =
    if e - 1 < minExponent ∨ m * 10 = 0 then
      { negative_ := false, mantissa_ := 0, exponent_ := -2147483648 }
    else
      { negative_ := neg, mantissa_ := m * 10, exponent_ := e - 1 } := by
  unfold Guard.bringIntoRange
  rw [if_pos (And.intro hresc hm_ne)]

/-- When `¬ (m < minM ∧ m ≠ 0)`, `bringIntoRange` keeps `m` and `e`. -/
lemma bringIntoRange_noscale_result {m : UInt64} {e : Int} {neg : Bool} {minM : UInt64}
    (hnresc : ¬ (m < minM ∧ m ≠ 0)) :
    Guard.bringIntoRange neg m e minM =
    if e < minExponent ∨ m = 0 then
      { negative_ := false, mantissa_ := 0, exponent_ := -2147483648 }
    else
      { negative_ := neg, mantissa_ := m, exponent_ := e } := by
  unfold Guard.bringIntoRange
  simp only [if_neg hnresc]

/-- At `largeRange.min`, a nonzero `bringIntoRange` output has exactly the input value `m · 10^e`. -/
lemma bringIntoRange_value_q (zn : Bool) (m : UInt64) (e : Int)
    (hne : (Guard.bringIntoRange zn m e largeRange.min).mantissa_ ≠ 0) :
    ((Guard.bringIntoRange zn m e largeRange.min).mantissa_.toNat : ℚ)
        * 10 ^ (Guard.bringIntoRange zn m e largeRange.min).exponent_
      = (m.toNat : ℚ) * 10 ^ e := by
  have hm_ne : m ≠ 0 := by
    intro h
    apply hne
    have hnresc : ¬ (m < largeRange.min ∧ m ≠ 0) := by
      intro hc
      exact hc.2 h
    rw [bringIntoRange_noscale_result hnresc]
    simp [h]
  by_cases hresc : m < largeRange.min
  · rw [bringIntoRange_rescale_result hresc hm_ne] at hne ⊢
    by_cases h_under : e - 1 < minExponent ∨ m * 10 = 0
    · rw [if_pos h_under] at hne
      exact absurd rfl hne
    · rw [if_neg h_under]
      have hm_mul_10 : (m * 10).toNat = m.toNat * 10 :=
        m_mul_ten_no_overflow (UInt64.lt_iff_toNat_lt.mp hresc)
      change ((m * 10).toNat : ℚ) * 10 ^ (e - 1) = (m.toNat : ℚ) * 10 ^ e
      rw [hm_mul_10]
      push_cast
      rw [show (e - 1 : ℤ) = e + (-1) from by ring,
          zpow_add₀ (by norm_num : (10 : ℚ) ≠ 0), zpow_neg_one]
      field_simp
  · have hnresc : ¬ (m < largeRange.min ∧ m ≠ 0) := by
      intro hc
      exact hresc hc.1
    rw [bringIntoRange_noscale_result hnresc] at hne ⊢
    by_cases h_under : e < minExponent ∨ m = 0
    · rw [if_pos h_under] at hne
      exact absurd rfl hne
    · rw [if_neg h_under]

/-- If the output mantissa is non-zero, the output sign equals the input `zn`. -/
lemma doRoundUp_negative_of_mant_ne
    (g : Guard) (zn : Bool) (m : UInt64) (e : Int)
    (minMant maxMant : UInt64) (mode : rounding_mode)
    (loc : Error) (res : RoundResult)
    (hok : g.doRoundUp zn m e minMant maxMant mode loc = .ok res)
    (hne : res.mantissa_ ≠ 0) :
    res.negative_ = zn := by
  unfold Guard.doRoundUp Guard.bringIntoRange at hok
  dsimp only [Guard.doDropDigit] at hok
  split_ifs at hok with h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 <;>
    (try (simp only [Except.ok.injEq] at hok)) <;>
    (try (simp only [reduceCtorEq] at hok)) <;>
    first
    | (subst hok; exact absurd rfl hne)
    | (subst hok; rfl)

set_option maxHeartbeats 1600000 in
-- split_ifs at hok ⊢ with 10 conditions creates ~2^10 cases, so extra heartbeats are needed
lemma doRoundUp_false_from_ok
    (g : Guard) (zn : Bool) (m : UInt64) (e : Int) (mode : rounding_mode)
    (loc : Error) (res : RoundResult)
    (hok : g.doRoundUp zn m e largeRange.min largeRange.max mode loc = .ok res) :
    g.doRoundUp false m e largeRange.min largeRange.max mode loc =
      .ok { negative_ := false, mantissa_ := res.mantissa_, exponent_ := res.exponent_ } := by
  -- The output mantissa/exponent are independent of `negative_`, so the `false` case succeeds with the same value.
  unfold Guard.doRoundUp Guard.bringIntoRange at hok ⊢
  dsimp only [Guard.doDropDigit] at hok ⊢
  split_ifs at hok ⊢ with h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 <;>
    (try (simp only [reduceCtorEq] at hok)) <;>
    (try (simp only [Except.ok.injEq] at hok)) <;>
    (try (obtain rfl := Except.ok.inj hok)) <;>
    (try subst hok) <;>
    (try rfl) <;>
    (try ring_nf)

end XRPL.Model.Protocol
