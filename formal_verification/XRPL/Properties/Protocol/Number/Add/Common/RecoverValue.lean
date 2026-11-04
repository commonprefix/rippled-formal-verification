import Mathlib.Tactic

import XRPL.Model.Protocol.Number
import XRPL.Properties.Protocol.Number.Add.Common.AlignDown
import XRPL.Properties.Protocol.Number.Add.Common.RecoverBasic
import XRPL.Properties.Protocol.Number.Common.Rounding.Guard
import XRPL.Properties.Protocol.Number.Common.Rounding.ScaleDown


namespace XRPL.Model.Protocol

/-- If `g` represents `f_g` and the loop does not pop when `xbit_` is set, the output guard represents some
`f_exit` and the diff-sign value `(m - f_g) * 10^e` is preserved. -/
theorem recover_preserves_represents
    (upperLimit m : UInt128) (hUL : upperLimit.toNat * 10 < 2 ^ 128)
    (e : Int) (g : Guard) (fuel : ℕ)
    (hm_pos : 1 ≤ m.toNat)
    {f_g : ℚ} (hrep : represents g f_g)
    (hdich : g.xbit_ = true →
      ¬ (m < upperLimit ∧ ¬ g.empty)) :
    ∃ f_exit : ℚ,
      represents (Number.operator_add.recover upperLimit m e g fuel).2.2 f_exit ∧
      ((m.toNat : ℚ) - f_g) * (10 : ℚ) ^ e
        = (((Number.operator_add.recover upperLimit m e g fuel).1.toNat : ℚ) - f_exit)
            * (10 : ℚ) ^ ((Number.operator_add.recover upperLimit m e g fuel).2.1) := by
  induction m, e, g, fuel using Number.operator_add.recover.induct (upperLimit := upperLimit)
    generalizing f_g with
  | case1 m e g =>
    refine ⟨f_g, hrep, ?_⟩
    rw [recover_noop_zero]
  | case2 m e g fuel hcond g' d hpop IH =>
    obtain ⟨h1, h2⟩ := hcond
    obtain ⟨_, _, _, _, _, hall⟩ := id hrep
    -- The pop happens, so `xbit_` must be false (contrapositive of `hdich`).
    have hxbit_false : g.xbit_ = false := by
      by_contra hx
      have hxt : g.xbit_ = true := by
        cases h : g.xbit_ with
        | false => exact absurd h hx
        | true => rfl
      exact (hdich hxt) ⟨h1, h2⟩
    rw [recover_step h1 h2]
    have hpop1 : g.pop.1 = g' := by rw [hpop]
    have hpop2 : g.pop.2 = d := by rw [hpop]
    rw [hpop1, hpop2]
    have hd_le_9 : d.toNat ≤ 9 := by
      rw [← hpop2]; exact pop_digit_le_9 g hall
    have hd_le_mt : toUInt128 d ≤ m * 10 := by
      rw [← hpop2]
      exact pop_digit_le_mul_ten_of_pos128 hUL hm_pos h1 (pop_digit_le_9 g hall)
    have hm_new_nat : (m * 10 - toUInt128 d).toNat = m.toNat * 10 - d.toNat :=
      recover_step_mantissa_nat128 hUL h1 hd_le_mt
    have hm10ge : 10 ≤ m.toNat * 10 := by nlinarith
    have hm_new_pos : 1 ≤ (m * 10 - toUInt128 d).toNat := by
      rw [hm_new_nat]; omega
    have hrep_pop : represents g.pop.1 (10 * f_g - (g.pop.2.toNat : ℚ)) :=
      represents_pop_of_xbit_false hrep hxbit_false
    rw [hpop1, hpop2] at hrep_pop
    -- The fresh guard `g'` also has `xbit_ = false`, so `hdich'` is vacuous.
    have hg'_xbit : g'.xbit_ = false := by
      have : g.pop.1.xbit_ = g.xbit_ := by rfl
      rw [hpop1] at this
      rw [this, hxbit_false]
    have hdich' : g'.xbit_ = true →
        ¬ ((m * 10 - toUInt128 d) < upperLimit ∧ ¬ g'.empty) := by
      intro hxt
      rw [hg'_xbit] at hxt
      exact absurd hxt (by decide)
    obtain ⟨f_exit, hrep_exit, hIH_eq⟩ := IH hm_new_pos hrep_pop hdich'
    refine ⟨f_exit, hrep_exit, ?_⟩
    rw [← hIH_eq]
    -- One-step value algebra: `(m - f_g) * 10^e = ((m*10-d) - (10 f_g - d)) * 10^(e-1)`.
    have h_mnew_q : ((m * 10 - toUInt128 d).toNat : ℚ) = (m.toNat : ℚ) * 10 - (d.toNat : ℚ) := by
      rw [hm_new_nat]
      have hle : d.toNat ≤ m.toNat * 10 := by omega
      rw [Nat.cast_sub hle]
      push_cast; ring
    rw [h_mnew_q]
    have he_pow : (10 : ℚ) ^ e = (10 : ℚ) ^ (e - 1) * 10 := by
      rw [show e = (e - 1) + 1 from by ring, zpow_add₀ (by norm_num : (10 : ℚ) ≠ 0)]
      simp
    rw [he_pow]
    field_simp
    ring
  | case3 m e g fuel hcond =>
    refine ⟨f_g, ?_, ?_⟩
    · have hprop : ¬ (m < upperLimit ∧ ¬ g.empty) := hcond
      rw [recover_noop_exit hprop]; exact hrep
    · have hprop : ¬ (m < upperLimit ∧ ¬ g.empty) := hcond
      rw [recover_noop_exit hprop]

/-- A guard that is empty and `represents f` forces `f = 0`. -/
lemma represents_zero_of_empty {g : Guard} {f : ℚ}
    (hrep : represents g f) (hempty : g.empty = true) : f = 0 := by
  obtain ⟨hd, hx⟩ : g.digits_ = 0 ∧ g.xbit_ = false := by
    have h : (g.digits_ == 0 && !g.xbit_) = true := hempty
    rw [Bool.and_eq_true] at h
    exact ⟨beq_iff_eq.mp h.1, by simpa using h.2⟩
  exact represents_eq_zero_of_digits_zero_xbit_false hd hx hrep

/-- If the `recover` output guard is empty, the diff-sign value `(m - f) * 10^e` equals the output
`m_out * 10^e_out` exactly, with no residue. -/
theorem recover_exact_of_empty
    (upperLimit m : UInt128) (hUL : upperLimit.toNat * 10 < 2 ^ 128)
    (e : Int) (g : Guard) (fuel : ℕ)
    (hm_pos : 1 ≤ m.toNat)
    {f : ℚ} (hrep : represents g f)
    (hempty : (Number.operator_add.recover upperLimit m e g fuel).2.2.empty = true) :
    ((m.toNat : ℚ) - f) * (10 : ℚ) ^ e
      = ((Number.operator_add.recover upperLimit m e g fuel).1.toNat : ℚ)
          * (10 : ℚ) ^ ((Number.operator_add.recover upperLimit m e g fuel).2.1) := by
  induction m, e, g, fuel using Number.operator_add.recover.induct (upperLimit := upperLimit)
    generalizing f with
  | case1 m e g =>
    rw [recover_noop_zero] at hempty ⊢
    rw [represents_zero_of_empty hrep hempty]
    ring
  | case2 m e g fuel hcond g' d hpop IH =>
    obtain ⟨h1, h2⟩ := hcond
    rw [recover_step h1 h2] at hempty ⊢
    have hpop1 : g.pop.1 = g' := by rw [hpop]
    have hpop2 : g.pop.2 = d := by rw [hpop]
    rw [hpop1, hpop2] at hempty ⊢
    obtain ⟨_, _, _, _, _, hall⟩ := id hrep
    -- An empty output forces `xbit_ = false` at the input (pop preserves xbit).
    have hxbit_false : g.xbit_ = false := by
      have hx := recover_xbit upperLimit (m * 10 - toUInt128 d) (e - 1) g' fuel
      have hout_xbit : (Number.operator_add.recover upperLimit (m * 10 - toUInt128 d)
          (e - 1) g' fuel).2.2.xbit_ = false := by
        have h : ((Number.operator_add.recover upperLimit (m * 10 - toUInt128 d)
            (e - 1) g' fuel).2.2.digits_ == 0
            && !(Number.operator_add.recover upperLimit (m * 10 - toUInt128 d)
                  (e - 1) g' fuel).2.2.xbit_) = true := hempty
        rw [Bool.and_eq_true] at h
        simpa using h.2
      rw [hx] at hout_xbit
      have hpop_xbit : g'.xbit_ = g.xbit_ := by rw [← hpop1]; rfl
      rw [hpop_xbit] at hout_xbit
      exact hout_xbit
    have hd_le_9 : d.toNat ≤ 9 := by
      rw [← hpop2]; exact pop_digit_le_9 g hall
    have hd_le_mt : toUInt128 d ≤ m * 10 := by
      rw [← hpop2]
      exact pop_digit_le_mul_ten_of_pos128 hUL hm_pos h1 (pop_digit_le_9 g hall)
    have hm_new_nat : (m * 10 - toUInt128 d).toNat = m.toNat * 10 - d.toNat :=
      recover_step_mantissa_nat128 hUL h1 hd_le_mt
    have hm10ge : 10 ≤ m.toNat * 10 := by nlinarith
    have hm_new_pos : 1 ≤ (m * 10 - toUInt128 d).toNat := by
      rw [hm_new_nat]; omega
    have hrep_pop : represents g.pop.1 (10 * f - (g.pop.2.toNat : ℚ)) :=
      represents_pop_of_xbit_false hrep hxbit_false
    rw [hpop1, hpop2] at hrep_pop
    have hIH_eq := IH hm_new_pos hrep_pop hempty
    rw [← hIH_eq]
    have h_mnew_q : ((m * 10 - toUInt128 d).toNat : ℚ) = (m.toNat : ℚ) * 10 - (d.toNat : ℚ) := by
      rw [hm_new_nat]
      have hle : d.toNat ≤ m.toNat * 10 := by omega
      rw [Nat.cast_sub hle]
      push_cast; ring
    rw [h_mnew_q]
    have he_pow : (10 : ℚ) ^ e = (10 : ℚ) ^ (e - 1) * 10 := by
      rw [show e = (e - 1) + 1 from by ring, zpow_add₀ (by norm_num : (10 : ℚ) ≠ 0)]
      simp
    rw [he_pow]
    ring
  | case3 m e g fuel hcond =>
    rw [recover_noop_exit hcond] at hempty ⊢
    rw [represents_zero_of_empty hrep hempty]
    ring

/-- `recover` preserves the diff-sign value, keeps all output nibbles at most 9, and keeps the hidden
fraction in `[0, 10^fuel * B)` when it starts in `[0, B)`. -/
theorem recover_value_preserved_bounded
    (upperLimit m : UInt128) (hUL : upperLimit.toNat * 10 < 2 ^ 128)
    (e : Int) (g : Guard) (fuel : ℕ)
    (hm_pos : 1 ≤ m.toNat)
    (hall : allNibblesAtMost9 g.digits_)
    (x B : ℚ) (hB_pos : 0 < B)
    (hx_nn : 0 ≤ x) (hx_lt : x < B) :
    ∃ x_after : ℚ,
      0 ≤ x_after ∧ x_after < (10 : ℚ) ^ fuel * B ∧
      allNibblesAtMost9 (Number.operator_add.recover upperLimit m e g fuel).2.2.digits_ ∧
      ((m.toNat : ℚ)
          - ((decimalValue g.digits_ : ℚ) / 10 ^ 16 + x)) * (10 : ℚ) ^ e
        = (((Number.operator_add.recover upperLimit m e g fuel).1.toNat : ℚ)
            - ((decimalValue (Number.operator_add.recover upperLimit m e g fuel).2.2.digits_ : ℚ)
                  / 10 ^ 16 + x_after))
          * (10 : ℚ) ^ ((Number.operator_add.recover upperLimit m e g fuel).2.1) := by
  induction m, e, g, fuel using Number.operator_add.recover.induct (upperLimit := upperLimit)
    generalizing x B with
  | case1 m e g =>
    refine ⟨x, hx_nn, ?_, ?_, ?_⟩
    · -- x < B = 1 * B = 10^0 * B
      rw [pow_zero, one_mul]; exact hx_lt
    · rw [recover_noop_zero]; exact hall
    · rw [recover_noop_zero]
  | case2 m e g fuel hcond g' d hpop IH =>
    obtain ⟨h1, h2⟩ := hcond
    rw [recover_step h1 h2]
    have hpop1 : g.pop.1 = g' := by rw [hpop]
    have hpop2 : g.pop.2 = d := by rw [hpop]
    rw [hpop1, hpop2]
    have hd_le_9 : d.toNat ≤ 9 := by
      rw [← hpop2]; exact pop_digit_le_9 g hall
    have hd_le_mt : toUInt128 d ≤ m * 10 := by
      rw [← hpop2]
      exact pop_digit_le_mul_ten_of_pos128 hUL hm_pos h1 (pop_digit_le_9 g hall)
    have hm_new_nat : (m * 10 - toUInt128 d).toNat = m.toNat * 10 - d.toNat :=
      recover_step_mantissa_nat128 hUL h1 hd_le_mt
    have hm10ge : 10 ≤ m.toNat * 10 := by nlinarith
    have hm_new_pos : 1 ≤ (m * 10 - toUInt128 d).toNat := by
      rw [hm_new_nat]; omega
    have hall_eq : allNibblesAtMost9 g'.digits_ := by
      rw [← hpop1]; exact allNibblesAtMost9_pop g hall
    -- New hidden fraction: 10 * x. New bound: 10 * B.
    have h10x_nn : 0 ≤ 10 * x := by linarith
    have h10B_pos : 0 < 10 * B := by linarith
    have h10x_lt : 10 * x < 10 * B := by linarith
    obtain ⟨x_after, hxa_nn, hxa_lt, hall_after, heq_IH⟩ :=
      IH hm_new_pos hall_eq (10 * x) (10 * B) h10B_pos h10x_nn h10x_lt
    refine ⟨x_after, hxa_nn, ?_, hall_after, ?_⟩
    · -- 10^fuel * (10 * B) = 10^(fuel+1) * B
      have hpow_eq : (10 : ℚ) ^ fuel * (10 * B) = (10 : ℚ) ^ (fuel + 1) * B := by
        rw [pow_succ]; ring
      have hxa_lt' : x_after < (10 : ℚ) ^ (fuel + 1) * B := by
        rw [← hpow_eq]; exact hxa_lt
      change x_after < (10 : ℚ) ^ (fuel + 1) * B
      exact hxa_lt'
    · -- Value equation: combine `decimalValue_pop_rat` and `recover_step_mantissa_nat128`.
      rw [← heq_IH]
      have h_dv : (decimalValue g'.digits_ : ℚ)
          = 10 * (decimalValue g.digits_ : ℚ) - (d.toNat : ℚ) * 10 ^ 16 := by
        rw [← hpop1, decimalValue_pop_rat g]
        have hd_eq : (g.pop.2.toNat : ℚ) = (nibble g.digits_ 15 : ℚ) := by
          exact_mod_cast pop_digit_eq_nibble_15 g
        rw [hpop2] at hd_eq
        linarith
      have h_mnew_q : ((m * 10 - toUInt128 d).toNat : ℚ) = (m.toNat : ℚ) * 10 - (d.toNat : ℚ) := by
        rw [hm_new_nat]
        have hle : d.toNat ≤ m.toNat * 10 := by omega
        rw [Nat.cast_sub hle]
        push_cast; ring
      rw [h_mnew_q, h_dv]
      have he_pow : (10 : ℚ) ^ e = (10 : ℚ) ^ (e - 1) * 10 := by
        rw [show e = (e - 1) + 1 from by ring, zpow_add₀ (by norm_num : (10 : ℚ) ≠ 0)]
        simp
      rw [he_pow]
      field_simp
      ring
  | case3 m e g fuel hcond =>
    refine ⟨x, hx_nn, ?_, ?_, ?_⟩
    · -- x < B ≤ 10^(fuel + 1) * B, since 10^k ≥ 1 (this case of `recover.induct` has fuel
      -- `fuel + 1`).
      have h1 : (1 : ℚ) ≤ (10 : ℚ) ^ (fuel + 1) :=
        one_le_pow₀ (by norm_num : (1 : ℚ) ≤ 10)
      change x < (10 : ℚ) ^ (fuel + 1) * B
      nlinarith
    · have hprop : ¬ (m < upperLimit ∧ ¬ g.empty) := hcond
      rw [recover_noop_exit hprop]; exact hall
    · have hprop : ¬ (m < upperLimit ∧ ¬ g.empty) := hcond
      rw [recover_noop_exit hprop]

set_option maxHeartbeats 800000 in
-- repeated `Number.operator_add.recover upperLimit m e g fuel` terms are expensive to elaborate
/-- `recover` preserves the diff-sign value `(m - f_g) * 10^e` with an output residue in `[0, 1 + 10^fuel / 10^16)`.
The slack `10^fuel / 10^16` is the worst-case growth of the hidden fraction over `fuel` pops. -/
theorem recover_value_in_unit_interval
    {upperLimit m : UInt128} (hUL : upperLimit.toNat * 10 < 2 ^ 128)
    {e : Int} {g : Guard} {fuel : ℕ}
    (hm_pos : 1 ≤ m.toNat)
    {f_g : ℚ} (hg : represents g f_g) :
    ∃ f_g_after : ℚ,
      0 ≤ f_g_after ∧
      f_g_after < 1 + (10 : ℚ) ^ fuel / 10 ^ 16 ∧
      ((m.toNat : ℚ) - f_g) * (10 : ℚ) ^ e
        = (((Number.operator_add.recover upperLimit m e g fuel).1.toNat : ℚ) - f_g_after)
          * (10 : ℚ) ^ ((Number.operator_add.recover upperLimit m e g fuel).2.1) := by
  obtain ⟨x, hx_nn, hx_lt, hf_eq, _, hall⟩ := hg
  have hB_pos : (0 : ℚ) < 1 / 10 ^ 16 := by positivity
  obtain ⟨x_after, hxa_nn, hxa_lt, hall_after, heq⟩ :=
    recover_value_preserved_bounded upperLimit m hUL e g fuel hm_pos hall x (1 / 10 ^ 16) hB_pos hx_nn hx_lt
  refine ⟨(decimalValue (Number.operator_add.recover upperLimit m e g fuel).2.2.digits_ : ℚ) / 10 ^ 16
          + x_after, ?_, ?_, ?_⟩
  · -- 0 ≤ residue
    have h16_pos : (0 : ℚ) < 10 ^ 16 := by positivity
    have h_dv_nn :
        (0 : ℚ) ≤ (decimalValue (Number.operator_add.recover upperLimit m e g fuel).2.2.digits_ : ℚ) / 10 ^ 16 := by
      apply div_nonneg
      · exact_mod_cast Nat.zero_le _
      · linarith
    linarith
  · -- residue < 1 + 10^fuel / 10^16
    have h16_pos : (0 : ℚ) < 10 ^ 16 := by positivity
    have h_nat : decimalValue (Number.operator_add.recover upperLimit m e g fuel).2.2.digits_ < 10 ^ 16 :=
      decimalValue_lt_pow_16 hall_after
    have h_q :
        (decimalValue (Number.operator_add.recover upperLimit m e g fuel).2.2.digits_ : ℚ) < (10 : ℚ) ^ 16 := by
      exact_mod_cast h_nat
    have h_dv_lt :
        (decimalValue (Number.operator_add.recover upperLimit m e g fuel).2.2.digits_ : ℚ) / 10 ^ 16 < 1 := by
      rw [div_lt_iff₀ h16_pos]; linarith
    have h_xa_eq : (10 : ℚ) ^ fuel * (1 / 10 ^ 16) = (10 : ℚ) ^ fuel / 10 ^ 16 := by ring
    rw [h_xa_eq] at hxa_lt
    linarith
  · rw [hf_eq]
    exact heq

set_option maxHeartbeats 800000 in
-- functional induction over `recover` with branch reindexing is heartbeat-heavy
/-- Like `recover_value_preserved_bounded`, but the hidden-fraction bound widens by `10^k` where `k = e - e_out`
is the actual number of pops, not `10^fuel`. A positive hidden fraction stays positive. -/
theorem recover_value_preserved_tight
    (upperLimit m : UInt128) (hUL : upperLimit.toNat * 10 < 2 ^ 128)
    (e : Int) (g : Guard) (fuel : ℕ)
    (hm_pos : 1 ≤ m.toNat)
    (hall : allNibblesAtMost9 g.digits_)
    (x B : ℚ) (hB_pos : 0 < B)
    (hx_nn : 0 ≤ x) (hx_lt : x < B) :
    ∃ x_after : ℚ, ∃ k : ℕ,
      k ≤ fuel ∧
      (Number.operator_add.recover upperLimit m e g fuel).2.1 = e - k ∧
      0 ≤ x_after ∧ x_after < (10 : ℚ) ^ k * B ∧
      (0 < x → 0 < x_after) ∧
      allNibblesAtMost9 (Number.operator_add.recover upperLimit m e g fuel).2.2.digits_ ∧
      ((m.toNat : ℚ)
          - ((decimalValue g.digits_ : ℚ) / 10 ^ 16 + x)) * (10 : ℚ) ^ e
        = (((Number.operator_add.recover upperLimit m e g fuel).1.toNat : ℚ)
            - ((decimalValue (Number.operator_add.recover upperLimit m e g fuel).2.2.digits_ : ℚ)
                  / 10 ^ 16 + x_after))
          * (10 : ℚ) ^ ((Number.operator_add.recover upperLimit m e g fuel).2.1) := by
  induction m, e, g, fuel using Number.operator_add.recover.induct (upperLimit := upperLimit)
    generalizing x B with
  | case1 m e g =>
    -- fuel = 0: recover is a no-op, k = 0.
    refine ⟨x, 0, le_refl _, ?_, hx_nn, ?_, fun h => h, ?_, ?_⟩
    · rw [recover_noop_zero]; push_cast; ring
    · rw [pow_zero, one_mul]; exact hx_lt
    · rw [recover_noop_zero]; exact hall
    · rw [recover_noop_zero]
  | case2 m e g fuel hcond g' d hpop IH =>
    obtain ⟨h1, h2⟩ := hcond
    rw [recover_step h1 h2]
    have hpop1 : g.pop.1 = g' := by rw [hpop]
    have hpop2 : g.pop.2 = d := by rw [hpop]
    rw [hpop1, hpop2]
    have hd_le_9 : d.toNat ≤ 9 := by
      rw [← hpop2]; exact pop_digit_le_9 g hall
    have hd_le_mt : toUInt128 d ≤ m * 10 := by
      rw [← hpop2]
      exact pop_digit_le_mul_ten_of_pos128 hUL hm_pos h1 (pop_digit_le_9 g hall)
    have hm_new_nat : (m * 10 - toUInt128 d).toNat = m.toNat * 10 - d.toNat :=
      recover_step_mantissa_nat128 hUL h1 hd_le_mt
    have hm10ge : 10 ≤ m.toNat * 10 := by nlinarith
    have hm_new_pos : 1 ≤ (m * 10 - toUInt128 d).toNat := by
      rw [hm_new_nat]; omega
    have hall_eq : allNibblesAtMost9 g'.digits_ := by
      rw [← hpop1]; exact allNibblesAtMost9_pop g hall
    have h10x_nn : 0 ≤ 10 * x := by linarith
    have h10B_pos : 0 < 10 * B := by linarith
    have h10x_lt : 10 * x < 10 * B := by linarith
    obtain ⟨x_after, k', hk'_le, hk'_eq, hxa_nn, hxa_lt, hxa_pos, hall_after, heq_IH⟩ :=
      IH hm_new_pos hall_eq (10 * x) (10 * B) h10B_pos h10x_nn h10x_lt
    refine ⟨x_after, k' + 1, by omega, ?_, hxa_nn, ?_,
      fun hx => hxa_pos (by linarith), hall_after, ?_⟩
    · -- e_out = (e - 1) - k' = e - (k' + 1)
      rw [hk'_eq]; push_cast; ring
    · -- 10^k' * (10 * B) = 10^(k' + 1) * B
      have hpow_eq : (10 : ℚ) ^ k' * (10 * B) = (10 : ℚ) ^ (k' + 1) * B := by
        rw [pow_succ]; ring
      rw [← hpow_eq]; exact hxa_lt
    · -- Value equation: same algebra as in `recover_value_preserved_bounded`.
      rw [← heq_IH]
      have h_dv : (decimalValue g'.digits_ : ℚ)
          = 10 * (decimalValue g.digits_ : ℚ) - (d.toNat : ℚ) * 10 ^ 16 := by
        rw [← hpop1, decimalValue_pop_rat g]
        have hd_eq : (g.pop.2.toNat : ℚ) = (nibble g.digits_ 15 : ℚ) := by
          exact_mod_cast pop_digit_eq_nibble_15 g
        rw [hpop2] at hd_eq
        linarith
      have h_mnew_q : ((m * 10 - toUInt128 d).toNat : ℚ) = (m.toNat : ℚ) * 10 - (d.toNat : ℚ) := by
        rw [hm_new_nat]
        have hle : d.toNat ≤ m.toNat * 10 := by omega
        rw [Nat.cast_sub hle]
        push_cast; ring
      rw [h_mnew_q, h_dv]
      have he_pow : (10 : ℚ) ^ e = (10 : ℚ) ^ (e - 1) * 10 := by
        rw [show e = (e - 1) + 1 from by ring, zpow_add₀ (by norm_num : (10 : ℚ) ≠ 0)]
        simp
      rw [he_pow]
      field_simp
      ring
  | case3 m e g fuel hcond =>
    -- Exit at the start: k = 0, bound is x < B = 10^0 * B.
    have hprop : ¬ (m < upperLimit ∧ ¬ g.empty) := hcond
    refine ⟨x, 0, Nat.zero_le _, ?_, hx_nn, ?_, fun h => h, ?_, ?_⟩
    · rw [recover_noop_exit hprop]; push_cast; ring
    · rw [pow_zero, one_mul]; exact hx_lt
    · rw [recover_noop_exit hprop]; exact hall
    · rw [recover_noop_exit hprop]

/-- If `10^J` divides the guard's decimal value on entry, then after `k = e - e_out` pops `10^(J + k)` divides
it, since each pop shifts the digits up one place and leaves a zero at the bottom. -/
theorem recover_decimalValue_dvd
    (upperLimit m : UInt128) (hUL : upperLimit.toNat * 10 < 2 ^ 128)
    (e : Int) (g : Guard) (fuel : ℕ)
    (hm_pos : 1 ≤ m.toNat)
    (hall : allNibblesAtMost9 g.digits_)
    (J : ℕ) (hdvd : 10 ^ J ∣ decimalValue g.digits_) :
    ∃ k : ℕ,
      (Number.operator_add.recover upperLimit m e g fuel).2.1 = e - k ∧
      10 ^ (J + k) ∣ decimalValue (Number.operator_add.recover upperLimit m e g fuel).2.2.digits_ := by
  induction m, e, g, fuel using Number.operator_add.recover.induct (upperLimit := upperLimit)
    generalizing J with
  | case1 m e g =>
    refine ⟨0, ?_, ?_⟩
    · rw [recover_noop_zero]; push_cast; ring
    · rw [recover_noop_zero, Nat.add_zero]; exact hdvd
  | case2 m e g fuel hcond g' d hpop IH =>
    obtain ⟨h1, h2⟩ := hcond
    rw [recover_step h1 h2]
    have hpop1 : g.pop.1 = g' := by rw [hpop]
    have hpop2 : g.pop.2 = d := by rw [hpop]
    rw [hpop1, hpop2]
    have hd_le_mt : toUInt128 d ≤ m * 10 := by
      rw [← hpop2]
      exact pop_digit_le_mul_ten_of_pos128 hUL hm_pos h1 (pop_digit_le_9 g hall)
    have hm_new_nat : (m * 10 - toUInt128 d).toNat = m.toNat * 10 - d.toNat :=
      recover_step_mantissa_nat128 hUL h1 hd_le_mt
    have hd_le_9 : d.toNat ≤ 9 := by
      rw [← hpop2]; exact pop_digit_le_9 g hall
    have hm10ge : 10 ≤ m.toNat * 10 := by nlinarith
    have hm_new_pos : 1 ≤ (m * 10 - toUInt128 d).toNat := by
      rw [hm_new_nat]; omega
    have hall_eq : allNibblesAtMost9 g'.digits_ := by
      rw [← hpop1]; exact allNibblesAtMost9_pop g hall
    -- The popped guard's decimal value gains one more factor of 10.
    have hdvd' : 10 ^ (J + 1) ∣ decimalValue g'.digits_ := by
      have heq := decimalValue_pop_eq g
      rw [hpop1] at heq
      by_cases hJ : J ≤ 15
      · have h10dv : 10 ^ (J + 1) ∣ 10 * decimalValue g.digits_ := by
          obtain ⟨c, hc⟩ := hdvd
          exact ⟨c, by rw [hc, pow_succ]; ring⟩
        have hd16 : 10 ^ (J + 1) ∣ nibble g.digits_ 15 * 10 ^ 16 :=
          Dvd.dvd.mul_left (pow_dvd_pow 10 (by omega)) _
        have hsub : decimalValue g'.digits_
            = 10 * decimalValue g.digits_ - nibble g.digits_ 15 * 10 ^ 16 := by omega
        rw [hsub]
        exact Nat.dvd_sub h10dv hd16
      · push Not at hJ
        have hlt : decimalValue g.digits_ < 10 ^ 16 := decimalValue_lt_pow_16 hall
        have hdv0 : decimalValue g.digits_ = 0 := by
          rcases Nat.eq_zero_or_pos (decimalValue g.digits_) with h | h
          · exact h
          · have hge : 10 ^ J ≤ decimalValue g.digits_ := Nat.le_of_dvd h hdvd
            have h16J : (10 : ℕ) ^ 16 ≤ 10 ^ J := Nat.pow_le_pow_right (by norm_num) (by omega)
            omega
        have hdv'0 : decimalValue g'.digits_ = 0 := by omega
        rw [hdv'0]
        exact dvd_zero _
    obtain ⟨k', hk'_eq, hk'_dvd⟩ := IH hm_new_pos hall_eq (J + 1) hdvd'
    refine ⟨k' + 1, ?_, ?_⟩
    · rw [hk'_eq]; push_cast; ring
    · rw [show J + (k' + 1) = J + 1 + k' from by ring]; exact hk'_dvd
  | case3 m e g fuel hcond =>
    have hprop : ¬ (m < upperLimit ∧ ¬ g.empty) := hcond
    refine ⟨0, ?_, ?_⟩
    · rw [recover_noop_exit hprop]; push_cast; ring
    · rw [recover_noop_exit hprop, Nat.add_zero]; exact hdvd

set_option maxHeartbeats 1600000 in
-- repeated `Number.operator_add.recover upperLimit m e g fuel` terms are expensive to elaborate
/-- After `k = e - e_out` pops, `recover` preserves the diff-sign value with a residue in `[0, 1 + 10^k / 10^16)`,
below 1 when `k ≤ 16` and positive when `xbit_` is set. The loop met its exit condition or ran `fuel` pops. -/
theorem recover_value_in_unit_interval_at_exit
    (upperLimit m : UInt128) (hUL : upperLimit.toNat * 10 < 2 ^ 128)
    (e : Int) (g : Guard) (f_g : ℚ) (fuel : ℕ)
    (_hf_g_nn : 0 ≤ f_g) (_hf_g_lt : f_g < 1)
    (hrep : represents g f_g)
    (hm_pos : 1 ≤ m.toNat) :
    let result := Number.operator_add.recover upperLimit m e g fuel
    ∃ f_g_after : ℚ, ∃ k : ℕ,
      k ≤ fuel ∧
      result.2.1 = e - k ∧
      0 ≤ f_g_after ∧
      f_g_after < 1 + (10 : ℚ) ^ k / 10 ^ 16 ∧
      (k ≤ 16 → f_g_after < 1) ∧
      (g.xbit_ = true → 0 < f_g_after) ∧
      ((m.toNat : ℚ) - f_g) * (10 : ℚ) ^ e
        = ((result.1.toNat : ℚ) - f_g_after) * (10 : ℚ) ^ result.2.1
      ∧ ((¬ (result.1 < upperLimit ∧ ¬ result.2.2.empty))
         ∨ k = fuel) := by
  obtain ⟨x, hx_nn, hx_lt, hf_eq, hxbit_iff, hall⟩ := hrep
  have hB_pos : (0 : ℚ) < 1 / 10 ^ 16 := by positivity
  obtain ⟨x_after, k, hk_le, hk_eq, hxa_nn, hxa_lt, hxa_pos, hall_after, heq⟩ :=
    recover_value_preserved_tight upperLimit m hUL e g fuel hm_pos hall x (1 / 10 ^ 16) hB_pos hx_nn hx_lt
  obtain ⟨k₂, hk₂_eq, hk₂_dvd⟩ :=
    recover_decimalValue_dvd upperLimit m hUL e g fuel hm_pos hall 0
      (by rw [pow_zero]; exact one_dvd _)
  have hkk : k₂ = k := by
    rw [hk_eq] at hk₂_eq
    omega
  rw [Nat.zero_add, hkk] at hk₂_dvd
  refine ⟨(decimalValue (Number.operator_add.recover upperLimit m e g fuel).2.2.digits_ : ℚ) / 10 ^ 16
            + x_after, k, hk_le, hk_eq, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- 0 ≤ residue
    have h16_pos : (0 : ℚ) < 10 ^ 16 := by positivity
    have h_dv_nn :
        (0 : ℚ) ≤ (decimalValue (Number.operator_add.recover upperLimit m e g fuel).2.2.digits_ : ℚ) / 10 ^ 16 := by
      apply div_nonneg
      · exact_mod_cast Nat.zero_le _
      · linarith
    linarith
  · -- residue < 1 + 10^k / 10^16.
    have h16_pos : (0 : ℚ) < 10 ^ 16 := by positivity
    have h_nat : decimalValue (Number.operator_add.recover upperLimit m e g fuel).2.2.digits_ < 10 ^ 16 :=
      decimalValue_lt_pow_16 hall_after
    have h_q :
        (decimalValue (Number.operator_add.recover upperLimit m e g fuel).2.2.digits_ : ℚ) < (10 : ℚ) ^ 16 := by
      exact_mod_cast h_nat
    have h_dv_lt :
        (decimalValue (Number.operator_add.recover upperLimit m e g fuel).2.2.digits_ : ℚ) / 10 ^ 16 < 1 := by
      rw [div_lt_iff₀ h16_pos]; linarith
    have h_xa_eq : (10 : ℚ) ^ k * (1 / 10 ^ 16) = (10 : ℚ) ^ k / 10 ^ 16 := by ring
    rw [h_xa_eq] at hxa_lt
    linarith
  · -- k ≤ 16 → residue < 1: the bottom k decimal digits are zeros, capping the
    -- decimal part at 1 - 10^k/10^16, which absorbs the hidden fraction's growth.
    intro hk16
    obtain ⟨c, hc⟩ := hk₂_dvd
    have hlt_nat : decimalValue (Number.operator_add.recover upperLimit m e g fuel).2.2.digits_ < 10 ^ 16 :=
      decimalValue_lt_pow_16 hall_after
    have hsplit : (10 : ℕ) ^ 16 = 10 ^ k * 10 ^ (16 - k) := by
      rw [← pow_add]; congr 1; omega
    have hc_lt : c < 10 ^ (16 - k) := by
      by_contra hge
      push Not at hge
      have h2 := Nat.mul_le_mul_left (10 ^ k) hge
      omega
    have hdv_add : decimalValue (Number.operator_add.recover upperLimit m e g fuel).2.2.digits_
        + 10 ^ k ≤ 10 ^ 16 := by
      have h3 := Nat.mul_le_mul_left (10 ^ k) (by omega : c + 1 ≤ 10 ^ (16 - k))
      rw [Nat.mul_add, mul_one] at h3
      omega
    have h16_pos : (0 : ℚ) < 10 ^ 16 := by positivity
    have hdv_q :
        (decimalValue (Number.operator_add.recover upperLimit m e g fuel).2.2.digits_ : ℚ)
          + (10 : ℚ) ^ k ≤ 10 ^ 16 := by
      have hcast : ((decimalValue (Number.operator_add.recover upperLimit m e g fuel).2.2.digits_
          + 10 ^ k : ℕ) : ℚ) ≤ ((10 ^ 16 : ℕ) : ℚ) := by
        exact_mod_cast hdv_add
      push_cast at hcast
      linarith
    have h_xa_eq : (10 : ℚ) ^ k * (1 / 10 ^ 16) = (10 : ℚ) ^ k / 10 ^ 16 := by ring
    rw [h_xa_eq] at hxa_lt
    have hsum_le :
        (decimalValue (Number.operator_add.recover upperLimit m e g fuel).2.2.digits_ : ℚ) / 10 ^ 16
          + (10 : ℚ) ^ k / 10 ^ 16 ≤ 1 := by
      rw [← add_div, div_le_one h16_pos]
      exact hdv_q
    linarith
  · -- xbit set: the hidden fraction is positive, so the residue is positive.
    intro hxb
    have hx_pos : 0 < x := hxbit_iff.mp hxb
    have h16_pos : (0 : ℚ) < 10 ^ 16 := by positivity
    have h_dv_nn :
        (0 : ℚ) ≤ (decimalValue (Number.operator_add.recover upperLimit m e g fuel).2.2.digits_ : ℚ) / 10 ^ 16 := by
      apply div_nonneg
      · exact_mod_cast Nat.zero_le _
      · linarith
    linarith [hxa_pos hx_pos]
  · rw [hf_eq]
    exact heq
  · -- Exit characterization
    rcases recover_output_exits_or_fuel_exhausted upperLimit m e g fuel with hexit | hfeq
    · left; exact hexit
    · right
      have : (e - fuel : ℤ) = e - k := by rw [← hfeq, ← hk_eq]
      omega

end XRPL.Model.Protocol
