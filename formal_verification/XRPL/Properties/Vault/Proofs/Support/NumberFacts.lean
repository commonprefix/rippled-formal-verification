import XRPL.Properties.Protocol.Number.Totality
import XRPL.Properties.Protocol.Number.Normalize.RoundsToRepresentable
import XRPL.Properties.Protocol.Number.ToRep.ToRep
import XRPL.Properties.Protocol.Number.Common.NumberBridge
import XRPL.Properties.Vault.Common.RoundMonotoneSatDiv
import XRPL.Properties.Vault.Common.WitnessSupport
import XRPL.Properties.Vault.Proofs.Support.Basic

/-! # `Number` facts

Facts about `Number`: rounding of the arithmetic operators, `to_rep`, `truncate`, signs. -/

namespace XRPL.Model.Protocol

/-- **Cap bounds the adjusted `Number.exponent`.** A normalized nonnegative
`Number` whose value fits `2 ^ 63 - 1` has a nonpositive `Number.exponent`. When
the mantissa exceeds `maxRep` (so the accessor bumps the exponent by one), a
nonnegative raw exponent would already push the value above `maxRep = 2 ^ 63 - 1`,
so the raw exponent is at most `-1` and the bumped exponent stays nonpositive. -/
lemma Number.exponent_fn_le_zero_of_cap (n : Number) (hnorm : n.isNormalized)
    (hneg : n.negative_ = false) (hcap : n.toRat ≤ 2 ^ 63 - 1) :
    n.exponent ≤ 0 := by
  have htoRat : n.toRat = (n.mantissa_.toNat : ℚ) * (10 : ℚ) ^ n.exponent_ :=
    Number.toRat_of_nonneg n hneg
  rcases hnorm with hz | ⟨hmlo, _hmhi, _, _hexp_lo, _hexp_hi⟩
  · rw [hz]; decide
  · unfold Number.exponent
    by_cases hgt : n.mantissa_ > maxRep
    · rw [if_pos hgt]
      by_contra hcon
      push_neg at hcon
      have hexp_nn : (0 : ℤ) ≤ n.exponent_ := by omega
      have hpow_ge1 : (1 : ℚ) ≤ (10 : ℚ) ^ n.exponent_ := by
        rw [show n.exponent_ = ((n.exponent_.toNat : ℤ)) from by omega, zpow_natCast]
        exact one_le_pow₀ (by norm_num)
      have hm_ge : (9223372036854775808 : ℚ) ≤ (n.mantissa_.toNat : ℚ) := by
        have hlt := UInt64.lt_iff_toNat_lt.mp hgt
        rw [maxRep_val] at hlt
        have h2 : (9223372036854775808 : ℕ) ≤ n.mantissa_.toNat := by omega
        exact_mod_cast h2
      have hge : (9223372036854775808 : ℚ) ≤ n.toRat := by
        rw [htoRat]
        calc (9223372036854775808 : ℚ) = 9223372036854775808 * 1 := by ring
          _ ≤ (n.mantissa_.toNat : ℚ) * (10 : ℚ) ^ n.exponent_ :=
              mul_le_mul hm_ge hpow_ge1 (by norm_num) (by positivity)
      have : (9223372036854775808 : ℚ) ≤ 2 ^ 63 - 1 := le_trans hge hcap
      norm_num at this
    · rw [if_neg hgt]
      by_contra hcon
      push_neg at hcon
      have hm_nat : (1000000000000000000 : ℕ) ≤ n.mantissa_.toNat := by
        have := UInt64.le_iff_toNat_le.mp hmlo; rwa [largeRange_min_val] at this
      have hm_q : (1000000000000000000 : ℚ) ≤ (n.mantissa_.toNat : ℚ) := by exact_mod_cast hm_nat
      have hexp1 : 1 ≤ n.exponent_.toNat := by omega
      have hpow : (10 : ℚ) ≤ 10 ^ n.exponent_.toNat := by
        calc (10 : ℚ) = 10 ^ 1 := (pow_one 10).symm
          _ ≤ 10 ^ n.exponent_.toNat := pow_le_pow_right₀ (by norm_num) hexp1
      have hge : (10000000000000000000 : ℚ) ≤ n.toRat := by
        rw [htoRat, show n.exponent_ = (n.exponent_.toNat : ℤ) from by omega, zpow_natCast]
        calc (10000000000000000000 : ℚ) = 1000000000000000000 * 10 := by norm_num
          _ ≤ (n.mantissa_.toNat : ℚ) * 10 ^ n.exponent_.toNat :=
              mul_le_mul hm_q hpow (by norm_num) (by positivity)
      have : (10000000000000000000 : ℚ) ≤ 2 ^ 63 - 1 := le_trans hge hcap
      norm_num at this

/-- **Forward totality of `Number.to_rep` on a nonnegative, small-exponent operand.**
A nonnegative `Number` with nonpositive adjusted `Number.exponent` converts to a
signed `Int64` without error. The `grow` overflow is unreachable (`offset ≤ 0`, so
`grow` is entered only at `offset = 0`, returning its input); the final
rounding-overflow is unreachable too (at `offset = 0` the empty start guard never
rounds up, and at `offset < 0` the floor-divide by at least ten lands strictly below
`maxRep`, so the round-up bump stays in range). -/
lemma Number.to_rep_ok_of_nonneg_exp_nonpos (n : Number) (mode : rounding_mode)
    (hneg : n.negative_ = false) (hexp : n.exponent ≤ 0) :
    ∃ r : Int64, n.to_rep mode = .ok r := by
  unfold Number.to_rep
  simp only
  by_cases hz : (n.mantissa == 0) = true
  · exact ⟨0, by rw [if_pos hz]⟩
  · rw [if_neg hz]
    have hD0_range : 0 ≤ n.mantissa.toInt ∧ n.mantissa.toInt ≤ (maxRep.toNat : ℤ) := by
      unfold Number.mantissa
      rw [if_neg (by rw [hneg]; decide)]
      by_cases hgt : n.mantissa_ > maxRep
      · rw [if_pos hgt]
        have hlt : (n.mantissa_ / 10).toNat < 2 ^ 63 := by
          rw [UInt64.toNat_div, uint64_ten_toNat]
          have := UInt64.toNat_lt_size n.mantissa_
          rw [uint64_size_val] at this; omega
        rw [UInt64.toInt64_toInt_of_lt _ hlt]
        refine ⟨Int.natCast_nonneg _, ?_⟩
        rw [UInt64.toNat_div, uint64_ten_toNat, maxRep_val]
        have := UInt64.toNat_lt_size n.mantissa_
        rw [uint64_size_val] at this; omega
      · rw [if_neg hgt]
        have hle : n.mantissa_.toNat ≤ maxRep.toNat :=
          UInt64.le_iff_toNat_le.mp (UInt64.not_lt.mp hgt)
        have hlt : n.mantissa_.toNat < 2 ^ 63 := by rw [maxRep_val] at hle; omega
        rw [UInt64.toInt64_toInt_of_lt _ hlt]
        exact ⟨Int.natCast_nonneg _, by exact_mod_cast hle⟩
    rw [hneg]
    simp only [Bool.false_eq_true, if_false]
    by_cases hexplt : n.exponent < 0
    · have hge : ¬ n.exponent ≥ 0 := by omega
      rw [if_pos hexplt, if_neg hge]
      simp only
      set sp := Number.to_rep.shift n.mantissa n.exponent Guard.new with hspdef
      have hDf : sp.1.toInt = n.mantissa.toInt / 10 ^ (-n.exponent).toNat := by
        have := shift_fst_eq n.mantissa n.exponent Guard.new hD0_range.1
        rwa [← hspdef] at this
      have hsp_nn : 0 ≤ sp.1.toInt := by
        rw [hDf]; exact Int.ediv_nonneg hD0_range.1 (by positivity)
      have hsp_lt : sp.1.toInt < (maxRep.toNat : ℤ) := by
        have hk_ne : (10 : ℤ) ^ (-n.exponent).toNat ≠ 0 := by positivity
        have hmul : sp.1.toInt * 10 ^ (-n.exponent).toNat ≤ n.mantissa.toInt := by
          rw [hDf]; exact Int.ediv_mul_le _ hk_ne
        have h10le : (10 : ℤ) ≤ 10 ^ (-n.exponent).toNat := by
          calc (10 : ℤ) = 10 ^ 1 := by ring
            _ ≤ 10 ^ (-n.exponent).toNat := pow_le_pow_right₀ (by norm_num) (by omega)
        have hmul10 : sp.1.toInt * 10 ≤ n.mantissa.toInt :=
          le_trans (mul_le_mul_of_nonneg_left h10le hsp_nn) hmul
        have hle := hD0_range.2
        rw [maxRep_val] at hle ⊢
        omega
      have hsp_lt_u64 : sp.1.toUInt64.toNat < maxRep.toNat := by
        have hnat := toUInt64_toNat_of_nonneg sp.1 hsp_nn; omega
      rw [pushOverflow_noop_of_lt_maxRep hsp_lt_u64 sp.2 mode]
      by_cases hb : (sp.2.round mode == 1 || sp.2.round mode == 0 && sp.1 % 2 == 1) = true
      · rw [if_pos hb, if_neg (show ¬ sp.1 ≥ maxRep.toInt64 from fun hc => by
          have := Int64.le_iff_toInt_le.mp hc
          rw [show maxRep.toInt64.toInt = (maxRep.toNat : ℤ) from by decide] at this
          omega)]
        exact ⟨_, rfl⟩
      · rw [if_neg hb, if_neg (show ¬ (maxRep.toInt64 < sp.1 ∧ sp.1 < maxRepUp.toInt64) from
          fun hc => by
            have := Int64.lt_iff_toInt_lt.mp hc.1
            rw [show maxRep.toInt64.toInt = (maxRep.toNat : ℤ) from by decide] at this
            omega)]
        exact ⟨_, rfl⟩
    · have hexpge : n.exponent ≥ 0 := not_lt.mp hexplt
      rw [if_neg hexplt, if_pos hexpge]
      have hgrow0 : Number.to_rep.grow n.mantissa n.exponent = .ok n.mantissa := by
        rw [Number.to_rep.grow, if_neg (show ¬ n.exponent > 0 from by omega)]
      rw [hgrow0]
      simp only
      have h_u64 : n.mantissa.toUInt64.toNat ≤ maxRep.toNat :=
        toUInt64_toNat_le_maxRep n.mantissa hD0_range.1 hD0_range.2
      rw [pushOverflow_noop_of_le_maxRep_of_empty h_u64 Guard.new mode (by decide)]
      rw [show Guard.new.round mode = -2 from by
        have := start_guard_round mode false; simpa using this]
      rw [if_neg (show ¬ ((-2 : Int) == 1 || (-2 : Int) == 0 && n.mantissa % 2 == 1) = true
        from by simp)]
      rw [if_neg (show ¬ (maxRep.toInt64 < n.mantissa ∧ n.mantissa < maxRepUp.toInt64) from
        fun hc => by
          have := Int64.lt_iff_toInt_lt.mp hc.1
          rw [show maxRep.toInt64.toInt = (maxRep.toNat : ℤ) from by decide] at this
          omega)]
      exact ⟨_, rfl⟩

/-- `to_rep` of a sign-cleared `Number` returns an integer in `[0, maxRep]`. -/
lemma Number.to_rep_nonneg_range (n : Number) (mode : rounding_mode) (r : Int64)
    (hneg : n.negative_ = false)
    (hok : n.to_rep mode = .ok r) :
    0 ≤ r.toInt ∧ r.toInt ≤ (maxRep.toNat : ℤ) := by
  unfold Number.to_rep at hok
  simp only at hok
  by_cases hz : (n.mantissa == 0) = true
  · rw [if_pos hz] at hok
    have hr : r = 0 := by injection hok with h; exact h.symm
    rw [hr]
    refine ⟨by decide, ?_⟩
    rw [show (0 : Int64).toInt = 0 from by decide, maxRep_val]
    norm_num
  · rw [if_neg hz] at hok
    -- the start magnitude is in [0, maxRep]
    have hD0_range : 0 ≤ n.mantissa.toInt ∧ n.mantissa.toInt ≤ (maxRep.toNat : ℤ) := by
      unfold Number.mantissa
      rw [if_neg (by rw [hneg]; decide)]
      by_cases hgt : n.mantissa_ > maxRep
      · rw [if_pos hgt]
        have hlt : (n.mantissa_ / 10).toNat < 2 ^ 63 := by
          rw [UInt64.toNat_div, uint64_ten_toNat]
          have := UInt64.toNat_lt_size n.mantissa_
          rw [uint64_size_val] at this
          omega
        rw [UInt64.toInt64_toInt_of_lt _ hlt]
        constructor
        · exact Int.natCast_nonneg _
        · rw [UInt64.toNat_div, uint64_ten_toNat, maxRep_val]
          have := UInt64.toNat_lt_size n.mantissa_
          rw [uint64_size_val] at this
          omega
      · rw [if_neg hgt]
        have hle : n.mantissa_.toNat ≤ maxRep.toNat := by
          have := UInt64.le_iff_toNat_le.mp (UInt64.not_lt.mp hgt)
          exact this
        have hlt : n.mantissa_.toNat < 2 ^ 63 := by rw [maxRep_val] at hle; omega
        rw [UInt64.toInt64_toInt_of_lt _ hlt]
        exact ⟨Int.natCast_nonneg _, by exact_mod_cast hle⟩
    rw [hneg] at hok
    simp only [Bool.false_eq_true, if_false] at hok
    by_cases hexp : n.exponent < 0
    · have hge : ¬ n.exponent ≥ 0 := by omega
      rw [if_pos hexp, if_neg hge] at hok
      simp only at hok
      set sp := Number.to_rep.shift n.mantissa n.exponent Guard.new with hspdef
      have hDf := shift_fst_eq n.mantissa n.exponent Guard.new hD0_range.1
      rw [← hspdef] at hDf
      have hsp_nn : 0 ≤ sp.1.toInt := by
        rw [hDf]; exact Int.ediv_nonneg hD0_range.1 (by positivity)
      have hsp_le : sp.1.toInt ≤ (maxRep.toNat : ℤ) := by
        rw [hDf]
        calc n.mantissa.toInt / 10 ^ (-n.exponent).toNat ≤ n.mantissa.toInt :=
              Int.ediv_le_self _ hD0_range.1
          _ ≤ (maxRep.toNat : ℤ) := hD0_range.2
      have h_sp1_u64 : sp.1.toUInt64.toNat ≤ maxRep.toNat :=
        toUInt64_toNat_le_maxRep sp.1 hsp_nn hsp_le
      by_cases hcusp : maxRep ≤ sp.1.toUInt64 ∧ sp.1.toUInt64 < maxRepUp
      · -- `pushOverflow` may push a digit, but the bounds argument below is uniform:
        -- the branch analysis only needs the round decision, handled per case.
        have hsp_eq : sp.1.toInt = (maxRep.toNat : ℤ) := by
          have h1 := UInt64.le_iff_toNat_le.mp hcusp.1
          have h2 : (sp.1.toUInt64.toNat : ℤ) = sp.1.toInt := toUInt64_toNat_of_nonneg sp.1 hsp_nn
          omega
        rcases hb : ((sp.2.pushOverflow sp.1.toUInt64 mode).round mode == 1
            || ((sp.2.pushOverflow sp.1.toUInt64 mode).round mode == 0 && sp.1 % 2 == 1)) with _ | _
        · rw [hb] at hok
          simp only [Bool.false_eq_true, if_false] at hok
          rw [if_neg (show ¬ (maxRep.toInt64 < sp.1 ∧ sp.1 < maxRepUp.toInt64) from by
            intro hc
            have hlt := (Int64.lt_iff_toInt_lt).mp hc.1
            rw [show maxRep.toInt64.toInt = (maxRep.toNat : ℤ) from by decide] at hlt
            omega)] at hok
          have hr : r = sp.1 := by injection hok with h; exact h.symm
          rw [hr]; exact ⟨hsp_nn, hsp_le⟩
        · rw [hb] at hok
          simp only [if_true] at hok
          by_cases hovf : sp.1 ≥ maxRep.toInt64
          · rw [if_pos hovf] at hok; exact absurd hok (by simp)
          · exfalso
            have := (Int64.lt_iff_toInt_lt).mp (Int64.not_le.mp hovf)
            rw [show maxRep.toInt64.toInt = (maxRep.toNat : ℤ) from by decide] at this
            omega
      · have h_sp1_lt : sp.1.toUInt64.toNat < maxRep.toNat := by
          rcases lt_or_eq_of_le h_sp1_u64 with h | h
          · exact h
          · exfalso
            apply hcusp
            constructor
            · rw [UInt64.le_iff_toNat_le, h]
            · rw [UInt64.lt_iff_toNat_lt, h]
              decide
        rw [pushOverflow_noop_of_lt_maxRep h_sp1_lt sp.2 mode] at hok
        rcases hb : (sp.2.round mode == 1 || (sp.2.round mode == 0 && sp.1 % 2 == 1)) with _ | _
        · rw [hb] at hok
          simp only [Bool.false_eq_true, if_false] at hok
          rw [if_neg (show ¬ (maxRep.toInt64 < sp.1 ∧ sp.1 < maxRepUp.toInt64) from by
            intro hc
            have hlt := (Int64.lt_iff_toInt_lt).mp hc.1
            rw [show maxRep.toInt64.toInt = (maxRep.toNat : ℤ) from by decide] at hlt
            omega)] at hok
          have hr : r = sp.1 := by injection hok with h; exact h.symm
          rw [hr]; exact ⟨hsp_nn, hsp_le⟩
        · rw [hb] at hok
          simp only [if_true] at hok
          by_cases hovf : sp.1 ≥ maxRep.toInt64
          · rw [if_pos hovf] at hok; exact absurd hok (by simp)
          · rw [if_neg hovf] at hok
            have hovf' : sp.1.toInt < (maxRep.toNat : ℤ) := by
              have := (Int64.lt_iff_toInt_lt).mp (Int64.not_le.mp hovf)
              rw [show maxRep.toInt64.toInt = (maxRep.toNat : ℤ) from by decide] at this
              exact this
            have hadd : (sp.1 + 1).toInt = sp.1.toInt + 1 := by
              rw [Int64.toInt_add, int64_one_toInt, Int.bmod_eq_iff (by norm_num)]
              rw [maxRep_val] at hovf'
              refine ⟨?_, ?_⟩ <;> push_cast <;> [omega; (rw [maxRep_val] at hsp_le; omega)]
            have hr : r = sp.1 + 1 := by injection hok with h; exact h.symm
            rw [hr, hadd]
            exact ⟨by omega, by omega⟩
    · have hexp' : n.exponent ≥ 0 := not_lt.mp hexp
      rw [if_neg hexp, if_pos hexp'] at hok
      cases hgrow : Number.to_rep.grow n.mantissa n.exponent with
      | error e => rw [hgrow] at hok; exact absurd hok (by simp)
      | ok drops =>
        rw [hgrow] at hok
        simp only at hok
        have h_drops_nn : 0 ≤ drops.toInt := by
          rw [grow_ok_eq _ drops n.exponent hD0_range.1 hgrow]
          exact mul_nonneg hD0_range.1 (by positivity)
        have h_drops_le : drops.toInt ≤ (maxRep.toNat : ℤ) :=
          grow_ok_le_maxRep _ drops n.exponent hD0_range.1 hD0_range.2 hgrow
        have h_drops_u64 : drops.toUInt64.toNat ≤ maxRep.toNat :=
          toUInt64_toNat_le_maxRep drops h_drops_nn h_drops_le
        have h_g_empty : (Guard.new).empty = true := by decide
        rw [pushOverflow_noop_of_le_maxRep_of_empty h_drops_u64 Guard.new mode h_g_empty] at hok
        rw [show Guard.new.round mode = -2 from by
          have := start_guard_round mode false
          simpa using this] at hok
        rw [if_neg (show ¬ ((-2 : Int) == 1 || (-2 : Int) == 0 && drops % 2 == 1) = true from by
          simp)] at hok
        rw [if_neg (show ¬ (maxRep.toInt64 < drops ∧ drops < maxRepUp.toInt64) from by
          intro hc
          have hlt := (Int64.lt_iff_toInt_lt).mp hc.1
          rw [show maxRep.toInt64.toInt = (maxRep.toNat : ℤ) from by decide] at hlt
          omega)] at hok
        have hr : r = drops := by injection hok with h; exact h.symm
        rw [hr]; exact ⟨h_drops_nn, h_drops_le⟩

/-- The `ofNumber` sign flag is just the operand's sign bit. -/
lemma Number.signum_neg_decide (n : Number) : decide (n.signum < 0) = n.negative_ := by
  unfold Number.signum
  rcases h : n.negative_ with _ | _
  · by_cases hm : (n.mantissa_ != 0) = true <;> simp [hm]
  · simp

/-- `truncateAux` divides out the negative exponent: the resulting value is the
natural quotient by `10 ^ (-e)`, the mantissa never grows, and a nonzero result
lands at exponent `0`. -/
lemma Number.truncateAux_val (m : UInt64) (e : Int) :
    e ≤ 0 →
    ((Number.truncateAux m e).1.toNat : ℚ) * 10 ^ (Number.truncateAux m e).2
        = ((m.toNat / 10 ^ (-e).toNat : ℕ) : ℚ) ∧
      (Number.truncateAux m e).1.toNat ≤ m.toNat ∧
      ((Number.truncateAux m e).1.toNat ≠ 0 → (Number.truncateAux m e).2 = 0) := by
  induction m, e using Number.truncateAux.induct with
  | case1 m e h ih =>
    intro he
    rw [show Number.truncateAux m e = Number.truncateAux (m / 10) (e + 1) from by
      rw [Number.truncateAux, if_pos h]]
    obtain ⟨hval, hle, hzero⟩ := ih (by omega)
    have hdiv10 : (m / 10).toNat = m.toNat / 10 := by
      rw [UInt64.toNat_div]
      rfl
    refine ⟨?_, ?_, hzero⟩
    · rw [hval]
      congr 1
      rw [hdiv10, Nat.div_div_eq_div_mul]
      congr 1
      have hd : (-e).toNat = (-(e + 1)).toNat + 1 := by omega
      rw [hd, pow_succ]
      ring
    · rw [hdiv10] at hle
      exact le_trans hle (Nat.div_le_self _ _)
  | case2 m e h =>
    intro he
    rw [show Number.truncateAux m e = (m, e) from by
      rw [Number.truncateAux, if_neg h]]
    by_cases he0 : e = 0
    · subst he0
      refine ⟨by norm_num, le_refl _, fun _ => rfl⟩
    · have hm : m = 0 := by
        rcases not_and_or.mp h with h1 | h2
        · omega
        · simpa using h2
      subst hm
      refine ⟨by norm_num, le_refl _, fun h0 => absurd rfl h0⟩

/-- **`Number.truncate` floors a non-negative normalized value.** The result is
the integer part, integer-valued, and normalized whenever nonzero. -/
lemma Number.truncate_floor (n t : Number) (hn : n.isNormalized)
    (hneg : n.negative_ = false) (hok : n.truncate = .ok t) :
    t.toRat = (⌊n.toRat⌋ : ℚ) ∧ (t.mantissa_ ≠ 0 → t.isNormalized) := by
  unfold Number.truncate at hok
  by_cases hg : n.exponent_ ≥ 0 ∨ n.mantissa_ = 0
  · rw [if_pos hg] at hok
    have ht : t = n := (Except.ok.inj hok).symm
    subst ht
    by_cases hm : t.mantissa_ = 0
    · have h0 : t.toRat = 0 := Number.toRat_eq_zero_of_mantissa_zero t hm
      rw [h0]
      norm_num
      exact fun h => absurd hm h
    · have hexp : 0 ≤ t.exponent_ := by
        rcases hg with h | h
        · exact h
        · exact absurd h hm
      have hval : t.toRat = ((t.mantissa_.toNat * 10 ^ t.exponent_.toNat : ℕ) : ℚ) := by
        rw [Number.toRat_of_nonneg t hneg]
        push_cast
        rw [← zpow_natCast (10 : ℚ) t.exponent_.toNat, Int.toNat_of_nonneg hexp]
      rw [hval, Int.floor_natCast]
      exact ⟨rfl, fun _ => hn⟩
  · rw [if_neg hg] at hok
    push_neg at hg
    obtain ⟨hexp_neg', hm_ne⟩ := hg
    have hexp_neg : n.exponent_ < 0 := by omega
    -- expose the truncated pair
    obtain ⟨hval, hle, hzero⟩ := Number.truncateAux_val n.mantissa_ n.exponent_ (le_of_lt hexp_neg)
    cases hp : Number.truncateAux n.mantissa_ n.exponent_ with
    | mk m' e' =>
      rw [hp] at hok hval hle hzero
      simp only [] at hok hval hle hzero
      -- the target integer value
      set K : ℕ := n.mantissa_.toNat / 10 ^ (-n.exponent_).toNat with hK
      -- the input to the final normalize denotes exactly `K`
      have hin_val : (Number.unchecked n.negative_ m' e').toRat = (K : ℚ) := by
        rw [Number.toRat_of_nonneg _
          (show (Number.unchecked n.negative_ m' e').negative_ = false from hneg)]
        exact hval
      -- `K` is the floor of the value
      have hfloor : ⌊n.toRat⌋ = (K : ℤ) := by
        have hd_pos : 0 < 10 ^ (-n.exponent_).toNat := by positivity
        have hnval : n.toRat = (n.mantissa_.toNat : ℚ) / ((10 ^ (-n.exponent_).toNat : ℕ) : ℚ) := by
          rw [Number.toRat_of_nonneg n hneg]
          push_cast
          rw [← zpow_natCast (10 : ℚ) (-n.exponent_).toNat,
            Int.toNat_of_nonneg (by omega : (0 : ℤ) ≤ -n.exponent_),
            zpow_neg, div_eq_mul_inv, inv_inv]
        rw [hnval, Int.floor_nat_div _ _ hd_pos]
      -- `K` is representable: at most 18 digits
      have hK_lt : K < 2 ^ 63 := by
        have hmb := hn.mantissaBounds hm_ne
        have hmax : n.mantissa_.toNat ≤ largeRange.max.toNat := UInt64.le_iff_toNat_le.mp hmb.2
        have hmaxv : largeRange.max.toNat = 9999999999999999999 := by decide
        have hd_ge : 10 ≤ 10 ^ (-n.exponent_).toNat := by
          have h1 : 1 ≤ (-n.exponent_).toNat := by omega
          calc (10 : ℕ) = 10 ^ 1 := by norm_num
            _ ≤ 10 ^ (-n.exponent_).toNat := Nat.pow_le_pow_right (by norm_num) h1
        have : K ≤ n.mantissa_.toNat / 10 := Nat.div_le_div_left hd_ge (by norm_num)
        have h10 : n.mantissa_.toNat / 10 ≤ 999999999999999999 := by omega
        omega
      -- the final normalize is exact on the representable target
      have hgrid := normalize_rounded_to_nearest (Number.unchecked n.negative_ m' e') t hok
      rw [hin_val] at hgrid
      have hrep : ∃ w : Number, w.isNormalized ∧ w.toRat = (K : ℚ) := by
        rcases Nat.eq_zero_or_pos K with h0 | hpos
        · exact ⟨Number.zero, Or.inl rfl, by rw [Number.toRat_zero, h0]; norm_num⟩
        · obtain ⟨w, hw1, _, hw3⟩ := Number.exists_normalized_of_pos_nat K hpos hK_lt
          exact ⟨w, hw1, hw3⟩
      obtain ⟨w, hw_norm, hw_val⟩ := hrep
      have hexact : t.toRat = (K : ℚ) :=
        Number.RoundsToRepresentable.eq_of_representable t _ hgrid w hw_norm hw_val
      refine ⟨by rw [hexact, hfloor]; norm_cast, ?_⟩
      intro ht_ne
      have hm' : m' ≠ 0 := by
        intro h0
        have hKzero : (K : ℚ) = 0 := by
          rw [← hval, h0]
          norm_num
        have := Number.toRat_ne_zero_of_mantissa_ne_zero t ht_ne
        rw [hexact] at this
        exact this hKzero
      exact normalize_result_isNormalized (Number.unchecked n.negative_ m' e') t .to_nearest
        hm' hok ht_ne

/-- `Number.truncate` is monotone on nonnegative normalized inputs. -/
lemma Number.truncate_toRat_mono (n₁ n₂ t₁ t₂ : Number)
    (hn₁ : n₁.isNormalized) (hn₂ : n₂.isNormalized)
    (hneg₁ : n₁.negative_ = false) (hneg₂ : n₂.negative_ = false)
    (hok₁ : n₁.truncate = .ok t₁) (hok₂ : n₂.truncate = .ok t₂)
    (hle : n₁.toRat ≤ n₂.toRat) : t₁.toRat ≤ t₂.toRat := by
  rw [(Number.truncate_floor n₁ t₁ hn₁ hneg₁ hok₁).1,
      (Number.truncate_floor n₂ t₂ hn₂ hneg₂ hok₂).1]
  exact_mod_cast Int.floor_mono hle

/-- The `Number.mantissa` accessor of a zero-mantissa record is zero. -/
lemma Number.mantissa_acc_zero {n : Number} (h : n.mantissa_ = 0) : n.mantissa = 0 := by
  unfold Number.mantissa
  rw [h, if_neg (by decide : ¬ ((0 : UInt64) > maxRep))]
  split <;> decide

/-- **Pricing chain monotone.** For fixed positive `k`, `d` (normalized, nonzero,
nonnegative), the map `a ↦ (k * a) / d` (`.to_nearest` at each stage) is monotone
in the varying positive operand `a`. -/
lemma Number.mul_div_num_mono (k d a₁ a₂ m₁ m₂ q₁ q₂ : Number)
    (hk : k.isNormalized) (hkm : k.mantissa_ ≠ 0) (hkneg : k.negative_ = false)
    (hd : d.isNormalized) (hdm : d.mantissa_ ≠ 0) (hdneg : d.negative_ = false)
    (ha₁ : a₁.isNormalized) (ha₁m : a₁.mantissa_ ≠ 0) (ha₁neg : a₁.negative_ = false)
    (ha₂ : a₂.isNormalized) (ha₂m : a₂.mantissa_ ≠ 0) (ha₂neg : a₂.negative_ = false)
    (hm₁ : k.operator_mul a₁ .to_nearest = .ok m₁) (hm₁m : m₁.mantissa_ ≠ 0)
    (hm₂ : k.operator_mul a₂ .to_nearest = .ok m₂) (hm₂m : m₂.mantissa_ ≠ 0)
    (hq₁ : m₁.operator_div d .to_nearest = .ok q₁) (hq₁m : q₁.mantissa_ ≠ 0)
    (hq₂ : m₂.operator_div d .to_nearest = .ok q₂) (hq₂m : q₂.mantissa_ ≠ 0)
    (hle : a₁.toRat ≤ a₂.toRat) : q₁.toRat ≤ q₂.toRat := by
  have hkpos := Number.toRat_pos_of_not_negative k hkneg hkm
  have hdpos := Number.toRat_pos_of_not_negative d hdneg hdm
  have ha₁pos := Number.toRat_pos_of_not_negative a₁ ha₁neg ha₁m
  have ha₂pos := Number.toRat_pos_of_not_negative a₂ ha₂neg ha₂m
  have hprod₁ : 0 < k.toRat * a₁.toRat := mul_pos hkpos ha₁pos
  have hprod₂ : 0 < k.toRat * a₂.toRat := mul_pos hkpos ha₂pos
  have hcm₁ := operator_mul_roundsCuspAware k a₁ m₁ hk ha₁ hkm ha₁m hm₁ hm₁m hprod₁
  have hcm₂ := operator_mul_roundsCuspAware k a₂ m₂ hk ha₂ hkm ha₂m hm₂ hm₂m hprod₂
  have hm₁neg : m₁.negative_ = false := by
    obtain ⟨_, _, _, _, _, hF⟩ :=
      operator_mul_algorithmic_facts_to_nearest k a₁ m₁ hk ha₁ hkm ha₁m hm₁ hm₁m
    rw [hF.result_neg, hkneg, ha₁neg]; rfl
  have hm₂neg : m₂.negative_ = false := by
    obtain ⟨_, _, _, _, _, hF⟩ :=
      operator_mul_algorithmic_facts_to_nearest k a₂ m₂ hk ha₂ hkm ha₂m hm₂ hm₂m
    rw [hF.result_neg, hkneg, ha₂neg]; rfl
  have hm₁pos := Number.toRat_pos_of_not_negative m₁ hm₁neg hm₁m
  have hm₂pos := Number.toRat_pos_of_not_negative m₂ hm₂neg hm₂m
  have hm₁norm := operator_mul_result_isNormalized k a₁ m₁ .to_nearest hk ha₁ hkm ha₁m hm₁ hm₁m
  have hm₂norm := operator_mul_result_isNormalized k a₂ m₂ .to_nearest hk ha₂ hkm ha₂m hm₂ hm₂m
  have hmle : m₁.toRat ≤ m₂.toRat :=
    operator_mul_left_mono_of_cuspAware k a₁ a₂ m₁ m₂ ha₁ ha₂ hm₁ hm₂ hcm₁ hcm₂
      hm₁pos hm₂pos hkpos ha₁pos hle
  have hquo₁ : 0 < m₁.toRat / d.toRat := div_pos hm₁pos hdpos
  have hquo₂ : 0 < m₂.toRat / d.toRat := div_pos hm₂pos hdpos
  have hcq₁ := operator_div_roundsCuspAware m₁ d q₁ hm₁norm hd hm₁m hdm hq₁ hq₁m hquo₁
  have hcq₂ := operator_div_roundsCuspAware m₂ d q₂ hm₂norm hd hm₂m hdm hq₂ hq₂m hquo₂
  have hq₁nn : 0 ≤ q₁.toRat := by
    obtain ⟨_, _, _, _, _, hF⟩ :=
      operator_div_algorithmic_facts_to_nearest m₁ d q₁ hm₁norm hd hm₁m hdm hq₁ hq₁m
    exact hF.result_nonneg hquo₁
  have hq₂nn : 0 ≤ q₂.toRat := by
    obtain ⟨_, _, _, _, _, hF⟩ :=
      operator_div_algorithmic_facts_to_nearest m₂ d q₂ hm₂norm hd hm₂m hdm hq₂ hq₂m
    exact hF.result_nonneg hquo₂
  have hq₁pos : 0 < q₁.toRat :=
    lt_of_le_of_ne hq₁nn (Ne.symm (Number.toRat_ne_zero_of_mantissa_ne_zero q₁ hq₁m))
  have hq₂pos : 0 < q₂.toRat :=
    lt_of_le_of_ne hq₂nn (Ne.symm (Number.toRat_ne_zero_of_mantissa_ne_zero q₂ hq₂m))
  exact operator_div_num_mono_of_cuspAware m₁ m₂ d q₁ q₂ hm₁norm hm₂norm hq₁ hq₂ hcq₁ hcq₂
    hq₁pos hq₂pos hdpos hm₁pos hmle

/-- Normalizing a zero mantissa yields the canonical zero, whatever the sign,
exponent, range or rounding mode. -/
lemma Number.normalized_zero_mantissa (neg : Bool) (e : Int) (mn mx : UInt64)
    (mode : rounding_mode) : Number.normalized neg 0 e mn mx mode = .ok Number.zero := by
  unfold Number.normalized Number.normalize doNormalize
  simp [Number.unchecked]

/-- **General-mode add normalization.** Mode-generic companion of
`operator_add_isNormalized_to_nearest`; the same-sign branch reads
`result.isNormalized` straight off `PostAlignSpec`, which is stated for any mode. -/
lemma operator_add_isNormalized (x y result : Number) (mode : rounding_mode)
    (hx : x.isNormalized) (hy : y.isNormalized)
    (hok : Number.operator_add x y mode = .ok result)
    (hresult : result.mantissa_ ≠ 0) :
    result.isNormalized := by
  by_cases hy_guard : y.operator_eq Number.zero = true
  · have h_result : result = x := by
      unfold Number.operator_add at hok
      rw [if_pos hy_guard] at hok
      exact (Except.ok.inj (show (Except.ok x : Except Error Number) = .ok result from hok)).symm
    rw [h_result]; exact hx
  by_cases hx_guard : x.operator_eq Number.zero = true
  · have h_result : result = y := by
      unfold Number.operator_add at hok
      rw [if_neg hy_guard, if_pos hx_guard] at hok
      exact (Except.ok.inj (show (Except.ok y : Except Error Number) = .ok result from hok)).symm
    rw [h_result]; exact hy
  by_cases heq_guard : x.operator_eq y.operator_neg = true
  · have h_result : result = Number.zero := by
      unfold Number.operator_add at hok
      rw [if_neg hy_guard, if_neg hx_guard, if_pos heq_guard] at hok
      exact (Except.ok.inj
        (show (Except.ok Number.zero : Except Error Number) = .ok result from hok)).symm
    exact absurd (show result.mantissa_ = 0 by rw [h_result]; rfl) hresult
  have hx_mant_ne : x.mantissa_ ≠ 0 := by
    intro h
    apply hx_guard
    have hx_zero : x = Number.zero := Number.eq_zero_of_mantissa_zero x hx h
    rw [hx_zero]; decide
  have hy_mant_ne : y.mantissa_ ≠ 0 := by
    intro h
    apply hy_guard
    have hy_zero : y = Number.zero := Number.eq_zero_of_mantissa_zero y hy h
    rw [hy_zero]; decide
  by_cases h_sign_eq : x.negative_ = y.negative_
  · obtain ⟨zm, ze', fr, g, rp, hspec⟩ :=
      operator_add_algorithmic_facts_same_sign_anyMode x y result mode hx hy hx_mant_ne hy_mant_ne
        h_sign_eq heq_guard hok
    exact hspec.result_norm
  · exact operator_add_result_isNormalized x y result mode hx hy hx_mant_ne hy_mant_ne
      h_sign_eq heq_guard hok hresult

/-- `to_rep.shift` never touches the sign bit (it only `push`es digits). -/
lemma Number.to_rep_shift_sbit (D : Int64) (off : Int) (g : Guard) :
    (Number.to_rep.shift D off g).2.sbit_ = g.sbit_ := by
  simp only [shift_eq_spec]
  induction D, off, g using shiftSpec.induct with
  | case1 drops offset gg hneg ih =>
    rw [shiftSpec, if_pos hneg, ih, Guard.push_sbit]
  | case2 drops offset gg hnneg =>
    rw [shiftSpec, if_neg hnneg]

/-- **Upper monotonicity of `operator_sub` under `.to_nearest`.** When the exact
difference `x - y` is at most a representable `z`, so is the rounded result: no
representable lies strictly between the truth and a value above `z`. -/
lemma Number.operator_sub_to_nearest_le (x y z result : Number)
    (hx : x.isNormalized) (hy : y.isNormalized) (hz : z.isNormalized)
    (hxm : x.mantissa_ ≠ 0) (hym : y.mantissa_ ≠ 0)
    (hne : ¬ x.operator_eq y)
    (hok : Number.operator_sub x y .to_nearest = .ok result)
    (hres : result.mantissa_ ≠ 0)
    (hz_ge : x.toRat - y.toRat ≤ z.toRat) :
    result.toRat ≤ z.toRat := by
  by_contra hlt
  push_neg at hlt
  have hyneg_norm : (y.operator_neg).isNormalized := Number.operator_neg_isNormalized y hy
  have hyneg_m : (y.operator_neg).mantissa_ ≠ 0 := by
    rw [Number.operator_neg_mantissa_of_ne y hym]; exact hym
  have hnz : ¬ x.operator_eq ((y.operator_neg).operator_neg) := by
    rw [neg_neg_of_mant_ne hym]; exact hne
  have hok' : Number.operator_add x (y.operator_neg) .to_nearest = .ok result := hok
  have hyneg_val : (y.operator_neg).toRat = - y.toRat := Number.toRat_neg y
  have h_ge : x.toRat + (y.operator_neg).toRat ≤ result.toRat := by
    rw [hyneg_val]; linarith [hz_ge, hlt]
  have hcontra := operator_add_no_inbetween_above x (y.operator_neg) result hx hyneg_norm
    hxm hyneg_m hnz hok' hres h_ge
  exact hcontra z hz hlt (by rw [hyneg_val]; linarith [hz_ge])

/-- **`.downward` addition of two non-negative operands stays inside the exact sum
and never goes negative.** All three of `operator_add`'s early exits keep the value,
and the general branch's relative error is far below `1`, so the floored sum cannot
cross zero. -/
lemma Number.operator_add_downward_nonneg_le (x y result : Number)
    (hx : x.isNormalized) (hy : y.isNormalized)
    (hxnn : 0 ≤ x.toRat) (hynn : 0 ≤ y.toRat)
    (hok : Number.operator_add x y .downward = .ok result) :
    result.toRat ≤ x.toRat + y.toRat ∧ 0 ≤ result.toRat := by
  have hok0 := hok
  unfold Number.operator_add at hok
  by_cases hy0 : y.operator_eq Number.zero = true
  · rw [if_pos hy0] at hok
    have hym : y.mantissa_ = 0 := by
      by_contra h
      rw [Number.operator_eq_zero_false_of_mantissa_ne y h] at hy0
      exact absurd hy0 (by simp)
    have hy0v : y.toRat = 0 := Number.toRat_eq_zero_of_mantissa_zero y hym
    rw [← Except.ok.inj hok, hy0v]
    exact ⟨by linarith, hxnn⟩
  · rw [if_neg hy0] at hok
    by_cases hx0 : x.operator_eq Number.zero = true
    · rw [if_pos hx0] at hok
      have hxm : x.mantissa_ = 0 := by
        by_contra h
        rw [Number.operator_eq_zero_false_of_mantissa_ne x h] at hx0
        exact absurd hx0 (by simp)
      have hx0v : x.toRat = 0 := Number.toRat_eq_zero_of_mantissa_zero x hxm
      rw [← Except.ok.inj hok, hx0v]
      exact ⟨by linarith, hynn⟩
    · rw [if_neg hx0] at hok
      by_cases hxy : x.operator_eq (y.operator_neg) = true
      · rw [if_pos hxy] at hok
        rw [← Except.ok.inj hok, Number.toRat_zero]
        exact ⟨by linarith, le_refl _⟩
      · have hxm : x.mantissa_ ≠ 0 := fun h =>
          hx0 (by rw [Number.eq_zero_of_mantissa_zero x hx h]; decide)
        have hym : y.mantissa_ ≠ 0 := fun h =>
          hy0 (by rw [Number.eq_zero_of_mantissa_zero y hy h]; decide)
        have hs : (0:ℚ) ≤ x.toRat + y.toRat := by linarith
        by_cases hrm : result.mantissa_ = 0
        · rw [Number.toRat_eq_zero_of_mantissa_zero result hrm]
          exact ⟨hs, le_refl _⟩
        · have hr := operator_add_rounds_downward x y result hx hy hxm hym
            (by simpa using hxy) hok0 hrm
          have hr' : result.toRat ≤ x.toRat + y.toRat ∧
              (x.toRat + y.toRat) - result.toRat ≤
                |x.toRat + y.toRat| * (11 / (2 ^ 63 - 18 : ℚ)) := hr
          rw [abs_of_nonneg hs] at hr'
          have hmul : (x.toRat + y.toRat) * (11 / (2 ^ 63 - 18 : ℚ)) ≤ x.toRat + y.toRat := by
            nlinarith [hs]
          exact ⟨hr'.1, by linarith [hr'.2, hmul]⟩

/-- A nonzero truncation forces a nonzero input mantissa. -/
lemma Number.truncate_source_ne_zero (n t : Number)
    (hok : n.truncate = .ok t) (ht : t.mantissa_ ≠ 0) : n.mantissa_ ≠ 0 := by
  intro h0
  unfold Number.truncate at hok
  rw [if_pos (Or.inr h0)] at hok
  rw [← Except.ok.inj hok] at ht
  exact ht h0

/-- `to_nearest` `Number` addition of two non-negative normalized operands rounds
within the keystone relative error, with the zero cases exact. -/
lemma operator_add_nonneg_rounds (x y result : Number)
    (hx : x.isNormalized) (hy : y.isNormalized)
    (hxnn : 0 ≤ x.toRat) (hynn : 0 ≤ y.toRat)
    (hok : Number.operator_add x y .to_nearest = .ok result) :
    RoundsWithin result (x.toRat + y.toRat) .to_nearest (6 / (2 ^ 63 - 3 : ℚ)) := by
  have hε : (0 : ℚ) ≤ 6 / (2 ^ 63 - 3 : ℚ) := by positivity
  by_cases hym : y.mantissa_ = 0
  · have hy0 : y = Number.zero := Number.eq_zero_of_mantissa_zero y hy hym
    have hres : result = x := by
      unfold Number.operator_add at hok
      rw [if_pos (by rw [hy0]; decide)] at hok
      exact (Except.ok.inj hok).symm
    refine RoundsWithin_mono result _ 0 _ _ (RoundsWithin_of_eq result _ _ ?_) hε
    rw [hres, hy0, Number.toRat_zero, add_zero]
    rfl
  by_cases hxm : x.mantissa_ = 0
  · have hx0 : x = Number.zero := Number.eq_zero_of_mantissa_zero x hx hxm
    have hres : result = y := by
      unfold Number.operator_add at hok
      rw [if_neg (Number.not_operator_eq_zero_of_mantissa_ne hym),
          if_pos (by rw [hx0]; decide)] at hok
      exact (Except.ok.inj hok).symm
    refine RoundsWithin_mono result _ 0 _ _ (RoundsWithin_of_eq result _ _ ?_) hε
    rw [hres, hx0, Number.toRat_zero, zero_add]
    rfl
  -- both nonzero: same-sign (non-negative) addition
  have hxneg : x.negative_ = false := by
    rcases hb : x.negative_ with _ | _
    · rfl
    · exfalso
      have := Number.toRat_of_neg x hb
      have hxpos : (0 : ℚ) < (x.mantissa_.toNat : ℚ) * 10 ^ x.exponent_ := by
        have h1 : x.mantissa_.toNat ≠ 0 := by
          intro h0; exact hxm (by rw [← UInt64.toNat_inj] at *; exact h0)
        have h2 : (1 : ℚ) ≤ (x.mantissa_.toNat : ℚ) := by
          exact_mod_cast Nat.one_le_iff_ne_zero.mpr h1
        positivity
      rw [this] at hxnn
      linarith
  have hyneg : y.negative_ = false := by
    rcases hb : y.negative_ with _ | _
    · rfl
    · exfalso
      have := Number.toRat_of_neg y hb
      have hypos : (0 : ℚ) < (y.mantissa_.toNat : ℚ) * 10 ^ y.exponent_ := by
        have h1 : y.mantissa_.toNat ≠ 0 := by
          intro h0; exact hym (by rw [← UInt64.toNat_inj] at *; exact h0)
        have h2 : (1 : ℚ) ≤ (y.mantissa_.toNat : ℚ) := by
          exact_mod_cast Nat.one_le_iff_ne_zero.mpr h1
        positivity
      rw [this] at hynn
      linarith
  have hnotz : ¬ x.operator_eq y.operator_neg = true := by
    intro hcon
    have hnegy : y.operator_neg = { y with negative_ := !y.negative_ } := by
      unfold Number.operator_neg
      rw [if_neg (by simpa using hym)]
    unfold Number.operator_eq at hcon
    rw [hnegy] at hcon
    simp only [Bool.and_eq_true, beq_iff_eq] at hcon
    have := hcon.1.1
    rw [hxneg, hyneg] at this
    exact Bool.noConfusion this
  have h := operator_add_rounds_same_sign_to_nearest x y result hx hy hxm hym
    (by rw [hxneg, hyneg]) hnotz hok
  refine RoundsWithin_mono result _ _ _ _ h (by norm_num)

/-- A positive-valued `Number` has a clear sign bit. -/
lemma Number.negative_false_of_pos (n : Number) (h : 0 < n.toRat) :
    n.negative_ = false := by
  rcases hb : n.negative_ with _ | _
  · rfl
  · exact absurd h (not_lt.mpr (Number.toRat_nonpos_of_negative n hb))

/-- Subtracting an equal (nonzero) `arn` yields `Number.zero` (`x - x = 0`). -/
lemma Number.operator_sub_eq_zero_of_operator_eq (x arn result : Number)
    (hxm : x.mantissa_ ≠ 0) (harnm : arn.mantissa_ ≠ 0)
    (heq : x.operator_eq arn = true)
    (hok : x.operator_sub arn .to_nearest = .ok result) : result = Number.zero := by
  unfold Number.operator_sub at hok
  unfold Number.operator_add at hok
  have hnegm : (arn.operator_neg).mantissa_ ≠ 0 := by
    rw [Number.operator_neg_mantissa_of_ne arn harnm]; exact harnm
  rw [if_neg (Number.not_operator_eq_zero_of_mantissa_ne hnegm)] at hok
  rw [if_neg (Number.not_operator_eq_zero_of_mantissa_ne hxm)] at hok
  have h3 : x.operator_eq ((arn.operator_neg).operator_neg) = true := by
    rw [neg_neg_of_mant_ne harnm]; exact heq
  rw [if_pos h3] at hok
  simp only [pure, Except.pure] at hok
  exact (Except.ok.inj hok).symm

/-- Subtracting a zero-mantissa `arn` is the identity (`operator_add x 0 = x`). -/
lemma Number.operator_sub_zero_right (x arn result : Number) (harn : arn.mantissa_ = 0)
    (hok : x.operator_sub arn .to_nearest = .ok result) : result = x := by
  unfold Number.operator_sub at hok
  have hneg0 : arn.operator_neg = Number.zero := by
    unfold Number.operator_neg; rw [if_pos (by rw [harn]; rfl)]
  rw [hneg0] at hok
  unfold Number.operator_add at hok
  rw [if_pos (by decide : Number.zero.operator_eq Number.zero = true)] at hok
  simp only [pure, Except.pure] at hok
  exact (Except.ok.inj hok).symm

/-- **Subtracting a non-negative operand under `.to_nearest` never overshoots the
minuend.** The rounded difference `x - y` is at most `x`: a zero result is `≤ x`
because `x ≥ 0`, an equal-operand cancellation gives the zero result, and the
generic case is `operator_sub_to_nearest_le` at `z = x` (using `x - y ≤ x`). -/
lemma Number.operator_sub_nonneg_le (x y result : Number)
    (hx : x.isNormalized) (hy : y.isNormalized)
    (hxm : x.mantissa_ ≠ 0) (hym : y.mantissa_ ≠ 0)
    (hxnn : 0 ≤ x.toRat) (hynn : 0 ≤ y.toRat)
    (hok : x.operator_sub y .to_nearest = .ok result) :
    result.toRat ≤ x.toRat := by
  by_cases hresm : result.mantissa_ = 0
  · rw [Number.toRat_eq_zero_of_mantissa_zero result hresm]; exact hxnn
  · have hne : ¬ x.operator_eq y := fun heq => by
      have hres0 := Number.operator_sub_eq_zero_of_operator_eq x y result hxm hym heq hok
      rw [hres0] at hresm; exact hresm rfl
    exact Number.operator_sub_to_nearest_le x y x result hx hy hx hxm hym hne hok hresm
      (by linarith [hynn])

/-- `J·10^ec` is a non-negative normalized `Number` for `1 ≤ J < 10^19` with the
sticky-tail condition and a small exponent window. Scaled generalization of
`Number.exists_normalized_of_pos_nat`. -/
lemma Number.exists_normalized_scaled (J : ℕ) (ec : ℤ)
    (h1 : 1 ≤ J) (h2 : J < 10 ^ 19)
    (h3 : J ≤ maxRep.toNat ∨ J % 10 = 0)
    (hlo : (-18 : ℤ) ≤ ec) (hhi : ec ≤ 0) :
    ∃ w : Number, w.isNormalized ∧ w.negative_ = false ∧
      w.toRat = (J : ℚ) * (10 : ℚ) ^ ec := by
  have hJne : J ≠ 0 := by omega
  have hlog_lo : 10 ^ Nat.log 10 J ≤ J := Nat.pow_log_le_self 10 hJne
  have hlog_hi : J < 10 ^ (Nat.log 10 J + 1) := Nat.lt_pow_succ_log_self (by norm_num) J
  set L := Nat.log 10 J with hL_def
  have hL_le : L ≤ 18 := by
    by_contra hcon
    push_neg at hcon
    have : (10 : ℕ) ^ 19 ≤ 10 ^ L := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  set k : ℕ := 18 - L with hk_def
  set M : ℕ := J * 10 ^ k with hM_def
  have hLk : L + k = 18 := by omega
  have hM_lo : 10 ^ 18 ≤ M := by
    calc (10 : ℕ) ^ 18 = 10 ^ L * 10 ^ k := by rw [← pow_add, hLk]
      _ ≤ J * 10 ^ k := mul_le_mul_of_nonneg_right hlog_lo (by positivity)
  have hM_hi : M < 10 ^ 19 := by
    calc M = J * 10 ^ k := rfl
      _ < 10 ^ (L + 1) * 10 ^ k := mul_lt_mul_of_pos_right hlog_hi (by positivity)
      _ = 10 ^ 19 := by rw [← pow_add]; congr 1; omega
  have hM_lt : M < UInt64.size := by rw [uint64_size_val]; omega
  have hM_toNat : (Nat.toUInt64 M).toNat = M :=
    UInt64.toNat_ofNat_of_lt' (by rw [uint64_size_val]; exact hM_lt)
  have hsticky : Nat.toUInt64 M ≤ maxRep ∨ (Nat.toUInt64 M).toNat % 10 = 0 := by
    by_cases hk0 : k = 0
    · rcases h3 with h3 | h3
      · left
        rw [UInt64.le_iff_toNat_le, hM_toNat]
        have hMJ : M = J := by rw [hM_def, hk0, pow_zero, Nat.mul_one]
        rw [hMJ]; exact h3
      · right
        rw [hM_toNat, hM_def, hk0, pow_zero, Nat.mul_one]
        exact h3
    · right
      rw [hM_toNat]
      have hdvd : (10 : ℕ) ∣ M := by
        rw [hM_def]
        exact Dvd.dvd.mul_left (dvd_pow_self 10 (by omega)) J
      omega
  refine ⟨⟨false, Nat.toUInt64 M, ec - (k : ℤ)⟩, ?_, rfl, ?_⟩
  · right
    refine ⟨?_, ?_, hsticky, ?_, ?_⟩
    · rw [UInt64.le_iff_toNat_le, largeRange_min_val, hM_toNat]; omega
    · rw [UInt64.le_iff_toNat_le, largeRange_max_val, hM_toNat]; omega
    · show minExponent ≤ ec - (k : ℤ); unfold minExponent; omega
    · show ec - (k : ℤ) ≤ maxExponent; unfold maxExponent; omega
  · rw [Number.toRat_of_nonneg _ rfl]
    show ((Nat.toUInt64 M).toNat : ℚ) * (10 : ℚ) ^ (ec - (k : ℤ)) = (J : ℚ) * (10 : ℚ) ^ ec
    rw [hM_toNat, hM_def, zpow_sub₀ (by norm_num : (10 : ℚ) ≠ 0), zpow_natCast]
    push_cast
    have h10k : (0 : ℚ) < (10 : ℚ) ^ k := by positivity
    field_simp

/-- **Exact subtraction of an integer within the int64 window.** For a normalized
`x` with `0 ≤ x ≤ 2^63 - 1` and an integer value `0 ≤ k ≤ x` held in a
normalized `aN`, the `to_nearest` subtraction returns exactly `x - k`: the
difference is representable, so the correctly-rounded result equals it.
(`0 ≤ x` is implied by `0 ≤ k ≤ x`.) -/
lemma operator_sub_exact_int_le (x aN result : Number) (k : ℚ)
    (hx : x.isNormalized) (hxle : x.toRat ≤ 2 ^ 63 - 1)
    (haN : aN.isNormalized) (haN_val : aN.toRat = k)
    (hk_int : k.den = 1) (hknn : 0 ≤ k) (hkle : k ≤ x.toRat)
    (hok : x.operator_sub aN .to_nearest = .ok result) :
    result.toRat = x.toRat - k := by
  have hrtr := operator_sub_rounded_to_nearest x aN result hx haN hok
  rw [haN_val] at hrtr
  -- a representable witness for x - k closes the goal
  suffices hwit : ∃ w : Number, w.isNormalized ∧ w.toRat = x.toRat - k by
    obtain ⟨w, hw_norm, hw_val⟩ := hwit
    exact Number.RoundsToRepresentable.eq_of_representable result _ hrtr w hw_norm hw_val
  by_cases hk0 : k = 0
  · exact ⟨x, hx, by rw [hk0, sub_zero]⟩
  have hk1 : 1 ≤ k := by
    have hnum_pos : 0 < k.num := by
      rcases lt_trichotomy k.num 0 with h | h | h
      · exact absurd (Rat.num_nonneg.mpr hknn) (by omega)
      · exact absurd (Rat.zero_iff_num_zero.mpr h) hk0
      · exact h
    have : (1 : ℚ) ≤ (k.num : ℚ) := by exact_mod_cast hnum_pos
    calc (1 : ℚ) ≤ (k.num : ℚ) := this
      _ = k := by
        conv_rhs => rw [← Rat.num_div_den k]
        rw [hk_int]; push_cast; ring
  have hx_mne : x.mantissa_ ≠ 0 := by
    intro h0
    have hx0 : x = Number.zero := Number.eq_zero_of_mantissa_zero x hx h0
    rw [hx0, Number.toRat_zero] at hkle
    linarith
  have hx_neg : x.negative_ = false := by
    by_contra hc
    have hc' : x.negative_ = true := by simpa using hc
    have := Number.toRat_of_neg x hc'
    have hmpos : 0 < (x.mantissa_.toNat : ℚ) := by
      have : 0 < x.mantissa_.toNat := by
        have := (hx.mantissaBounds_nat hx_mne).1; omega
      exact_mod_cast this
    nlinarith [zpow_pos (show (0:ℚ) < 10 from by norm_num) x.exponent_,
      le_trans hknn hkle]
  have hx_val : x.toRat = (x.mantissa_.toNat : ℚ) * (10 : ℚ) ^ x.exponent_ :=
    Number.toRat_of_nonneg x hx_neg
  obtain ⟨hmA_lo, hmA_hi⟩ := hx.mantissaBounds_nat hx_mne
  have hexp_range : minExponent ≤ x.exponent_ ∧ x.exponent_ ≤ maxExponent := by
    rcases hx with h_zero | ⟨_, _, _, hlo, hhi⟩
    · exact absurd (show x.mantissa_ = 0 by rw [h_zero]; rfl) hx_mne
    · exact ⟨hlo, hhi⟩
  set eA := x.exponent_ with heA_def
  have heA_le : eA ≤ 0 := by
    by_contra hc
    push_neg at hc
    have h10 : (10 : ℚ) ^ (1 : ℤ) ≤ (10 : ℚ) ^ eA := zpow_le_zpow_right₀ (by norm_num) (by omega)
    have hm18 : ((10 : ℕ) ^ 18 : ℚ) ≤ (x.mantissa_.toNat : ℚ) := by exact_mod_cast hmA_lo
    rw [hx_val] at hxle
    push_cast at hm18
    nlinarith [hxle, h10, hm18]
  have heA_ge : (-18 : ℤ) ≤ eA := by
    by_contra hc
    push_neg at hc
    have h10 : (10 : ℚ) ^ eA ≤ (10 : ℚ) ^ (-19 : ℤ) := zpow_le_zpow_right₀ (by norm_num) (by omega)
    have hm19 : (x.mantissa_.toNat : ℚ) < ((10 : ℕ) ^ 19 : ℚ) := by exact_mod_cast hmA_hi
    have hxlt : x.toRat < 1 := by
      rw [hx_val]
      push_cast at hm19
      calc (x.mantissa_.toNat : ℚ) * (10 : ℚ) ^ eA
          < 10 ^ 19 * (10 : ℚ) ^ (-19 : ℤ) := by
            have hmnn : (0 : ℚ) ≤ (x.mantissa_.toNat : ℚ) := by positivity
            have hppos : (0 : ℚ) < (10 : ℚ) ^ eA := zpow_pos (by norm_num) _
            nlinarith [h10, hm19, hppos]
        _ = 1 := by
            rw [show ((10 : ℚ) ^ 19 : ℚ) = (10 : ℚ) ^ (19 : ℤ) from by norm_num,
              ← zpow_add₀ (by norm_num : (10 : ℚ) ≠ 0)]
            norm_num
    linarith
  -- the integer k scaled onto x's grid
  set K : ℕ := k.num.toNat with hK_def
  have hK_val : (K : ℚ) = k := by
    rw [hK_def]
    have : (k.num.toNat : ℤ) = k.num := Int.toNat_of_nonneg (Rat.num_nonneg.mpr hknn)
    have hq : ((k.num.toNat : ℤ) : ℚ) = (k.num : ℚ) := by exact_mod_cast this
    push_cast at hq ⊢
    rw [hq]
    conv_rhs => rw [← Rat.num_div_den k]
    rw [hk_int]; push_cast; ring
  set KK : ℕ := K * 10 ^ (-eA).toNat with hKK_def
  have hpow_eq : ((10 : ℚ) ^ (-eA).toNat) * (10 : ℚ) ^ eA = 1 := by
    rw [← zpow_natCast (10 : ℚ) (-eA).toNat, ← zpow_add₀ (by norm_num : (10 : ℚ) ≠ 0)]
    rw [show ((-eA).toNat : ℤ) + eA = 0 from by omega]
    norm_num
  have hKK_le : KK ≤ x.mantissa_.toNat := by
    have hcross : (KK : ℚ) ≤ (x.mantissa_.toNat : ℚ) := by
      rw [hKK_def]
      push_cast
      have h1 : (K : ℚ) * ((10 : ℚ) ^ (-eA).toNat) * (10 : ℚ) ^ eA ≤
          (x.mantissa_.toNat : ℚ) * (10 : ℚ) ^ eA := by
        rw [mul_assoc, hpow_eq, mul_one, hK_val, ← hx_val]
        exact hkle
      have hppos : (0 : ℚ) < (10 : ℚ) ^ eA := zpow_pos (by norm_num) _
      exact le_of_mul_le_mul_right (by rw [mul_assoc] at h1 ⊢; exact h1) hppos
    exact_mod_cast hcross
  set J : ℕ := x.mantissa_.toNat - KK with hJ_def
  have hJ_val : (J : ℚ) * (10 : ℚ) ^ eA = x.toRat - k := by
    rw [hJ_def, hx_val]
    push_cast [Nat.cast_sub hKK_le]
    rw [hKK_def]
    push_cast
    rw [sub_mul, mul_assoc, hpow_eq, mul_one, hK_val]
  by_cases hJ0 : J = 0
  · refine ⟨Number.zero, Or.inl rfl, ?_⟩
    rw [Number.toRat_zero, ← hJ_val, hJ0]
    norm_num
  have hsticky : J ≤ maxRep.toNat ∨ J % 10 = 0 := by
    by_cases hJle : J ≤ maxRep.toNat
    · exact Or.inl hJle
    · right
      push_neg at hJle
      have hmA_gt : maxRep.toNat < x.mantissa_.toNat := by
        have : J ≤ x.mantissa_.toNat := by rw [hJ_def]; omega
        omega
      have heA_neg : eA ≤ -1 := by
        by_contra hc
        push_neg at hc
        have heA0 : eA = 0 := by omega
        have hxq : x.toRat = (x.mantissa_.toNat : ℚ) := by
          rw [hx_val, heA0]; norm_num
        rw [hxq] at hxle
        have hlt : (x.mantissa_.toNat : ℚ) < 2 ^ 63 := by linarith
        have : x.mantissa_.toNat < 2 ^ 63 := by exact_mod_cast hlt
        rw [maxRep_val] at hmA_gt
        omega
      have hmA_mod : x.mantissa_.toNat % 10 = 0 := by
        rcases hx with h_zero | ⟨_, _, hst, _, _⟩
        · exact absurd (show x.mantissa_ = 0 by rw [h_zero]; rfl) hx_mne
        · rcases hst with hst | hst
          · exact absurd (UInt64.le_iff_toNat_le.mp hst) (by omega)
          · exact hst
      have hKK_dvd : (10 : ℕ) ∣ KK := by
        rw [hKK_def]
        exact Dvd.dvd.mul_left (dvd_pow_self 10 (by omega)) K
      have hmA_dvd : (10 : ℕ) ∣ x.mantissa_.toNat := Nat.dvd_of_mod_eq_zero hmA_mod
      rw [hJ_def]
      obtain ⟨a, ha⟩ := hmA_dvd
      obtain ⟨b, hb⟩ := hKK_dvd
      rw [ha, hb]
      omega
  obtain ⟨w, hw_norm, _, hw_val⟩ := Number.exists_normalized_scaled J eA
    (by omega) (by rw [hJ_def]; omega) hsticky heA_ge heA_le
  exact ⟨w, hw_norm, by rw [hw_val, hJ_val]⟩

/-- **`to_rep.shift` accumulates the dropped fraction in the guard.** Starting from
a guard representing `f`, shifting `D ≥ 0` down by `k = (-off).toNat` decimal places
leaves a guard representing `f / 10^k + (D mod 10^k) / 10^k`. -/
lemma Number.to_rep_shift_represents (D : Int64) (off : Int) (g : Guard) :
    0 ≤ D.toInt → ∀ f : ℚ, represents g f →
    represents (Number.to_rep.shift D off g).2
      (f / 10 ^ (-off).toNat + ((D.toInt % 10 ^ (-off).toNat : ℤ) : ℚ) / 10 ^ (-off).toNat) := by
  simp only [shift_eq_spec]
  induction D, off, g using shiftSpec.induct with
  | case1 drops offset gg hneg ih =>
    intro h0 f hg
    rw [shiftSpec, if_pos hneg]
    have hdiv_nn : 0 ≤ (drops / 10).toInt := by
      rw [toInt_div_ten_of_nonneg drops h0]; exact Int.ediv_nonneg h0 (by norm_num)
    have hd_toInt : ((drops % 10).toUInt64.toNat : ℤ) = drops.toInt % 10 := by
      have h1 := toUInt64_toNat_of_nonneg (drops % 10)
        (by rw [toInt_mod_ten_of_nonneg drops h0]; exact Int.emod_nonneg _ (by norm_num))
      rw [h1, toInt_mod_ten_of_nonneg drops h0]
    have hd_lt : (drops % 10).toUInt64.toNat < 10 := by
      have := toInt_mod_ten_of_nonneg drops h0
      have hlt : drops.toInt % 10 < 10 := Int.emod_lt_of_pos _ (by norm_num)
      omega
    have hpush := represents_push hg (d := (drops % 10).toUInt64) hd_lt
    have hgoal := ih hdiv_nn ((f + ((drops % 10).toUInt64.toNat : ℚ)) / 10) hpush
    have hk1 : (-(offset + 1)).toNat = (-offset).toNat - 1 := by omega
    have hk_pos : 1 ≤ (-offset).toNat := by omega
    set k : ℕ := (-offset).toNat with hkdef
    rw [hk1] at hgoal
    -- the accumulated fraction equals the target closed form
    have hEq : f / 10 ^ k + ((drops.toInt % 10 ^ k : ℤ) : ℚ) / 10 ^ k
        = (f + ((drops % 10).toUInt64.toNat : ℚ)) / 10 / 10 ^ (k - 1)
          + (((drops / 10).toInt % 10 ^ (k - 1) : ℤ) : ℚ) / 10 ^ (k - 1) := by
      rw [toInt_div_ten_of_nonneg drops h0]
      have hd0_q : ((drops % 10).toUInt64.toNat : ℚ) = ((drops.toInt % 10 : ℤ) : ℚ) := by
        exact_mod_cast hd_toInt
      rw [hd0_q]
      have hstep_q : ((drops.toInt % 10 ^ k : ℤ) : ℚ)
          = ((drops.toInt % 10 : ℤ) : ℚ) + 10 * (((drops.toInt / 10) % 10 ^ (k - 1) : ℤ) : ℚ) := by
        have h := int_emod_pow10_succ drops.toInt (k - 1)
        rw [show (k - 1) + 1 = k from by omega] at h
        rw [h]; push_cast; ring
      rw [hstep_q, show (10 : ℚ) ^ k = 10 ^ (k - 1) * 10 from by rw [← pow_succ]; congr 1; omega]
      field_simp
      ring
    rw [hEq]
    exact hgoal
  | case2 drops offset gg hnneg =>
    intro h0 f hg
    rw [shiftSpec, if_neg hnneg]
    have hk0 : (-offset).toNat = 0 := by omega
    rw [hk0]
    simp only [pow_zero, Int.emod_one, div_one, Int.cast_zero, add_zero]
    exact hg

/-- **`.to_nearest` `to_rep` on a normalized `Number` rounds within `1/2`.** The
round-to-nearest guard decision (`round = 1` for fraction `> 1/2`, `= 0` for
`= 1/2` with even tie-break, `= -1` for `< 1/2`) keeps the integer result within
half a unit of the value. Sharpens `to_rep_within_one` for `to_nearest`. -/
lemma Number.to_rep_to_nearest_within_half (n : Number) (r : Int64)
    (hn : n.isNormalized) (hneg : n.negative_ = false)
    (hok : n.to_rep .to_nearest = .ok r) :
    |(r.toInt : ℚ) - n.toRat| ≤ (1 / 2 : ℚ) := by
  by_cases hexp0 : 0 ≤ n.exponent
  · rw [to_rep_exact_of_exponent_nonneg n .to_nearest r hn hexp0 hok, sub_self, abs_zero]
    norm_num
  · push_neg at hexp0
    unfold Number.to_rep at hok
    simp only at hok
    by_cases hz : (n.mantissa == 0) = true
    · rw [if_pos hz] at hok
      have hr : r = 0 := by injection hok with h; exact h.symm
      have hmant0 : n.mantissa.toInt = 0 := by rw [beq_iff_eq] at hz; rw [hz]; decide
      have htr : n.toRat = 0 := by rw [← mantissa_mul_exponent_eq_toRat n hn, hmant0]; norm_num
      rw [hr, htr, show (0 : Int64).toInt = 0 from by decide]; norm_num
    · rw [if_neg hz] at hok
      have hmag_nn : 0 ≤ n.mantissa.toInt := (mantissa_sign n).2 hneg
      have hmagM_le : n.mantissa.toInt.natAbs ≤ maxRep.toNat := mantissa_natAbs_le_maxRep n hn
      rw [hneg] at hok
      simp only [Bool.false_eq_true, if_false] at hok
      rw [if_pos hexp0, if_neg (by omega : ¬ n.exponent ≥ 0)] at hok
      simp only at hok
      set sp := Number.to_rep.shift n.mantissa n.exponent Guard.new with hspdef
      set k : ℕ := (-n.exponent).toNat with hkdef
      have hk_pos : 1 ≤ k := by rw [hkdef]; omega
      have hk_cast : (k : ℤ) = -n.exponent := by rw [hkdef]; omega
      -- floor value and its remainder fraction
      have hDf : sp.1.toInt = n.mantissa.toInt / 10 ^ k := by
        rw [hspdef]; exact shift_fst_eq n.mantissa n.exponent Guard.new hmag_nn
      have hsp_nn : 0 ≤ sp.1.toInt := by rw [hDf]; exact Int.ediv_nonneg hmag_nn (by positivity)
      have hval : n.toRat = (n.mantissa.toInt : ℚ) * (10 : ℚ) ^ n.exponent :=
        (mantissa_mul_exponent_eq_toRat n hn).symm
      have hexp_pow : (10 : ℚ) ^ n.exponent = ((10 : ℚ) ^ k)⁻¹ := by
        rw [show n.exponent = -(k : ℤ) from by omega, zpow_neg, zpow_natCast]
      -- `frac = n.toRat - sp.1 = (n.mantissa mod 10^k)/10^k`
      set frac : ℚ := ((n.mantissa.toInt % 10 ^ k : ℤ) : ℚ) / 10 ^ k with hfrac_def
      have h10k_pos : (0 : ℚ) < 10 ^ k := by positivity
      have h10k_ne : (10 : ℚ) ^ k ≠ 0 := ne_of_gt h10k_pos
      have hd_q : (n.mantissa.toInt : ℚ)
          = 10 ^ k * ((n.mantissa.toInt / 10 ^ k : ℤ) : ℚ) + ((n.mantissa.toInt % 10 ^ k : ℤ) : ℚ) := by
        exact_mod_cast (Int.mul_ediv_add_emod n.mantissa.toInt (10 ^ k)).symm
      have hval_frac : n.toRat = (sp.1.toInt : ℚ) + frac := by
        have key : (n.mantissa.toInt : ℚ) = (sp.1.toInt : ℚ) * 10 ^ k + ((n.mantissa.toInt % 10 ^ k : ℤ) : ℚ) := by
          rw [hDf]; linear_combination hd_q
        rw [hval, hexp_pow, ← div_eq_mul_inv, hfrac_def, key]
        field_simp
      have hfrac_nn : 0 ≤ frac := by
        rw [hfrac_def]; apply div_nonneg _ (le_of_lt h10k_pos)
        exact_mod_cast Int.emod_nonneg _ (by positivity)
      have hfrac_lt : frac < 1 := by
        rw [hfrac_def, div_lt_one h10k_pos]
        exact_mod_cast Int.emod_lt_of_pos _ (by positivity)
      -- the guard represents `frac`, and `pushOverflow` is a no-op (`sp.1 < maxRep`)
      have hrep : represents sp.2 frac := by
        have := Number.to_rep_shift_represents n.mantissa n.exponent Guard.new hmag_nn 0 represents_new
        rw [← hspdef, ← hkdef] at this
        simpa [hfrac_def] using this
      have hsp_lt : sp.1.toUInt64.toNat < maxRep.toNat := by
        have h2 : n.mantissa.toInt ≤ (maxRep.toNat : ℤ) := by omega
        have hsp_lt_int : sp.1.toInt < (maxRep.toNat : ℤ) := by
          by_contra hcon
          push_neg at hcon
          have hmul_le : sp.1.toInt * 10 ^ k ≤ n.mantissa.toInt := by
            rw [hDf]; exact Int.ediv_mul_le _ (by positivity)
          have h10k_ge : (10 : ℤ) ≤ 10 ^ k := by
            calc (10 : ℤ) = 10 ^ 1 := by norm_num
              _ ≤ 10 ^ k := pow_le_pow_right₀ (by norm_num) hk_pos
          have hmr : (1 : ℤ) ≤ maxRep.toNat := by decide
          nlinarith [hmul_le, h2, hcon, h10k_ge, hmr,
            mul_le_mul_of_nonneg_right hcon (show (0 : ℤ) ≤ 10 ^ k from by positivity),
            mul_le_mul_of_nonneg_left h10k_ge (show (0 : ℤ) ≤ (maxRep.toNat : ℤ) from by positivity)]
        have hnat : (sp.1.toUInt64.toNat : ℤ) = sp.1.toInt := toUInt64_toNat_of_nonneg sp.1 hsp_nn
        omega
      have hpof : sp.2.pushOverflow sp.1.toUInt64 .to_nearest = sp.2 :=
        pushOverflow_noop_of_lt_maxRep hsp_lt sp.2 .to_nearest
      rw [hpof] at hok
      -- cusp clamp never fires, and the round decision drives the ±1/2 bound
      have hno_cusp : ¬ (maxRep.toInt64 < sp.1 ∧ sp.1 < maxRepUp.toInt64) := fun hc => by
        have hlt := (Int64.lt_iff_toInt_lt).mp hc.1
        rw [show maxRep.toInt64.toInt = (maxRep.toNat : ℤ) from by decide] at hlt
        have hnat : (sp.1.toUInt64.toNat : ℤ) = sp.1.toInt := toUInt64_toNat_of_nonneg sp.1 hsp_nn
        omega
      by_cases hb : (sp.2.round .to_nearest == 1 || (sp.2.round .to_nearest == 0 && sp.1 % 2 == 1)) = true
      · -- round up: fraction ≥ 1/2, so `1 - frac ≤ 1/2`
        rw [if_pos hb] at hok
        by_cases hovf : sp.1 ≥ maxRep.toInt64
        · rw [if_pos hovf] at hok; exact absurd hok (by simp)
        · rw [if_neg hovf] at hok
          have hovf' : sp.1.toInt < (maxRep.toNat : ℤ) := by
            have := (Int64.lt_iff_toInt_lt).mp (Int64.not_le.mp hovf)
            rwa [show maxRep.toInt64.toInt = (maxRep.toNat : ℤ) from by decide] at this
          have hadd : (sp.1 + 1).toInt = sp.1.toInt + 1 := by
            rw [Int64.toInt_add, int64_one_toInt, Int.bmod_eq_iff (by norm_num)]
            rw [maxRep_val] at hovf'; refine ⟨by omega, by push_cast; omega⟩
          have hr : r = sp.1 + 1 := by injection hok with h; exact h.symm
          have hfrac_ge : (1 / 2 : ℚ) ≤ frac := by
            rw [Bool.or_eq_true] at hb
            rcases hb with h1 | h1
            · rw [beq_iff_eq] at h1
              exact le_of_lt (represents_round_eq_one hrep h1)
            · rw [Bool.and_eq_true, beq_iff_eq] at h1
              exact le_of_eq (represents_round_eq_zero hrep h1.1).symm
          rw [hr, hadd, hval_frac]
          push_cast
          rw [abs_le]
          clear hovf hno_cusp hb hok hrep
          constructor <;> linarith
      · -- no round up: fraction ≤ 1/2
        have hfrac_le : frac ≤ (1 / 2 : ℚ) := by
          by_contra hcon
          push_neg at hcon
          have : sp.2.round .to_nearest = 1 := represents_f_gt_half hrep hcon
          rw [this] at hb; simp at hb
        rw [if_neg hb] at hok
        rw [if_neg hno_cusp] at hok
        have hr : r = sp.1 := by injection hok with h; exact h.symm
        rw [hr, hval_frac]
        rw [abs_le]
        clear hno_cusp hb hok hrep
        constructor <;> linarith

end XRPL.Model.Protocol
