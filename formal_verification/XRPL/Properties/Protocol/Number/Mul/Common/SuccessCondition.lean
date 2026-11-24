import XRPL.Properties.Protocol.Number.Common.Rounding.SuccessCondition
import XRPL.Properties.Protocol.Number.Common.Rounding.Normalize
import XRPL.Properties.Protocol.Number.Mul.Common.Decompose
import XRPL.Properties.Protocol.Number.Normalize.Common.ResultFacts

/-! # Exact success condition for `operator_mul`

`x * y` succeeds exactly when the rounded product is at most `maxRepUp * 10^maxExponent`. The bound on the exact
product depends on the rounding mode. -/

namespace XRPL.Model.Protocol

/-- `normalize` accepts a `doRoundUp` result unless its mantissa is above `maxRepUp` at the top exponent. -/
lemma Number.normalize_roundResult_ok_iff {g : Guard} {neg : Bool} {m : UInt64} {e : Int} {mode : rounding_mode}
    {loc : Error} {res : RoundResult} (h_lb : mantissaFloor ≤ m.toNat) (h_ub : m.toNat ≤ maxRepUp.toNat)
    (hok : g.doRoundUp neg m e largeRange.min largeRange.max mode loc = .ok res) :
    (∃ result, res.toNumber.normalize largeRange.min largeRange.max mode = .ok result) ↔
      ¬ (res.mantissa_.toNat > maxRepUp.toNat ∧ res.exponent_ ≥ maxExponent) := by
  by_cases hrm : res.mantissa_ = 0
  · refine iff_of_true ⟨Number.zero, ?_⟩ ?_
    · show doNormalize res.toNumber.negative_ res.toNumber.mantissa_ res.toNumber.exponent_
        largeRange.min largeRange.max mode = .ok Number.zero
      rw [doNormalize_eq_spec]
      all_goals try min_fit
      unfold doNormalizeSpec
      rw [ite_eq_left (show (res.toNumber.mantissa_ == 0) = true from by
        show (res.mantissa_ == 0) = true; rw [beq_iff_eq]; exact hrm)]
    · rintro ⟨h, -⟩
      rw [hrm] at h
      exact absurd h (by decide)
  · obtain ⟨h_res_min, h_res_max, h_res_exp, h_res_mod⟩ :=
      doRoundUp_output_invariants_upTo_maxRepUp_anyMode g neg m e mode h_lb h_ub loc res hok hrm
    have h_exp_le : res.exponent_ ≤ maxExponent := doRoundUp_exponent_le_max g neg m e mode loc res hok
    constructor
    · rintro ⟨result, hres⟩
      exact Number.normalize_no_cusp_overflow h_res_min h_res_max h_res_exp hres
    · intro hnot
      exact ⟨res.toNumber, doNormalize_id mode res.negative_ res.mantissa_ res.exponent_
        h_res_min h_res_max h_res_exp h_res_mod h_exp_le fun h => lt_of_not_ge fun hge => hnot ⟨h, hge⟩⟩

/-- The last two steps of `operator_mul`, `doRoundUp` then `normalize`, on a scaled mantissa `zm`. Below the top
exponent they succeed, at it they fail only when `maxRepUp` carries, one above only `922337203685477581` can pass. -/
lemma Number.operator_mul_tail_ok_iff (g : Guard) (zn : Bool) (zm : UInt64) (ze' : Int) (mode : rounding_mode)
    (hlo : 922337203685477581 ≤ zm.toNat) (hhi : zm.toNat ≤ 9223372036854775810) :
    (∃ result, (match g.doRoundUp zn zm ze' largeRange.min largeRange.max mode .overflow with
        | .error err => Except.error err
        | .ok res => res.toNumber.normalize largeRange.min largeRange.max mode) = .ok result) ↔
      (ze' < maxExponent ∨
        (ze' = maxExponent ∧ ¬(zm.toNat = 9223372036854775810 ∧ g.roundsUpTwice mode = true)) ∨
        (ze' = maxExponent + 1 ∧ zm.toNat = 922337203685477581 ∧ g.roundsUpOdd mode = false)) := by
  have hmru : maxRepUp.toNat = 9223372036854775810 := rfl
  have hub : zm.toNat ≤ maxRepUp.toNat := by rw [hmru]; exact hhi
  by_cases hz : ze' < maxExponent
  · refine iff_of_true ?_ (Or.inl hz)
    obtain ⟨res, hres, hexp⟩ := Guard.doRoundUp_ok_of_le_maxRepUp g zn zm ze' mode .overflow
      (UInt64.le_iff_toNat_le.mpr hub) (le_of_lt hz)
    have hlt : res.exponent_ < maxExponent :=
      lt_of_le_of_lt hexp (max_lt hz (by unfold maxExponent; norm_num))
    rw [hres]
    exact (Number.normalize_roundResult_ok_iff (by omega) hub hres).mpr fun h => absurd h.2 (not_le.mpr hlt)
  obtain ⟨M', E', hspec, hshape⟩ := Guard.doRoundUp_top_shape g zn zm ze' mode .overflow hlo hhi (not_lt.mp hz)
  by_cases hE : E' > maxExponent
  · rw [hspec, ite_eq_left hE]
    refine iff_of_false (by rintro ⟨r, hr⟩; cases hr) ?_
    rcases hshape with ⟨h1, -, -, hE'⟩ | ⟨h1, -, -, hE'⟩ | ⟨h1, -, -, hE', -⟩ | ⟨h1, -, -, hE'⟩ <;>
      (rintro (h | ⟨h, -⟩ | ⟨h, h', -⟩) <;> omega)
  have hok : g.doRoundUp zn zm ze' largeRange.min largeRange.max mode .overflow =
      .ok { negative_ := zn, mantissa_ := M', exponent_ := E' } := by rw [hspec, ite_eq_right hE]
  have hnorm := Number.normalize_roundResult_ok_iff (mode := mode) (by omega) hub hok
  rw [hmru] at hnorm
  rw [hok]
  refine hnorm.trans ?_
  show ¬(M'.toNat > 9223372036854775810 ∧ E' ≥ maxExponent) ↔ _
  -- for the mantissa `922337203685477581` the plain round-up decision is the odd-mantissa one
  have hodd : zm.toNat = 922337203685477581 →
      (g.round mode == 1 || (g.round mode == 0 && zm % 2 == 1)) = g.roundsUpOdd mode := by
    intro h
    have hzm : zm = 922337203685477581 := UInt64.toNat_inj.mp h
    rw [hzm]
    show (g.round mode == 1 || (g.round mode == 0 && ((922337203685477581 : UInt64) % 2 == 1)))
      = (g.round mode == 1 || g.round mode == 0)
    rw [show ((922337203685477581 : UInt64) % 2 == 1) = true from by decide, Bool.and_true]
  rcases hshape with ⟨hn, hc, hM, hE'⟩ | ⟨hn, hc, hM, hE'⟩ | ⟨hn, hM1, hM2, hE', hlast⟩ |
    ⟨hn, ht, hM, hE'⟩
  · constructor
    · intro hL
      by_cases hze : ze' = maxExponent
      · exact Or.inr (Or.inl ⟨hze, fun h => by omega⟩)
      · have hn' : zm.toNat = 922337203685477581 := by
          by_contra hne
          exact hL ⟨by omega, by omega⟩
        exact Or.inr (Or.inr ⟨by omega, hn', by rw [← hodd hn']; exact hc⟩)
    · rintro (h | ⟨h, -⟩ | ⟨h, hn', -⟩) ⟨hgt, hge⟩ <;> omega
  · constructor
    · intro hL
      have hze : ze' = maxExponent := by
        by_contra hne
        exact hL ⟨by omega, by omega⟩
      exact Or.inr (Or.inl ⟨hze, fun h => by omega⟩)
    · rintro (h | ⟨h, -⟩ | ⟨h, hn', hu⟩) ⟨hgt, hge⟩
      · omega
      · omega
      · rw [hodd hn'] at hc
        rw [hc] at hu
        exact Bool.noConfusion hu
  · constructor
    · intro _
      refine Or.inr (Or.inl ⟨by omega, fun h => ?_⟩)
      have ht := h.2
      rw [hlast h.1] at ht
      exact Bool.noConfusion ht
    · rintro _ ⟨hgt, -⟩
      omega
  · constructor
    · intro hL
      exact absurd ⟨by omega, by omega⟩ hL
    · rintro (h | ⟨-, h⟩ | ⟨h, -, -⟩) _
      · omega
      · exact absurd ⟨hn, ht⟩ h
      · omega

/-- `10^e` against `10^maxExponent`: at most a tenth, equal, ten times, or at least a hundred times. -/
lemma zpow_top_zone (e : Int) :
    ∃ c : ℚ, (10 : ℚ) ^ e = c * (10 : ℚ) ^ (maxExponent : ℤ) ∧
      ((e < maxExponent ∧ 0 < c ∧ c ≤ 1 / 10) ∨ (e = maxExponent ∧ c = 1) ∨
        (e = maxExponent + 1 ∧ c = 10) ∨ (maxExponent + 2 ≤ e ∧ 100 ≤ c)) := by
  refine ⟨(10 : ℚ) ^ (e - maxExponent), ?_, ?_⟩
  · rw [← zpow_add₀ (by norm_num : (10 : ℚ) ≠ 0), sub_add_cancel]
  · rcases lt_trichotomy e maxExponent with he | he | he
    · refine Or.inl ⟨he, zpow_pos (by norm_num) _, ?_⟩
      calc (10 : ℚ) ^ (e - maxExponent) ≤ (10 : ℚ) ^ (-1 : ℤ) :=
            zpow_le_zpow_right₀ (by norm_num) (by omega)
        _ = 1 / 10 := by norm_num
    · exact Or.inr (Or.inl ⟨he, by rw [he, sub_self, zpow_zero]⟩)
    · by_cases he1 : e = maxExponent + 1
      · refine Or.inr (Or.inr (Or.inl ⟨he1, ?_⟩))
        rw [show e - maxExponent = 1 from by omega, zpow_one]
      · refine Or.inr (Or.inr (Or.inr ⟨by omega, ?_⟩))
        calc (100 : ℚ) = (10 : ℚ) ^ (2 : ℤ) := by norm_num
          _ ≤ (10 : ℚ) ^ (e - maxExponent) := zpow_le_zpow_right₀ (by norm_num) (by omega)

/-- With no round-up the scaled product passes exactly when its value is below `9223372036854775820` at the top
exponent. -/
lemma mul_truncating_ok_iff_value (n : ℕ) (f : ℚ) (e : Int) (hlo : 922337203685477581 ≤ n)
    (hhi : n ≤ 9223372036854775810) (hf0 : 0 ≤ f) (hf1 : f < 1) :
    (e < maxExponent ∨ e = maxExponent ∨ (e = maxExponent + 1 ∧ n = 922337203685477581)) ↔
      ((n : ℚ) + f) * (10 : ℚ) ^ e < 9223372036854775820 * (10 : ℚ) ^ (maxExponent : ℤ) := by
  obtain ⟨c, hc, hzone⟩ := zpow_top_zone e
  have hT : (0 : ℚ) < (10 : ℚ) ^ (maxExponent : ℤ) := zpow_pos (by norm_num) _
  have hnlo : (922337203685477581 : ℚ) ≤ (n : ℚ) := by exact_mod_cast hlo
  have hnhi : (n : ℚ) ≤ 9223372036854775810 := by exact_mod_cast hhi
  rw [hc]
  generalize (10 : ℚ) ^ (maxExponent : ℤ) = T at hT ⊢
  rw [show ((n : ℚ) + f) * (c * T) = (((n : ℚ) + f) * c) * T from by ring, mul_lt_mul_iff_of_pos_right hT]
  rcases hzone with ⟨he, hc0, hc1⟩ | ⟨he, rfl⟩ | ⟨he, rfl⟩ | ⟨he, hc2⟩
  · refine iff_of_true (Or.inl he) ?_
    have := mul_le_mul_of_nonneg_left hc1 (by linarith : (0 : ℚ) ≤ (n : ℚ) + f)
    linarith
  · exact iff_of_true (Or.inr (Or.inl he)) (by linarith)
  · constructor
    · rintro (h | h | ⟨-, hn⟩)
      · omega
      · omega
      · rw [hn]; push_cast; linarith
    · intro h
      have hn : n = 922337203685477581 := by
        by_contra hne
        have h2 : (922337203685477582 : ℚ) ≤ (n : ℚ) := by exact_mod_cast (by omega : 922337203685477582 ≤ n)
        linarith
      exact Or.inr (Or.inr ⟨he, hn⟩)
  · refine iff_of_false (by rintro (h | h | ⟨h, -⟩) <;> omega) ?_
    have := mul_le_mul (by linarith : (922337203685477581 : ℚ) ≤ (n : ℚ) + f) hc2 (by norm_num)
      (by linarith : (0 : ℚ) ≤ (n : ℚ) + f)
    linarith

/-- With a round-up on any dropped fraction the scaled product passes exactly when its value is at most
`maxRepUp` at the top exponent. -/
lemma mul_away_ok_iff_value (n : ℕ) (f : ℚ) (e : Int) (hlo : 922337203685477581 ≤ n)
    (hhi : n ≤ 9223372036854775810) (hf0 : 0 ≤ f) (hf1 : f < 1) :
    (e < maxExponent ∨ (e = maxExponent ∧ ¬(n = 9223372036854775810 ∧ 0 < f)) ∨
        (e = maxExponent + 1 ∧ n = 922337203685477581 ∧ ¬ 0 < f)) ↔
      ((n : ℚ) + f) * (10 : ℚ) ^ e ≤ 9223372036854775810 * (10 : ℚ) ^ (maxExponent : ℤ) := by
  obtain ⟨c, hc, hzone⟩ := zpow_top_zone e
  have hT : (0 : ℚ) < (10 : ℚ) ^ (maxExponent : ℤ) := zpow_pos (by norm_num) _
  have hnlo : (922337203685477581 : ℚ) ≤ (n : ℚ) := by exact_mod_cast hlo
  have hnhi : (n : ℚ) ≤ 9223372036854775810 := by exact_mod_cast hhi
  rw [hc]
  generalize (10 : ℚ) ^ (maxExponent : ℤ) = T at hT ⊢
  rw [show ((n : ℚ) + f) * (c * T) = (((n : ℚ) + f) * c) * T from by ring, mul_le_mul_iff_of_pos_right hT]
  rcases hzone with ⟨he, hc0, hc1⟩ | ⟨he, rfl⟩ | ⟨he, rfl⟩ | ⟨he, hc2⟩
  · refine iff_of_true (Or.inl he) ?_
    have := mul_le_mul_of_nonneg_left hc1 (by linarith : (0 : ℚ) ≤ (n : ℚ) + f)
    linarith
  · rw [mul_one]
    constructor
    · rintro (h | ⟨-, h⟩ | ⟨h, -, -⟩)
      · omega
      · by_cases hn : n = 9223372036854775810
        · have hf : ¬ 0 < f := fun hf => h ⟨hn, hf⟩
          rw [hn]; push_cast; linarith
        · have h2 : (n : ℚ) ≤ 9223372036854775809 := by exact_mod_cast (by omega : n ≤ 9223372036854775809)
          linarith
      · omega
    · intro h
      refine Or.inr (Or.inl ⟨he, ?_⟩)
      rintro ⟨hn, hf⟩
      rw [hn] at h; push_cast at h; linarith
  · constructor
    · rintro (h | ⟨h, -⟩ | ⟨-, hn, hf⟩)
      · omega
      · omega
      · rw [hn]; push_cast; linarith
    · intro h
      have hn : n = 922337203685477581 := by
        by_contra hne
        have h2 : (922337203685477582 : ℚ) ≤ (n : ℚ) := by exact_mod_cast (by omega : 922337203685477582 ≤ n)
        linarith
      refine Or.inr (Or.inr ⟨he, hn, fun hf => ?_⟩)
      rw [hn] at h; push_cast at h; linarith
  · refine iff_of_false (by rintro (h | ⟨h, -⟩ | ⟨h, -, -⟩) <;> omega) ?_
    have := mul_le_mul (by linarith : (922337203685477581 : ℚ) ≤ (n : ℚ) + f) hc2 (by norm_num)
      (by linarith : (0 : ℚ) ≤ (n : ℚ) + f)
    linarith

/-- With a round-up from one half the scaled product passes exactly when its value is below
`9223372036854775815` at the top exponent. -/
lemma mul_nearest_ok_iff_value (n : ℕ) (f : ℚ) (e : Int) (hlo : 922337203685477581 ≤ n)
    (hhi : n ≤ 9223372036854775810) (hf0 : 0 ≤ f) (hf1 : f < 1) :
    (e < maxExponent ∨ e = maxExponent ∨ (e = maxExponent + 1 ∧ n = 922337203685477581 ∧ ¬ 1 / 2 ≤ f)) ↔
      ((n : ℚ) + f) * (10 : ℚ) ^ e < 9223372036854775815 * (10 : ℚ) ^ (maxExponent : ℤ) := by
  obtain ⟨c, hc, hzone⟩ := zpow_top_zone e
  have hT : (0 : ℚ) < (10 : ℚ) ^ (maxExponent : ℤ) := zpow_pos (by norm_num) _
  have hnlo : (922337203685477581 : ℚ) ≤ (n : ℚ) := by exact_mod_cast hlo
  have hnhi : (n : ℚ) ≤ 9223372036854775810 := by exact_mod_cast hhi
  rw [hc]
  generalize (10 : ℚ) ^ (maxExponent : ℤ) = T at hT ⊢
  rw [show ((n : ℚ) + f) * (c * T) = (((n : ℚ) + f) * c) * T from by ring, mul_lt_mul_iff_of_pos_right hT]
  rcases hzone with ⟨he, hc0, hc1⟩ | ⟨he, rfl⟩ | ⟨he, rfl⟩ | ⟨he, hc2⟩
  · refine iff_of_true (Or.inl he) ?_
    have := mul_le_mul_of_nonneg_left hc1 (by linarith : (0 : ℚ) ≤ (n : ℚ) + f)
    linarith
  · exact iff_of_true (Or.inr (Or.inl he)) (by linarith)
  · constructor
    · rintro (h | h | ⟨-, hn, hf⟩)
      · omega
      · omega
      · rw [hn]; push_cast; linarith
    · intro h
      have hn : n = 922337203685477581 := by
        by_contra hne
        have h2 : (922337203685477582 : ℚ) ≤ (n : ℚ) := by exact_mod_cast (by omega : 922337203685477582 ≤ n)
        linarith
      refine Or.inr (Or.inr ⟨he, hn, fun hf => ?_⟩)
      rw [hn] at h; push_cast at h; linarith
  · refine iff_of_false (by rintro (h | h | ⟨h, -, -⟩) <;> omega) ?_
    have := mul_le_mul (by linarith : (922337203685477581 : ℚ) ≤ (n : ℚ) + f) hc2 (by norm_num)
      (by linarith : (0 : ℚ) ≤ (n : ℚ) + f)
    linarith

/-- In `to_nearest` the last two steps of `operator_mul` succeed exactly when the scaled product is below
`9223372036854775815` at the top exponent. -/
lemma Number.operator_mul_tail_ok_iff_nearest (g : Guard) (zn : Bool) (zm : UInt64) (ze' : Int) (f : ℚ)
    (hlo : 922337203685477581 ≤ zm.toNat) (hhi : zm.toNat ≤ 9223372036854775810) (hrep : represents g f) :
    (∃ result, (match g.doRoundUp zn zm ze' largeRange.min largeRange.max .to_nearest .overflow with
        | .error err => Except.error err
        | .ok res => res.toNumber.normalize largeRange.min largeRange.max .to_nearest) = .ok result) ↔
      ((zm.toNat : ℚ) + f) * (10 : ℚ) ^ ze' < 9223372036854775815 * (10 : ℚ) ^ (maxExponent : ℤ) := by
  rw [Number.operator_mul_tail_ok_iff g zn zm ze' .to_nearest hlo hhi,
    ← mul_nearest_ok_iff_value zm.toNat f ze' hlo hhi (represents_nonneg hrep) (represents_lt_one hrep),
    Guard.roundsUpTwice_to_nearest, ← Guard.roundsUpOdd_to_nearest hrep]
  simp only [Bool.false_eq_true, and_false, not_false_eq_true, and_true, Bool.not_eq_true]

/-- In a directed mode whose guard does not round up, the last two steps of `operator_mul` succeed exactly when
the scaled product is below `9223372036854775820` at the top exponent. -/
lemma Number.operator_mul_tail_ok_iff_truncating (g : Guard) (zn : Bool) (zm : UInt64) (ze' : Int)
    (mode : rounding_mode) (f : ℚ) (hlo : 922337203685477581 ≤ zm.toNat) (hhi : zm.toNat ≤ 9223372036854775810)
    (hf0 : 0 ≤ f) (hf1 : f < 1) (hm : mode ≠ .to_nearest) (hr : (g.round mode == 1) = false) :
    (∃ result, (match g.doRoundUp zn zm ze' largeRange.min largeRange.max mode .overflow with
        | .error err => Except.error err
        | .ok res => res.toNumber.normalize largeRange.min largeRange.max mode) = .ok result) ↔
      ((zm.toNat : ℚ) + f) * (10 : ℚ) ^ ze' < 9223372036854775820 * (10 : ℚ) ^ (maxExponent : ℤ) := by
  rw [Number.operator_mul_tail_ok_iff g zn zm ze' mode hlo hhi,
    ← mul_truncating_ok_iff_value zm.toNat f ze' hlo hhi hf0 hf1,
    (Guard.roundsUp_directed g mode hm).1, (Guard.roundsUp_directed g mode hm).2, hr]
  simp only [Bool.false_eq_true, and_false, not_false_eq_true, and_true]

/-- In a directed mode whose guard rounds up on any dropped fraction, the last two steps of `operator_mul` succeed
exactly when the scaled product is at most `maxRepUp` at the top exponent. -/
lemma Number.operator_mul_tail_ok_iff_away (g : Guard) (zn : Bool) (zm : UInt64) (ze' : Int)
    (mode : rounding_mode) (f : ℚ) (hlo : 922337203685477581 ≤ zm.toNat) (hhi : zm.toNat ≤ 9223372036854775810)
    (hf0 : 0 ≤ f) (hf1 : f < 1) (hm : mode ≠ .to_nearest) (hr : (g.round mode == 1) = true ↔ 0 < f) :
    (∃ result, (match g.doRoundUp zn zm ze' largeRange.min largeRange.max mode .overflow with
        | .error err => Except.error err
        | .ok res => res.toNumber.normalize largeRange.min largeRange.max mode) = .ok result) ↔
      ((zm.toNat : ℚ) + f) * (10 : ℚ) ^ ze' ≤ 9223372036854775810 * (10 : ℚ) ^ (maxExponent : ℤ) := by
  rw [Number.operator_mul_tail_ok_iff g zn zm ze' mode hlo hhi,
    ← mul_away_ok_iff_value zm.toNat f ze' hlo hhi hf0 hf1,
    (Guard.roundsUp_directed g mode hm).1, (Guard.roundsUp_directed g mode hm).2, ← hr]
  simp only [Bool.not_eq_true]

/-- The sign bit of a product tells the sign of the exact product. -/
lemma Number.mul_toRat_sign (x y : Number) :
    ((x.negative_ != y.negative_) = false → 0 ≤ x.toRat * y.toRat) ∧
      ((x.negative_ != y.negative_) = true → x.toRat * y.toRat ≤ 0) := by
  constructor
  · intro h
    have hs : x.negative_ = y.negative_ := by simpa using h
    cases hxn : x.negative_
    · exact mul_nonneg (Number.toRat_nonneg_of_nonnegative x hxn)
        (Number.toRat_nonneg_of_nonnegative y (hs ▸ hxn))
    · exact mul_nonneg_of_nonpos_of_nonpos (Number.toRat_nonpos_of_negative x hxn)
        (Number.toRat_nonpos_of_negative y (hs ▸ hxn))
  · intro h
    have hs : x.negative_ ≠ y.negative_ := by simpa using h
    cases hxn : x.negative_
    · have hyn : y.negative_ = true := by cases hy : y.negative_ <;> simp_all
      exact mul_nonpos_of_nonneg_of_nonpos (Number.toRat_nonneg_of_nonnegative x hxn)
        (Number.toRat_nonpos_of_negative y hyn)
    · have hyn : y.negative_ = false := by cases hy : y.negative_ <;> simp_all
      exact mul_nonpos_of_nonpos_of_nonneg (Number.toRat_nonpos_of_negative x hxn)
        (Number.toRat_nonneg_of_nonnegative y hyn)

/-- In `to_nearest`, `x * y` succeeds exactly when the exact product is below
`9223372036854775815 * 10^maxExponent` in size. -/
lemma Number.operator_mul_ok_iff_to_nearest_proof (x y : Number)
    (hx : x.isNormalized) (hy : y.isNormalized)
    (hx0 : x.mantissa_ ≠ 0) (hy0 : y.mantissa_ ≠ 0) :
    (∃ result, x.operator_mul y .to_nearest = .ok result) ↔
      |x.toRat * y.toRat| < 9223372036854775815 * (10 : ℚ) ^ (maxExponent : ℤ) := by
  obtain ⟨zm, ze', f, g, hlo, hhi, -, -, -, hval, hrep, -, hspec⟩ :=
    Number.operator_mulSpec_scaled x y .to_nearest hx hy hx0 hy0
  rw [Number.operator_mul_eq_spec, hspec, hval]
  exact Number.operator_mul_tail_ok_iff_nearest g _ zm ze' f hlo hhi hrep

/-- In `towards_zero`, `x * y` succeeds exactly when the exact product is below
`9223372036854775820 * 10^maxExponent` in size. -/
lemma Number.operator_mul_ok_iff_towards_zero_proof (x y : Number)
    (hx : x.isNormalized) (hy : y.isNormalized)
    (hx0 : x.mantissa_ ≠ 0) (hy0 : y.mantissa_ ≠ 0) :
    (∃ result, x.operator_mul y .towards_zero = .ok result) ↔
      |x.toRat * y.toRat| < 9223372036854775820 * (10 : ℚ) ^ (maxExponent : ℤ) := by
  obtain ⟨zm, ze', f, g, hlo, hhi, hf0, hf1, -, hval, -, -, hspec⟩ :=
    Number.operator_mulSpec_scaled x y .towards_zero hx hy hx0 hy0
  rw [Number.operator_mul_eq_spec, hspec, hval]
  exact Number.operator_mul_tail_ok_iff_truncating g _ zm ze' .towards_zero f hlo hhi hf0 hf1 (by decide)
    (Guard.round_towards_zero_ne_one g)

/-- In `downward`, `x * y` succeeds exactly when the exact product is at least `-maxRepUp * 10^maxExponent` and
below `9223372036854775820 * 10^maxExponent`. -/
lemma Number.operator_mul_ok_iff_downward_proof (x y : Number)
    (hx : x.isNormalized) (hy : y.isNormalized)
    (hx0 : x.mantissa_ ≠ 0) (hy0 : y.mantissa_ ≠ 0) :
    (∃ result, x.operator_mul y .downward = .ok result) ↔
      -(9223372036854775810 * (10 : ℚ) ^ (maxExponent : ℤ)) ≤ x.toRat * y.toRat ∧
        x.toRat * y.toRat < 9223372036854775820 * (10 : ℚ) ^ (maxExponent : ℤ) := by
  obtain ⟨zm, ze', f, g, hlo, hhi, hf0, hf1, -, hval, hrep, hsbit, hspec⟩ :=
    Number.operator_mulSpec_scaled x y .downward hx hy hx0 hy0
  have hsign := Number.mul_toRat_sign x y
  have hone := Guard.round_downward_eq_one_iff hrep
  have hT : (0 : ℚ) < (10 : ℚ) ^ (maxExponent : ℤ) := zpow_pos (by norm_num) _
  rw [Number.operator_mul_eq_spec, hspec]
  cases hzn : (x.negative_ != y.negative_)
  · -- a product that is not negative rounds toward zero
    have hr : (g.round .downward == 1) = false := by
      rw [← Bool.not_eq_true, hone, hsbit, hzn]; simp
    have hp := hsign.1 hzn
    refine (Number.operator_mul_tail_ok_iff_truncating g _ zm ze' .downward f hlo hhi hf0 hf1 (by decide) hr).trans ?_
    rw [← hval, abs_of_nonneg hp]
    generalize (10 : ℚ) ^ (maxExponent : ℤ) = T at hT ⊢
    generalize x.toRat * y.toRat = p at hp ⊢
    exact ⟨fun h => ⟨by linarith, h⟩, fun h => h.2⟩
  · -- a product that is not positive rounds away from zero on any dropped fraction
    have hr : (g.round .downward == 1) = true ↔ 0 < f := by
      rw [hone, hsbit, hzn]; simp
    have hp := hsign.2 hzn
    refine (Number.operator_mul_tail_ok_iff_away g _ zm ze' .downward f hlo hhi hf0 hf1 (by decide) hr).trans ?_
    rw [← hval, abs_of_nonpos hp]
    generalize (10 : ℚ) ^ (maxExponent : ℤ) = T at hT ⊢
    generalize x.toRat * y.toRat = p at hp ⊢
    exact ⟨fun h => ⟨by linarith, by linarith⟩, fun h => by linarith [h.1]⟩

/-- In `upward`, `x * y` succeeds exactly when the exact product is above `-9223372036854775820 * 10^maxExponent`
and at most `maxRepUp * 10^maxExponent`. -/
lemma Number.operator_mul_ok_iff_upward_proof (x y : Number)
    (hx : x.isNormalized) (hy : y.isNormalized)
    (hx0 : x.mantissa_ ≠ 0) (hy0 : y.mantissa_ ≠ 0) :
    (∃ result, x.operator_mul y .upward = .ok result) ↔
      -(9223372036854775820 * (10 : ℚ) ^ (maxExponent : ℤ)) < x.toRat * y.toRat ∧
        x.toRat * y.toRat ≤ 9223372036854775810 * (10 : ℚ) ^ (maxExponent : ℤ) := by
  obtain ⟨zm, ze', f, g, hlo, hhi, hf0, hf1, -, hval, hrep, hsbit, hspec⟩ :=
    Number.operator_mulSpec_scaled x y .upward hx hy hx0 hy0
  have hsign := Number.mul_toRat_sign x y
  have hone := Guard.round_upward_eq_one_iff hrep
  have hT : (0 : ℚ) < (10 : ℚ) ^ (maxExponent : ℤ) := zpow_pos (by norm_num) _
  rw [Number.operator_mul_eq_spec, hspec]
  cases hzn : (x.negative_ != y.negative_)
  · -- a product that is not negative rounds away from zero on any dropped fraction
    have hr : (g.round .upward == 1) = true ↔ 0 < f := by
      rw [hone, hsbit, hzn]; simp
    have hp := hsign.1 hzn
    refine (Number.operator_mul_tail_ok_iff_away g _ zm ze' .upward f hlo hhi hf0 hf1 (by decide) hr).trans ?_
    rw [← hval, abs_of_nonneg hp]
    generalize (10 : ℚ) ^ (maxExponent : ℤ) = T at hT ⊢
    generalize x.toRat * y.toRat = p at hp ⊢
    exact ⟨fun h => ⟨by linarith, h⟩, fun h => h.2⟩
  · -- a product that is not positive rounds toward zero
    have hr : (g.round .upward == 1) = false := by
      rw [← Bool.not_eq_true, hone, hsbit, hzn]; simp
    have hp := hsign.2 hzn
    refine (Number.operator_mul_tail_ok_iff_truncating g _ zm ze' .upward f hlo hhi hf0 hf1 (by decide) hr).trans ?_
    rw [← hval, abs_of_nonpos hp]
    generalize (10 : ℚ) ^ (maxExponent : ℤ) = T at hT ⊢
    generalize x.toRat * y.toRat = p at hp ⊢
    exact ⟨fun h => ⟨by linarith, by linarith⟩, fun h => by linarith [h.1]⟩

/-- Every `operator_mul` error is an overflow error. -/
lemma Number.operator_mul_error_isOverflow {x y : Number} {mode : rounding_mode} {err : Error}
    (h : x.operator_mul y mode = .error err) : isOverflow err = true := by
  rw [Number.operator_mul_eq_spec] at h
  unfold Number.operator_mulSpec at h
  split at h
  · cases h
  split at h
  · cases h
  dsimp only at h
  split at h
  · rename_i err' herr
    cases h
    exact Guard.doRoundUp_error_isOverflow largeRange_min_toNat_le rfl herr
  · exact doNormalize_error_isOverflow largeRange_min_toNat_le h

/-- In `to_nearest`, `x * y` fails with an overflow error when the exact product is at or above
`9223372036854775815 * 10^maxExponent` in size. -/
lemma Number.operator_mul_overflow_to_nearest_proof (x y : Number)
    (hx : x.isNormalized) (hy : y.isNormalized)
    (hx0 : x.mantissa_ ≠ 0) (hy0 : y.mantissa_ ≠ 0)
    (h : 9223372036854775815 * (10 : ℚ) ^ (maxExponent : ℤ) ≤ |x.toRat * y.toRat|) :
    ∃ err, x.operator_mul y .to_nearest = .error err ∧ isOverflow err = true :=
  overflow_of_not_ok
    (fun hok => absurd ((Number.operator_mul_ok_iff_to_nearest_proof x y hx hy hx0 hy0).mp hok) (not_lt.mpr h))
    (fun _ herr => Number.operator_mul_error_isOverflow herr)

/-- In `towards_zero`, `x * y` fails with an overflow error when the exact product is at or above
`9223372036854775820 * 10^maxExponent` in size. -/
lemma Number.operator_mul_overflow_towards_zero_proof (x y : Number)
    (hx : x.isNormalized) (hy : y.isNormalized)
    (hx0 : x.mantissa_ ≠ 0) (hy0 : y.mantissa_ ≠ 0)
    (h : 9223372036854775820 * (10 : ℚ) ^ (maxExponent : ℤ) ≤ |x.toRat * y.toRat|) :
    ∃ err, x.operator_mul y .towards_zero = .error err ∧ isOverflow err = true :=
  overflow_of_not_ok
    (fun hok => absurd ((Number.operator_mul_ok_iff_towards_zero_proof x y hx hy hx0 hy0).mp hok) (not_lt.mpr h))
    (fun _ herr => Number.operator_mul_error_isOverflow herr)

/-- In `downward`, `x * y` fails with an overflow error when the exact product is below
`-maxRepUp * 10^maxExponent` or at least `9223372036854775820 * 10^maxExponent`. -/
lemma Number.operator_mul_overflow_downward_proof (x y : Number)
    (hx : x.isNormalized) (hy : y.isNormalized)
    (hx0 : x.mantissa_ ≠ 0) (hy0 : y.mantissa_ ≠ 0)
    (h : x.toRat * y.toRat < -(9223372036854775810 * (10 : ℚ) ^ (maxExponent : ℤ)) ∨
      9223372036854775820 * (10 : ℚ) ^ (maxExponent : ℤ) ≤ x.toRat * y.toRat) :
    ∃ err, x.operator_mul y .downward = .error err ∧ isOverflow err = true :=
  overflow_of_not_ok
    (fun hok => by
      have hb := (Number.operator_mul_ok_iff_downward_proof x y hx hy hx0 hy0).mp hok
      rcases h with h | h
      · exact absurd hb.1 (not_le.mpr h)
      · exact absurd hb.2 (not_lt.mpr h))
    (fun _ herr => Number.operator_mul_error_isOverflow herr)

/-- In `upward`, `x * y` fails with an overflow error when the exact product is at most
`-9223372036854775820 * 10^maxExponent` or above `maxRepUp * 10^maxExponent`. -/
lemma Number.operator_mul_overflow_upward_proof (x y : Number)
    (hx : x.isNormalized) (hy : y.isNormalized)
    (hx0 : x.mantissa_ ≠ 0) (hy0 : y.mantissa_ ≠ 0)
    (h : x.toRat * y.toRat ≤ -(9223372036854775820 * (10 : ℚ) ^ (maxExponent : ℤ)) ∨
      9223372036854775810 * (10 : ℚ) ^ (maxExponent : ℤ) < x.toRat * y.toRat) :
    ∃ err, x.operator_mul y .upward = .error err ∧ isOverflow err = true :=
  overflow_of_not_ok
    (fun hok => by
      have hb := (Number.operator_mul_ok_iff_upward_proof x y hx hy hx0 hy0).mp hok
      rcases h with h | h
      · exact absurd hb.1 (not_lt.mpr h)
      · exact absurd hb.2 (not_le.mpr h))
    (fun _ herr => Number.operator_mul_error_isOverflow herr)

end XRPL.Model.Protocol
