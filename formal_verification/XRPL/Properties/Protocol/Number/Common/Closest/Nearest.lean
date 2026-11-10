import XRPL.Properties.Protocol.Number.Common.Closest.NearestDefs
import XRPL.Properties.Protocol.Number.Common.Closest.NoInbetween
import XRPL.Properties.Protocol.Number.Common.Rounding.DoRoundUp.ValueChar

/-! # The `to_nearest` rounding step picks a nearest Number -/

namespace XRPL.Model.Protocol

/-- No normalized Number lies strictly between `lo` and `hi`, and `lo ≤ |truth| ≤ hi`. A result with the sign of
`truth` and the magnitude of the nearer of `lo` and `hi` is a nearest Number. -/
private lemma roundsToNearest_of_neighbours (result : Number) (truth lo hi : ℚ)
    (hlo_nn : 0 ≤ lo) (hlo : lo ≤ |truth|) (hhi : |truth| ≤ hi)
    (hgap_pos : ∀ m : Number, m.isNormalized → 0 < m.toRat → lo < m.toRat → m.toRat < hi → False)
    (hgap_neg : ∀ m : Number, m.isNormalized → m.toRat < 0 → -hi < m.toRat → m.toRat < -lo → False)
    (hpick : (|result.toRat| = lo ∧ 2 * |truth| ≤ lo + hi) ∨ (|result.toRat| = hi ∧ lo + hi ≤ 2 * |truth|))
    (h_res_nn : 0 < truth → 0 ≤ result.toRat)
    (h_res_np : truth < 0 → result.toRat ≤ 0) :
    result.RoundsToNearest truth := by
  have h_dist : |result.toRat - truth| = |(|result.toRat| - |truth|)| := by
    rcases lt_trichotomy truth 0 with h | h | h
    · rw [abs_of_nonpos (h_res_np h), abs_of_neg h, ← abs_neg]
      congr 1
      ring
    · rw [h, abs_zero, sub_zero, sub_zero, abs_abs]
    · rw [abs_of_nonneg (h_res_nn h), abs_of_pos h]
  have h_lo_side : |result.toRat - truth| ≤ |truth| - lo := by
    rw [h_dist]
    rcases hpick with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h, abs_le] <;> constructor <;> linarith
  have h_hi_side : |result.toRat - truth| ≤ hi - |truth| := by
    rw [h_dist]
    rcases hpick with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h, abs_le] <;> constructor <;> linarith
  intro m hm
  have h_rev := abs_abs_sub_abs_le_abs_sub m.toRat truth
  have h_m_side : |m.toRat| ≤ lo ∨ hi ≤ |m.toRat| := by
    by_contra h
    push Not at h
    rcases le_or_gt 0 m.toRat with h0 | h0
    · rw [abs_of_nonneg h0] at h
      exact hgap_pos m hm (by linarith) h.1 h.2
    · rw [abs_of_neg h0] at h
      exact hgap_neg m hm h0 (by linarith) (by linarith)
  rcases h_m_side with h | h
  · have := neg_abs_le (|m.toRat| - |truth|)
    linarith
  · have := le_abs_self (|m.toRat| - |truth|)
    linarith

/-- In `to_nearest`, a nonzero `doRoundUp` output at `maxRepUp` keeps the value `maxRepUp · 10^ze`. A round-up drops
the digit `0` and the second rounding never fires. -/
private lemma doRoundUp_value_to_nearest_maxRepUp (g : Guard) (ze : Int) (loc : Error) (res : RoundResult)
    (hok : g.doRoundUp false maxRepUp ze largeRange.min largeRange.max .to_nearest loc = .ok res)
    (hne : res.mantissa_ ≠ 0) :
    (res.mantissa_.toNat : ℚ) * 10 ^ res.exponent_ = (maxRepCuspTarget : ℚ) * 10 ^ ze := by
  have h_pof : g.pushOverflowSpec maxRepUp .to_nearest = g := by
    unfold Guard.pushOverflowSpec
    rw [if_neg (by decide)]
  have h_top : (g.push (maxRepUp % 10)).digits_.toNat < 5764607523034234880 := by
    rw [toNat_push_digits, show (maxRepUp % 10).toNat = 0 from by decide]
    have := UInt64.toNat_lt_size g.digits_
    simp only [UInt64.size] at this
    omega
  have h_ru' : (((g.push (maxRepUp % 10)).round .to_nearest == 1) ||
      (((g.push (maxRepUp % 10)).round .to_nearest == 0) && (maxRepUp / 10 % 2 == 1))) = false := by
    rcases Guard.round_to_nearest_of_top_lt_five _ h_top with h | h <;> rw [h] <;> decide
  replace hok := Guard.doRoundUp_ok_spec hok
  unfold Guard.doRoundUpSpec at hok
  dsimp only [Guard.doDropDigit] at hok
  rw [h_pof] at hok
  simp only [show ¬ (maxRepUp < largeRange.max ∧ maxRepUp < maxRep) from by decide,
    show ¬ (maxRep < maxRepUp ∧ maxRepUp < maxRepUp) from by decide, h_ru', Bool.false_eq_true,
    if_false] at hok
  split_ifs at hok
  · obtain rfl := Except.ok.inj hok
    rw [bringIntoRange_value_q false (maxRepUp / 10) (ze + 1) hne,
      show (maxRepUp / 10).toNat = 922337203685477581 from by decide, zpow_add₀ (by norm_num), zpow_one]
    push_cast
    ring
  · obtain rfl := Except.ok.inj hok
    rw [bringIntoRange_value_q false maxRepUp ze hne, show maxRepUp.toNat = 9223372036854775810 from rfl]
    push_cast
    ring

/-- A guard with the digit `6` pushed on top rounds up in `to_nearest`. -/
private lemma round_push_six (g : Guard) : (g.push 6).round .to_nearest = 1 := by
  have hd : 6917529027641081856 ≤ (g.push 6).digits_.toNat := by
    rw [toNat_push_digits, show (6 : UInt64).toNat = 6 from rfl]
    omega
  have hne : ¬ (g.push 6).empty := by
    intro he
    have h0 : (g.push 6).digits_ = 0 := by
      unfold Guard.empty Guard.unrecoverable at he
      simp only [Bool.and_eq_true, beq_iff_eq] at he
      exact he.1
    rw [h0] at hd
    simp at hd
  rw [round_to_nearest_def hne, if_pos]
  rw [GT.gt, UInt64.lt_iff_toNat_lt,
    show (0x5000_0000_0000_0000 : UInt64).toNat = 5764607523034234880 from by decide]
  omega

/-- A guard with the digit `3` pushed on top does not round up in `to_nearest`. -/
private lemma round_push_three (g : Guard) :
    (g.push 3).round .to_nearest = -1 ∨ (g.push 3).round .to_nearest = -2 := by
  apply Guard.round_to_nearest_of_top_lt_five
  rw [toNat_push_digits, show (3 : UInt64).toNat = 3 from rfl]
  have := UInt64.toNat_lt_size g.digits_
  simp only [UInt64.size] at this
  omega

/-- Inside the cusp, `to_nearest` `pushOverflow` pushes `6` when `zm = maxRep + 2` or the guard rounds up or ties,
and pushes `3` otherwise. -/
private lemma pushOverflow_cusp_eq (g : Guard) (zm : UInt64)
    (h_lb : maxRep.toNat < zm.toNat) (h_ub : zm.toNat < maxRepUp.toNat) :
    g.pushOverflowSpec zm .to_nearest =
      if zm.toNat = maxRepNat + 2 ∨ g.round .to_nearest = 1 ∨ g.round .to_nearest = 0 then g.push 6
      else g.push 3 := by
  have h_zm : zm = 9223372036854775808 ∨ zm = 9223372036854775809 := by
    rw [maxRep_val] at h_lb
    rw [show maxRepUp.toNat = maxRepCuspTarget from rfl] at h_ub
    rcases (by omega : zm.toNat = 9223372036854775808 ∨ zm.toNat = 9223372036854775809) with h | h
    · exact Or.inl (UInt64.toNat_inj.mp h)
    · exact Or.inr (UInt64.toNat_inj.mp h)
  unfold Guard.pushOverflowSpec
  rcases h_zm with rfl | rfl
  · rw [if_pos (by decide)]
    dsimp only
    rw [if_pos (by decide : (9223372036854775808 : UInt64) % 10 < 9)]
    by_cases h : g.round .to_nearest = 1 ∨ g.round .to_nearest = 0
    · rw [if_pos (Or.inr h), if_pos (by rcases h with h | h <;> rw [h] <;> decide)]
      congr 1
    · push Not at h
      rw [if_neg (by simp [h.1, h.2]), if_neg (by simp [h.1, h.2])]
      congr 1
  · rw [if_pos (by decide)]
    dsimp only
    rw [if_neg (by decide : ¬ (9223372036854775809 : UInt64) % 10 < 9), if_pos (Or.inl (by decide))]
    congr 1


/-- `.to_nearest` rounding of the state `±(zm + f)·10^ze'` returns a nearest normalized Number, when the guard
rounds `f` like exact rounding. -/
lemma doRoundUp_nearest_frame (result : Number) (truth : ℚ)
    (zm : UInt64) (ze' : Int) (f : ℚ) (g : Guard) (res_pos : RoundResult) (loc : Error)
    (hzm_succ : mantissaFloorSucc ≤ zm.toNat)
    (hzm_le : zm.toNat ≤ maxRepUp.toNat)
    (hf_nn : 0 ≤ f) (hf_lt : f < 1)
    (h_truth_abs : |truth| = ((zm.toNat : ℚ) + f) * 10 ^ ze')
    (hg : g.RoundsLike f)
    (h_rup_pos : g.doRoundUp false zm ze' largeRange.min largeRange.max .to_nearest loc = .ok res_pos)
    (h_result_abs : |result.toRat| = (res_pos.mantissa_.toNat : ℚ) * 10 ^ res_pos.exponent_)
    (hres_pos_mant_ne : res_pos.mantissa_ ≠ 0)
    (h_res_nn : 0 < truth → 0 ≤ result.toRat)
    (h_res_np : truth < 0 → result.toRat ≤ 0) :
    result.RoundsToNearest truth := by
  have h10 : (0 : ℚ) < (10 : ℚ) ^ ze' := zpow_pos (by norm_num) _
  have hfu : 0 ≤ f * 10 ^ ze' := mul_nonneg hf_nn h10.le
  have hfu1 : f * 10 ^ ze' < 10 ^ ze' := by nlinarith
  have h_maxR : maxRep.toNat = maxRepNat := maxRep_val
  have h_maxRU : maxRepUp.toNat = maxRepCuspTarget := rfl
  have h_maxR_q : (maxRep.toNat : ℚ) = maxRepNat := by rw [h_maxR]; norm_num
  have h_zm_lt : zm.toNat < (10 : ℕ) ^ 19 := by
    have h_pow19 : (10 : ℕ) ^ 19 = tenPow19 := by decide
    omega
  rcases lt_trichotomy zm.toNat maxRep.toNat with h_lt | h_eq | h_gt
  · -- Below `maxRep` the neighbours are `zm` and `zm + 1`.
    refine roundsToNearest_of_neighbours result truth ((zm.toNat : ℚ) * 10 ^ ze')
      (((zm.toNat : ℚ) + 1) * 10 ^ ze') (by positivity) (by rw [h_truth_abs]; linarith)
      (by rw [h_truth_abs]; linarith)
      (fun m hm h0 h1 h2 => no_normalized_in_open_ulp_gap_pos_zm ze' zm.toNat hzm_succ h_zm_lt m hm h0 h1 h2)
      (fun m hm h0 h1 h2 => no_normalized_in_open_ulp_gap_neg_zm ze' zm.toNat hzm_succ h_zm_lt m hm h0 h1 h2)
      ?_ h_res_nn h_res_np
    by_cases h_ru : g.shouldRoundUp_to_nearest zm
    · have h_val := doRoundUp_value_to_nearest_roundUp_noCusp g zm ze' h_ru (by omega) loc res_pos h_rup_pos
        hres_pos_mant_ne
      have h_f : 1 / 2 ≤ f := by
        rcases h_ru with h1 | ⟨h0, _⟩
        · exact (hg.2.1.mp h1).le
        · exact (hg.2.2.mp h0).ge
      have := mul_le_mul_of_nonneg_right h_f h10.le
      refine Or.inr ⟨by rw [h_result_abs, h_val], ?_⟩
      rw [h_truth_abs]
      linarith
    · have h_val := doRoundUp_value_no_roundUp g zm ze' h_ru h_lt.le loc res_pos h_rup_pos hres_pos_mant_ne
      have h_f : f ≤ 1 / 2 := by
        by_contra h
        exact h_ru (Or.inl (hg.2.1.mpr (lt_of_not_ge h)))
      have := mul_le_mul_of_nonneg_right h_f h10.le
      refine Or.inl ⟨by rw [h_result_abs, h_val], ?_⟩
      rw [h_truth_abs]
      linarith
  · -- At `maxRep` the result stays `maxRep`, and the next Number up is `maxRepUp`.
    have h_val := doRoundUp_value_to_nearest_maxRep g zm ze' (UInt64.toNat_inj.mp h_eq) loc res_pos h_rup_pos
      hres_pos_mant_ne
    have h_zq : (zm.toNat : ℚ) = maxRepNat := by rw [h_eq, h_maxR]; norm_num
    refine roundsToNearest_of_neighbours result truth ((maxRep.toNat : ℚ) * 10 ^ ze')
      ((maxRepCuspTarget : ℚ) * 10 ^ ze') (by positivity) (by rw [h_truth_abs, h_maxR_q, h_zq]; linarith)
      (by rw [h_truth_abs, h_zq]; linarith)
      (fun m hm h0 h1 h2 => no_normalized_in_cusp_gap_pos ze' m hm h0 h1 h2)
      (fun m hm h0 h1 h2 => no_normalized_in_cusp_gap_neg ze' m hm h0 h1 h2)
      (Or.inl ⟨by rw [h_result_abs, h_val], by rw [h_truth_abs, h_maxR_q, h_zq]; linarith⟩) h_res_nn h_res_np
  rcases Nat.lt_or_ge zm.toNat maxRepUp.toNat with h_lt_up | h_ge_up
  · -- Inside the cusp the neighbours are `maxRep` and `maxRepUp`.
    have h_zm_cases : zm.toNat = maxRepNat + 1 ∨ zm.toNat = maxRepNat + 2 := by omega
    have h_zq_lb : (maxRepNat : ℚ) + 1 ≤ zm.toNat := by
      exact_mod_cast (by omega : maxRepNat + 1 ≤ zm.toNat)
    have h_zq_ub : (zm.toNat : ℚ) ≤ maxRepNat + 2 := by
      exact_mod_cast (by omega : zm.toNat ≤ maxRepNat + 2)
    obtain ⟨v, h_val, h_cases⟩ := doRoundUp_value_cuspRange_cases g zm ze' .to_nearest h_gt hzm_le loc res_pos
      h_rup_pos hres_pos_mant_ne
    have h_push := pushOverflow_cusp_eq g zm h_gt h_lt_up
    refine roundsToNearest_of_neighbours result truth ((maxRep.toNat : ℚ) * 10 ^ ze')
      ((maxRepCuspTarget : ℚ) * 10 ^ ze') (by positivity) (by rw [h_truth_abs, h_maxR_q]; nlinarith)
      (by rw [h_truth_abs]; nlinarith)
      (fun m hm h0 h1 h2 => no_normalized_in_cusp_gap_pos ze' m hm h0 h1 h2)
      (fun m hm h0 h1 h2 => no_normalized_in_cusp_gap_neg ze' m hm h0 h1 h2) ?_ h_res_nn h_res_np
    rcases h_cases with ⟨hv, _, hb⟩ | ⟨hv, ⟨h_up, _⟩ | ⟨_, hb⟩⟩ | ⟨_, h_up, _⟩
    · -- Kept at `maxRep`: there was no round-up, so `zm = maxRep + 1` and `f ≤ 1/2`.
      have h_cond : ¬ (zm.toNat = maxRepNat + 2 ∨ g.round .to_nearest = 1 ∨ g.round .to_nearest = 0) := by
        intro h
        rw [h_push, if_pos h, round_push_six] at hb
        simp at hb
      push Not at h_cond
      obtain ⟨h_ne2, h_ne1, _⟩ := h_cond
      have h_zq : (zm.toNat : ℚ) = maxRepNat + 1 := by
        have : zm.toNat = maxRepNat + 1 := by omega
        rw [this]
        norm_num
      have h_f : f ≤ 1 / 2 := by
        by_contra h
        exact h_ne1 (hg.2.1.mpr (lt_of_not_ge h))
      have := mul_le_mul_of_nonneg_right h_f h10.le
      refine Or.inl ⟨by rw [h_result_abs, h_val, hv, h_maxR_q], ?_⟩
      rw [h_truth_abs, h_maxR_q, h_zq]
      linarith
    · omega
    · -- Moved up to `maxRepUp`: there was a round-up, so `zm + f ≥ maxRep + 3/2`.
      have h_cond : zm.toNat = maxRepNat + 2 ∨ g.round .to_nearest = 1 ∨ g.round .to_nearest = 0 := by
        by_contra h
        rw [h_push, if_neg h] at hb
        rcases round_push_three g with h3 | h3 <;> rw [h3] at hb <;> simp at hb
      have h_mid : (maxRepNat : ℚ) + 3 / 2 ≤ zm.toNat + f := by
        rcases h_cond with h | h | h
        · have : (zm.toNat : ℚ) = maxRepNat + 2 := by rw [h]; norm_num
          linarith
        · linarith [hg.2.1.mp h]
        · linarith [hg.2.2.mp h]
      have := mul_le_mul_of_nonneg_right h_mid h10.le
      refine Or.inr ⟨by rw [h_result_abs, h_val, hv]; norm_num, ?_⟩
      rw [h_truth_abs, h_maxR_q]
      linarith
    · omega
  · -- At `maxRepUp` the result stays `maxRepUp`, and the next Number up is `maxRepUp + 10`.
    have h_eq_up : zm = maxRepUp := UInt64.toNat_inj.mp (by omega)
    subst h_eq_up
    have h_val := doRoundUp_value_to_nearest_maxRepUp g ze' loc res_pos h_rup_pos hres_pos_mant_ne
    have h_zq : (maxRepUp.toNat : ℚ) = maxRepCuspTarget := by rw [h_maxRU]; norm_num
    refine roundsToNearest_of_neighbours result truth ((maxRepCuspTarget : ℚ) * 10 ^ ze')
      ((twoPow63Add12 : ℚ) * 10 ^ ze') (by positivity) (by rw [h_truth_abs, h_zq]; linarith)
      (by rw [h_truth_abs, h_zq]; linarith)
      (fun m hm h0 h1 h2 => no_normalized_in_upper_cusp_gap_pos ze' m hm h0 h1 h2)
      (fun m hm h0 h1 h2 => no_normalized_in_upper_cusp_gap_neg ze' m hm h0 h1 h2)
      (Or.inl ⟨by rw [h_result_abs, h_val], by rw [h_truth_abs, h_zq]; linarith⟩) h_res_nn h_res_np

end XRPL.Model.Protocol
