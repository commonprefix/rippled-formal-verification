import XRPL.Properties.Protocol.Number.Common.Closest.Nearest
import XRPL.Properties.Protocol.Number.Common.Rounding.Normalize128Nearest
import XRPL.Properties.Protocol.Number.Add.Common.ToNearest.RoundedHelpers

/-! # `to_nearest` addition and subtraction return a nearest Number -/

namespace XRPL.Model.Protocol

/-- An exact result is a nearest Number. -/
lemma Number.roundsToNearest_of_eq {result : Number} {truth : ℚ} (h : result.toRat = truth) :
    result.RoundsToNearest truth := by
  intro m _
  rw [h, sub_self, abs_zero]
  exact abs_nonneg _

/-- A `to_nearest` addition of normalized Numbers returns a nearest Number, unless it flushes a nonzero sum to
zero. -/
lemma Number.operator_add_nearest (x y result : Number)
    (hx : x.isNormalized) (hy : y.isNormalized)
    (hok : Number.operator_add x y .to_nearest = .ok result)
    (hresult : result.mantissa_ ≠ 0 ∨ x.toRat + y.toRat = 0) :
    result.RoundsToNearest (x.toRat + y.toRat) := by
  -- Zero `y`: the model returns `x`.
  by_cases hy_guard : y.operator_eq Number.zero = true
  · have hy0 : y.toRat = 0 :=
      Number.toRat_eq_zero_of_mantissa_zero y (Number.mantissa_eq_zero_of_operator_eq_zero hy_guard)
    have h_result : result = x := by
      replace hok := Number.operator_add_ok_spec hok
      unfold Number.operator_addSpec at hok
      rw [if_pos hy_guard] at hok
      exact (Except.ok.inj (show (Except.ok x : Except Error Number) = .ok result from hok)).symm
    exact Number.roundsToNearest_of_eq (by rw [h_result, hy0, add_zero])
  -- Zero `x`: the model returns `y`.
  by_cases hx_guard : x.operator_eq Number.zero = true
  · have hx0 : x.toRat = 0 :=
      Number.toRat_eq_zero_of_mantissa_zero x (Number.mantissa_eq_zero_of_operator_eq_zero hx_guard)
    have h_result : result = y := by
      replace hok := Number.operator_add_ok_spec hok
      unfold Number.operator_addSpec at hok
      rw [if_neg hy_guard, if_pos hx_guard] at hok
      exact (Except.ok.inj (show (Except.ok y : Except Error Number) = .ok result from hok)).symm
    exact Number.roundsToNearest_of_eq (by rw [h_result, hx0, zero_add])
  -- Exact cancellation: the model returns zero.
  by_cases heq_guard : x.operator_eq y.operator_neg = true
  · have h_result : result = Number.zero := by
      replace hok := Number.operator_add_ok_spec hok
      unfold Number.operator_addSpec at hok
      rw [if_neg hy_guard, if_neg hx_guard, if_pos heq_guard] at hok
      exact (Except.ok.inj
        (show (Except.ok Number.zero : Except Error Number) = .ok result from hok)).symm
    exact Number.roundsToNearest_of_eq (by rw [h_result, Number.toRat_zero, add_truth_zero_of_eq_neg x y heq_guard])
  have hx_mant_ne : x.mantissa_ ≠ 0 := fun h => hx_guard (by rw [Number.eq_zero_of_mantissa_zero x hx h]; decide)
  have hy_mant_ne : y.mantissa_ ≠ 0 := fun h => hy_guard (by rw [Number.eq_zero_of_mantissa_zero y hy h]; decide)
  have h_truth_ne : x.toRat + y.toRat ≠ 0 :=
    operator_add_truth_ne x y hx hy hx_mant_ne hy_mant_ne heq_guard .to_nearest result hok
  have hres : result.mantissa_ ≠ 0 := hresult.resolve_right h_truth_ne
  by_cases h_sign_eq : x.negative_ = y.negative_
  · obtain ⟨zm, ze', f, g, res_pos, hs⟩ :=
      operator_add_algorithmic_facts_same_sign_anyMode x y result .to_nearest hx hy hx_mant_ne hy_mant_ne
        h_sign_eq heq_guard hok
    exact doRoundUp_nearest_frame result (x.toRat + y.toRat) zm ze' f g res_pos .overflow hs.zm_succ
      hs.zm_le_maxRepUp hs.f_nonneg hs.f_lt_one hs.value_eq (Guard.roundsLike_of_represents hs.represents_f)
      hs.rounds hs.result_abs hs.res_mant_ne
      (fun h_pos => Number.toRat_nonneg_of_nonnegative result
        (hs.result_neg.trans (add_same_sign_xn_false_of_truth_pos x y h_sign_eq h_pos)))
      (fun h_neg => Number.toRat_nonpos_of_negative result
        (hs.result_neg.trans (add_same_sign_xn_true_of_truth_neg x y h_sign_eq h_neg)))
  · obtain ⟨M, ze0, δ, zn, sticky, hδ_low, _hδ_le, hsticky_zero, hM_pos, hM_lt, hM_big,
        htruth, hok128, hsign, hδ_lt, hsticky_pos⟩ :=
      operator_add_algorithmic_facts_diff_sign_represents x y result .to_nearest hx hy
        hx_mant_ne hy_mant_ne h_sign_eq heq_guard hok
    obtain ⟨zm, ze', f, g, res_pos, hzm_succ, hzm_le, hf_nn, hf_lt, h_value, h_rup_pos, h_result_abs,
        hres_pos_mant_ne, h_neg, hg⟩ :=
      doNormalize128_nearest_facts zn M ze0 δ sticky hδ_low hδ_lt hsticky_zero hsticky_pos hM_pos
        (lt_trans hM_lt (by norm_num))
        (fun hst => by
          have h2 : ((10 : ℚ) ^ 20) ≤ (M.toNat : ℚ) := by exact_mod_cast hM_big hst
          linarith [le_of_lt hδ_lt])
        result hok128 hres
    exact doRoundUp_nearest_frame result (x.toRat + y.toRat) zm ze' f g res_pos .normalize2 hzm_succ hzm_le
      hf_nn hf_lt (htruth.trans h_value) hg h_rup_pos h_result_abs hres_pos_mant_ne
      (fun h_pos => Number.toRat_nonneg_of_nonnegative result (h_neg.trans (zn_eq_false_of_pos hsign.1 h_pos)))
      (fun h_negT => Number.toRat_nonpos_of_negative result (h_neg.trans (zn_eq_true_of_neg hsign.2 h_negT)))

/-- A `to_nearest` subtraction of normalized Numbers returns a nearest Number, unless it flushes a nonzero
difference to zero. -/
lemma Number.operator_sub_nearest (x y result : Number)
    (hx : x.isNormalized) (hy : y.isNormalized)
    (hok : Number.operator_sub x y .to_nearest = .ok result)
    (hresult : result.mantissa_ ≠ 0 ∨ x.toRat - y.toRat = 0) :
    result.RoundsToNearest (x.toRat - y.toRat) := by
  unfold Number.operator_sub at hok
  have h_truth_eq : x.toRat - y.toRat = x.toRat + y.operator_neg.toRat := by
    rw [Number.toRat_neg]
    ring
  rw [h_truth_eq] at hresult ⊢
  exact Number.operator_add_nearest x y.operator_neg result hx (Number.operator_neg_isNormalized y hy) hok hresult

end XRPL.Model.Protocol
