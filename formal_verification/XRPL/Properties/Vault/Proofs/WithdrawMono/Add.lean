import XRPL.Properties.Protocol.Number.Common.Rounding.Normalize128.RoundFacts
import XRPL.Properties.Vault.Common.MonotoneCore

/-! # `to_nearest` diff-sign addition below the 16-digit carry point

Away from the `maxRep` cusp the diff-sign `operator_add` rounds to a nearest
representable. We only need this for truths just below `9999999999999999500·10^j`,
where the scaled mantissa is far from the cusp. -/

namespace XRPL.Model.SingleAssetVault.WdMono

open XRPL.Model.Protocol

/-- A diff-sign `to_nearest` sum whose truth lies in
`(9999999999999999490·10^j, 9999999999999999500·10^j)` is a nearest representable. -/
lemma add_nearestTo_below_carry (x y s : Number)
    (hx : x.isNormalized) (hy : y.isNormalized)
    (hxm : x.mantissa_ ≠ 0) (hym : y.mantissa_ ≠ 0)
    (hdiff : x.negative_ ≠ y.negative_) (hnz : ¬ x.operator_eq y.operator_neg)
    (hok : Number.operator_add x y .to_nearest = .ok s) (hs : s.mantissa_ ≠ 0) (j : ℤ)
    (hlo : (9999999999999999490 : ℚ) * 10 ^ j < x.toRat + y.toRat)
    (hhi : x.toRat + y.toRat < (9999999999999999500 : ℚ) * 10 ^ j) :
    s.NearestTo (x.toRat + y.toRat) := by
  obtain ⟨M, ze0, δ, zn, sticky, hδ_low, _hδ_le, hsticky_zero, hM_pos, hM_lt, hM_big,
      htruth, hok128, hsign, hδ_lt, hsticky_pos⟩ :=
    operator_add_algorithmic_facts_diff_sign_represents x y s .to_nearest hx hy hxm hym
      hdiff hnz hok
  obtain ⟨zm, ze', f, g, res_pos, _hfloor, hzm_le, hf_nn, hf_lt, _, hval, hrounds, habs,
      hresne, hneg, hsucc, hr1, hr0, hf1, _hf0⟩ :=
    doNormalize128_algorithmic_facts_round zn M ze0 δ sticky .to_nearest hδ_low hδ_lt
      hsticky_zero hsticky_pos hM_pos (lt_trans hM_lt (by norm_num))
      (fun hst => by
        have h2 : ((10 : ℚ) ^ 20) ≤ (M.toNat : ℚ) := by exact_mod_cast hM_big hst
        nlinarith [le_of_lt hδ_lt])
      s hok128 hs
  set t := x.toRat + y.toRat with ht_def
  have hj : (0 : ℚ) < 10 ^ j := zpow_pos (by norm_num) _
  have hpos : 0 < t := lt_trans (by positivity) hlo
  have htv : t = ((zm.toNat : ℚ) + f) * 10 ^ ze' := by
    rw [← abs_of_pos hpos, htruth, hval]
  have hze : (0 : ℚ) < 10 ^ ze' := zpow_pos (by norm_num) _
  have hmaxUp : maxRepUp.toNat = 9223372036854775810 := by decide
  have hmax : maxRep.toNat = 9223372036854775807 := by decide
  -- the scaled mantissa sits far below the cusp
  have hclean : zm.toNat + 1 ≤ maxRep.toNat := by
    rcases le_or_gt ze' j with hle | hlt
    · exfalso
      have h1 : (10 : ℚ) ^ ze' ≤ 10 ^ j := zpow_le_zpow_right₀ (by norm_num) hle
      have hzmq : (zm.toNat : ℚ) ≤ 9223372036854775810 := by exact_mod_cast (hmaxUp ▸ hzm_le)
      have : t < 9223372036854775811 * 10 ^ j := by
        rw [htv]; nlinarith
      linarith
    · have h1 : (10 : ℚ) ^ (j + 1) ≤ 10 ^ ze' := zpow_le_zpow_right₀ (by norm_num) (by omega)
      have h2 : (10 : ℚ) ^ (j + 1) = 10 * 10 ^ j := by
        rw [zpow_add₀ (by norm_num)]; ring
      have hlt' : (zm.toNat : ℚ) * 10 ^ ze' < 999999999999999950 * 10 ^ ze' := by
        have : (zm.toNat : ℚ) * 10 ^ ze' ≤ t := by rw [htv]; nlinarith
        nlinarith
      have : (zm.toNat : ℚ) < 999999999999999950 := lt_of_mul_lt_mul_right hlt' (le_of_lt hze)
      have : zm.toNat < 999999999999999950 := by exact_mod_cast this
      omega
  have hsnn : s.negative_ = false := hneg.trans (zn_eq_false_of_pos hsign.1 hpos)
  have hs_abs : s.toRat = (res_pos.mantissa_.toNat : ℚ) * 10 ^ res_pos.exponent_ := by
    rw [← abs_of_nonneg (Number.toRat_nonneg_of_nonnegative s hsnn)]; exact habs
  have hcase : (s.toRat = (zm.toNat : ℚ) * 10 ^ ze' ∧ f ≤ 1 / 2)
      ∨ (s.toRat = ((zm.toNat : ℚ) + 1) * 10 ^ ze' ∧ 1 / 2 ≤ f) := by
    by_cases hru : g.shouldRoundUp_to_nearest zm
    · right
      refine ⟨by rw [hs_abs, doRoundUp_value_to_nearest_roundUp_noCusp g zm ze' hru hclean _
        res_pos hrounds hresne], ?_⟩
      rcases hru with h1 | ⟨h0, _⟩
      · exact le_of_lt (hr1 h1)
      · exact le_of_eq (hr0 h0).symm
    · left
      refine ⟨by rw [hs_abs, doRoundUp_value_no_roundUp g zm ze' hru (by omega) _ res_pos
        hrounds hresne], ?_⟩
      by_contra hgt
      push_neg at hgt
      exact hru (Or.inl (hf1 hgt))
  exact Number.nearestTo_of_gap t f zm ze' s hpos htv hf_nn hf_lt hsucc
    (by omega) hcase

end XRPL.Model.SingleAssetVault.WdMono
