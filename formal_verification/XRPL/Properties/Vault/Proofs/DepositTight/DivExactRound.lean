import XRPL.Properties.Protocol.Number.Common.Rounding.DoRoundUp.ValueChar

/-! # `doRoundUp` rounds any fraction on the guard's side of the half -/

namespace XRPL.Model.SingleAssetVault.DepTight

open XRPL.Model.Protocol

/-- A guard that does not round up in `.to_nearest` represents at most one half. -/
lemma noRoundUp_half (g : Guard) (m : UInt64) (f : ℚ) (hrep : represents g f)
    (hru : ¬ g.shouldRoundUp_to_nearest m) : f ≤ 1 / 2 := by
  by_contra h
  exact hru (Or.inl (represents_f_gt_half hrep (lt_of_not_ge h)))

/-- A guard whose round value is neither up nor a tie represents less than one half. -/
lemma lt_half_of_round_ne (g : Guard) (f : ℚ) (hrep : represents g f)
    (hr1 : g.round .to_nearest ≠ 1) (hr0 : g.round .to_nearest ≠ 0) : f < 1 / 2 := by
  by_contra h
  rcases lt_or_eq_of_le (le_of_not_gt h) with h | h
  · exact hr1 (represents_f_gt_half hrep h)
  · exact hr0 (represents_half_round_eq_zero hrep h.symm)

/-- `to_nearest` `doRoundUp` meets the sharp relative bound for any true fraction `f`
that lies on the same side of `1/2` as a fraction `ft` the guard represents. -/
lemma doRoundUp_to_nearest_cell (g : Guard) (zm : UInt64) (ze : Int) (ft f : ℚ)
    (hrep : represents g ft) (hf_nn : 0 ≤ f) (hf_le1 : f ≤ 1)
    (hlt : ft < 1 / 2 → f ≤ 1 / 2) (hgt : 1 / 2 < ft → 1 / 2 ≤ f)
    (heq : ft = 1 / 2 → f = 1 / 2)
    (h_zm_gt : (mantissaFloor : ℕ) < zm.toNat)
    (h_zm_le : zm.toNat ≤ maxRepUp.toNat)
    (loc : Error) (res : RoundResult)
    (hok : g.doRoundUp false zm ze largeRange.min largeRange.max .to_nearest loc = .ok res)
    (hne : res.mantissa_ ≠ 0) :
    |(res.mantissa_.toNat : ℚ) * 10 ^ res.exponent_ - ((zm.toNat : ℚ) + f) * 10 ^ ze|
      ≤ ((zm.toNat : ℚ) + f) * 10 ^ ze * (5 / (2 ^ 63 + 7 : ℕ)) := by
  have hu : (0 : ℚ) ≤ (10 : ℚ) ^ ze := le_of_lt (zpow_pos (by norm_num) _)
  have hN : (((2 ^ 63 + 7 : ℕ)) : ℚ) = 9223372036854775815 := by push_cast; norm_num
  have hzm_q : (922337203685477581 : ℚ) ≤ (zm.toNat : ℚ) := by
    exact_mod_cast (show 922337203685477581 ≤ zm.toNat by omega)
  have hmr : maxRep.toNat = maxRepNat := maxRep_val
  by_cases hcusp : maxRep.toNat < zm.toNat
  · exact doRoundUp_rounds_to_nearest_supTight_cusp_bounds g zm ze f hf_nn hf_le1 hcusp h_zm_le loc res hok hne
  push Not at hcusp
  by_cases hlow : zm.toNat + 1 ≤ maxRep.toNat
  · by_cases hru : g.shouldRoundUp_to_nearest zm
    · have hval := doRoundUp_value_to_nearest_roundUp_noCusp g zm ze hru hlow loc res hok hne
      have hf_ge : 1 / 2 ≤ f := by
        rcases hru with h1 | ⟨h0, _⟩
        · exact hgt (represents_round_eq_one hrep h1)
        · exact le_of_eq (heq (represents_round_eq_zero hrep h0)).symm
      rw [hval, show ((zm.toNat : ℚ) + 1) * 10 ^ ze - ((zm.toNat : ℚ) + f) * 10 ^ ze
          = (1 - f) * 10 ^ ze from by ring, abs_mul, abs_of_nonneg (by linarith),
        abs_of_nonneg hu, hN]
      have h : 1 - f ≤ ((zm.toNat : ℚ) + f) * (5 / 9223372036854775815) := by linarith
      calc (1 - f) * 10 ^ ze ≤ (((zm.toNat : ℚ) + f) * (5 / 9223372036854775815)) * 10 ^ ze :=
            mul_le_mul_of_nonneg_right h hu
        _ = _ := by ring
    · have hval := doRoundUp_value_no_roundUp g zm ze hru (by omega) loc res hok hne
      have hf_le : f ≤ 1 / 2 := by
        rcases lt_or_eq_of_le (noRoundUp_half g zm ft hrep hru) with h | h
        · exact hlt h
        · exact le_of_eq (heq h)
      rw [hval, show (zm.toNat : ℚ) * 10 ^ ze - ((zm.toNat : ℚ) + f) * 10 ^ ze
          = -(f * 10 ^ ze) from by ring, abs_neg, abs_mul, abs_of_nonneg hf_nn,
        abs_of_nonneg hu, hN]
      have h : f ≤ ((zm.toNat : ℚ) + f) * (5 / 9223372036854775815) := by linarith
      calc f * 10 ^ ze ≤ (((zm.toNat : ℚ) + f) * (5 / 9223372036854775815)) * 10 ^ ze :=
            mul_le_mul_of_nonneg_right h hu
        _ = _ := by ring
  · have hzm_eq : zm = maxRep := UInt64.toNat_inj.mp (by omega)
    have hzq : (zm.toNat : ℚ) = 9223372036854775807 := by
      rw [hzm_eq, hmr]; norm_num
    have hclose : ∀ E : ℚ, |E| ≤ 3 →
        |E * 10 ^ ze| ≤ ((zm.toNat : ℚ) + f) * 10 ^ ze * (5 / (2 ^ 63 + 7 : ℕ)) := by
      intro E hE
      rw [abs_mul, abs_of_nonneg hu, hN, hzq]
      have h : |E| ≤ ((9223372036854775807 : ℚ) + f) * (5 / 9223372036854775815) := by
        linarith
      calc |E| * 10 ^ ze ≤ (((9223372036854775807 : ℚ) + f) * (5 / 9223372036854775815))
            * 10 ^ ze := mul_le_mul_of_nonneg_right h hu
        _ = _ := by ring
    -- At `maxRep` `doRoundUp` keeps `maxRep` whatever the guard, an error of `f` units.
    have hval := doRoundUp_value_to_nearest_maxRep g zm ze hzm_eq loc res hok hne
    rw [hval, ← hzm_eq, show (zm.toNat : ℚ) * 10 ^ ze - ((zm.toNat : ℚ) + f) * 10 ^ ze
        = (-f) * 10 ^ ze from by ring]
    exact hclose _ (by rw [abs_neg, abs_of_nonneg hf_nn]; linarith)

end XRPL.Model.SingleAssetVault.DepTight
