import XRPL.Properties.Protocol.Number.Common.Rounding.DoRoundUp.ValueChar

/-! # `doRoundUp` rounds any fraction on the guard's side of the half -/

namespace XRPL.Model.SingleAssetVault.DepTight

open XRPL.Model.Protocol

set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false

/-- `doRoundUp_rounds_to_nearest_supTight_cusp` for any fraction `f ∈ [0,1]`. -/
lemma doRoundUp_to_nearest_cusp_any (g : Guard) (zm : UInt64) (ze : Int) (f : ℚ)
    (hf_nn : 0 ≤ f) (hf_lt1 : f ≤ 1)
    (h_zm_gt : maxRep.toNat < zm.toNat)
    (h_zm_le : zm.toNat ≤ maxRepUp.toNat)
    (loc : Error) (res_pos : RoundResult)
    (hok_pos : g.doRoundUp false zm ze largeRange.min largeRange.max .to_nearest loc = .ok res_pos)
    (hres_pos_mant_ne : res_pos.mantissa_ ≠ 0) :
    |(res_pos.mantissa_.toNat : ℚ) * 10 ^ res_pos.exponent_ -
       ((zm.toNat : ℚ) + f) * 10 ^ ze|
      ≤ ((zm.toNat : ℚ) + f) * 10 ^ ze * (5 / (2 ^ 63 + 7 : ℕ)) := by
  have h10ze_pos : (0 : ℚ) < (10 : ℚ) ^ ze := zpow_pos (by norm_num) _
  have h10ze_nn : (0 : ℚ) ≤ (10 : ℚ) ^ ze := le_of_lt h10ze_pos
  have h_denom : (((2 ^ 63 + 7 : ℕ)) : ℚ) = 9223372036854775815 := by push_cast; norm_num
  have hzm_ge_nat : (9223372036854775808 : ℕ) ≤ zm.toNat := by
    rw [maxRep_val] at h_zm_gt; omega
  have hzm_ge_q : (9223372036854775808 : ℚ) ≤ (zm.toNat : ℚ) := by exact_mod_cast hzm_ge_nat
  -- A reusable closer: |E| ≤ 3 suffices against the allowance.
  have h_close : ∀ E : ℚ, |E| ≤ 3 →
      |E| * (10 : ℚ) ^ ze ≤ ((zm.toNat : ℚ) + f) * 10 ^ ze * (5 / ((2 ^ 63 + 7 : ℕ) : ℚ)) := by
    intro E hE
    rw [h_denom]
    rw [show ((zm.toNat : ℚ) + f) * 10 ^ ze * (5 / 9223372036854775815)
          = (5 * ((zm.toNat : ℚ) + f) / 9223372036854775815) * 10 ^ ze from by ring]
    apply mul_le_mul_of_nonneg_right _ h10ze_nn
    rw [le_div_iff₀ (by norm_num : (0 : ℚ) < 9223372036854775815)]
    nlinarith [hE, hzm_ge_q, hf_nn]
  unfold Guard.doRoundUp Guard.bringIntoRange at hok_pos
  dsimp only [Guard.doDropDigit] at hok_pos
  by_cases h_eq_up : zm = maxRepUp
  · -- zm = maxRepUp: pushOverflow no-op; both round paths land on value maxRepUp · 10^ze.
    subst h_eq_up
    have h_pof : g.pushOverflow maxRepUp .to_nearest = g := by
      unfold Guard.pushOverflow
      rw [if_neg]
      intro ⟨_, h⟩
      exact absurd (UInt64.lt_iff_toNat_lt.mp h) (lt_irrefl _)
    rw [h_pof] at hok_pos
    have h_not_noncusp : ¬ (maxRepUp < largeRange.max ∧ maxRepUp < maxRep) := by decide
    have h_not_cusp : ¬ (maxRep < maxRepUp ∧ maxRepUp < maxRepUp) := by decide
    have hup_q : ((maxRepUp.toNat : ℕ) : ℚ) = 9223372036854775810 := by
      rw [show maxRepUp.toNat = maxRepUpNat from rfl]; norm_num
    by_cases h_ru : (g.round .to_nearest == 1 || (g.round .to_nearest == 0 && maxRepUp % 2 == 1)) = true
    · -- round-up: drop-digit path; pushed-zero guard always rounds down.
      rw [show (g.round .to_nearest == 1 || (g.round .to_nearest == 0 && maxRepUp % 2 == 1)) = true
          from h_ru] at hok_pos
      rw [if_pos rfl, if_neg h_not_noncusp, if_neg h_not_cusp] at hok_pos
      have hdig : (g.push (maxRepUp % 10)).digits_.toNat < 5764607523034234880 := by
        have h := toNat_push_digits g (maxRepUp % 10)
        have h0 : (maxRepUp % 10).toNat = 0 := by decide
        rw [h0] at h
        have hlt : g.digits_.toNat < 2 ^ 64 := by
          have hsz := UInt64.toNat_lt_size g.digits_
          rwa [show UInt64.size = 2 ^ 64 from rfl] at hsz
        omega
      have h_ru'_false : ((g.push (maxRepUp % 10)).round .to_nearest == 1
          || ((g.push (maxRepUp % 10)).round .to_nearest == 0 && (maxRepUp / 10) % 2 == 1)) = false := by
        by_cases hemp : (g.push (maxRepUp % 10)).empty = true
        · rw [show (g.push (maxRepUp % 10)).round .to_nearest = -2 from by
            unfold Guard.round; rw [if_pos hemp]]
          rfl
        · rw [round_to_nearest_def hemp]
          have h5 : (0x5000_0000_0000_0000 : UInt64).toNat = 5764607523034234880 := by decide
          have h_not_gt : ¬ ((g.push (maxRepUp % 10)).digits_ > 0x5000_0000_0000_0000) := by
            intro h
            have := UInt64.lt_iff_toNat_lt.mp h
            rw [h5] at this; omega
          have h_lt : (g.push (maxRepUp % 10)).digits_ < 0x5000_0000_0000_0000 := by
            rw [UInt64.lt_iff_toNat_lt, h5]; exact hdig
          rw [if_neg h_not_gt, if_pos h_lt]
          rfl
      rw [show ((g.push (maxRepUp % 10)).round .to_nearest == 1
          || ((g.push (maxRepUp % 10)).round .to_nearest == 0 && (maxRepUp / 10) % 2 == 1)) = false
          from h_ru'_false] at hok_pos
      simp only [Bool.false_eq_true, if_false] at hok_pos
      have h_resc : maxRepUp / 10 < largeRange.min ∧ maxRepUp / 10 ≠ 0 := by decide
      rw [if_pos h_resc] at hok_pos
      simp only [] at hok_pos
      by_cases h_under : ze + 1 - 1 < minExponent ∨ (maxRepUp / 10) * 10 = 0
      · exfalso; apply hres_pos_mant_ne
        simp only [if_pos h_under] at hok_pos
        have hzexp : ¬ ((-2147483648 : Int) > maxExponent) := by norm_num [maxExponent]
        simp only [hzexp, if_false] at hok_pos
        exact (Except.ok.inj hok_pos).symm ▸ rfl
      · push Not at h_under
        obtain ⟨hexp, -⟩ := h_under
        have h_not_under : ¬ (ze + 1 - 1 < minExponent ∨ (maxRepUp / 10) * 10 = 0) := by
          push Not; exact ⟨hexp, by decide⟩
        simp only [if_neg h_not_under] at hok_pos
        have h_no_ovf : ¬ (ze + 1 - 1 > maxExponent) := by
          intro h_ovf; simp only [if_pos h_ovf] at hok_pos; simp at hok_pos
        simp only [if_neg h_no_ovf] at hok_pos
        obtain rfl := Except.ok.inj hok_pos
        change |(((maxRepUp / 10) * 10).toNat : ℚ) * 10 ^ (ze + 1 - 1) -
            ((maxRepUp.toNat : ℚ) + f) * 10 ^ ze|
          ≤ ((maxRepUp.toNat : ℚ) + f) * 10 ^ ze * (5 / ((2 ^ 63 + 7 : ℕ) : ℚ))
        rw [show ((maxRepUp / 10) * 10).toNat = 9223372036854775810 from by decide,
            show (ze + 1 - 1 : ℤ) = ze from by ring, hup_q,
            show (((9223372036854775810 : ℕ)) : ℚ) = (9223372036854775810 : ℚ) from by norm_num]
        rw [show (9223372036854775810 : ℚ) * 10 ^ ze - (9223372036854775810 + f) * 10 ^ ze
              = -(f * 10 ^ ze) from by ring, abs_neg, abs_mul,
            abs_of_nonneg h10ze_nn, abs_of_nonneg hf_nn]
        have hcf := h_close f (by rw [abs_of_nonneg hf_nn]; linarith)
        rw [abs_of_nonneg hf_nn, hup_q] at hcf
        exact hcf
    · -- no round-up: the no-roundUp cusp test fails; keep maxRepUp.
      rw [Bool.not_eq_true] at h_ru
      rw [show (g.round .to_nearest == 1 || (g.round .to_nearest == 0 && maxRepUp % 2 == 1)) = false
          from h_ru] at hok_pos
      simp only [Bool.false_eq_true, if_false] at hok_pos
      rw [if_neg h_not_cusp] at hok_pos
      have h_no_resc : ¬ (maxRepUp < largeRange.min ∧ maxRepUp ≠ 0) := by decide
      rw [if_neg h_no_resc] at hok_pos
      simp only [] at hok_pos
      by_cases h_under : ze < minExponent ∨ (maxRepUp : UInt64) = 0
      · exfalso; apply hres_pos_mant_ne
        simp only [if_pos h_under] at hok_pos
        have hzexp : ¬ ((-2147483648 : Int) > maxExponent) := by norm_num [maxExponent]
        simp only [hzexp, if_false] at hok_pos
        exact (Except.ok.inj hok_pos).symm ▸ rfl
      · push Not at h_under
        obtain ⟨hexp, -⟩ := h_under
        have h_not_under : ¬ (ze < minExponent ∨ (maxRepUp : UInt64) = 0) := by
          push Not; exact ⟨hexp, by decide⟩
        simp only [if_neg h_not_under] at hok_pos
        have h_no_ovf : ¬ (ze > maxExponent) := by
          intro h_ovf; simp only [if_pos h_ovf] at hok_pos; simp at hok_pos
        simp only [if_neg h_no_ovf] at hok_pos
        obtain rfl := Except.ok.inj hok_pos
        change |(maxRepUp.toNat : ℚ) * 10 ^ ze - ((maxRepUp.toNat : ℚ) + f) * 10 ^ ze|
          ≤ ((maxRepUp.toNat : ℚ) + f) * 10 ^ ze * (5 / ((2 ^ 63 + 7 : ℕ) : ℚ))
        rw [show (maxRepUp.toNat : ℚ) * 10 ^ ze - ((maxRepUp.toNat : ℚ) + f) * 10 ^ ze
              = -(f * 10 ^ ze) from by ring, abs_neg, abs_mul,
            abs_of_nonneg h10ze_nn, abs_of_nonneg hf_nn]
        have := h_close f (by rw [abs_of_nonneg hf_nn]; linarith)
        rw [abs_of_nonneg hf_nn] at this
        exact this
  · -- maxRep < zm < maxRepUp: clamp to maxRepUp (round-up) or maxRep (no round-up).
    have h_lt_up_nat : zm.toNat < maxRepUp.toNat := by
      have hne : zm.toNat ≠ maxRepUp.toNat := fun h => h_eq_up (UInt64.toNat_inj.mp h)
      omega
    have hzm_le_q : (zm.toNat : ℚ) ≤ 9223372036854775809 := by
      exact_mod_cast (by rw [show maxRepUp.toNat = maxRepUpNat from rfl] at h_lt_up_nat
                        ; omega : zm.toNat ≤ 9223372036854775809)
    have h_m_lt_up : zm < maxRepUp := UInt64.lt_iff_toNat_lt.mpr h_lt_up_nat
    have h_maxRep_lt_m : maxRep < zm := UInt64.lt_iff_toNat_lt.mpr h_zm_gt
    have h_cusp_cond : maxRep < zm ∧ zm < maxRepUp := ⟨h_maxRep_lt_m, h_m_lt_up⟩
    have h_not_noncusp : ¬ (zm < largeRange.max ∧ zm < maxRep) := by
      intro ⟨_, h⟩
      exact absurd (UInt64.lt_iff_toNat_lt.mp h) (by omega)
    by_cases h_ru : ((g.pushOverflow zm .to_nearest).round .to_nearest == 1
        || ((g.pushOverflow zm .to_nearest).round .to_nearest == 0 && zm % 2 == 1)) = true
    · -- round-up: clamp up to maxRepUp.
      rw [show ((g.pushOverflow zm .to_nearest).round .to_nearest == 1
          || ((g.pushOverflow zm .to_nearest).round .to_nearest == 0 && zm % 2 == 1)) = true from h_ru] at hok_pos
      rw [if_pos rfl, if_neg h_not_noncusp, if_pos h_cusp_cond] at hok_pos
      have h_no_resc : ¬ (maxRepUp < largeRange.min ∧ maxRepUp ≠ 0) := by decide
      rw [if_neg h_no_resc] at hok_pos
      simp only [] at hok_pos
      by_cases h_under : ze < minExponent ∨ (maxRepUp : UInt64) = 0
      · exfalso; apply hres_pos_mant_ne
        simp only [if_pos h_under] at hok_pos
        have hzexp : ¬ ((-2147483648 : Int) > maxExponent) := by norm_num [maxExponent]
        simp only [hzexp, if_false] at hok_pos
        exact (Except.ok.inj hok_pos).symm ▸ rfl
      · push Not at h_under
        obtain ⟨hexp, -⟩ := h_under
        have h_not_under : ¬ (ze < minExponent ∨ (maxRepUp : UInt64) = 0) := by
          push Not; exact ⟨hexp, by decide⟩
        simp only [if_neg h_not_under] at hok_pos
        have h_no_ovf : ¬ (ze > maxExponent) := by
          intro h_ovf; simp only [if_pos h_ovf] at hok_pos; simp at hok_pos
        simp only [if_neg h_no_ovf] at hok_pos
        obtain rfl := Except.ok.inj hok_pos
        change |(maxRepUp.toNat : ℚ) * 10 ^ ze - ((zm.toNat : ℚ) + f) * 10 ^ ze|
          ≤ ((zm.toNat : ℚ) + f) * 10 ^ ze * (5 / ((2 ^ 63 + 7 : ℕ) : ℚ))
        rw [show (maxRepUp.toNat : ℚ) * 10 ^ ze - ((zm.toNat : ℚ) + f) * 10 ^ ze
              = ((maxRepUp.toNat : ℚ) - (zm.toNat : ℚ) - f) * 10 ^ ze from by ring,
            abs_mul, abs_of_nonneg h10ze_nn]
        apply h_close
        have hup_q : ((maxRepUp.toNat : ℕ) : ℚ) = 9223372036854775810 := by
          rw [show maxRepUp.toNat = maxRepUpNat from rfl]; norm_num
        rw [abs_le]
        constructor
        · rw [hup_q]; linarith
        · rw [hup_q]; linarith
    · -- no round-up: clamp down to maxRep.
      rw [Bool.not_eq_true] at h_ru
      rw [show ((g.pushOverflow zm .to_nearest).round .to_nearest == 1
          || ((g.pushOverflow zm .to_nearest).round .to_nearest == 0 && zm % 2 == 1)) = false from h_ru] at hok_pos
      simp only [Bool.false_eq_true, if_false] at hok_pos
      rw [if_pos h_cusp_cond] at hok_pos
      have h_no_resc : ¬ (maxRep < largeRange.min ∧ maxRep ≠ 0) := by decide
      rw [if_neg h_no_resc] at hok_pos
      simp only [] at hok_pos
      by_cases h_under : ze < minExponent ∨ (maxRep : UInt64) = 0
      · exfalso; apply hres_pos_mant_ne
        simp only [if_pos h_under] at hok_pos
        have hzexp : ¬ ((-2147483648 : Int) > maxExponent) := by norm_num [maxExponent]
        simp only [hzexp, if_false] at hok_pos
        exact (Except.ok.inj hok_pos).symm ▸ rfl
      · push Not at h_under
        obtain ⟨hexp, -⟩ := h_under
        have h_not_under : ¬ (ze < minExponent ∨ (maxRep : UInt64) = 0) := by
          push Not; exact ⟨hexp, by decide⟩
        simp only [if_neg h_not_under] at hok_pos
        have h_no_ovf : ¬ (ze > maxExponent) := by
          intro h_ovf; simp only [if_pos h_ovf] at hok_pos; simp at hok_pos
        simp only [if_neg h_no_ovf] at hok_pos
        obtain rfl := Except.ok.inj hok_pos
        change |(maxRep.toNat : ℚ) * 10 ^ ze - ((zm.toNat : ℚ) + f) * 10 ^ ze|
          ≤ ((zm.toNat : ℚ) + f) * 10 ^ ze * (5 / ((2 ^ 63 + 7 : ℕ) : ℚ))
        rw [show (maxRep.toNat : ℚ) * 10 ^ ze - ((zm.toNat : ℚ) + f) * 10 ^ ze
              = ((maxRep.toNat : ℚ) - (zm.toNat : ℚ) - f) * 10 ^ ze from by ring,
            abs_mul, abs_of_nonneg h10ze_nn]
        apply h_close
        have hrep_q : ((maxRep.toNat : ℕ) : ℚ) = 9223372036854775807 := by
          rw [maxRep_val]; norm_num
        rw [abs_le]
        constructor
        · rw [hrep_q]; linarith
        · rw [hrep_q]; linarith

lemma round_eq_one_ne_empty {g : Guard} (h : g.round .to_nearest = 1) : ¬ g.empty := by
  intro he
  unfold Guard.round at h
  rw [if_pos he] at h
  exact absurd h (by decide)

lemma round_eq_zero_ne_empty {g : Guard} (h : g.round .to_nearest = 0) : ¬ g.empty := by
  intro he
  unfold Guard.round at h
  rw [if_pos he] at h
  exact absurd h (by decide)

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
  · exact doRoundUp_to_nearest_cusp_any g zm ze f hf_nn hf_le1 hcusp h_zm_le loc res hok hne
  push Not at hcusp
  by_cases hlow : zm.toNat + 1 ≤ maxRep.toNat
  · have hzm_hi : (zm.toNat : ℚ) ≤ 9223372036854775806 := by
      exact_mod_cast (show zm.toNat ≤ 9223372036854775806 by omega)
    by_cases hru : g.shouldRoundUp_to_nearest zm
    · have hval := doRoundUp_value_to_nearest_roundUp_noCusp g zm ze hru hlow loc res hok hne
      have hf_ge : 1 / 2 ≤ f := by
        rcases hru with h1 | ⟨h0, _⟩
        · exact hgt ((round_correct (round_eq_one_ne_empty h1) hrep).1.mp h1)
        · exact le_of_eq (heq ((round_correct (round_eq_zero_ne_empty h0) hrep).2.2.mp h0)).symm
      rw [hval, show ((zm.toNat : ℚ) + 1) * 10 ^ ze - ((zm.toNat : ℚ) + f) * 10 ^ ze
          = (1 - f) * 10 ^ ze from by ring, abs_mul, abs_of_nonneg (by linarith),
        abs_of_nonneg hu, hN]
      have h : 1 - f ≤ ((zm.toNat : ℚ) + f) * (5 / 9223372036854775815) := by linarith
      calc (1 - f) * 10 ^ ze ≤ (((zm.toNat : ℚ) + f) * (5 / 9223372036854775815)) * 10 ^ ze :=
            mul_le_mul_of_nonneg_right h hu
        _ = _ := by ring
    · have hval := doRoundUp_value_no_roundUp g zm ze hru (by omega) loc res hok hne
      have hf_le : f ≤ 1 / 2 := by
        by_cases hemp : g.empty = true
        · obtain ⟨hd, hx⟩ : g.digits_ = 0 ∧ g.xbit_ = false := by
            have h : (g.digits_ == 0 && !g.xbit_) = true := hemp
            rw [Bool.and_eq_true] at h
            exact ⟨beq_iff_eq.mp h.1, by simpa using h.2⟩
          have hft0 : ft = 0 := represents_eq_zero_of_digits_zero_xbit_false hd hx hrep
          exact hlt (by rw [hft0]; norm_num)
        · obtain ⟨hp, -, hz⟩ := round_correct hemp hrep
          rcases lt_trichotomy ft (1 / 2) with h | h | h
          · exact hlt h
          · exact le_of_eq (heq h)
          · exact absurd (Or.inl (hp.mpr h)) hru
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
    by_cases hru : g.shouldRoundUp_to_nearest zm
    · rcases hru with h1 | h0
      · have hval := doRoundUp_value_to_nearest_roundUp_cusp_round1 g zm ze hzm_eq h1 loc res
          hok hne
        rw [hval, ← hzm_eq, show (zm.toNat : ℚ) * 10 ^ ze - ((zm.toNat : ℚ) + f) * 10 ^ ze
          = (-f) * 10 ^ ze from by ring]
        exact hclose _ (by rw [abs_neg, abs_of_nonneg hf_nn]; linarith)
      · have hval := doRoundUp_value_to_nearest_roundUp_cusp g zm ze hzm_eq h0 loc res hok hne
        rw [hval, show (9223372036854775810 : ℚ) * 10 ^ ze - ((zm.toNat : ℚ) + f) * 10 ^ ze
          = ((9223372036854775810 : ℚ) - zm.toNat - f) * 10 ^ ze from by ring]
        exact hclose _ (by rw [hzq, abs_le]; constructor <;> norm_num <;> linarith)
    · have hval := doRoundUp_value_no_roundUp g zm ze hru (by omega) loc res hok hne
      rw [hval, show (zm.toNat : ℚ) * 10 ^ ze - ((zm.toNat : ℚ) + f) * 10 ^ ze
          = (-f) * 10 ^ ze from by ring]
      exact hclose _ (by rw [abs_neg, abs_of_nonneg hf_nn]; linarith)

end XRPL.Model.SingleAssetVault.DepTight
