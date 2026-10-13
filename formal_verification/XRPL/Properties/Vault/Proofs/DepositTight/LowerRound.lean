import XRPL.Properties.Protocol.Number.Common.Rounding.DoRoundUp.ValueChar
import XRPL.Properties.Protocol.Number.Common.Rounding.Guard

/-! # Where a `.to_nearest` `doRoundUp` can land below its input -/

namespace XRPL.Model.SingleAssetVault.DepTight

open XRPL.Model.Protocol

lemma push_round_one (g : Guard) (d : UInt64) (hd : 6 ≤ d.toNat) (hd' : d.toNat < 16) :
    (g.push d).round .to_nearest = 1 := by
  have hdig := toNat_push_digits g d
  have hmod : d.toNat % 16 = d.toNat := Nat.mod_eq_of_lt hd'
  rw [hmod] at hdig
  have hne : ¬ (g.push d).empty = true := by
    intro h
    have h0 : (g.push d).digits_ = 0 := by
      have h' : ((g.push d).digits_ == 0 && !(g.push d).xbit_) = true := h
      rw [Bool.and_eq_true] at h'
      exact beq_iff_eq.mp h'.1
    have : (g.push d).digits_.toNat = 0 := by rw [h0]; rfl
    omega
  rw [round_to_nearest_def hne]
  have hgt : (g.push d).digits_ > 5764607523034234880 := by
    show (5764607523034234880 : UInt64) < (g.push d).digits_
    rw [UInt64.lt_iff_toNat_lt, show (5764607523034234880 : UInt64).toNat = 5764607523034234880
      from rfl]
    omega
  rw [if_pos hgt]

lemma push3_round_lt (g : Guard) :
    (g.push 3).round .to_nearest ≠ 1 ∧ (g.push 3).round .to_nearest ≠ 0 := by
  by_cases hemp : (g.push 3).empty = true
  · have : (g.push 3).round .to_nearest = -2 := by unfold Guard.round; rw [if_pos hemp]
    rw [this]; decide
  · have hdig := toNat_push_digits g 3
    have h3 : (3 : UInt64).toNat = 3 := rfl
    rw [h3] at hdig
    have hsz : g.digits_.toNat < 2 ^ 64 := UInt64.toNat_lt_size g.digits_
    have hlt : (g.push 3).digits_ < 5764607523034234880 := by
      rw [UInt64.lt_iff_toNat_lt, show (5764607523034234880 : UInt64).toNat = 5764607523034234880
        from rfl]
      omega
    have hngt : ¬ (g.push 3).digits_ > 5764607523034234880 := by
      intro h
      have := UInt64.lt_iff_toNat_lt.mp h
      have := UInt64.lt_iff_toNat_lt.mp hlt
      omega
    rw [round_to_nearest_def hemp, if_neg hngt, if_pos hlt]
    decide

/-- The pushed overflow guard of the two interior cusp mantissas. -/
lemma pushOverflow_cusp (g : Guard) (m : UInt64) (hm : m.toNat = 9223372036854775808 ∨
    m.toNat = 9223372036854775809) :
    (g.pushOverflow m .to_nearest).round .to_nearest = 1 ∨
      (m.toNat = 9223372036854775808 ∧ g.round .to_nearest ≠ 1 ∧ g.round .to_nearest ≠ 0 ∧
        (g.pushOverflow m .to_nearest).round .to_nearest ≠ 1 ∧
        (g.pushOverflow m .to_nearest).round .to_nearest ≠ 0) := by
  rcases hm with hm | hm
  · have hm' : m = 9223372036854775808 := UInt64.toNat_inj.mp (by rw [hm]; rfl)
    subst hm'
    by_cases hr : g.round .to_nearest = 1 ∨ g.round .to_nearest = 0
    · left
      have hp : g.pushOverflow 9223372036854775808 .to_nearest = g.push 6 := by
        have hb : (g.round .to_nearest == 1 || (g.round .to_nearest == 0 &&
            (9223372036854775808 : UInt64) == maxRep + (maxRepUp - maxRep) / 2)) = true := by
          rcases hr with h | h <;> (rw [h]; decide)
        unfold Guard.pushOverflow
        rw [if_pos (by decide)]
        simp only [show (9223372036854775808 : UInt64) % 10 < 9 from by decide, if_true, hb]
        rw [if_neg (by decide)]
        congr 1
      rw [hp]
      exact push_round_one g 6 (by decide) (by decide)
    · right
      push Not at hr
      have hb : (g.round .to_nearest == 1 || (g.round .to_nearest == 0 &&
          (9223372036854775808 : UInt64) == maxRep + (maxRepUp - maxRep) / 2)) = false := by
        simp [hr.1, hr.2]
      have hp : g.pushOverflow 9223372036854775808 .to_nearest = g.push 3 := by
        unfold Guard.pushOverflow
        rw [if_pos (by decide)]
        simp only [show (9223372036854775808 : UInt64) % 10 < 9 from by decide, if_true, hb,
          Bool.false_eq_true, if_false]
        rw [if_neg (by decide)]
        congr 1
      rw [hp]
      exact ⟨hm, hr.1, hr.2, push3_round_lt g⟩
  · have hm' : m = 9223372036854775809 := UInt64.toNat_inj.mp (by rw [hm]; rfl)
    subst hm'
    left
    have hp : g.pushOverflow 9223372036854775809 .to_nearest = g.push 6 := by
      unfold Guard.pushOverflow
      rw [if_pos (by decide)]
      simp only [show ¬ ((9223372036854775809 : UInt64) % 10 < 9) from by decide, if_false]
      rw [if_neg (by decide)]
      congr 1
    rw [hp]
    exact push_round_one g 6 (by decide) (by decide)

lemma noRoundUp_half (g : Guard) (m : UInt64) (f : ℚ) (hrep : represents g f)
    (hru : ¬ g.shouldRoundUp_to_nearest m) : f ≤ 1 / 2 := by
  by_cases hemp : g.empty = true
  · obtain ⟨hd, hx⟩ : g.digits_ = 0 ∧ g.xbit_ = false := by
      have h : (g.digits_ == 0 && !g.xbit_) = true := hemp
      rw [Bool.and_eq_true] at h
      exact ⟨beq_iff_eq.mp h.1, by simpa using h.2⟩
    rw [represents_eq_zero_of_digits_zero_xbit_false hd hx hrep]; norm_num
  · obtain ⟨hp, hn, hz⟩ := round_correct hemp hrep
    have hv : g.round .to_nearest = 1 ∨ g.round .to_nearest = 0 ∨
        g.round .to_nearest = -1 := by
      rw [round_to_nearest_def hemp]
      split_ifs <;> simp
    unfold Guard.shouldRoundUp_to_nearest at hru
    rcases hv with h | h | h
    · exact absurd (Or.inl h) hru
    · exact le_of_eq (hz.mp h)
    · exact le_of_lt (hn.mp h)

/-- A `.to_nearest` `doRoundUp` of `m + f` lands at `m + 1` or above, at `m` itself,
or (only from the interior cusp `maxRep + 1` with `f < 1/2`) at `maxRep`. -/
lemma doRoundUp_lower (g : Guard) (m : UInt64) (e : Int) (f : ℚ)
    (hrep : represents g f) (hub : m.toNat ≤ maxRepUp.toNat)
    (loc : Error) (res : RoundResult)
    (hok : g.doRoundUp false m e largeRange.min largeRange.max .to_nearest loc = .ok res)
    (hne : res.mantissa_ ≠ 0) :
    ((m.toNat : ℚ) + 1) * 10 ^ e ≤ (res.mantissa_.toNat : ℚ) * 10 ^ res.exponent_ ∨
    ((res.mantissa_.toNat : ℚ) * 10 ^ res.exponent_ = (m.toNat : ℚ) * 10 ^ e ∧
      ((f ≤ 1 / 2 ∧ m.toNat ≤ 9223372036854775807) ∨ m.toNat = 9223372036854775807 ∨
        m.toNat = 9223372036854775810)) ∨
    ((res.mantissa_.toNat : ℚ) * 10 ^ res.exponent_ = 9223372036854775807 * 10 ^ e ∧
      m.toNat = 9223372036854775808 ∧ f < 1 / 2) := by
  have h10 : (0 : ℚ) < 10 ^ e := zpow_pos (by norm_num) _
  have hmR : maxRep.toNat = 9223372036854775807 := maxRep_val
  have hmU : maxRepUp.toNat = 9223372036854775810 := rfl
  by_cases hle : m.toNat ≤ maxRep.toNat
  · by_cases hru : g.shouldRoundUp_to_nearest m
    · by_cases hno : m.toNat + 1 ≤ maxRep.toNat
      · left
        rw [doRoundUp_value_to_nearest_roundUp_noCusp g m e hru hno loc res hok hne]
      · have hm : m = maxRep := UInt64.toNat_inj.mp (by omega)
        rcases hru with h1 | h0
        · right; left
          refine ⟨?_, Or.inr (Or.inl (by rw [hm]; exact hmR))⟩
          rw [doRoundUp_value_to_nearest_roundUp_cusp_round1 g m e hm h1 loc res hok hne, hm]
        · left
          rw [doRoundUp_value_to_nearest_roundUp_cusp g m e hm h0 loc res hok hne, hm, hmR]
          apply mul_le_mul_of_nonneg_right _ (le_of_lt h10)
          norm_num
    · right; left
      refine ⟨doRoundUp_value_no_roundUp g m e hru hle loc res hok hne,
        Or.inl ⟨noRoundUp_half g m f hrep hru, by rw [hmR] at hle; exact hle⟩⟩
  · push Not at hle
    unfold Guard.doRoundUp Guard.bringIntoRange at hok
    dsimp only [Guard.doDropDigit] at hok
    by_cases h_eq_up : m = maxRepUp
    · subst h_eq_up
      right; left
      refine ⟨?_, Or.inr (Or.inr hmU)⟩
      have h_pof : g.pushOverflow maxRepUp .to_nearest = g := by
        unfold Guard.pushOverflow
        rw [if_neg]
        intro ⟨_, h⟩
        exact absurd (UInt64.lt_iff_toNat_lt.mp h) (lt_irrefl _)
      rw [h_pof] at hok
      have h_not_noncusp : ¬ (maxRepUp < largeRange.max ∧ maxRepUp < maxRep) := by decide
      have h_not_cusp : ¬ (maxRep < maxRepUp ∧ maxRepUp < maxRepUp) := by decide
      by_cases h_ru : (g.round .to_nearest == 1 ||
          (g.round .to_nearest == 0 && maxRepUp % 2 == 1)) = true
      · rw [show (g.round .to_nearest == 1 || (g.round .to_nearest == 0 && maxRepUp % 2 == 1))
            = true from h_ru] at hok
        rw [if_pos rfl, if_neg h_not_noncusp, if_neg h_not_cusp] at hok
        have hdig : (g.push (maxRepUp % 10)).digits_.toNat < 5764607523034234880 := by
          have h := toNat_push_digits g (maxRepUp % 10)
          have h0 : (maxRepUp % 10).toNat = 0 := by decide
          rw [h0] at h
          have hlt : g.digits_.toNat < 2 ^ 64 := UInt64.toNat_lt_size g.digits_
          omega
        have h_ru'_false : ((g.push (maxRepUp % 10)).round .to_nearest == 1
            || ((g.push (maxRepUp % 10)).round .to_nearest == 0 &&
              (maxRepUp / 10) % 2 == 1)) = false := by
          by_cases hemp : (g.push (maxRepUp % 10)).empty = true
          · rw [show (g.push (maxRepUp % 10)).round .to_nearest = -2 from by
              unfold Guard.round; rw [if_pos hemp]]
            rfl
          · rw [round_to_nearest_def hemp]
            have h5 : (5764607523034234880 : UInt64).toNat = 5764607523034234880 := rfl
            have h_not_gt : ¬ ((g.push (maxRepUp % 10)).digits_ > 5764607523034234880) := by
              intro h
              have := UInt64.lt_iff_toNat_lt.mp h
              rw [h5] at this; omega
            have h_lt : (g.push (maxRepUp % 10)).digits_ < 5764607523034234880 := by
              rw [UInt64.lt_iff_toNat_lt, h5]; exact hdig
            rw [if_neg h_not_gt, if_pos h_lt]
            rfl
        rw [h_ru'_false] at hok
        simp only [Bool.false_eq_true, if_false] at hok
        have h_resc : maxRepUp / 10 < largeRange.min ∧ maxRepUp / 10 ≠ 0 := by decide
        rw [if_pos h_resc] at hok
        simp only [] at hok
        by_cases h_under : e + 1 - 1 < minExponent ∨ (maxRepUp / 10) * 10 = 0
        · exfalso; apply hne
          simp only [if_pos h_under] at hok
          have hzexp : ¬ ((-2147483648 : Int) > maxExponent) := by norm_num [maxExponent]
          simp only [hzexp, if_false] at hok
          exact (Except.ok.inj hok).symm ▸ rfl
        · simp only [if_neg h_under] at hok
          have h_no_ovf : ¬ (e + 1 - 1 > maxExponent) := by
            intro h_ovf; simp only [if_pos h_ovf] at hok; simp at hok
          simp only [if_neg h_no_ovf] at hok
          obtain rfl := Except.ok.inj hok
          change ((((maxRepUp / 10) * 10).toNat : ℕ) : ℚ) * 10 ^ (e + 1 - 1)
            = (maxRepUp.toNat : ℚ) * 10 ^ e
          rw [show ((maxRepUp / 10) * 10).toNat = maxRepUp.toNat from by decide,
            show (e + 1 - 1 : ℤ) = e from by ring]
      · rw [Bool.not_eq_true] at h_ru
        rw [show (g.round .to_nearest == 1 || (g.round .to_nearest == 0 && maxRepUp % 2 == 1))
            = false from h_ru] at hok
        simp only [Bool.false_eq_true, if_false] at hok
        rw [if_neg h_not_cusp] at hok
        have h_no_resc : ¬ (maxRepUp < largeRange.min ∧ maxRepUp ≠ 0) := by decide
        rw [if_neg h_no_resc] at hok
        simp only [] at hok
        by_cases h_under : e < minExponent ∨ (maxRepUp : UInt64) = 0
        · exfalso; apply hne
          simp only [if_pos h_under] at hok
          have hzexp : ¬ ((-2147483648 : Int) > maxExponent) := by norm_num [maxExponent]
          simp only [hzexp, if_false] at hok
          exact (Except.ok.inj hok).symm ▸ rfl
        · simp only [if_neg h_under] at hok
          have h_no_ovf : ¬ (e > maxExponent) := by
            intro h_ovf; simp only [if_pos h_ovf] at hok; simp at hok
          simp only [if_neg h_no_ovf] at hok
          obtain rfl := Except.ok.inj hok
          rfl
    · have h_lt_up_nat : m.toNat < maxRepUp.toNat := by
        have hne' : m.toNat ≠ maxRepUp.toNat := fun h => h_eq_up (UInt64.toNat_inj.mp h)
        omega
      have hm2 : m.toNat = 9223372036854775808 ∨ m.toNat = 9223372036854775809 := by omega
      have h_m_lt_up : m < maxRepUp := UInt64.lt_iff_toNat_lt.mpr h_lt_up_nat
      have h_maxRep_lt_m : maxRep < m := UInt64.lt_iff_toNat_lt.mpr hle
      have h_cusp_cond : maxRep < m ∧ m < maxRepUp := ⟨h_maxRep_lt_m, h_m_lt_up⟩
      have h_not_noncusp : ¬ (m < largeRange.max ∧ m < maxRep) := by
        intro ⟨_, h⟩
        exact absurd (UInt64.lt_iff_toNat_lt.mp h) (by omega)
      by_cases h_ru : ((g.pushOverflow m .to_nearest).round .to_nearest == 1
          || ((g.pushOverflow m .to_nearest).round .to_nearest == 0 && m % 2 == 1)) = true
      · left
        rw [show ((g.pushOverflow m .to_nearest).round .to_nearest == 1
            || ((g.pushOverflow m .to_nearest).round .to_nearest == 0 && m % 2 == 1)) = true
            from h_ru] at hok
        rw [if_pos rfl, if_neg h_not_noncusp, if_pos h_cusp_cond] at hok
        have h_no_resc : ¬ (maxRepUp < largeRange.min ∧ maxRepUp ≠ 0) := by decide
        rw [if_neg h_no_resc] at hok
        simp only [] at hok
        by_cases h_under : e < minExponent ∨ (maxRepUp : UInt64) = 0
        · exfalso; apply hne
          simp only [if_pos h_under] at hok
          have hzexp : ¬ ((-2147483648 : Int) > maxExponent) := by norm_num [maxExponent]
          simp only [hzexp, if_false] at hok
          exact (Except.ok.inj hok).symm ▸ rfl
        · simp only [if_neg h_under] at hok
          have h_no_ovf : ¬ (e > maxExponent) := by
            intro h_ovf; simp only [if_pos h_ovf] at hok; simp at hok
          simp only [if_neg h_no_ovf] at hok
          obtain rfl := Except.ok.inj hok
          change ((m.toNat : ℚ) + 1) * 10 ^ e ≤ (maxRepUp.toNat : ℚ) * 10 ^ e
          apply mul_le_mul_of_nonneg_right _ (le_of_lt h10)
          rw [hmU]
          have : (m.toNat : ℚ) ≤ 9223372036854775809 := by
            exact_mod_cast (by omega : m.toNat ≤ 9223372036854775809)
          push_cast
          linarith
      · right; right
        rw [Bool.not_eq_true] at h_ru
        have hpo := pushOverflow_cusp g m hm2
        rcases hpo with h1 | ⟨hm808, hr1, hr0, -, -⟩
        · rw [h1] at h_ru; simp at h_ru
        refine ⟨?_, hm808, ?_⟩
        · rw [show ((g.pushOverflow m .to_nearest).round .to_nearest == 1
              || ((g.pushOverflow m .to_nearest).round .to_nearest == 0 && m % 2 == 1)) = false
              from h_ru] at hok
          simp only [Bool.false_eq_true, if_false] at hok
          rw [if_pos h_cusp_cond] at hok
          have h_no_resc : ¬ (maxRep < largeRange.min ∧ maxRep ≠ 0) := by decide
          rw [if_neg h_no_resc] at hok
          simp only [] at hok
          by_cases h_under : e < minExponent ∨ (maxRep : UInt64) = 0
          · exfalso; apply hne
            simp only [if_pos h_under] at hok
            have hzexp : ¬ ((-2147483648 : Int) > maxExponent) := by norm_num [maxExponent]
            simp only [hzexp, if_false] at hok
            exact (Except.ok.inj hok).symm ▸ rfl
          · simp only [if_neg h_under] at hok
            have h_no_ovf : ¬ (e > maxExponent) := by
              intro h_ovf; simp only [if_pos h_ovf] at hok; simp at hok
            simp only [if_neg h_no_ovf] at hok
            obtain rfl := Except.ok.inj hok
            change (maxRep.toNat : ℚ) * 10 ^ e = _
            rw [hmR]; norm_num
        · by_cases hemp : g.empty = true
          · obtain ⟨hd, hx⟩ : g.digits_ = 0 ∧ g.xbit_ = false := by
              have h : (g.digits_ == 0 && !g.xbit_) = true := hemp
              rw [Bool.and_eq_true] at h
              exact ⟨beq_iff_eq.mp h.1, by simpa using h.2⟩
            rw [represents_eq_zero_of_digits_zero_xbit_false hd hx hrep]; norm_num
          · obtain ⟨hp, hn, hz⟩ := round_correct hemp hrep
            have hv : g.round .to_nearest = 1 ∨ g.round .to_nearest = 0 ∨
                g.round .to_nearest = -1 := by
              rw [round_to_nearest_def hemp]
              split_ifs <;> simp
            rcases hv with h | h | h
            · exact absurd h hr1
            · exact absurd h hr0
            · exact hn.mp h

end XRPL.Model.SingleAssetVault.DepTight
