import XRPL.Properties.Protocol.Number.Common.Notation
import Mathlib.Tactic

import XRPL.Properties.Protocol.Number.Normalize.Common.ToNearest.AlgorithmicFacts


namespace XRPL.Model.Protocol

/-! # Result-shape facts for `Number.normalize`

`Number.normalize` ends in `doRoundUp` with no second normalize, so the result needs its own proofs that it is
normalized and that its mantissa stays `≤ maxRepUp` at the top exponent. -/

/-- `doRoundUp` succeeds only with exponent `≤ maxExponent` (the final overflow
check errors otherwise). -/
lemma doRoundUp_exponent_le_max
    (g : Guard) (neg : Bool) (m : UInt64) (e : Int) (mode : rounding_mode) (loc : Error)
    (res : RoundResult)
    (hok : g.doRoundUp neg m e largeRange.min largeRange.max mode loc = .ok res) :
    res.exponent_ ≤ maxExponent := by
  replace hok := Guard.doRoundUp_ok_spec hok
  unfold Guard.doRoundUpSpec at hok
  dsimp only [Guard.doDropDigit] at hok
  set gP : Guard := g.pushOverflowSpec m mode with hgP_def
  have h_extract : ∀ r' : RoundResult,
      (if r'.exponent_ > maxExponent then (.error loc : Except Error RoundResult)
       else .ok r') = .ok res → res.exponent_ ≤ maxExponent := by
    intro r' h
    by_cases h_ovf : r'.exponent_ > maxExponent
    · rw [ite_eq_left h_ovf] at h; cases h
    · rw [ite_eq_right h_ovf] at h
      rw [← Except.ok.inj h]
      exact not_lt.mp h_ovf
  by_cases hb : ((gP.round mode == 1) || ((gP.round mode == 0) && (m % 2 == 1))) = true
  · rw [ite_eq_left hb] at hok
    by_cases hC1 : m < largeRange.max ∧ m < maxRep
    · rw [ite_eq_left hC1] at hok
      exact h_extract _ hok
    · rw [ite_eq_right hC1] at hok
      by_cases hC2 : maxRep < m ∧ m < maxRepUp
      · rw [ite_eq_left hC2] at hok
        exact h_extract _ hok
      · rw [ite_eq_right hC2] at hok
        exact h_extract _ hok
  · rw [ite_eq_right hb] at hok
    by_cases hC2 : maxRep < m ∧ m < maxRepUp
    · rw [ite_eq_left hC2] at hok
      exact h_extract _ hok
    · rw [ite_eq_right hC2] at hok
      exact h_extract _ hok

set_option maxHeartbeats 800000 in
-- full 6-leaf doRoundUp navigation with per-leaf bringIntoRange case analysis
/-- At the top exponent the `doRoundUp` output mantissa stays `≤ maxRepUp`, given that the guard is empty
whenever the input mantissa is above `1844674407370955161`. -/
lemma doRoundUp_mantissa_le_maxRepUp_at_maxExp
    (g : Guard) (neg : Bool) (m : UInt64) (e : Int) (mode : rounding_mode) (loc : Error)
    (h_m_le : m.toNat ≤ maxRepUp.toNat)
    (h_cap_exp : m.toNat < 1000000000000000000 → e ≤ maxExponent)
    (h_empty_above : 1844674407370955161 < m.toNat → g.empty = true)
    (res : RoundResult)
    (hok : g.doRoundUp neg m e largeRange.min largeRange.max mode loc = .ok res)
    (h_exp_ge : res.exponent_ ≥ maxExponent) :
    res.mantissa_ ≤ maxRepUp := by
  have hmaxRepUp_toNat : maxRepUp.toNat = maxRepUpNat := rfl
  have hmaxRep_toNat : maxRep.toNat = 9223372036854775807 := maxRep_val
  -- Leaf analysis: a `bringIntoRange` result is a flush, a kept mantissa at the
  -- same exponent, or a rescaled small mantissa at the decremented exponent.
  have h_leaf : ∀ (m' : UInt64) (e' : Int),
      res = Guard.bringIntoRangeSpec neg m' e' largeRange.min →
      res.mantissa_.toNat = 0 ∨
      (res.mantissa_.toNat = m'.toNat ∧ res.exponent_ = e') ∨
      (m'.toNat < 10 ^ 18 ∧ res.exponent_ = e' - 1) := by
    intro m' e' hres_eq
    have hmin_v : largeRange.min.toNat = 1000000000000000000 := largeRange_min_val
    by_cases hm0 : m' = 0
    · rw [bringIntoRange_noscale_result (by intro ⟨_, hne⟩; exact hne hm0),
          ite_eq_left (Or.inr hm0)] at hres_eq
      subst hres_eq
      left
      rfl
    by_cases hresc : m' < largeRange.min
    · rw [bringIntoRange_rescale_result hresc hm0] at hres_eq
      by_cases h_under : e' - 1 < minExponent ∨ m' * 10 = 0
      · rw [ite_eq_left h_under] at hres_eq
        subst hres_eq
        left
        rfl
      · rw [ite_eq_right h_under] at hres_eq
        subst hres_eq
        right; right
        refine ⟨?_, rfl⟩
        have h1 := UInt64.lt_iff_toNat_lt.mp hresc
        omega
    · rw [bringIntoRange_noscale_result (by intro ⟨h, _⟩; exact hresc h)] at hres_eq
      by_cases h_under : e' < minExponent ∨ m' = 0
      · rw [ite_eq_left h_under] at hres_eq
        subst hres_eq
        left
        rfl
      · rw [ite_eq_right h_under] at hres_eq
        subst hres_eq
        right; left
        exact ⟨rfl, rfl⟩
  replace hok := Guard.doRoundUp_ok_spec hok
  unfold Guard.doRoundUpSpec at hok
  dsimp only [Guard.doDropDigit] at hok
  set gP : Guard := g.pushOverflowSpec m mode with hgP_def
  have h_extract : ∀ r' : RoundResult,
      (if r'.exponent_ > maxExponent then (.error loc : Except Error RoundResult)
       else .ok r') = .ok res → res = r' := by
    intro r' h
    by_cases h_ovf : r'.exponent_ > maxExponent
    · rw [ite_eq_left h_ovf] at h; cases h
    · rw [ite_eq_right h_ovf] at h; exact (Except.ok.inj h).symm
  by_cases hb : ((gP.round mode == 1) || ((gP.round mode == 0) && (m % 2 == 1))) = true
  · rw [ite_eq_left hb] at hok
    by_cases hC1 : m < largeRange.max ∧ m < maxRep
    · -- round-up, in-range: bringIntoRange (m+1).
      rw [ite_eq_left hC1] at hok
      have hres_eq := h_extract _ hok
      have hzm_lt : m.toNat < maxRep.toNat := UInt64.lt_iff_toNat_lt.mp hC1.2
      have hadd : (m + 1).toNat = m.toNat + 1 := m_add_one_no_overflow (le_of_lt hzm_lt)
      rcases h_leaf _ _ hres_eq with h0 | ⟨hm, _⟩ | ⟨hsmall, hexp⟩
      · rw [UInt64.le_iff_toNat_le]; omega
      · rw [UInt64.le_iff_toNat_le]; omega
      · exfalso
        have hsm : m.toNat < 1000000000000000000 := by omega
        have := h_cap_exp hsm
        omega
    · rw [ite_eq_right hC1] at hok
      by_cases hC2 : maxRep < m ∧ m < maxRepUp
      · -- round-up, cusp clamp to maxRepUp.
        rw [ite_eq_left hC2] at hok
        have hres_eq := h_extract _ hok
        rcases h_leaf _ _ hres_eq with h0 | ⟨hm, _⟩ | ⟨hsmall, _⟩
        · rw [UInt64.le_iff_toNat_le]; omega
        · rw [UInt64.le_iff_toNat_le]; omega
        · exfalso; omega
      · -- drop-digit leg: m ∈ {maxRep, maxRepUp}, where the guard is empty and
        -- the round decision cannot have fired.
        exfalso
        have hzm_lt_max : m < largeRange.max := by
          rw [UInt64.lt_iff_toNat_lt, largeRange_max_val]
          omega
        have hzm_ge_rep : maxRep.toNat ≤ m.toNat := by
          by_contra hlt
          push Not at hlt
          exact hC1 ⟨hzm_lt_max, UInt64.lt_iff_toNat_lt.mpr hlt⟩
        have hzm_cases : m.toNat = maxRep.toNat ∨ m.toNat = maxRepUp.toNat := by
          by_contra hno
          push Not at hno
          apply hC2
          constructor
          · rw [UInt64.lt_iff_toNat_lt]; omega
          · rw [UInt64.lt_iff_toNat_lt]; omega
        have hempty : g.empty = true := h_empty_above (by omega)
        have hgP_eq : gP = g := by
          rcases hzm_cases with h | h
          · rw [hgP_def]
            exact pushOverflow_noop_of_le_maxRep_of_empty (by omega) g mode hempty
          · rw [hgP_def]
            unfold Guard.pushOverflowSpec
            rw [ite_eq_right]
            intro ⟨_, h2⟩
            have := UInt64.lt_iff_toNat_lt.mp h2; omega
        rw [hgP_eq, empty_guard_round_neg_two g mode hempty] at hb
        simp at hb
  · rw [ite_eq_right hb] at hok
    by_cases hC2 : maxRep < m ∧ m < maxRepUp
    · -- truncate, cusp clamp to maxRep.
      rw [ite_eq_left hC2] at hok
      have hres_eq := h_extract _ hok
      rcases h_leaf _ _ hres_eq with h0 | ⟨hm, _⟩ | ⟨hsmall, _⟩
      · rw [UInt64.le_iff_toNat_le]; omega
      · rw [UInt64.le_iff_toNat_le]; omega
      · exfalso; omega
    · -- truncate, identity.
      rw [ite_eq_right hC2] at hok
      have hres_eq := h_extract _ hok
      rcases h_leaf _ _ hres_eq with h0 | ⟨hm, _⟩ | ⟨hsmall, hexp⟩
      · rw [UInt64.le_iff_toNat_le]; omega
      · rw [UInt64.le_iff_toNat_le]; omega
      · exfalso
        have hsm : m.toNat < 1000000000000000000 := by omega
        have := h_cap_exp hsm
        omega

set_option maxHeartbeats 800000 in
-- full 6-leaf doRoundUp navigation including the live drop-digit leg
/-- Without any guard-emptiness hypothesis, the `doRoundUp` output mantissa at the top exponent stays
`≤ maxRepNat + 13` (`= 9223372036854775820`), since the drop-digit leg outputs at most `(maxRepUp/10 + 1)·10`. -/
lemma doRoundUp_mantissa_le_cuspTop_at_maxExp
    (g : Guard) (neg : Bool) (m : UInt64) (e : Int) (mode : rounding_mode) (loc : Error)
    (h_m_le : m.toNat ≤ maxRepUp.toNat)
    (h_cap_exp : m.toNat < 1000000000000000000 → e ≤ maxExponent)
    (res : RoundResult)
    (hok : g.doRoundUp neg m e largeRange.min largeRange.max mode loc = .ok res)
    (h_exp_ge : res.exponent_ ≥ maxExponent) :
    res.mantissa_.toNat ≤ 9223372036854775820 := by
  have hmaxRepUp_toNat : maxRepUp.toNat = maxRepUpNat := rfl
  have hmaxRep_toNat : maxRep.toNat = 9223372036854775807 := maxRep_val
  -- Extended leaf analysis: the rescale arm also reports the tenfold mantissa.
  have h_leaf : ∀ (m' : UInt64) (e' : Int),
      res = Guard.bringIntoRangeSpec neg m' e' largeRange.min →
      res.mantissa_.toNat = 0 ∨
      (res.mantissa_.toNat = m'.toNat ∧ res.exponent_ = e') ∨
      (res.mantissa_.toNat = m'.toNat * 10 ∧ m'.toNat < 10 ^ 18 ∧ res.exponent_ = e' - 1) := by
    intro m' e' hres_eq
    have hmin_v : largeRange.min.toNat = 1000000000000000000 := largeRange_min_val
    by_cases hm0 : m' = 0
    · rw [bringIntoRange_noscale_result (by intro ⟨_, hne⟩; exact hne hm0),
          ite_eq_left (Or.inr hm0)] at hres_eq
      subst hres_eq
      left
      rfl
    by_cases hresc : m' < largeRange.min
    · have hm_lt18 : m'.toNat < 10 ^ 18 := by
        have h1 := UInt64.lt_iff_toNat_lt.mp hresc
        omega
      rw [bringIntoRange_rescale_result hresc hm0] at hres_eq
      by_cases h_under : e' - 1 < minExponent ∨ m' * 10 = 0
      · rw [ite_eq_left h_under] at hres_eq
        subst hres_eq
        left
        rfl
      · rw [ite_eq_right h_under] at hres_eq
        subst hres_eq
        right; right
        exact ⟨m_mul_ten_no_overflow hm_lt18, hm_lt18, rfl⟩
    · rw [bringIntoRange_noscale_result (by intro ⟨h, _⟩; exact hresc h)] at hres_eq
      by_cases h_under : e' < minExponent ∨ m' = 0
      · rw [ite_eq_left h_under] at hres_eq
        subst hres_eq
        left
        rfl
      · rw [ite_eq_right h_under] at hres_eq
        subst hres_eq
        right; left
        exact ⟨rfl, rfl⟩
  replace hok := Guard.doRoundUp_ok_spec hok
  unfold Guard.doRoundUpSpec at hok
  dsimp only [Guard.doDropDigit] at hok
  set gP : Guard := g.pushOverflowSpec m mode with hgP_def
  have h_extract : ∀ r' : RoundResult,
      (if r'.exponent_ > maxExponent then (.error loc : Except Error RoundResult)
       else .ok r') = .ok res → res = r' := by
    intro r' h
    by_cases h_ovf : r'.exponent_ > maxExponent
    · rw [ite_eq_left h_ovf] at h; cases h
    · rw [ite_eq_right h_ovf] at h; exact (Except.ok.inj h).symm
  by_cases hb : ((gP.round mode == 1) || ((gP.round mode == 0) && (m % 2 == 1))) = true
  · rw [ite_eq_left hb] at hok
    by_cases hC1 : m < largeRange.max ∧ m < maxRep
    · rw [ite_eq_left hC1] at hok
      have hres_eq := h_extract _ hok
      have hzm_lt : m.toNat < maxRep.toNat := UInt64.lt_iff_toNat_lt.mp hC1.2
      have hadd : (m + 1).toNat = m.toNat + 1 := m_add_one_no_overflow (le_of_lt hzm_lt)
      rcases h_leaf _ _ hres_eq with h0 | ⟨hm, _⟩ | ⟨_, hsmall, hexp⟩
      · omega
      · omega
      · exfalso
        have := h_cap_exp (by omega)
        omega
    · rw [ite_eq_right hC1] at hok
      by_cases hC2 : maxRep < m ∧ m < maxRepUp
      · rw [ite_eq_left hC2] at hok
        have hres_eq := h_extract _ hok
        rcases h_leaf _ _ hres_eq with h0 | ⟨hm, _⟩ | ⟨_, hsmall, _⟩
        · omega
        · omega
        · exfalso; omega
      · -- drop-digit leg.
        rw [ite_eq_right hC2] at hok
        have h_div_toNat : (m / 10).toNat = m.toNat / 10 := by
          rw [UInt64.toNat_div]; rfl
        by_cases hb' : (((gP.push (m % 10)).round mode == 1)
            || (((gP.push (m % 10)).round mode == 0) && (m / 10 % 2 == 1))) = true
        · rw [ite_eq_left hb'] at hok
          have hres_eq := h_extract _ hok
          have h_toNat : (m / 10 + 1).toNat = m.toNat / 10 + 1 := by
            rw [UInt64.toNat_add, h_div_toNat]
            rw [Nat.mod_eq_of_lt (by simpa using (by omega : m.toNat / 10 + 1 < 2 ^ 64))]
            rfl
          rcases h_leaf _ _ hres_eq with h0 | ⟨hm, _⟩ | ⟨hm, _, _⟩
          · omega
          · omega
          · omega
        · rw [ite_eq_right hb'] at hok
          have hres_eq := h_extract _ hok
          rcases h_leaf _ _ hres_eq with h0 | ⟨hm, _⟩ | ⟨hm, _, _⟩
          · omega
          · omega
          · omega
  · rw [ite_eq_right hb] at hok
    by_cases hC2 : maxRep < m ∧ m < maxRepUp
    · rw [ite_eq_left hC2] at hok
      have hres_eq := h_extract _ hok
      rcases h_leaf _ _ hres_eq with h0 | ⟨hm, _⟩ | ⟨_, hsmall, _⟩
      · omega
      · omega
      · exfalso; omega
    · rw [ite_eq_right hC2] at hok
      have hres_eq := h_extract _ hok
      rcases h_leaf _ _ hres_eq with h0 | ⟨hm, _⟩ | ⟨_, hsmall, hexp⟩
      · omega
      · omega
      · exfalso
        have := h_cap_exp (by omega)
        omega

/-- In every mode, a successful `normalize` with nonzero result exposes its `doRoundUp` stage together with
the input-side facts the result lemmas need. -/
theorem Number.normalize_doRoundUp_stage (n result : Number) (mode : rounding_mode)
    (hn_mant_ne : n.mantissa_ ≠ 0)
    (hok : n.normalize largeRange.min largeRange.max mode = .ok result)
    (hresult : result.mantissa_ ≠ 0) :
    ∃ (m3 : UInt64) (e3 : Int) (g3 : Guard) (res : RoundResult),
      g3.doRoundUp n.negative_ m3 e3 largeRange.min largeRange.max mode
        .normalize2 = .ok res ∧
      result = res.toNumber ∧
      mantissaFloor ≤ m3.toNat ∧
      m3.toNat ≤ maxRepUp.toNat ∧
      (m3.toNat < 1000000000000000000 → e3 ≤ maxExponent) ∧
      (1844674407370955161 < m3.toNat → g3.empty = true) := by
  unfold Number.normalize at hok
  replace hok := doNormalize_ok_spec hok
  unfold doNormalizeSpec at hok
  rw [beq_eq_false_iff_ne.mpr hn_mant_ne] at hok
  simp only [Bool.false_eq_true, ite_false] at hok
  set su := doNormalize_scaleUpSpec largeRange.min n.mantissa_ n.exponent_ with hsu_def
  set m1 : UInt64 := su.1 with hm1_def
  set e1 : Int := su.2 with he1_def
  set g0 : Guard := if n.negative_ then Guard.new.set_negative else Guard.new with hg0_def
  obtain ⟨m2, e2, g2, hsd⟩ : ∃ m2 e2 g2,
      doNormalize_scaleDown largeRange.max m1 e1 g0 = .ok (m2, e2, g2) := by
    match hsd : doNormalize_scaleDown largeRange.max m1 e1 g0 with
    | .error e => rw [hsd] at hok; exact absurd hok (by intro h; cases h)
    | .ok (m2, e2, g2) => exact ⟨m2, e2, g2, rfl⟩
  rw [hsd] at hok
  simp only at hok
  by_cases hzero : e2 < minExponent ∨ m2 < largeRange.min
  · rw [show (decide (e2 < minExponent) || decide (m2 < largeRange.min)) = true from by
      rcases hzero with h | h
      · simp [h]
      · simp [h]] at hok
    simp only [ite_true] at hok
    have : Number.zero = result := Except.ok.inj hok
    rw [← this] at hresult
    exact absurd rfl hresult
  · push Not at hzero
    obtain ⟨he2_ge, hm2_ge⟩ := hzero
    rw [show (decide (e2 < minExponent) || decide (m2 < largeRange.min)) = false from by
      rw [Bool.or_eq_false_iff]
      exact ⟨decide_eq_false (not_lt.mpr he2_ge), decide_eq_false hm2_ge⟩] at hok
    simp only [Bool.false_eq_true, ite_false] at hok
    obtain ⟨m3, e3, g3, hcap⟩ : ∃ m3 e3 g3,
        doNormalize_capAtMaxRep m2 e2 g2 = .ok (m3, e3, g3) := by
      match hcap : doNormalize_capAtMaxRep m2 e2 g2 with
      | .error e => rw [hcap] at hok; exact absurd hok (by intro h; cases h)
      | .ok (m3, e3, g3) => exact ⟨m3, e3, g3, rfl⟩
    rw [hcap] at hok
    simp only at hok
    obtain ⟨res, hrup⟩ : ∃ res,
        g3.doRoundUp n.negative_ m3 e3 largeRange.min largeRange.max mode
          .normalize2 = .ok res := by
      match hrup : g3.doRoundUp n.negative_ m3 e3 largeRange.min largeRange.max mode
          .normalize2 with
      | .error e => rw [hrup] at hok; exact absurd hok (by intro h; cases h)
      | .ok res => exact ⟨res, rfl⟩
    rw [hrup] at hok
    simp only at hok
    have hresult_eq : result = res.toNumber := (Except.ok.inj hok).symm
    have hm2_ge_min : largeRange.min.toNat ≤ m2.toNat := by
      rw [UInt64.lt_iff_toNat_lt] at hm2_ge
      omega
    have hminMant_v : largeRange.min.toNat = 1000000000000000000 := largeRange_min_val
    have h64 : m2.toNat < 2 ^ 64 := UInt64.toNat_lt_size m2
    refine ⟨m3, e3, g3, res, hrup, hresult_eq, ?_, ?_, ?_, ?_⟩
    · -- mantissaFloor ≤ m3.
      unfold doNormalize_capAtMaxRep at hcap
      by_cases hmr : m2 > maxRepUp
      · rw [ite_eq_left hmr] at hcap
        by_cases hexp3 : e2 ≥ maxExponent
        · rw [ite_eq_left hexp3] at hcap; exact absurd hcap (by intro h; cases h)
        · rw [ite_eq_right hexp3] at hcap
          simp only [divu10] at hcap
          have hm3_eq : m3 = m2 / 10 := ((Prod.mk.inj (Except.ok.inj hcap)).1).symm
          rw [hm3_eq, UInt64.toNat_div, show (10 : UInt64).toNat = 10 from rfl]
          have hmr_nat : maxRepUp.toNat < m2.toNat := UInt64.lt_iff_toNat_lt.mp hmr
          rw [show maxRepUp.toNat = maxRepUpNat from rfl] at hmr_nat
          omega
      · rw [ite_eq_right hmr] at hcap
        have hm3_eq : m3 = m2 := ((Prod.mk.inj (Except.ok.inj hcap)).1).symm
        rw [hm3_eq]
        rw [hminMant_v] at hm2_ge_min
        omega
    · -- m3 ≤ maxRepUp.
      unfold doNormalize_capAtMaxRep at hcap
      by_cases hmr : m2 > maxRepUp
      · rw [ite_eq_left hmr] at hcap
        by_cases hexp3 : e2 ≥ maxExponent
        · rw [ite_eq_left hexp3] at hcap; exact absurd hcap (by intro h; cases h)
        · rw [ite_eq_right hexp3] at hcap
          simp only [divu10] at hcap
          have hm3_eq : m3 = m2 / 10 := ((Prod.mk.inj (Except.ok.inj hcap)).1).symm
          rw [hm3_eq, UInt64.toNat_div, show (10 : UInt64).toNat = 10 from rfl,
              show maxRepUp.toNat = maxRepUpNat from rfl]
          omega
      · rw [ite_eq_right hmr] at hcap
        have hm3_eq : m3 = m2 := ((Prod.mk.inj (Except.ok.inj hcap)).1).symm
        have hmr_nat : ¬ maxRepUp.toNat < m2.toNat := fun h =>
          hmr (UInt64.lt_iff_toNat_lt.mpr h)
        rw [hm3_eq]
        omega
    · -- m3 < 10^18 → e3 ≤ maxExponent (only the cap divide can shrink below 10^18).
      intro hm3_lt
      unfold doNormalize_capAtMaxRep at hcap
      by_cases hmr : m2 > maxRepUp
      · rw [ite_eq_left hmr] at hcap
        by_cases hexp3 : e2 ≥ maxExponent
        · rw [ite_eq_left hexp3] at hcap; exact absurd hcap (by intro h; cases h)
        · rw [ite_eq_right hexp3] at hcap
          simp only [divu10] at hcap
          have he3_eq : e3 = e2 + 1 :=
            ((Prod.mk.inj (Prod.mk.inj (Except.ok.inj hcap)).2).1).symm
          omega
      · rw [ite_eq_right hmr] at hcap
        have hm3_eq : m3 = m2 := ((Prod.mk.inj (Except.ok.inj hcap)).1).symm
        exfalso
        rw [hm3_eq] at hm3_lt
        rw [hminMant_v] at hm2_ge_min
        omega
    · -- m3 above the scaleDown/cap output ceilings → both stages were identity.
      intro hgt
      have hcap_id : m3 = m2 ∧ g3 = g2 := by
        unfold doNormalize_capAtMaxRep at hcap
        by_cases hmr : m2 > maxRepUp
        · exfalso
          rw [ite_eq_left hmr] at hcap
          by_cases hexp3 : e2 ≥ maxExponent
          · rw [ite_eq_left hexp3] at hcap; exact absurd hcap (by intro h; cases h)
          · rw [ite_eq_right hexp3] at hcap
            simp only [divu10] at hcap
            have hm3_eq : m3 = m2 / 10 := ((Prod.mk.inj (Except.ok.inj hcap)).1).symm
            have hdiv : m3.toNat = m2.toNat / 10 := by
              rw [hm3_eq, UInt64.toNat_div, show (10 : UInt64).toNat = 10 from rfl]
            omega
        · rw [ite_eq_right hmr] at hcap
          have h1 : m3 = m2 := ((Prod.mk.inj (Except.ok.inj hcap)).1).symm
          have h2 : g3 = g2 := (Prod.mk.inj (Prod.mk.inj (Except.ok.inj hcap)).2).2.symm
          exact ⟨h1, h2⟩
      obtain ⟨hm32, hg32⟩ := hcap_id
      have hsd_id : g2 = g0 := by
        by_cases hm1_gt : m1 > largeRange.max
        · exfalso
          have hb := doNormalize_scaleDown_fired_output_le largeRange.max m1 e1 g0
            m2 e2 g2 hm1_gt hsd
          have hm23 : m2.toNat = m3.toNat := by rw [hm32]
          omega
        · rw [doNormalize_scaleDown, dite_eq_right hm1_gt] at hsd
          exact ((Prod.mk.inj (Prod.mk.inj (Except.ok.inj hsd)).2).2).symm
      have hg3_g0 : g3 = g0 := by rw [hg32, hsd_id]
      rw [hg3_g0, hg0_def]
      by_cases hn : n.negative_
      · rw [ite_eq_left hn]; decide
      · rw [ite_eq_right hn]; decide

/-- A zero mantissa forces `toRat = 0` (any sign/exponent). -/
lemma Number.toRat_eq_zero_of_mantissa_zero (n : Number) (h : n.mantissa_ = 0) :
    n.toRat = 0 := by
  have habs := abs_toRat_eq n
  rw [show (n.mantissa_.toNat : ℚ) = 0 from by
        rw [show n.mantissa_.toNat = 0 from by rw [h]; rfl]; norm_num,
      zero_mul] at habs
  exact abs_eq_zero.mp habs

/-- A nonzero mantissa forces `toRat ≠ 0` (any sign/exponent). -/
lemma Number.toRat_ne_zero_of_mantissa_ne_zero (n : Number) (h : n.mantissa_ ≠ 0) :
    n.toRat ≠ 0 := by
  intro h0
  have habs := abs_toRat_eq n
  rw [h0, abs_zero] at habs
  have h10 : (0 : ℚ) < (10 : ℚ) ^ n.exponent_ := zpow_pos (by norm_num) _
  have hm_pos : (0 : ℚ) < (n.mantissa_.toNat : ℚ) := by
    have hp : 0 < n.mantissa_.toNat := by
      rcases Nat.eq_zero_or_pos n.mantissa_.toNat with hz | hp
      · exact absurd (UInt64.toNat_inj.mp (by rw [hz]; rfl)) h
      · exact hp
    exact_mod_cast hp
  exact absurd habs.symm (ne_of_gt (mul_pos hm_pos h10))

/-- The result of a successful `normalize` with nonzero mantissa is
normalized. -/
theorem Number.normalize_result_isNormalized (n result : Number) (mode : rounding_mode)
    (hn_mant_ne : n.mantissa_ ≠ 0)
    (hok : n.normalize largeRange.min largeRange.max mode = .ok result)
    (hresult : result.mantissa_ ≠ 0) :
    result.isNormalized := by
  obtain ⟨m3, e3, g3, res, hrup, hresult_eq, hfloor, hle, _, _⟩ :=
    Number.normalize_doRoundUp_stage n result mode hn_mant_ne hok hresult
  have hres_ne : res.mantissa_ ≠ 0 := by
    rw [hresult_eq] at hresult
    exact hresult
  obtain ⟨h1, h2, h3, h4⟩ :=
    doRoundUp_output_invariants_upTo_maxRepUp_anyMode g3 n.negative_ m3 e3 mode
      hfloor hle .normalize2 res hrup hres_ne
  have h_exp_le : res.exponent_ ≤ maxExponent :=
    doRoundUp_exponent_le_max g3 n.negative_ m3 e3 mode .normalize2 res hrup
  right
  rw [hresult_eq]
  refine ⟨UInt64.le_iff_toNat_le.mpr h1, UInt64.le_iff_toNat_le.mpr h2, ?_, h3, h_exp_le⟩
  by_cases hcase : res.mantissa_.toNat ≤ maxRep.toNat
  · left
    exact UInt64.le_iff_toNat_le.mpr hcase
  · right
    exact h4 (by omega)

/-- A successful `normalize` with nonzero result mantissa forces a nonzero operand mantissa, since
`doNormalize` returns `Number.zero` for a zero-mantissa input. -/
theorem Number.normalize_operand_ne_zero (n result : Number) (mode : rounding_mode)
    (hok : n.normalize largeRange.min largeRange.max mode = .ok result)
    (hresult : result.mantissa_ ≠ 0) :
    n.mantissa_ ≠ 0 := by
  intro hn0
  unfold Number.normalize at hok
  replace hok := doNormalize_ok_spec hok
  unfold doNormalizeSpec at hok
  rw [ite_eq_left (by rw [beq_iff_eq]; exact hn0)] at hok
  have : Number.zero = result := Except.ok.inj hok
  rw [← this] at hresult
  exact absurd rfl hresult

/-- At the top exponent the `normalize` result mantissa stays `≤ maxRepUp`. -/
theorem Number.normalize_no_overflow_mantissa (n result : Number) (mode : rounding_mode)
    (hn_mant_ne : n.mantissa_ ≠ 0)
    (hok : n.normalize largeRange.min largeRange.max mode = .ok result)
    (hresult : result.mantissa_ ≠ 0)
    (h_exp_ge : result.exponent_ ≥ maxExponent) :
    result.mantissa_ ≤ maxRepUp := by
  obtain ⟨m3, e3, g3, res, hrup, hresult_eq, _, hle, hcap_exp, hempty⟩ :=
    Number.normalize_doRoundUp_stage n result mode hn_mant_ne hok hresult
  rw [hresult_eq] at h_exp_ge ⊢
  exact doRoundUp_mantissa_le_maxRepUp_at_maxExp g3 n.negative_ m3 e3 mode
    .normalize2 hle hcap_exp hempty res hrup h_exp_ge

end XRPL.Model.Protocol
