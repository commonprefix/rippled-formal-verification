import XRPL.Properties.Protocol.Number.Mul.Common.ToNearest.RoundedHelpers
import XRPL.Properties.Protocol.Number.Div.Common.ToNearest.RoundedHelpers
import XRPL.Properties.Protocol.Number.Mul.RoundsToRepresentable
import XRPL.Properties.Protocol.Number.Div.RoundsToRepresentable
import XRPL.Properties.Protocol.Number.Common.Closest.OpExact
import XRPL.Properties.Protocol.Number.Common.Closest.Gap
import XRPL.Properties.Protocol.Number.Common.Rounding.DoRoundUp.ValueChar

/-! # Monotone round-to-nearest for `Number`

Round-to-nearest is monotone when each result is a nearest representable to its exact value (`round_mono_core`).
`nearestTo_of_gap` and `doRoundUp_clean_down_up` establish that on the regular grid range, for the addition proof. -/

namespace XRPL.Model.Protocol

/-- `r` is a nearest representable to the exact value `t`: no normalized `Number` is closer to `t` than `r`. -/
def Number.NearestTo (r : Number) (t : ℚ) : Prop :=
  ∀ m : Number, m.isNormalized → |r.toRat - t| ≤ |m.toRat - t|

/-- Round-to-nearest is monotone: ordered exact values give ordered results, when each result is a nearest
representable and equal exact values give equal results. -/
lemma round_mono_core (t₁ t₂ : ℚ) (r₁ r₂ : Number)
    (h₁ : r₁.NearestTo t₁) (h₂ : r₂.NearestTo t₂)
    (hr₁ : r₁.isNormalized) (hr₂ : r₂.isNormalized)
    (hle : t₁ ≤ t₂) (hdet : t₁ = t₂ → r₁.toRat = r₂.toRat) :
    r₁.toRat ≤ r₂.toRat := by
  by_contra hcon
  push Not at hcon
  -- distances, squared: `r₁` is at least as close to `t₁` as `r₂`, and vice versa
  have e1 : |r₁.toRat - t₁| ≤ |r₂.toRat - t₁| := h₁ r₂ hr₂
  have e2 : |r₂.toRat - t₂| ≤ |r₁.toRat - t₂| := h₂ r₁ hr₁
  have hsq1 : (r₁.toRat - t₁) * (r₁.toRat - t₁) ≤ (r₂.toRat - t₁) * (r₂.toRat - t₁) := by
    have h := mul_self_le_mul_self (abs_nonneg (r₁.toRat - t₁)) e1
    rwa [abs_mul_abs_self, abs_mul_abs_self] at h
  have hsq2 : (r₂.toRat - t₂) * (r₂.toRat - t₂) ≤ (r₁.toRat - t₂) * (r₁.toRat - t₂) := by
    have h := mul_self_le_mul_self (abs_nonneg (r₂.toRat - t₂)) e2
    rwa [abs_mul_abs_self, abs_mul_abs_self] at h
  -- midpoint pinning: with `r₂ < r₁`, `hsq1 ⟹ r₁+r₂ ≤ 2t₁`, `hsq2 ⟹ 2t₂ ≤ r₁+r₂`
  have hmid1 : r₁.toRat + r₂.toRat ≤ 2 * t₁ := by nlinarith [hsq1, hcon]
  have hmid2 : 2 * t₂ ≤ r₁.toRat + r₂.toRat := by nlinarith [hsq2, hcon]
  have hteq : t₁ = t₂ := le_antisymm hle (by linarith [hmid1, hmid2])
  linarith [hdet hteq, hcon]

/-- A result that rounds a positive exact value `(zm + f)·10^ze'` down with `f ≤ 1/2`, or up with `f ≥ 1/2`, on a
regular grid cell is a nearest representable to it. -/
lemma Number.nearestTo_of_gap (t f : ℚ) (zm : UInt64) (ze' : Int) (r : Number)
    (hpos : 0 < t)
    (hval : t = ((zm.toNat : ℚ) + f) * 10 ^ ze')
    (hf_nn : 0 ≤ f) (hf_lt : f < 1)
    (hzm_lo : mantissaFloorSucc ≤ zm.toNat)
    (hzm_hi : zm.toNat < 10 ^ 19)
    (hcase : (r.toRat = (zm.toNat : ℚ) * 10 ^ ze' ∧ f ≤ 1 / 2)
           ∨ (r.toRat = ((zm.toNat : ℚ) + 1) * 10 ^ ze' ∧ 1 / 2 ≤ f)) :
    r.NearestTo t := by
  intro m hm
  have hpow : (0 : ℚ) < (10 : ℚ) ^ ze' := zpow_pos (by norm_num) _
  have hzm_pos : (0 : ℚ) < (zm.toNat : ℚ) := by
    have : (0 : ℕ) < zm.toNat := by
      have : (0 : ℕ) < mantissaFloorSucc := by norm_num
      omega
    exact_mod_cast this
  rcases hcase with ⟨hr, hf_le⟩ | ⟨hr, hf_ge⟩
  · -- rounded down: r = zm·10^ze', within `f·10^ze'` below `t`
    rw [hr, hval]
    by_cases hmL : m.toRat ≤ (zm.toNat : ℚ) * 10 ^ ze'
    · rw [abs_of_nonpos (by nlinarith [hpow, hf_nn]),
          abs_of_nonpos (by nlinarith [hpow, hmL, hf_nn])]
      nlinarith [hpow, hmL]
    · push Not at hmL
      have hmpos : 0 < m.toRat := lt_trans (by positivity) hmL
      have hmge : ((zm.toNat : ℚ) + 1) * 10 ^ ze' ≤ m.toRat := by
        by_contra hlt
        push Not at hlt
        exact no_normalized_in_open_ulp_gap_pos_zm ze' zm.toNat hzm_lo hzm_hi m hm hmpos hmL hlt
      rw [abs_of_nonpos (by nlinarith [hpow, hf_nn]),
          abs_of_nonneg (by nlinarith [hpow, hmge])]
      nlinarith [hpow, hmge, hf_le]
  · -- rounded up: r = (zm+1)·10^ze', within `(1-f)·10^ze'` above `t`
    rw [hr, hval]
    by_cases hmU : ((zm.toNat : ℚ) + 1) * 10 ^ ze' ≤ m.toRat
    · rw [abs_of_nonneg (by nlinarith [hpow, hf_lt]),
          abs_of_nonneg (by nlinarith [hpow, hmU, hf_lt])]
      nlinarith [hpow, hmU]
    · push Not at hmU
      have hmle : m.toRat ≤ (zm.toNat : ℚ) * 10 ^ ze' := by
        by_cases hmpos : 0 < m.toRat
        · by_contra hgt
          push Not at hgt
          exact no_normalized_in_open_ulp_gap_pos_zm ze' zm.toNat hzm_lo hzm_hi m hm hmpos hgt hmU
        · push Not at hmpos
          nlinarith [hpow, hzm_pos, hmpos]
      rw [abs_of_nonneg (by nlinarith [hpow, hf_lt]),
          abs_of_nonpos (by nlinarith [hpow, hmle, hf_lt])]
      nlinarith [hpow, hmle, hf_ge]

/-- On the regular range, a positive `to_nearest` `doRoundUp` result is `zm·10^ze'` with `f ≤ 1/2` (round down) or
`(zm+1)·10^ze'` with `f ≥ 1/2` (round up). -/
lemma doRoundUp_clean_down_up (g : Guard) (zm : UInt64) (ze' : Int) (f : ℚ)
    (res_pos : RoundResult) (result : Number) (loc : Error)
    (hf_rep : represents g f)
    (hrounds : g.doRoundUp false zm ze' largeRange.min largeRange.max .to_nearest loc
      = .ok res_pos)
    (habs : result.toRat = (res_pos.mantissa_.toNat : ℚ) * 10 ^ res_pos.exponent_)
    (hres_ne : res_pos.mantissa_ ≠ 0)
    (hzm_hi : zm.toNat + 1 ≤ maxRep.toNat) :
    (result.toRat = (zm.toNat : ℚ) * 10 ^ ze' ∧ f ≤ 1 / 2)
  ∨ (result.toRat = ((zm.toNat : ℚ) + 1) * 10 ^ ze' ∧ 1 / 2 ≤ f) := by
  by_cases hru : g.shouldRoundUp_to_nearest zm
  · right
    have hval := doRoundUp_value_to_nearest_roundUp_noCusp g zm ze' hru hzm_hi loc res_pos
      hrounds hres_ne
    refine ⟨by rw [habs, hval], ?_⟩
    rcases hru with h1 | ⟨h0, _⟩
    · exact le_of_lt (represents_round_eq_one hf_rep h1)
    · exact le_of_eq (represents_round_eq_zero hf_rep h0).symm
  · left
    have hzm_le : zm.toNat ≤ maxRep.toNat := by omega
    have hval := doRoundUp_value_no_roundUp g zm ze' hru hzm_le loc res_pos hrounds hres_ne
    refine ⟨by rw [habs, hval], ?_⟩
    by_contra hlt
    push Not at hlt
    exact hru (Or.inl (represents_f_gt_half hf_rep hlt))

/-- `operator_mul` is deterministic at a tie: equal exact products with the same nonzero left factor give equal
results. -/
lemma operator_mul_toRat_eq_of_truth_eq (x y₁ y₂ r₁ r₂ : Number)
    (hy₁ : y₁.isNormalized) (hy₂ : y₂.isNormalized)
    (hok₁ : Number.operator_mul x y₁ .to_nearest = .ok r₁)
    (hok₂ : Number.operator_mul x y₂ .to_nearest = .ok r₂)
    (hx : x.toRat ≠ 0)
    (heq : x.toRat * y₁.toRat = x.toRat * y₂.toRat) :
    r₁.toRat = r₂.toRat := by
  have hy : y₁.toRat = y₂.toRat := mul_left_cancel₀ hx heq
  have hyy : y₁ = y₂ := hy₁.toRat_inj hy₂ hy
  subst hyy
  rw [Except.ok.inj (hok₁.symm.trans hok₂)]

/-- `operator_div` is deterministic at a tie: equal exact quotients with the same nonzero divisor give equal
results. -/
lemma operator_div_toRat_eq_of_truth_eq (a₁ a₂ b r₁ r₂ : Number)
    (ha₁ : a₁.isNormalized) (ha₂ : a₂.isNormalized)
    (hok₁ : Number.operator_div a₁ b .to_nearest = .ok r₁)
    (hok₂ : Number.operator_div a₂ b .to_nearest = .ok r₂)
    (hb : b.toRat ≠ 0)
    (heq : a₁.toRat / b.toRat = a₂.toRat / b.toRat) :
    r₁.toRat = r₂.toRat := by
  have ha : a₁.toRat = a₂.toRat := by
    have h := heq
    rw [div_eq_div_iff hb hb] at h
    exact mul_right_cancel₀ hb h
  have haa : a₁ = a₂ := ha₁.toRat_inj ha₂ ha
  subst haa
  rw [Except.ok.inj (hok₁.symm.trans hok₂)]

end XRPL.Model.Protocol
