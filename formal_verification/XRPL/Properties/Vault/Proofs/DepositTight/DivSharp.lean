import XRPL.Properties.Protocol.Number.Common.Rounding.Normalize128.Facts
import XRPL.Properties.Protocol.Number.Common.ProofTactics
import XRPL.Properties.Protocol.Number.Div.Common.ToNearest.AlgorithmicFacts
import XRPL.Properties.Protocol.Number.Common.Helpers
import XRPL.Properties.Protocol.Number.Div.Common.Decompose

/-! # A sharper `.to_nearest` division bound -/

namespace XRPL.Model.SingleAssetVault.DepTight

open XRPL.Model.Protocol

/-- Relative `.to_nearest` error budget of `doNormalize128` (hence `operator_div`):
the half-ULP `5/(2^63+7)` plus the sticky-tail slip `11·10⁻²¹`. -/
def divSharpε : ℚ := 555 / 10 ^ 21

set_option maxHeartbeats 3200000 in
-- Four-stage pipeline composition over large UInt128 terms needs a raised budget.
/-- `doNormalize128_rounds_to_nearest` with the slip bounded by `11·10⁻²¹`. -/
lemma doNormalize128_rounds_to_nearest_sharp
    (zn : Bool) (M : UInt128) (e : Int) (δ : ℚ) (sticky : Bool)
    (hδ_low : 0 ≤ δ) (hδ_le : δ ≤ 1)
    (hsticky_zero : sticky = false → δ = 0)
    (hM_pos : 1 ≤ M.toNat) (hM_lt : M.toNat < 10 ^ 23)
    (hδM : sticky = true → δ * 10 ^ 20 ≤ (M.toNat : ℚ))
    (result : Number)
    (hok : doNormalize128 zn M e largeRange.min largeRange.max .to_nearest sticky = .ok result)
    (hres : result.mantissa_ ≠ 0) :
    |(|result.toRat|) - ((M.toNat : ℚ) + δ) * 10 ^ e|
      ≤ ((M.toNat : ℚ) + δ) * 10 ^ e * divSharpε
    ∧ result.negative_ = zn := by
  have hminM_v : largeRange.min.toNat = 1000000000000000000 := largeRange_min_val
  have hmaxM_v : largeRange.max.toNat = 9999999999999999999 := largeRange_max_val
  -- M ≠ 0.
  have hM_ne : ¬ (M == 0) = true := by
    intro h
    have : M = 0 := by exact_mod_cast beq_iff_eq.mp h
    rw [this] at hM_pos
    simp at hM_pos
  unfold doNormalize128 at hok
  rw [if_neg hM_ne] at hok
  simp only [] at hok
  -- scaleUp stage.
  rcases hsu : doNormalize128.scaleUp largeRange.min M e with ⟨M₁, e₁⟩
  rw [hsu] at hok
  simp only [] at hok
  -- Unified post-scaleUp facts: the value is exact and the tail rescales to δ₁
  -- (δ₁ = δ·10^(e−e₁) ≤ 1 since either scaleUp is the identity or M₁ < 10^19
  -- with the tail-vs-mantissa ratio δ·10^20 ≤ M preserved by the rescale).
  obtain ⟨hval_su, hM₁_pos, hM₁_lt, he₁_le, hM₁_size⟩ :
      ((M₁.toNat : ℚ) * 10 ^ e₁ = (M.toNat : ℚ) * 10 ^ e)
      ∧ 1 ≤ M₁.toNat ∧ M₁.toNat < 10 ^ 23 ∧ e₁ ≤ e
      ∧ (M₁ = M ∧ e₁ = e ∨ M₁.toNat < 10 ^ 19) := by
    have hfacts := doNormalize128_scaleUp_facts largeRange.min M e hminM_v hM_pos hM_lt
    rw [hsu] at hfacts
    exact hfacts
  have h10e_pos : (0 : ℚ) < (10 : ℚ) ^ e := zpow_pos (by norm_num) _
  have h10e₁_pos : (0 : ℚ) < (10 : ℚ) ^ e₁ := zpow_pos (by norm_num) _
  set δ₁ : ℚ := δ * 10 ^ (e - e₁) with hδ₁_def
  have hδ₁_nn : 0 ≤ δ₁ :=
    mul_nonneg hδ_low (le_of_lt (zpow_pos (by norm_num) _))
  have hδ₁_zero : sticky = false → δ₁ = 0 := by
    intro hst
    rw [hδ₁_def, hsticky_zero hst, zero_mul]
  have hval₁ : ((M₁.toNat : ℚ) + δ₁) * 10 ^ e₁ = ((M.toNat : ℚ) + δ) * 10 ^ e := by
    rw [hδ₁_def, add_mul, add_mul, hval_su]
    congr 1
    rw [show δ * 10 ^ (e - e₁) * 10 ^ e₁ = δ * (10 ^ (e - e₁) * 10 ^ e₁) from by ring,
        ← zpow_add₀ (by norm_num : (10 : ℚ) ≠ 0), show e - e₁ + e₁ = e from by omega]
  have hδ₁M : δ₁ * 10 ^ 20 ≤ (M₁.toNat : ℚ) := by
    by_cases hst : sticky = true
    · have h := hδM hst
      have lhs_eq : δ₁ * 10 ^ 20 * 10 ^ e₁ = δ * 10 ^ 20 * 10 ^ e := by
        rw [hδ₁_def,
            show δ * 10 ^ (e - e₁) * 10 ^ 20 * 10 ^ e₁
              = δ * 10 ^ 20 * (10 ^ (e - e₁) * 10 ^ e₁) from by ring,
            ← zpow_add₀ (by norm_num : (10 : ℚ) ≠ 0), show e - e₁ + e₁ = e from by omega]
      have hfin : δ₁ * 10 ^ 20 * 10 ^ e₁ ≤ (M₁.toNat : ℚ) * 10 ^ e₁ := by
        rw [lhs_eq, hval_su]
        exact mul_le_mul_of_nonneg_right h (le_of_lt h10e_pos)
      exact le_of_mul_le_mul_right hfin h10e₁_pos
    · rw [Bool.not_eq_true] at hst
      rw [hδ₁_zero hst, zero_mul]
      exact Nat.cast_nonneg _
  have hδ₁_le : δ₁ ≤ 1 := by
    rcases hM₁_size with ⟨_, heeq⟩ | hlt19
    · rw [hδ₁_def, heeq, sub_self, zpow_zero, mul_one]
      exact hδ_le
    · have hM₁q : (M₁.toNat : ℚ) < 10 ^ 19 := by exact_mod_cast hlt19
      linarith [hδ₁M, hM₁q]
  -- Initial guard: represents with the appropriate shadow.
  set g₀ : Guard := (if sticky = true
      then (if zn then Guard.new.set_negative else Guard.new).set_sticky
      else (if zn then Guard.new.set_negative else Guard.new)) with hg₀_def
  set ftilde₀ : ℚ := (if sticky = true then (1 : ℚ) / 10 ^ 17 else 0) with hft₀_def
  have hrep₀ : represents g₀ ftilde₀ := by
    rw [hg₀_def, hft₀_def]
    by_cases hst : sticky = true
    · rw [if_pos hst, if_pos hst]
      exact represents_sticky_initial128 zn
    · rw [if_neg hst, if_neg hst]
      exact represents_initial128 zn
  -- (`set g₀` has already abstracted the model's seeded guard inside `hok`.)
  -- scaleDown stage.
  cases hsd : doNormalize_scaleDown128 largeRange.max M₁ e₁ g₀ with
  | error err =>
    except_clash hsd hok
  | ok sd =>
    rw [hsd] at hok
    simp only [] at hok
    obtain ⟨φ₂, ftilde₂, h2nn, h2lt, h2rep, h2slip, h2val, h2le, h2lt22, h2exp, h2sbit, h2xbit,
            _, _⟩ :=
      doNormalize_scaleDown128_repr largeRange.max M₁ e₁ g₀ hmaxM_v δ₁ ftilde₀
        hδ₁_nn hδ₁_le hrep₀ hM₁_lt sd hsd
    -- Underflow check must be false (else the result is zero).
    by_cases hund : (sd.2.1 < minExponent || sd.1 < toUInt128 largeRange.min) = true
    · rw [if_pos hund] at hok
      exfalso; apply hres
      have := Except.ok.inj hok
      rw [← this]
      rfl
    · rw [if_neg hund] at hok
      rw [Bool.not_eq_true, Bool.or_eq_false_iff] at hund
      obtain ⟨hund1, hund2⟩ := hund
      have he₂_ge : minExponent ≤ sd.2.1 := by
        by_contra h
        push_neg at h
        exact absurd (decide_eq_true h) (by rw [hund1]; simp)
      have hM₂_ge : 1000000000000000000 ≤ sd.1.toNat := by
        by_contra h
        push_neg at h
        apply absurd (decide_eq_true (show sd.1 < toUInt128 largeRange.min from by
          rw [BitVec.lt_def, toNat_toUInt128, hminM_v]; exact h))
        rw [hund2]; simp
      -- Convert to UInt64.
      have hM₂_fit : sd.1.toNat < 2 ^ 64 := by
        rw [hmaxM_v] at h2le
        omega
      have hM₂u_toNat : (toUInt64 sd.1).toNat = sd.1.toNat := toNat_toUInt64 hM₂_fit
      -- capAtMaxRep stage.
      cases hcap : doNormalize_capAtMaxRep (toUInt64 sd.1) sd.2.1 sd.2.2 with
      | error err =>
        except_clash hcap hok
      | ok cp =>
        rw [hcap] at hok
        simp only [] at hok
        obtain ⟨φ₃, ftilde₃, h3nn, h3lt, h3rep, h3slip, h3val, h3floor, h3le, h3exp, h3sbit, h3xbit,
                _, _⟩ :=
          doNormalize_capAtMaxRep_repr (toUInt64 sd.1) sd.2.1 sd.2.2
            (by rw [hM₂u_toNat]; exact hM₂_ge)
            (by rw [hM₂u_toNat]; rw [hmaxM_v] at h2le; exact h2le)
            φ₂ ftilde₂ h2nn h2lt h2rep cp hcap
        -- Final doRoundUp.
        cases hru : cp.2.2.doRoundUp zn cp.1 cp.2.1 largeRange.min largeRange.max
            .to_nearest .normalize2 with
        | error err =>
          except_clash hru hok
        | ok res =>
          rw [hru] at hok
          have h_result : result = res.toNumber := (Except.ok.inj hok).symm
          have hres_mant : res.mantissa_ ≠ 0 := by
            rw [h_result] at hres
            exact hres
          -- Positive-sign doRoundUp for the supTight lemma.
          set res_pos : RoundResult :=
            { negative_ := false, mantissa_ := res.mantissa_, exponent_ := res.exponent_ }
            with hres_pos_def
          have h_rup_pos : cp.2.2.doRoundUp false cp.1 cp.2.1 largeRange.min largeRange.max
              .to_nearest .normalize2 = .ok res_pos :=
            doRoundUp_false_from_ok cp.2.2 zn cp.1 cp.2.1 .to_nearest .normalize2 res hru
          have hres_pos_mant : res_pos.mantissa_ ≠ 0 := hres_mant
          have h_floor_le : (mantissaFloor : ℕ) ≤ cp.1.toNat := le_of_lt h3floor
          have h_floor_vac : cp.1.toNat = mantissaFloor → (8 : ℚ) / 10 ≤ ftilde₃ := by
            intro h
            exfalso
            omega
          have h_sup := doRoundUp_rounds_to_nearest_supTight_upTo_maxRepUp
            cp.2.2 cp.1 cp.2.1 ftilde₃ h3rep h_floor_le h3le h_floor_vac
            .normalize2 res_pos h_rup_pos hres_pos_mant
          -- |result.toRat| in terms of res.
          have h_abs : |result.toRat| = (res.mantissa_.toNat : ℚ) * 10 ^ res.exponent_ := by
            rw [h_result, abs_toRat_eq res.toNumber]
            rfl
          have h_neg : result.negative_ = zn := by
            rw [h_result]
            exact doRoundUp_negative_of_mant_ne cp.2.2 zn cp.1 cp.2.1 _ _ _
              .normalize2 res hru hres_mant
          refine ⟨?_, h_neg⟩
          -- Assemble the triangle.
          set V : ℚ := ((M.toNat : ℚ) + δ) * 10 ^ e with hV_def
          set A : ℚ := ((cp.1.toNat : ℚ) + ftilde₃) * 10 ^ cp.2.1 with hA_def
          set W : ℚ := ((cp.1.toNat : ℚ) + φ₃) * 10 ^ cp.2.1 with hW_def
          have hVW : W = V := by
            rw [← h3val, hM₂u_toNat, ← h2val, hval₁]
          have h_sup' : |(|result.toRat|) - A| ≤ A * (5 / ((2 ^ 63 + 7 : ℕ) : ℚ)) := by
            rw [h_abs, hA_def]
            exact h_sup
          -- Slip at the final scale, bounded uniformly via the tail-vs-mantissa
          -- ratio: |δ₁ − f̃₀| ≤ δ₁ + 10⁻¹⁷, δ₁·10²⁰ ≤ M₁, and M₁ + δ₁ ≥ 10¹⁸
          -- (the post-scaleDown mantissa is ≥ 10¹⁸ at a no-smaller exponent),
          -- so the slip is at most V/10¹⁹.
          have h_slip_chain : |φ₃ - ftilde₃| * (10 : ℚ) ^ cp.2.1 ≤ |δ₁ - ftilde₀| * (10 : ℚ) ^ e₁ := by
            calc |φ₃ - ftilde₃| * (10 : ℚ) ^ cp.2.1 ≤ |φ₂ - ftilde₂| * (10 : ℚ) ^ sd.2.1 := h3slip
              _ ≤ |δ₁ - ftilde₀| * (10 : ℚ) ^ e₁ := h2slip
          -- |A - V| ≤ slip at scale.
          have hAV : |A - V| ≤ |φ₃ - ftilde₃| * (10 : ℚ) ^ cp.2.1 := by
            rw [← hVW, hA_def, hW_def]
            rw [show ((cp.1.toNat : ℚ) + ftilde₃) * 10 ^ cp.2.1
                  - ((cp.1.toNat : ℚ) + φ₃) * 10 ^ cp.2.1
                = (ftilde₃ - φ₃) * 10 ^ cp.2.1 from by ring]
            rw [abs_mul, abs_of_nonneg (le_of_lt (zpow_pos (by norm_num : (0:ℚ) < 10) _))]
            rw [abs_sub_comm]
          have h_slip_small : |φ₃ - ftilde₃| * (10 : ℚ) ^ cp.2.1
              ≤ V * (11 / 10 ^ 21) := by
            have h_shadow : |δ₁ - ftilde₀| ≤ δ₁ + 1 / 10 ^ 17 := by
              have hft_nn : (0 : ℚ) ≤ ftilde₀ := by
                rw [hft₀_def]; split_ifs <;> positivity
              have hft_le : ftilde₀ ≤ 1 / 10 ^ 17 := by
                rw [hft₀_def]; split_ifs <;> norm_num
              rw [abs_le]
              constructor <;> linarith [hδ₁_nn]
            have hsd_q : (1000000000000000000 : ℚ) ≤ (sd.1.toNat : ℚ) := by
              exact_mod_cast hM₂_ge
            have hM₁δ_ge : (1000000000000000000 : ℚ) ≤ (M₁.toNat : ℚ) + δ₁ := by
              have h1 : (1000000000000000000 : ℚ) * (10 : ℚ) ^ e₁
                  ≤ ((M₁.toNat : ℚ) + δ₁) * 10 ^ e₁ := by
                rw [h2val]
                calc (1000000000000000000 : ℚ) * (10 : ℚ) ^ e₁
                    ≤ (1000000000000000000 : ℚ) * (10 : ℚ) ^ sd.2.1 :=
                      mul_le_mul_of_nonneg_left
                        (zpow_le_zpow_right₀ (by norm_num) h2exp) (by norm_num)
                  _ ≤ ((sd.1.toNat : ℚ) + φ₂) * 10 ^ sd.2.1 :=
                      mul_le_mul_of_nonneg_right (by linarith [h2nn])
                        (le_of_lt (zpow_pos (by norm_num) _))
              exact le_of_mul_le_mul_right h1 h10e₁_pos
            have h_core : δ₁ + 1 / 10 ^ 17 ≤ ((M₁.toNat : ℚ) + δ₁) * (11 / 10 ^ 21) := by
              norm_num at hδ₁M hM₁δ_ge ⊢
              linarith [hδ₁M, hδ₁_nn, hM₁δ_ge]
            calc |φ₃ - ftilde₃| * (10 : ℚ) ^ cp.2.1
                ≤ |δ₁ - ftilde₀| * (10 : ℚ) ^ e₁ := h_slip_chain
              _ ≤ (δ₁ + 1 / 10 ^ 17) * (10 : ℚ) ^ e₁ :=
                  mul_le_mul_of_nonneg_right h_shadow (le_of_lt h10e₁_pos)
              _ ≤ (((M₁.toNat : ℚ) + δ₁) * (11 / 10 ^ 21)) * (10 : ℚ) ^ e₁ :=
                  mul_le_mul_of_nonneg_right h_core (le_of_lt h10e₁_pos)
              _ = (((M₁.toNat : ℚ) + δ₁) * (10 : ℚ) ^ e₁) * (11 / 10 ^ 21) := by ring
              _ = V * (11 / 10 ^ 21) := by rw [hval₁]
          -- A ≤ V + slip.
          have hA_le : A ≤ V + V * (11 / 10 ^ 21) := by
            have h1 : A - V ≤ |A - V| := le_abs_self _
            have h2 := le_trans hAV h_slip_small
            linarith
          have hV_pos : 0 < V := by
            rw [hV_def]
            have hM1 : (1 : ℚ) ≤ (M.toNat : ℚ) := by exact_mod_cast hM_pos
            have : (0 : ℚ) < (M.toNat : ℚ) + δ := by linarith
            exact mul_pos this (zpow_pos (by norm_num) _)
          -- Final triangle.
          have h_denom : (((2 ^ 63 + 7 : ℕ)) : ℚ) = 9223372036854775815 := by push_cast; norm_num
          calc |(|result.toRat|) - V|
              ≤ |(|result.toRat|) - A| + |A - V| := abs_sub_le _ A _
            _ ≤ A * (5 / ((2 ^ 63 + 7 : ℕ) : ℚ)) + V * (11 / 10 ^ 21) :=
                add_le_add h_sup' (le_trans hAV h_slip_small)
            _ ≤ (V + V * (11 / 10 ^ 21)) * (5 / ((2 ^ 63 + 7 : ℕ) : ℚ)) + V * (11 / 10 ^ 21) := by
                have hc : (0 : ℚ) ≤ 5 / ((2 ^ 63 + 7 : ℕ) : ℚ) := by
                  rw [h_denom]; norm_num
                exact add_le_add (mul_le_mul_of_nonneg_right hA_le hc) (le_refl _)
            _ ≤ V * divSharpε := by
                rw [h_denom, divSharpε]
                nlinarith [hV_pos]

lemma operator_div_rounds_to_nearest_sharp (x y result : Number)
    (hx : x.isNormalized) (hy : y.isNormalized)
    (hok : Number.operator_div x y .to_nearest = .ok result)
    (hresult : result.mantissa_ ≠ 0) :
    |result.toRat - x.toRat / y.toRat| ≤ |x.toRat / y.toRat| * divSharpε := by
  obtain ⟨hx_mant_ne, hy_mant_ne⟩ := operator_div_operands_ne_zero hx hy hok hresult
  obtain ⟨M, ze', δ, zn, sticky, hδ_low, hδ_le, hsticky_zero, hM_pos, hM_lt, hδM,
      htruth, hok128, hsign, _, _⟩ :=
    operator_div_algorithmic_facts_represents x y result .to_nearest hx hy
      hx_mant_ne hy_mant_ne hok
  obtain ⟨hbound, hneg⟩ :=
    doNormalize128_rounds_to_nearest_sharp zn M ze' δ sticky hδ_low hδ_le hsticky_zero
      hM_pos hM_lt hδM result hok128 hresult
  have h_abs_diff_eq : |result.toRat - x.toRat / y.toRat|
      = |(|result.toRat| - |x.toRat / y.toRat|)| :=
    abs_diff_eq_abs_sub_abs_of_sign_aligned result (x.toRat / y.toRat)
      (fun h_neg => hsign.1 (hneg ▸ h_neg))
      (fun h_pos => hsign.2 (hneg ▸ h_pos))
  rw [h_abs_diff_eq, htruth]
  exact hbound

end XRPL.Model.SingleAssetVault.DepTight
