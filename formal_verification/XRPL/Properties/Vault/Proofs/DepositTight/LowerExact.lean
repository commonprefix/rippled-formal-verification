import XRPL.Properties.Vault.Proofs.DepositTight.LowerRound
import XRPL.Properties.Vault.Proofs.DepositTight.DivExact

/-! # The quotient stage seen from below, without sticky slip -/

namespace XRPL.Model.SingleAssetVault.DepTight

open XRPL.Model.Protocol

set_option maxHeartbeats 3200000 in
-- Same four-stage pipeline as the exact keystone.
/-- `doNormalize128` (`.to_nearest`) lands on a grid point at or above the value, half a
step below it at most (one step at `maxRep`/`maxRepUp`), or on `maxRep` from the interior
cusp within `maxRep + 3/2` steps. -/
lemma doNormalize128_lower_exact
    (zn : Bool) (M : UInt128) (e : Int) (δ : ℚ) (sticky : Bool)
    (hδ_low : 0 ≤ δ) (hδ_lt : δ < 1)
    (hsticky_zero : sticky = false → δ = 0)
    (hM_pos : 1 ≤ M.toNat) (hM_lt : M.toNat < 10 ^ 23)
    (hδM : sticky = true → δ * 10 ^ 20 ≤ (M.toNat : ℚ))
    (result : Number)
    (hok : doNormalize128 zn M e largeRange.min largeRange.max .to_nearest sticky = .ok result)
    (hres : result.mantissa_ ≠ 0) :
    ((((M.toNat : ℚ) + δ) * 10 ^ e ≤ |result.toRat| ∧
        ∃ E : ℤ, ∃ n : ℕ, 10 ^ 18 ≤ n ∧ n < 10 ^ 19 ∧ (9223372036854775807 < n → n % 10 = 0) ∧
          |result.toRat| = (n : ℚ) * 10 ^ E) ∨
      (∃ E : ℤ, ∃ m : ℕ, 922337203685477581 ≤ m ∧ |result.toRat| = (m : ℚ) * 10 ^ E ∧
        ((M.toNat : ℚ) + δ) * 10 ^ e < ((m : ℚ) + 1) * 10 ^ E ∧
        ((((M.toNat : ℚ) + δ) * 10 ^ e ≤ ((m : ℚ) + 1 / 2) * 10 ^ E ∧ m ≤ 9223372036854775807) ∨
          m = 9223372036854775807 ∨ m = 9223372036854775810)) ∨
      (∃ E : ℤ, |result.toRat| = 9223372036854775807 * 10 ^ E ∧
        ((M.toNat : ℚ) + δ) * 10 ^ e ≤ (9223372036854775808 + 1 / 2) * 10 ^ E)) ∧
    result.negative_ = zn := by
  have hminM_v : largeRange.min.toNat = 1000000000000000000 := largeRange_min_val
  have hmaxM_v : largeRange.max.toNat = 9999999999999999999 := largeRange_max_val
  have hM_ne : ¬ (M == 0) = true := by
    intro h
    have : M = 0 := by exact_mod_cast beq_iff_eq.mp h
    rw [this] at hM_pos
    simp at hM_pos
  unfold doNormalize128 at hok
  rw [if_neg hM_ne] at hok
  simp only [] at hok
  rcases hsu : doNormalize128.scaleUp largeRange.min M e with ⟨M₁, e₁⟩
  rw [hsu] at hok
  simp only [] at hok
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
  have hδ₁_lt : δ₁ < 1 := by
    rcases hM₁_size with ⟨_, heeq⟩ | hlt19
    · rw [hδ₁_def, heeq, sub_self, zpow_zero, mul_one]
      exact hδ_lt
    · have hM₁q : (M₁.toNat : ℚ) < 10 ^ 19 := by exact_mod_cast hlt19
      linarith [hδ₁M, hM₁q]
  have hδ₁_le : δ₁ ≤ 1 := le_of_lt hδ₁_lt
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
  have hft₀_nn : (0 : ℚ) ≤ ftilde₀ := by rw [hft₀_def]; split_ifs <;> positivity
  have hft₀_lt : ftilde₀ < 1 := by rw [hft₀_def]; split_ifs <;> norm_num
  have hft₀_zero : ftilde₀ = 0 → δ₁ = 0 := by
    intro h
    by_cases hst : sticky = true
    · rw [hft₀_def, if_pos hst] at h; norm_num at h
    · exact hδ₁_zero (by simpa using hst)
  cases hsd : doNormalize_scaleDown128 largeRange.max M₁ e₁ g₀ with
  | error err =>
    except_clash hsd hok
  | ok sd =>
    rw [hsd] at hok
    simp only [] at hok
    obtain ⟨φ₂, -, h2nn, h2lt, -, -, h2val, h2le, -, h2exp, -, -, -, h2lt1⟩ :=
      doNormalize_scaleDown128_repr largeRange.max M₁ e₁ g₀ hmaxM_v δ₁ ftilde₀
        hδ₁_nn hδ₁_le hrep₀ hM₁_lt sd hsd
    obtain ⟨ψ₂, ftilde₂, -, -, h2rep, h2slip, h2sval, -, -, -, -, -, -, -⟩ :=
      doNormalize_scaleDown128_repr largeRange.max M₁ e₁ g₀ hmaxM_v ftilde₀ ftilde₀
        hft₀_nn (le_of_lt hft₀_lt) hrep₀ hM₁_lt sd hsd
    have hψ₂ : ψ₂ = ftilde₂ := by
      rw [sub_self, abs_zero, zero_mul] at h2slip
      have h := abs_nonneg (ψ₂ - ftilde₂)
      have hz : |ψ₂ - ftilde₂| = 0 := by
        have hp : (0 : ℚ) < (10 : ℚ) ^ sd.2.1 := zpow_pos (by norm_num) _
        nlinarith
      linarith [abs_eq_zero.mp hz]
    rw [hψ₂] at h2sval
    by_cases hund : (sd.2.1 < minExponent || sd.1 < toUInt128 largeRange.min) = true
    · rw [if_pos hund] at hok
      exfalso; apply hres
      have := Except.ok.inj hok
      rw [← this]
      rfl
    · rw [if_neg hund] at hok
      rw [Bool.not_eq_true, Bool.or_eq_false_iff] at hund
      obtain ⟨-, hund2⟩ := hund
      have hM₂_ge : 1000000000000000000 ≤ sd.1.toNat := by
        by_contra h
        push Not at h
        apply absurd (decide_eq_true (show sd.1 < toUInt128 largeRange.min from by
          rw [BitVec.lt_def, toNat_toUInt128, hminM_v]; exact h))
        rw [hund2]; simp
      have hM₂_fit : sd.1.toNat < 2 ^ 64 := by
        rw [hmaxM_v] at h2le
        omega
      have hM₂u_toNat : (toUInt64 sd.1).toNat = sd.1.toNat := toNat_toUInt64 hM₂_fit
      cases hcap : doNormalize_capAtMaxRep (toUInt64 sd.1) sd.2.1 sd.2.2 with
      | error err =>
        except_clash hcap hok
      | ok cp =>
        rw [hcap] at hok
        simp only [] at hok
        have hge : 1000000000000000000 ≤ (toUInt64 sd.1).toNat := by rw [hM₂u_toNat]; exact hM₂_ge
        have hle : (toUInt64 sd.1).toNat ≤ 9999999999999999999 := by
          rw [hM₂u_toNat]; rw [hmaxM_v] at h2le; exact h2le
        obtain ⟨φ₃, -, h3nn, h3le1, -, -, h3val, h3floor, h3le, h3exp, -, -, -, h3lt1⟩ :=
          doNormalize_capAtMaxRep_repr (toUInt64 sd.1) sd.2.1 sd.2.2 hge hle
            φ₂ ftilde₂ h2nn h2lt h2rep cp hcap
        obtain ⟨ψ₃, ftilde₃, -, -, h3rep, h3slip, h3sval, -, -, -, -, -, -, -⟩ :=
          doNormalize_capAtMaxRep_repr (toUInt64 sd.1) sd.2.1 sd.2.2 hge hle
            ftilde₂ ftilde₂ (represents_nonneg h2rep) (le_of_lt (represents_lt_one h2rep))
            h2rep cp hcap
        have hψ₃ : ψ₃ = ftilde₃ := by
          rw [sub_self, abs_zero, zero_mul] at h3slip
          have hz : |ψ₃ - ftilde₃| = 0 := by
            have hp : (0 : ℚ) < (10 : ℚ) ^ cp.2.1 := zpow_pos (by norm_num) _
            nlinarith [abs_nonneg (ψ₃ - ftilde₃)]
          linarith [abs_eq_zero.mp hz]
        rw [hψ₃] at h3sval
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
          set res_pos : RoundResult :=
            { negative_ := false, mantissa_ := res.mantissa_, exponent_ := res.exponent_ }
            with hres_pos_def
          have h_rup_pos : cp.2.2.doRoundUp false cp.1 cp.2.1 largeRange.min largeRange.max
              .to_nearest .normalize2 = .ok res_pos :=
            doRoundUp_false_from_ok cp.2.2 zn cp.1 cp.2.1 .to_nearest .normalize2 res hru
          have h_abs : |result.toRat| = (res.mantissa_.toNat : ℚ) * 10 ^ res.exponent_ := by
            rw [h_result, abs_toRat_eq res.toNumber]
            rfl
          have h_neg : result.negative_ = zn := by
            rw [h_result]
            exact doRoundUp_negative_of_mant_ne cp.2.2 zn cp.1 cp.2.1 _ _ _
              .normalize2 res hru hres_mant
          refine ⟨?_, h_neg⟩
          -- truth and shadow at the final scale
          obtain ⟨k, hk⟩ : ∃ k : ℕ, cp.2.1 = e₁ + k :=
            ⟨(cp.2.1 - e₁).toNat, by omega⟩
          have hsc : (10 : ℚ) ^ cp.2.1 = 10 ^ e₁ * (10 : ℚ) ^ k := by
            rw [hk, zpow_add₀ (by norm_num : (10 : ℚ) ≠ 0), zpow_natCast]
          have hT : (M₁.toNat : ℚ) + δ₁ = ((cp.1.toNat : ℚ) + φ₃) * 10 ^ k := by
            have h' : ((M₁.toNat : ℚ) + δ₁) * 10 ^ e₁
                = (((cp.1.toNat : ℚ) + φ₃) * 10 ^ k) * 10 ^ e₁ := by
              rw [h2val, ← hM₂u_toNat, h3val, hsc]; ring
            exact mul_right_cancel₀ (ne_of_gt h10e₁_pos) h'
          have hS : (M₁.toNat : ℚ) + ftilde₀ = ((cp.1.toNat : ℚ) + ftilde₃) * 10 ^ k := by
            have h' : ((M₁.toNat : ℚ) + ftilde₀) * 10 ^ e₁
                = (((cp.1.toNat : ℚ) + ftilde₃) * 10 ^ k) * 10 ^ e₁ := by
              rw [h2sval, ← hM₂u_toNat, h3sval, hsc]; ring
            exact mul_right_cancel₀ (ne_of_gt h10e₁_pos) h'
          set D : ℤ := (M₁.toNat : ℤ) - (cp.1.toNat : ℤ) * 10 ^ k with hD_def
          have hDq : ((D : ℤ) : ℚ) = (M₁.toNat : ℚ) - (cp.1.toNat : ℚ) * 10 ^ k := by
            rw [hD_def]; push_cast; ring
          have hφ₃P : φ₃ * 10 ^ k = D + δ₁ := by rw [hDq]; linarith
          have hf₃P : ftilde₃ * 10 ^ k = D + ftilde₀ := by rw [hDq]; linarith
          have hft₃_nn := represents_nonneg h3rep
          have hft₃_lt := represents_lt_one h3rep
          have hP_pos : (0 : ℚ) < (10 : ℚ) ^ k := by positivity
          have hcell : (ftilde₃ < 1 / 2 → φ₃ ≤ 1 / 2) ∧ (1 / 2 < ftilde₃ → 1 / 2 ≤ φ₃) ∧
              (ftilde₃ = 1 / 2 → φ₃ = 1 / 2) := by
            rcases Nat.eq_zero_or_pos k with hk0 | hkpos
            · -- no digit dropped: the tail is below `1/10`
              rw [hk0, pow_zero, mul_one] at hφ₃P hf₃P
              have hD0 : D = 0 := by
                have a : (-1 : ℚ) < D := by linarith
                have b : (D : ℚ) < 1 := by linarith
                have a' : -1 < D := by exact_mod_cast a
                have b' : D < 1 := by exact_mod_cast b
                omega
              rw [hD0, Int.cast_zero, zero_add] at hφ₃P hf₃P
              have hM₁eq : (M₁.toNat : ℚ) = cp.1.toNat := by
                rw [hD0, hk0, pow_zero, mul_one] at hDq
                push_cast at hDq
                linarith
              have hcap_q : (cp.1.toNat : ℚ) ≤ 9223372036854775810 := by
                exact_mod_cast (show cp.1.toNat ≤ 9223372036854775810 from h3le)
              have hδ₁_small : δ₁ < 1 / 2 := by
                rw [hM₁eq] at hδ₁M
                nlinarith
              have hft_small : ftilde₀ ≤ 1 / 10 ^ 17 := by
                rw [hft₀_def]; split_ifs <;> norm_num
              refine ⟨fun _ => by linarith, fun h => ?_, fun h => ?_⟩
              · exfalso; norm_num at hft_small; linarith
              · exfalso; norm_num at hft_small; linarith
            · -- `10^k = 2·H`
              obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
              set H : ℤ := 5 * 10 ^ j with hH_def
              have hHq : (10 : ℚ) ^ (j + 1) = 2 * (H : ℚ) := by
                rw [hH_def]; push_cast; ring
              obtain ⟨c1, c2, c3⟩ := cell_of_even D H ftilde₀ δ₁ hft₀_nn hft₀_lt hδ₁_nn hδ₁_le
                hft₀_zero
              rw [hHq] at hφ₃P hf₃P
              have hH_pos : (0 : ℚ) < H := by rw [hH_def]; positivity
              refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
              · have := c1 (by nlinarith)
                nlinarith
              · have := c2 (by nlinarith)
                nlinarith
              · have := c3 (by rw [← hf₃P, h]; ring)
                have h2 : φ₃ * (2 * H) = 1 / 2 * (2 * H) := by rw [hφ₃P, this]; ring
                exact mul_right_cancel₀ (by positivity) h2
          obtain ⟨hc1, -, hc3⟩ := hcell
          have hφ₃lt : φ₃ < 1 := h3lt1 (h2lt1 hδ₁_lt)
          have hV : ((cp.1.toNat : ℚ) + φ₃) * 10 ^ cp.2.1 = ((M.toNat : ℚ) + δ) * 10 ^ e := by
            rw [← hval₁, h2val, ← hM₂u_toNat, h3val]
          rw [← hV]
          have hR : |result.toRat| = (res_pos.mantissa_.toNat : ℚ) * 10 ^ res_pos.exponent_ := h_abs
          have hγ : (0 : ℚ) < 10 ^ cp.2.1 := zpow_pos (by norm_num) _
          have hhalf : ftilde₃ ≤ 1 / 2 → φ₃ ≤ 1 / 2 := by
            intro h
            rcases lt_or_eq_of_le h with h | h
            · exact hc1 h
            · exact le_of_eq (hc3 h)
          have hlow := doRoundUp_lower cp.2.2 cp.1 cp.2.1 ftilde₃ h3rep h3le .normalize2 res_pos
            h_rup_pos hres_mant
          rw [← hR] at hlow
          rcases hlow with hup | ⟨heq, hcase⟩ | ⟨hcv, hm, hf⟩
          · left
            refine ⟨?_, ?_⟩
            · have : ((cp.1.toNat : ℚ) + φ₃) * 10 ^ cp.2.1 < ((cp.1.toNat : ℚ) + 1) * 10 ^ cp.2.1 :=
                mul_lt_mul_of_pos_right (by linarith) hγ
              linarith
            · obtain ⟨hlo, hhi, -, h10⟩ := doRoundUp_output_invariants_to_nearest_upTo_maxRepUp
                cp.2.2 false cp.1 cp.2.1 (le_of_lt h3floor) h3le .normalize2 res_pos h_rup_pos
                hres_mant
              rw [largeRange_min_val] at hlo
              rw [largeRange_max_val] at hhi
              rw [maxRep_val] at h10
              exact ⟨res_pos.exponent_, res_pos.mantissa_.toNat, hlo, by omega, h10, hR⟩
          · right; left
            refine ⟨cp.2.1, cp.1.toNat, by omega, heq,
              mul_lt_mul_of_pos_right (by linarith) hγ, ?_⟩
            rcases hcase with ⟨hf, hm⟩ | hm | hm
            · left
              refine ⟨mul_le_mul_of_nonneg_right (by linarith [hhalf hf]) (le_of_lt hγ), hm⟩
            · right; left; exact hm
            · right; right; exact hm
          · right; right
            refine ⟨cp.2.1, hcv, ?_⟩
            have hm' : (cp.1.toNat : ℚ) = 9223372036854775808 := by exact_mod_cast hm
            rw [hm']
            exact mul_le_mul_of_nonneg_right (by linarith [hhalf (le_of_lt hf)]) (le_of_lt hγ)

lemma operator_div_lower_exact (x y result : Number)
    (hx : x.isNormalized) (hy : y.isNormalized)
    (hok : Number.operator_div x y .to_nearest = .ok result)
    (hresult : result.mantissa_ ≠ 0) :
    (|x.toRat / y.toRat| ≤ |result.toRat| ∧
        ∃ E : ℤ, ∃ n : ℕ, 10 ^ 18 ≤ n ∧ n < 10 ^ 19 ∧ (9223372036854775807 < n → n % 10 = 0) ∧
          |result.toRat| = (n : ℚ) * 10 ^ E) ∨
      (∃ E : ℤ, ∃ m : ℕ, 922337203685477581 ≤ m ∧ |result.toRat| = (m : ℚ) * 10 ^ E ∧
        |x.toRat / y.toRat| < ((m : ℚ) + 1) * 10 ^ E ∧
        ((|x.toRat / y.toRat| ≤ ((m : ℚ) + 1 / 2) * 10 ^ E ∧ m ≤ 9223372036854775807) ∨
          m = 9223372036854775807 ∨ m = 9223372036854775810)) ∨
      (∃ E : ℤ, |result.toRat| = 9223372036854775807 * 10 ^ E ∧
        |x.toRat / y.toRat| ≤ (9223372036854775808 + 1 / 2) * 10 ^ E) := by
  obtain ⟨hx_mant_ne, hy_mant_ne⟩ := operator_div_operands_ne_zero hx hy hok hresult
  obtain ⟨M, ze', δ, zn, sticky, hδ_low, -, hsticky_zero, hM_pos, hM_lt, hδM,
      htruth, hok128, -, hδ_lt, -⟩ :=
    operator_div_algorithmic_facts_represents x y result .to_nearest hx hy
      hx_mant_ne hy_mant_ne hok
  rw [htruth]
  exact (doNormalize128_lower_exact zn M ze' δ sticky hδ_low hδ_lt hsticky_zero hM_pos
    hM_lt hδM result hok128 hresult).1

end XRPL.Model.SingleAssetVault.DepTight
