import XRPL.Properties.Vault.Proofs.DepositTight.LowerRound
import XRPL.Properties.Vault.Proofs.DepositTight.DivExact

/-! # The quotient stage seen from below, without sticky slip -/

namespace XRPL.Model.SingleAssetVault.DepTight

open XRPL.Model.Protocol

/-- `doNormalize128` (`.to_nearest`) lands on a grid point at or above the value, half a step below it
at most (one step at `maxRep`/`maxRepUp`), or on `maxRep` from the interior cusp. -/
private lemma doNormalize128_lower_exact
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
  obtain ⟨g, zm, ze, ft, f, res, hrep, -, -, hflt, hc1, -, hc3, hfloor, hub, hV, hru, hne, habs,
      hneg⟩ :=
    doNormalize128_to_nearest_stages zn M e δ sticky hδ_low (le_of_lt hδ_lt) hsticky_zero hM_pos
      hM_lt hδM result hok hres
  refine ⟨?_, hneg⟩
  have hflt' : f < 1 := hflt hδ_lt
  have hγ : (0 : ℚ) < 10 ^ ze := zpow_pos (by norm_num) _
  have hhalf : ft ≤ 1 / 2 → f ≤ 1 / 2 := by
    intro h
    rcases lt_or_eq_of_le h with h | h
    · exact hc1 h
    · exact le_of_eq (hc3 h)
  rw [← hV, habs]
  rcases doRoundUp_lower g zm ze ft hrep hub .normalize2 res hru hne with
    hup | ⟨heq, hcase⟩ | ⟨hcv, hm, hf⟩
  · left
    refine ⟨?_, ?_⟩
    · have : ((zm.toNat : ℚ) + f) * 10 ^ ze < ((zm.toNat : ℚ) + 1) * 10 ^ ze :=
        mul_lt_mul_of_pos_right (by linarith) hγ
      linarith
    · obtain ⟨hlo, hhi, -, h10⟩ := doRoundUp_output_invariants_to_nearest_upTo_maxRepUp
        g false zm ze (le_of_lt hfloor) hub .normalize2 res hru hne
      rw [largeRange_min_val] at hlo
      rw [largeRange_max_val] at hhi
      rw [maxRep_val] at h10
      exact ⟨res.exponent_, res.mantissa_.toNat, hlo, by omega, h10, rfl⟩
  · right; left
    refine ⟨ze, zm.toNat, by omega, heq, mul_lt_mul_of_pos_right (by linarith) hγ, ?_⟩
    rcases hcase with ⟨hf, hm⟩ | hm | hm
    · left
      exact ⟨mul_le_mul_of_nonneg_right (by linarith [hhalf hf]) (le_of_lt hγ), hm⟩
    · right; left; exact hm
    · right; right; exact hm
  · right; right
    refine ⟨ze, hcv, ?_⟩
    have hm' : (zm.toNat : ℚ) = 9223372036854775808 := by exact_mod_cast hm
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
