import XRPL.Properties.Vault.Proofs.Roundtrip.DivHalf
import XRPL.Properties.Vault.Proofs.DepositTight.DivSharp
import XRPL.Properties.Protocol.Number.Common.NumberBridge
import XRPL.Properties.Vault.Proofs.Support.NumberFacts

/-! # Integer rounding of a quotient

An integer `z` within half a unit of a `.to_nearest` quotient `Q` of true value `v` is
within `0.552` of `v` below the int64 cusp, within half a unit from `9.3·10¹⁷` on, and
equals `maxRep` above it. -/

namespace XRPL.Model.SingleAssetVault.RtT

open XRPL.Model.Protocol

lemma num_int_of_ge (n : Number) (hn : n.isNormalized)
    (hge : (922337203685477581 : ℚ) ≤ n.toRat) : ∃ z : ℤ, n.toRat = z := by
  have hpos : 0 < n.toRat := lt_of_lt_of_le (by norm_num) hge
  have hm : n.mantissa_ ≠ 0 := fun h => by
    rw [Number.toRat_eq_zero_of_mantissa_zero n h] at hpos; exact lt_irrefl _ hpos
  have hneg := Number.negative_false_of_pos n hpos
  have hv := Number.toRat_of_nonneg n hneg
  obtain ⟨hlo, hhi⟩ := hn.mantissaBounds_nat hm
  have hhiq : (n.mantissa_.toNat : ℚ) < 10 ^ 19 := by exact_mod_cast hhi
  rcases le_or_gt 0 n.exponent_ with he | he
  · obtain ⟨k, hk⟩ : ∃ k : ℕ, n.exponent_ = k := ⟨n.exponent_.toNat, by omega⟩
    refine ⟨(n.mantissa_.toNat : ℤ) * 10 ^ k, ?_⟩
    rw [hv, hk, zpow_natCast]; push_cast; ring
  rcases lt_or_eq_of_le (show n.exponent_ ≤ -1 by omega) with he2 | he1
  · exfalso
    have h1 : (10 : ℚ) ^ n.exponent_ ≤ 10 ^ (-2 : ℤ) := zpow_le_zpow_right₀ (by norm_num) (by omega)
    have h2 : n.toRat < 10 ^ 19 * 10 ^ (-2 : ℤ) := by
      rw [hv]
      calc (n.mantissa_.toNat : ℚ) * 10 ^ n.exponent_ ≤ (n.mantissa_.toNat : ℚ) * 10 ^ (-2 : ℤ) :=
            mul_le_mul_of_nonneg_left h1 (by positivity)
        _ < 10 ^ 19 * 10 ^ (-2 : ℤ) := mul_lt_mul_of_pos_right hhiq (by positivity)
    norm_num at h2; linarith
  · have hv1 : n.toRat = (n.mantissa_.toNat : ℚ) / 10 := by rw [hv, he1]; norm_num; ring
    have hbig : 9223372036854775807 < n.mantissa_.toNat := by
      have : (9223372036854775810 : ℚ) ≤ n.mantissa_.toNat := by rw [hv1] at hge; linarith
      exact_mod_cast (show (9223372036854775807 : ℚ) < n.mantissa_.toNat by linarith)
    have h10 : n.mantissa_.toNat % 10 = 0 := by
      rcases hn with h0 | ⟨-, -, hrep, -, -⟩
      · exact absurd (show n.mantissa_ = 0 by rw [h0]; rfl) hm
      · rcases hrep with h | h
        · exfalso
          have : n.mantissa_.toNat ≤ 9223372036854775807 := by
            have := UInt64.le_iff_toNat_le.mp h; simpa [maxRep] using this
          omega
        · exact h
    obtain ⟨N, hN⟩ : ∃ N : ℕ, n.mantissa_.toNat = 10 * N := ⟨n.mantissa_.toNat / 10, by omega⟩
    refine ⟨(N : ℤ), ?_⟩
    rw [hv1, hN]; push_cast; ring

lemma int_eq_of_close (z w : ℤ) (h : |(z : ℚ) - w| ≤ 1 / 2) : z = w := by
  have h1 := abs_le.mp h
  have ha : (z : ℚ) - w < 1 := by linarith
  have hb : -1 < (z : ℚ) - w := by linarith
  have ha' : z - w < 1 := by exact_mod_cast ha
  have hb' : -1 < z - w := by exact_mod_cast hb
  omega

lemma int_div_cert (x y Q : Number) (hx : x.isNormalized) (hy : y.isNormalized)
    (hok : Number.operator_div x y .to_nearest = .ok Q) (hv : 0 < x.toRat / y.toRat)
    (z : ℤ) (hzQ : |(z : ℚ) - Q.toRat| ≤ 1 / 2) (hzmax : (z : ℚ) ≤ 9223372036854775807) :
    (x.toRat / y.toRat < 9223372036854775807 → |(z : ℚ) - x.toRat / y.toRat| ≤ 69 / 125) ∧
    (925 * 10 ^ 15 ≤ x.toRat / y.toRat → x.toRat / y.toRat < 9223372036854775807 →
      |(z : ℚ) - x.toRat / y.toRat| ≤ 1 / 2) ∧
    (9223372036854775807 ≤ x.toRat / y.toRat → (z : ℚ) = 9223372036854775807) := by
  set v := x.toRat / y.toRat with hvdef
  have hrr := operator_div_rounded_to_nearest x y Q hx hy hok
  have hQn : ∀ w : ℤ, Q.toRat = w → z = w := fun w hw => int_eq_of_close z w (by rw [← hw]; exact hzQ)
  have hzQ' := abs_le.mp hzQ
  by_cases hQm : Q.mantissa_ = 0
  · have hxm : x.mantissa_ ≠ 0 := fun h => by
      rw [hvdef, Number.toRat_eq_zero_of_mantissa_zero x h, zero_div] at hv; exact lt_irrefl _ hv
    have hym : y.mantissa_ ≠ 0 := fun h => by
      rw [hvdef, Number.toRat_eq_zero_of_mantissa_zero y h, div_zero] at hv; exact lt_irrefl _ hv
    have hsm := operator_div_underflow_truth_small x y Q .to_nearest hx hy hxm hym hok hQm
    rw [abs_of_pos hv] at hsm
    have htiny : (10 : ℚ) ^ (18 : ℕ) * (10 : ℚ) ^ (minExponent : ℤ) ≤ 1 / 10 := by
      have : (10 : ℚ) ^ (minExponent : ℤ) ≤ 10 ^ (-19 : ℤ) :=
        zpow_le_zpow_right₀ (by norm_num) (by norm_num [minExponent])
      have h2 : (10 : ℚ) ^ (18 : ℕ) * 10 ^ (-19 : ℤ) = 1 / 10 := by norm_num
      rw [← h2]; exact mul_le_mul_of_nonneg_left this (by positivity)
    have hQ0 : Q.toRat = 0 := Number.toRat_eq_zero_of_mantissa_zero Q hQm
    have hz0 : z = 0 := hQn 0 (by rw [hQ0]; simp)
    rw [hz0]; push_cast
    refine ⟨fun _ => ?_, fun h => ?_, fun h => ?_⟩
    · rw [abs_le]; constructor <;> linarith
    · exfalso; linarith
    · exfalso; linarith
  have hrel := DepTight.operator_div_rounds_to_nearest_sharp x y Q hx hy hok hQm
  rw [abs_of_pos hv] at hrel
  have hrel' := abs_le.mp hrel
  have hε : DepTight.divSharpε = 555 / 10 ^ 21 := rfl
  rw [hε] at hrel'
  obtain ⟨zm, k, hlo, hhi, hvlo, hvhi, hfl, hcert⟩ := div_half x y Q hx hy hok hQm hv
  rw [← hvdef] at hrel' hvlo hvhi hfl hcert hrr
  have hzmq : (922337203685477580 : ℚ) ≤ zm := by exact_mod_cast hlo
  have hzmq' : (zm : ℚ) ≤ 9223372036854775810 := by exact_mod_cast hhi
  have hmx : (⟨false, 9223372036854775807, 0⟩ : Number).isNormalized := by decide
  have hmx1 : (⟨false, 9223372036854775807, -1⟩ : Number).isNormalized := by decide
  have h7 : (9223372036854775807 : UInt64).toNat = 9223372036854775807 := by decide
  have hmxv : (⟨false, 9223372036854775807, 0⟩ : Number).toRat = 9223372036854775807 := by
    rw [Number.toRat_of_nonneg _ rfl]; simp only [h7]; norm_num
  have hmxv1 : (⟨false, 9223372036854775807, -1⟩ : Number).toRat = 9223372036854775807 / 10 := by
    rw [Number.toRat_of_nonneg _ rfl]; simp only [h7]; norm_num
  refine ⟨fun hlt => ?_, fun h93 hlt => ?_, fun hge => ?_⟩
  rotate_left 2
  · have hQge := Number.RoundsToRepresentable.ge_of_ge_normalized Q v hrr _ hmx (by rw [hmxv]; exact hge)
    rw [hmxv] at hQge
    obtain ⟨w, hw⟩ := num_int_of_ge Q (operator_div_result_isNormalized x y Q .to_nearest hx hy
      (fun h => by rw [hvdef, Number.toRat_eq_zero_of_mantissa_zero x h, zero_div] at hv
                   exact lt_irrefl _ hv)
      (fun h => by rw [hvdef, Number.toRat_eq_zero_of_mantissa_zero y h, div_zero] at hv
                   exact lt_irrefl _ hv) hok hQm) (by linarith)
    have := hQn w hw
    subst this
    rw [hw] at hQge
    linarith
  all_goals
    have hk : k ≤ 0 := by
      by_contra hk
      have h10 : (10 : ℚ) ≤ 10 ^ k := by
        have := zpow_le_zpow_right₀ (show (1 : ℚ) ≤ 10 by norm_num) (show (1 : ℤ) ≤ k by omega)
        simpa using this
      have hzm0 : zm = 922337203685477580 := by
        have : (zm : ℚ) * 10 < 922337203685477580 * 10 + 10 := by nlinarith
        have : (zm : ℚ) < 922337203685477581 := by linarith
        have : zm < 922337203685477581 := by exact_mod_cast this
        omega
      have := hfl hzm0
      rw [hzm0] at this; push_cast at this
      nlinarith
  · -- the half-unit branch below the cusp
    rcases (show k ≤ -2 ∨ k = -1 ∨ k = 0 by omega) with hk2 | hk1 | hk0
    · have hu : (10 : ℚ) ^ k ≤ 1 / 100 := by
        have := zpow_le_zpow_right₀ (show (1 : ℚ) ≤ 10 by norm_num) hk2
        norm_num at this ⊢; exact this
      have hu0 : (0 : ℚ) < 10 ^ k := zpow_pos (by norm_num) _
      by_cases hzl : zm < 9223372036854775807
      · have := abs_le.mp (hcert hzl).2
        rw [abs_le]; constructor <;> nlinarith
      · have hv9 : v < 9223372036854775811 / 100 := by nlinarith
        rw [abs_le]; constructor <;> nlinarith
    · subst hk1
      have hu : (10 : ℚ) ^ (-1 : ℤ) = 1 / 10 := by norm_num
      rw [hu] at hvlo hvhi
      by_cases hzl : zm < 9223372036854775807
      · have := abs_le.mp (hcert hzl).2
        rw [hu] at this
        rw [abs_le]; constructor <;> linarith
      · have hzm7 : (9223372036854775807 : ℚ) ≤ zm := by
          have : 9223372036854775807 ≤ zm := by omega
          exact_mod_cast this
        have hQge := Number.RoundsToRepresentable.ge_of_ge_normalized Q v hrr _ hmx1
          (by rw [hmxv1]; linarith)
        rw [hmxv1] at hQge
        have hz81 : z = 922337203685477581 := by
          by_cases hQ81 : (922337203685477581 : ℚ) ≤ Q.toRat
          · obtain ⟨w, hw⟩ := num_int_of_ge Q (operator_div_result_isNormalized x y Q .to_nearest
              hx hy (fun h => by rw [hvdef, Number.toRat_eq_zero_of_mantissa_zero x h, zero_div] at hv
                                 exact lt_irrefl _ hv)
              (fun h => by rw [hvdef, Number.toRat_eq_zero_of_mantissa_zero y h, div_zero] at hv
                           exact lt_irrefl _ hv) hok hQm) hQ81
            have hzw := hQn w hw
            subst hzw
            have h1 : (z : ℚ) < 922337203685477582 := by rw [← hw]; nlinarith
            have h2 : z < 922337203685477582 := by exact_mod_cast h1
            have h3 : (922337203685477581 : ℚ) ≤ z := by rw [← hw]; exact hQ81
            have h4 : 922337203685477581 ≤ z := by exact_mod_cast h3
            omega
          · have h1 : (z : ℚ) < 922337203685477582 := by linarith
            have h3 : (922337203685477580 : ℚ) < z := by linarith
            have h2 : z < 922337203685477582 := by exact_mod_cast h1
            have h4 : 922337203685477580 < z := by exact_mod_cast h3
            omega
        rw [hz81]; push_cast
        rw [abs_le]; constructor <;> linarith
    · subst hk0
      rw [zpow_zero, mul_one] at hvlo hvhi
      have hzl : zm < 9223372036854775807 := by
        have : (zm : ℚ) < 9223372036854775807 := by linarith
        exact_mod_cast this
      obtain ⟨hQv, hh⟩ := hcert hzl
      rw [zpow_zero, mul_one] at hQv hh
      have hzQ2 : z = Q.toRat := by
        rcases hQv with h | h
        · have := hQn zm (by rw [h]; push_cast; ring); rw [this, h]; push_cast; ring
        · have := hQn (zm + 1) (by rw [h]; push_cast; ring); rw [this, h]; push_cast; ring
      rw [hzQ2]
      exact le_trans hh (by norm_num)
  · rcases (show k ≤ -1 ∨ k = 0 by omega) with hk1 | hk0
    · exfalso
      have hu : (10 : ℚ) ^ k ≤ 1 / 10 := by
        have := zpow_le_zpow_right₀ (show (1 : ℚ) ≤ 10 by norm_num) hk1
        norm_num at this ⊢; exact this
      have := mul_le_mul_of_nonneg_left hu (show (0 : ℚ) ≤ (zm : ℚ) + 1 by positivity)
      linarith
    · subst hk0
      rw [zpow_zero, mul_one] at hvlo hvhi
      have h1 : (zm : ℚ) < 9223372036854775807 := lt_of_le_of_lt hvlo hlt
      have hzl : zm < 9223372036854775807 := by exact_mod_cast h1
      obtain ⟨hQv, hh⟩ := hcert hzl
      rw [zpow_zero, mul_one] at hQv hh
      have hzQ2 : z = Q.toRat := by
        rcases hQv with h | h
        · have := hQn zm (by rw [h]; push_cast; ring); rw [this, h]; push_cast; ring
        · have := hQn (zm + 1) (by rw [h]; push_cast; ring); rw [this, h]; push_cast; ring
      rw [hzQ2]; exact hh

/-- Between `9.3·10¹⁶` and `9.22·10¹⁷` the quotient sits on the `0.1` grid, so the integer is
within `0.55` of the true value. -/
lemma int_div_mid (x y Q : Number) (hx : x.isNormalized) (hy : y.isNormalized)
    (hok : Number.operator_div x y .to_nearest = .ok Q) (hv : 0 < x.toRat / y.toRat)
    (z : ℤ) (hzQ : |(z : ℚ) - Q.toRat| ≤ 1 / 2) :
    93 * 10 ^ 15 ≤ x.toRat / y.toRat → x.toRat / y.toRat < 922 * 10 ^ 15 →
      |(z : ℚ) - x.toRat / y.toRat| ≤ 11 / 20 := by
  intro hlo hhi
  have hzQ' := abs_le.mp hzQ
  by_cases hQm : Q.mantissa_ = 0
  · exfalso
    have hxm : x.mantissa_ ≠ 0 := fun h => by
      rw [Number.toRat_eq_zero_of_mantissa_zero x h, zero_div] at hv; exact lt_irrefl _ hv
    have hym : y.mantissa_ ≠ 0 := fun h => by
      rw [Number.toRat_eq_zero_of_mantissa_zero y h, div_zero] at hv; exact lt_irrefl _ hv
    have hsm := operator_div_underflow_truth_small x y Q .to_nearest hx hy hxm hym hok hQm
    rw [abs_of_pos hv] at hsm
    have : (10 : ℚ) ^ (minExponent : ℤ) ≤ 10 ^ (-19 : ℤ) :=
      zpow_le_zpow_right₀ (by norm_num) (by norm_num [minExponent])
    have h2 : (10 : ℚ) ^ (18 : ℕ) * 10 ^ (-19 : ℤ) = 1 / 10 := by norm_num
    have h3 := mul_le_mul_of_nonneg_left this (show (0 : ℚ) ≤ 10 ^ (18 : ℕ) by positivity)
    rw [h2] at h3
    linarith
  obtain ⟨zm, k, hlo', hhi', hvlo, hvhi, -, hcert⟩ := div_half x y Q hx hy hok hQm hv
  have hzmq : (922337203685477580 : ℚ) ≤ zm := by exact_mod_cast hlo'
  have hzmq' : (zm : ℚ) ≤ 9223372036854775810 := by exact_mod_cast hhi'
  rcases (show k ≤ -2 ∨ k = -1 ∨ 0 ≤ k by omega) with hk | hk | hk
  · exfalso
    have hu : (10 : ℚ) ^ k ≤ 1 / 100 := by
      have := zpow_le_zpow_right₀ (show (1 : ℚ) ≤ 10 by norm_num) hk
      norm_num at this ⊢; exact this
    have := mul_le_mul_of_nonneg_left hu (show (0 : ℚ) ≤ (zm : ℚ) + 1 by positivity)
    linarith
  · subst hk
    have hu : (10 : ℚ) ^ (-1 : ℤ) = 1 / 10 := by norm_num
    rw [hu] at hvlo hvhi
    have hzl : zm < 9223372036854775807 := by
      have : (zm : ℚ) < 9223372036854775807 := by linarith
      exact_mod_cast this
    have := abs_le.mp (hcert hzl).2
    rw [hu] at this
    rw [abs_le]; constructor <;> linarith
  · exfalso
    have h1 : (1 : ℚ) ≤ 10 ^ k := one_le_zpow₀ (by norm_num) hk
    have := mul_le_mul_of_nonneg_left h1 (show (0 : ℚ) ≤ (zm : ℚ) by positivity)
    linarith

end XRPL.Model.SingleAssetVault.RtT
