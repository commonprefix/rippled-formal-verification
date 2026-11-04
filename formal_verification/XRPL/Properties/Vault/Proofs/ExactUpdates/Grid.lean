import XRPL.Properties.Protocol.Number.Common.NumberBridge
import XRPL.Properties.Vault.Proofs.Support.Integral

/-! # Representable values on a decimal grid

A whole number of steps of a decimal grid is the value of a normalized `Number`, and so is a
difference that stays on the grid. -/

namespace XRPL.Model.SingleAssetVault.Exact

open XRPL.Model.Protocol

/-- A positive integer below `2^63` times `10^g` is the value of a normalized `Number`. -/
lemma exists_normalized_grid (K : ℕ) (g : ℤ) (h1 : 1 ≤ K) (h2 : K < 2 ^ 63)
    (hlo : minExponent + 18 ≤ g) (hhi : g ≤ maxExponent) :
    ∃ w : Number, w.isNormalized ∧ w.toRat = (K : ℚ) * 10 ^ g := by
  have hVne : K ≠ 0 := by omega
  have hlog_lo : 10 ^ Nat.log 10 K ≤ K := Nat.pow_log_le_self 10 hVne
  have hlog_hi : K < 10 ^ (Nat.log 10 K + 1) := Nat.lt_pow_succ_log_self (by norm_num) K
  set L := Nat.log 10 K with hL_def
  have hL_le : L ≤ 18 := by
    by_contra hcon
    rw [not_le] at hcon
    have : (10 : ℕ) ^ 19 ≤ 10 ^ L := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h63 : (2 : ℕ) ^ 63 < 10 ^ 19 := by norm_num
    omega
  set k : ℕ := 18 - L with hk_def
  set M : ℕ := K * 10 ^ k with hM_def
  have hLk : L + k = 18 := by omega
  have hM_lo : 10 ^ 18 ≤ M := by
    calc (10 : ℕ) ^ 18 = 10 ^ L * 10 ^ k := by rw [← pow_add, hLk]
      _ ≤ K * 10 ^ k := mul_le_mul_of_nonneg_right hlog_lo (by positivity)
  have hM_hi : M < 10 ^ 19 := by
    calc M = K * 10 ^ k := rfl
      _ < 10 ^ (L + 1) * 10 ^ k := mul_lt_mul_of_pos_right hlog_hi (by positivity)
      _ = 10 ^ 19 := by rw [← pow_add]; congr 1; omega
  have hM_lt : M < UInt64.size := by rw [uint64_size_val]; omega
  have hM_toNat : (Nat.toUInt64 M).toNat = M :=
    UInt64.toNat_ofNat_of_lt' (by rw [uint64_size_val]; exact hM_lt)
  have hsticky : (Nat.toUInt64 M) ≤ maxRep ∨ (Nat.toUInt64 M).toNat % 10 = 0 := by
    by_cases hk0 : k = 0
    · left
      rw [UInt64.le_iff_toNat_le, hM_toNat, maxRep_val]
      have hMV : M = K := by rw [hM_def, hk0, pow_zero, Nat.mul_one]
      rw [hMV]; omega
    · right
      rw [hM_toNat]
      have hdvd : (10 : ℕ) ∣ M := by
        rw [hM_def]
        exact Dvd.dvd.mul_left (dvd_pow_self 10 (by omega)) K
      omega
  refine ⟨⟨false, Nat.toUInt64 M, g - (k : ℤ)⟩, ?_, ?_⟩
  · right
    refine ⟨?_, ?_, hsticky, ?_, ?_⟩
    · show largeRange.min ≤ Nat.toUInt64 M
      rw [UInt64.le_iff_toNat_le, largeRange_min_val, hM_toNat]; omega
    · show Nat.toUInt64 M ≤ largeRange.max
      rw [UInt64.le_iff_toNat_le, largeRange_max_val, hM_toNat]; omega
    · show minExponent ≤ g - (k : ℤ); omega
    · show g - (k : ℤ) ≤ maxExponent; omega
  · rw [Number.toRat_of_nonneg _ rfl]
    show ((Nat.toUInt64 M).toNat : ℚ) * (10 : ℚ) ^ (g - (k : ℤ)) = (K : ℚ) * 10 ^ g
    rw [hM_toNat, hM_def, zpow_sub₀ (by norm_num : (10 : ℚ) ≠ 0), zpow_natCast]
    push_cast
    field_simp

/-- A positive integer below `2^63` times `10^g` (as an integer) is representable. -/
private lemma exists_normalized_grid_int (K : ℤ) (g : ℤ) (h1 : 0 < K) (h2 : K < 2 ^ 63)
    (hlo : minExponent + 18 ≤ g) (hhi : g ≤ maxExponent) :
    ∃ w : Number, w.isNormalized ∧ w.toRat = (K : ℚ) * 10 ^ g := by
  obtain ⟨w, hw, hwv⟩ := exists_normalized_grid K.toNat g (by omega) (by omega) hlo hhi
  refine ⟨w, hw, ?_⟩
  rw [hwv]
  congr 1
  have : ((K.toNat : ℤ) : ℚ) = (K : ℚ) := by rw [Int.toNat_of_nonneg h1.le]
  exact_mod_cast this

/-- A difference on a grid is representable. `x - y` with `0 ≤ y ≤ x` and `y ∈ 10^s·ℤ` is the
value of a normalized `Number` when it fits `2^63` steps of `10^s` in case `s ≤ exponent x`. -/
lemma sub_representable_grid (x : Number) (yv : ℚ) (s j : ℤ) (hx : x.isNormalized)
    (hy0 : 0 ≤ yv) (hyx : yv ≤ x.toRat) (hj : yv = (j : ℚ) * 10 ^ s)
    (hs : minExponent + 37 ≤ s) (hs' : s ≤ maxExponent)
    (hnear : 0 < yv → s ≤ x.exponent_ → x.toRat - yv < 2 ^ 63 * 10 ^ s) :
    ∃ w : Number, w.isNormalized ∧ w.toRat = x.toRat - yv := by
  rcases eq_or_lt_of_le hy0 with hy00 | hypos
  · exact ⟨x, hx, by rw [← hy00, sub_zero]⟩
  rcases eq_or_lt_of_le (sub_nonneg.mpr hyx) with hD0 | hDpos
  · exact ⟨Number.zero, Or.inl rfl, by rw [Number.toRat_zero, ← hD0]⟩
  have hxpos : 0 < x.toRat := lt_of_lt_of_le hypos hyx
  have hxm : x.mantissa_ ≠ 0 := fun h => by
    rw [Number.toRat_eq_zero_of_mantissa_zero x h] at hxpos; exact lt_irrefl _ hxpos
  have hxv := Number.toRat_of_nonneg x (Number.negative_false_of_nonneg x hx hxpos.le)
  obtain ⟨hmlo, hmhi⟩ := hx.mantissaBounds_nat hxm
  obtain ⟨hsticky, hxe_lo, hxe_hi⟩ : (x.mantissa_ ≤ maxRep ∨ x.mantissa_.toNat % 10 = 0) ∧
      minExponent ≤ x.exponent_ ∧ x.exponent_ ≤ maxExponent := by
    rcases hx with h0 | ⟨_, _, h3, h4, h5⟩
    · exact absurd (by rw [h0]; rfl) hxm
    · exact ⟨h3, h4, h5⟩
  have hs0 : (0 : ℚ) < 10 ^ s := zpow_pos (by norm_num) _
  have hj1 : 0 < j := by
    have : (0 : ℚ) < (j : ℚ) := by
      rw [hj] at hypos; exact pos_of_mul_pos_left hypos hs0.le
    exact_mod_cast this
  set m := x.mantissa_.toNat with hm_def
  set e := x.exponent_ with he_def
  by_cases hse : s ≤ e
  · obtain ⟨d, hd⟩ : ∃ d : ℕ, e = s + d := ⟨(e - s).toNat, by omega⟩
    have hD : x.toRat - yv = (((m : ℤ) * 10 ^ d - j : ℤ) : ℚ) * 10 ^ s := by
      rw [hxv, hj, hd, zpow_add₀ (by norm_num : (10 : ℚ) ≠ 0), zpow_natCast]
      push_cast; ring
    have hKpos : (0 : ℤ) < (m : ℤ) * 10 ^ d - j := by
      have : (0 : ℚ) < (((m : ℤ) * 10 ^ d - j : ℤ) : ℚ) := by
        rw [hD] at hDpos; exact pos_of_mul_pos_left hDpos hs0.le
      exact_mod_cast this
    have hKlt : (m : ℤ) * 10 ^ d - j < 2 ^ 63 := by
      have h := hnear hypos hse
      rw [hD] at h
      have : (((m : ℤ) * 10 ^ d - j : ℤ) : ℚ) < 2 ^ 63 := lt_of_mul_lt_mul_right h hs0.le
      exact_mod_cast this
    obtain ⟨w, hw, hwv⟩ := exists_normalized_grid_int _ s hKpos hKlt (by omega) hs'
    exact ⟨w, hw, by rw [hwv, hD]⟩
  · rw [not_le] at hse
    obtain ⟨d, hd⟩ : ∃ d : ℕ, s = e + 1 + d := ⟨(s - e - 1).toNat, by omega⟩
    have he0 : (0 : ℚ) < 10 ^ e := zpow_pos (by norm_num) _
    -- the grid step of `y` is far above the bottom of `x`'s window
    have hse19 : s < e + 19 := by
      by_contra hc
      rw [not_lt] at hc
      have h1 : (10 : ℚ) ^ s ≤ yv := by
        rw [hj]
        have : (1 : ℚ) ≤ (j : ℚ) := by exact_mod_cast hj1
        nlinarith
      have h2 : x.toRat < (10 : ℚ) ^ (e + 19) := by
        rw [hxv, zpow_add₀ (by norm_num : (10 : ℚ) ≠ 0), mul_comm ((10 : ℚ) ^ e)]
        exact mul_lt_mul_of_pos_right (by exact_mod_cast hmhi) he0
      have h3 : (10 : ℚ) ^ (e + 19) ≤ 10 ^ s := zpow_le_zpow_right₀ (by norm_num) hc
      linarith
    have hD : x.toRat - yv = (((m : ℤ) - 10 * (j * 10 ^ d) : ℤ) : ℚ) * 10 ^ e := by
      rw [hxv, hj, hd, zpow_add₀ (by norm_num : (10 : ℚ) ≠ 0),
        zpow_add₀ (by norm_num : (10 : ℚ) ≠ 0), zpow_natCast]
      push_cast; ring
    have hKpos : (0 : ℤ) < (m : ℤ) - 10 * (j * 10 ^ d) := by
      have : (0 : ℚ) < (((m : ℤ) - 10 * (j * 10 ^ d) : ℤ) : ℚ) := by
        rw [hD] at hDpos; exact pos_of_mul_pos_left hDpos he0.le
      exact_mod_cast this
    have hJ0 : 0 ≤ j * 10 ^ d := by positivity
    rcases hsticky with hle | hmod
    · have hmle : m ≤ 9223372036854775807 := by
        rw [hm_def]; rw [UInt64.le_iff_toNat_le, maxRep_val] at hle; exact hle
      obtain ⟨w, hw, hwv⟩ := exists_normalized_grid_int _ e hKpos (by omega) (by omega) hxe_hi
      exact ⟨w, hw, by rw [hwv, hD]⟩
    · obtain ⟨m', hm'⟩ : ∃ m' : ℕ, m = 10 * m' := ⟨m / 10, by omega⟩
      have hD' : x.toRat - yv = (((m' : ℤ) - j * 10 ^ d : ℤ) : ℚ) * 10 ^ (e + 1) := by
        rw [hD, hm', zpow_add₀ (by norm_num : (10 : ℚ) ≠ 0)]
        push_cast; ring
      have hK'pos : (0 : ℤ) < (m' : ℤ) - j * 10 ^ d := by omega
      obtain ⟨w, hw, hwv⟩ := exists_normalized_grid_int _ (e + 1) hK'pos (by omega) (by omega)
        (by omega)
      exact ⟨w, hw, by rw [hwv, hD']⟩

end XRPL.Model.SingleAssetVault.Exact
