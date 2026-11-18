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

end XRPL.Model.SingleAssetVault.Exact
