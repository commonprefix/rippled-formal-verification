import XRPL.Properties.Vault.Proofs.DepositTight.Clamp

/-! # A `.to_nearest` fractional pack below half a step past a grid point stays at or below it -/

namespace XRPL.Model.SingleAssetVault.RtT

open XRPL.Model.Protocol

lemma pack_setup (n : Number) (r : STAmount) (hn : n.isNormalized) (hnn : 0 ≤ n.toRat)
    (hok : STAmount.ofNumber .fractional n .to_nearest = .ok r) (hr : r.mValue ≠ 0) :
    r.IOUCanonical ∧ r.mIsNegative = false ∧ r.toRat - n.toRat ≤ 1 / 2 * 10 ^ r.exponent ∧
      ∀ j : ℤ, -100 ≤ j → j + 4 ≤ r.exponent → WdMono.carryPt j ≤ n.toRat := by
  have hnz : n.mantissa_ ≠ 0 := STAmount.ofNumber_source_ne_zero _ n .to_nearest r hok hr
  have hneg := Number.negative_false_of_normalized_nonneg n hn hnn
  obtain ⟨hrc, hrn, hh, -, -⟩ := WdMono.frac_pack n r hn hneg hnz hok hr
  exact ⟨hrc, hrn, (abs_le.mp hh).2, fun j hj hk => (WdMono.exp_ge_iff n r hn hnn hok j hj).mp hk⟩

lemma mant_val (s : STAmount) (hn : s.mIsNegative = false) :
    s.toRat = (s.mValue.toNat : ℚ) * 10 ^ s.exponent := STAmount.toRat_of_nonneg s hn

lemma carry_val (k : ℤ) (d : ℕ) :
    WdMono.carryPt (k - d) = 9999999999999999500 / 10 ^ d * (10 : ℚ) ^ k := by
  unfold WdMono.carryPt
  rw [zpow_sub₀ (by norm_num), zpow_natCast]; ring

/-- Below `G + ½·10^k` (`k` the exponent of the canonical `G`) the pack is at most `G`. -/
lemma pack_le (n : Number) (G r : STAmount) (hn : n.isNormalized) (hnn : 0 ≤ n.toRat)
    (hG : G.IOUCanonical) (hGn : G.mIsNegative = false)
    (hlt : n.toRat < G.toRat + 1 / 2 * 10 ^ G.exponent)
    (hok : STAmount.ofNumber .fractional n .to_nearest = .ok r) : r.toRat ≤ G.toRat := by
  by_contra hgt
  replace hgt := not_le.mp hgt
  have hG0 : 0 ≤ G.toRat := by rw [mant_val G hGn]; positivity
  have hr : r.mValue ≠ 0 := fun h => by
    rw [STAmount.toRat_eq_zero_of_mValue_zero r h] at hgt; linarith
  obtain ⟨hrc, hrn, hh, hcar⟩ := pack_setup n r hn hnn hok hr
  obtain ⟨hGlo, -⟩ := DepTight.canon_band G hG hGn
  obtain ⟨-, hrhi⟩ := DepTight.canon_band r hrc hrn
  have hk : (-96 : ℤ) ≤ G.exponent := hG.exp_lo
  have hGm : (G.mValue.toNat : ℚ) + 1 ≤ 10 ^ 16 := by
    have := hG.mant_hi; exact_mod_cast (show G.mValue.toNat + 1 ≤ 10 ^ 16 by omega)
  have hGv := mant_val G hGn
  have hp : (0 : ℚ) < 10 ^ G.exponent := zpow_pos (by norm_num) _
  rcases lt_trichotomy r.exponent G.exponent with hlt' | heq | hgt'
  · have : (10 : ℚ) ^ (r.exponent + 16) ≤ 10 ^ (G.exponent + 15) :=
      zpow_le_zpow_right₀ (by norm_num) (by omega)
    linarith
  · have hrv := mant_val r hrn
    rw [heq] at hrv hh
    rw [hrv, hGv] at hgt
    have hm : (G.mValue.toNat : ℚ) < r.mValue.toNat := lt_of_mul_lt_mul_right hgt hp.le
    have hm' : (G.mValue.toNat : ℚ) + 1 ≤ r.mValue.toNat := by
      have : G.mValue.toNat < r.mValue.toNat := by exact_mod_cast hm
      exact_mod_cast (show G.mValue.toNat + 1 ≤ r.mValue.toNat by omega)
    have : ((G.mValue.toNat : ℚ) + 1) * 10 ^ G.exponent ≤ r.mValue.toNat * 10 ^ G.exponent :=
      mul_le_mul_of_nonneg_right hm' hp.le
    rw [hGv] at hlt
    rw [hrv] at hh
    nlinarith
  · have := hcar (G.exponent - 3) (by omega) (by omega)
    rw [show G.exponent - 3 = G.exponent - ((3 : ℕ) : ℤ) by norm_num, carry_val] at this
    rw [hGv] at hlt
    nlinarith

/-- Below `P + 3/2·10^k` the pack is at most `P + 10^k`. -/
lemma pack_le_succ (n : Number) (P r : STAmount) (hn : n.isNormalized) (hnn : 0 ≤ n.toRat)
    (hP : P.IOUCanonical) (hPn : P.mIsNegative = false)
    (hlt : n.toRat < P.toRat + 3 / 2 * 10 ^ P.exponent)
    (hok : STAmount.ofNumber .fractional n .to_nearest = .ok r) :
    r.toRat ≤ P.toRat + 10 ^ P.exponent := by
  by_contra hgt
  replace hgt := not_le.mp hgt
  have hP0 : 0 ≤ P.toRat := by rw [mant_val P hPn]; positivity
  have hp : (0 : ℚ) < 10 ^ P.exponent := zpow_pos (by norm_num) _
  have hr : r.mValue ≠ 0 := fun h => by
    rw [STAmount.toRat_eq_zero_of_mValue_zero r h] at hgt; linarith
  obtain ⟨hrc, hrn, hh, hcar⟩ := pack_setup n r hn hnn hok hr
  obtain ⟨hPlo, -⟩ := DepTight.canon_band P hP hPn
  obtain ⟨hrlo, hrhi⟩ := DepTight.canon_band r hrc hrn
  have hk : (-96 : ℤ) ≤ P.exponent := hP.exp_lo
  have hPv := mant_val P hPn
  have hrv := mant_val r hrn
  have hPm : (P.mValue.toNat : ℚ) + 1 ≤ 10 ^ 16 := by
    have := hP.mant_hi; exact_mod_cast (show P.mValue.toNat + 1 ≤ 10 ^ 16 by omega)
  rcases lt_trichotomy r.exponent P.exponent with hlt' | heq | hgt'
  · have : (10 : ℚ) ^ (r.exponent + 16) ≤ 10 ^ (P.exponent + 15) :=
      zpow_le_zpow_right₀ (by norm_num) (by omega)
    linarith
  · rw [heq] at hrv hh
    rw [hrv, hPv] at hgt
    have hm : ((P.mValue.toNat : ℚ) + 1) * 10 ^ P.exponent < r.mValue.toNat * 10 ^ P.exponent := by
      linarith
    have hm1 : (P.mValue.toNat : ℚ) + 1 < r.mValue.toNat := lt_of_mul_lt_mul_right hm hp.le
    have hm' : (P.mValue.toNat : ℚ) + 2 ≤ r.mValue.toNat := by
      have : P.mValue.toNat + 1 < r.mValue.toNat := by exact_mod_cast hm1
      exact_mod_cast (show P.mValue.toNat + 2 ≤ r.mValue.toNat by omega)
    have : ((P.mValue.toNat : ℚ) + 2) * 10 ^ P.exponent ≤ r.mValue.toNat * 10 ^ P.exponent :=
      mul_le_mul_of_nonneg_right hm' hp.le
    rw [hPv] at hlt
    rw [hrv] at hh
    nlinarith
  · by_cases h2 : P.exponent + 2 ≤ r.exponent
    · have := hcar (P.exponent - 2) (by omega) (by omega)
      rw [show P.exponent - 2 = P.exponent - ((2 : ℕ) : ℤ) by norm_num, carry_val] at this
      rw [hPv] at hlt
      nlinarith
    · have h1 : r.exponent = P.exponent + 1 := by omega
      have hc := hcar (P.exponent - 3) (by omega) (by omega)
      rw [show P.exponent - 3 = P.exponent - ((3 : ℕ) : ℤ) by norm_num, carry_val] at hc
      have h10 : (10 : ℚ) ^ r.exponent = 10 * 10 ^ P.exponent := by
        rw [h1, zpow_add_one₀ (by norm_num)]; ring
      rw [h10] at hrv hh
      have hmlo : (10 : ℚ) ^ 15 ≤ r.mValue.toNat := by exact_mod_cast hrc.mant_lo
      rw [hPv] at hlt hgt
      by_cases hm : r.mValue.toNat = 10 ^ 15
      · have hrr : r.toRat = 10 ^ 16 * 10 ^ P.exponent := by
          rw [hrv, hm]; push_cast; ring
        rw [hrr] at hgt
        have hlt2 : (P.mValue.toNat : ℚ) + 1 < 10 ^ 16 := by
          have : ((P.mValue.toNat : ℚ) + 1) * 10 ^ P.exponent < 10 ^ 16 * 10 ^ P.exponent := by
            linarith
          exact lt_of_mul_lt_mul_right this hp.le
        have hle2 : (P.mValue.toNat : ℚ) + 2 ≤ 10 ^ 16 := by
          have : P.mValue.toNat + 1 < 10 ^ 16 := by exact_mod_cast hlt2
          exact_mod_cast (show P.mValue.toNat + 2 ≤ 10 ^ 16 by omega)
        nlinarith
      · have hm1 : (10 : ℚ) ^ 15 + 1 ≤ r.mValue.toNat := by
          have := hrc.mant_lo
          exact_mod_cast (show 10 ^ 15 + 1 ≤ r.mValue.toNat by omega)
        nlinarith

end XRPL.Model.SingleAssetVault.RtT
