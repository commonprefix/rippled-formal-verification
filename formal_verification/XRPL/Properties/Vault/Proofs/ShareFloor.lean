import XRPL.Properties.Vault.Proofs.DepositAccuracy

/-! # Whole share counts at the floor of the ideal

A share count priced with 19-digit `Number`s lands within `sharesε` relatively of the exact ideal. When the ideal
keeps more than that distance from every whole number, a truncated count is exactly the ideal rounded down. -/

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol

/-- A whole count at most `sharesε` relatively above the ideal is at most the ideal, when the ideal keeps more than
that distance from every whole number. -/
lemma shares_le_ideal_of_gap (I k e : ℚ) (hk : k.den = 1) (hk0 : 0 ≤ k) (he0 : 0 ≤ e) (he : e ≤ sharesε)
    (hup : k ≤ I * (1 + e)) (hgap : ∀ n : ℤ, I * sharesε < |I - n|) : k ≤ I := by
  have hI : 0 ≤ I := by
    by_contra h
    push Not at h
    nlinarith
  have hn := hgap (⌊I⌋ + 1)
  have hfl := Int.lt_floor_add_one I
  have hle := Int.floor_le I
  push_cast at hn
  rw [abs_of_neg (by linarith)] at hn
  have hIe : I * e ≤ I * sharesε := mul_le_mul_of_nonneg_left he hI
  have hlt : k < (⌊I⌋ : ℚ) + 1 := by nlinarith
  have hkn : k = (k.num : ℚ) := (Rat.coe_int_num_of_den_eq_one hk).symm
  rw [hkn] at hlt ⊢
  have hle' : k.num ≤ ⌊I⌋ := by
    have : k.num < ⌊I⌋ + 1 := by exact_mod_cast hlt
    omega
  calc (k.num : ℚ) ≤ ⌊I⌋ := by exact_mod_cast hle'
    _ ≤ I := hle

/-- A whole count less than one plus `sharesε` relatively below a nonnegative ideal is above the ideal less one,
when the ideal keeps more than that distance from every whole number. -/
lemma ideal_sub_one_lt_of_gap (I k e : ℚ) (hk : k.den = 1) (hI : 0 ≤ I) (he : e ≤ sharesε)
    (hlo : I * (1 - e) - 1 < k) (hgap : ∀ n : ℤ, I * sharesε < |I - n|) : I - 1 < k := by
  have hn := hgap ⌊I⌋
  have hle := Int.floor_le I
  have hfl := Int.lt_floor_add_one I
  rw [abs_of_nonneg (by linarith)] at hn
  have hIe : I * e ≤ I * sharesε := mul_le_mul_of_nonneg_left he hI
  have hgt : (⌊I⌋ : ℚ) - 1 < k := by nlinarith
  have hkn : k = (k.num : ℚ) := (Rat.coe_int_num_of_den_eq_one hk).symm
  rw [hkn] at hgt ⊢
  have hge : ⌊I⌋ ≤ k.num := by
    have : ⌊I⌋ - 1 < k.num := by exact_mod_cast hgt
    omega
  have : (⌊I⌋ : ℚ) ≤ k.num := by exact_mod_cast hge
  linarith

/-- Both sides of `shares_le_ideal_of_gap` and `ideal_sub_one_lt_of_gap` from bounds in the deposit form. -/
lemma shares_floor_of_gap (I k eLo eUp : ℚ) (hLo : eLo ≤ sharesε) (hUp0 : 0 ≤ eUp) (hUp : eUp ≤ sharesε)
    (h : k.den = 1 ∧ 0 ≤ k ∧ I * (1 - eLo) - 1 < k ∧ k ≤ I * (1 + eUp))
    (hgap : ∀ n : ℤ, I * sharesε < |I - n|) :
    k.den = 1 ∧ 0 ≤ k ∧ I - 1 < k ∧ k ≤ I :=
  have hle := shares_le_ideal_of_gap I k eUp h.1 h.2.1 hUp0 hUp h.2.2.2 hgap
  ⟨h.1, h.2.1, ideal_sub_one_lt_of_gap I k eLo h.1 (le_trans h.2.1 hle) hLo h.2.2.1 hgap, hle⟩

/-- A whole count at most the ideal and less than one below it is the ideal rounded down. -/
lemma shares_eq_floor (I k : ℚ) (hk : k.den = 1) (hlo : I - 1 < k) (hup : k ≤ I) : k = ⌊I⌋ := by
  have hkn : k = (k.num : ℚ) := (Rat.coe_int_num_of_den_eq_one hk).symm
  rw [hkn] at hlo hup ⊢
  have h1 : k.num ≤ ⌊I⌋ := Int.le_floor.mpr hup
  have h2 : ⌊I⌋ < k.num + 1 := by
    rw [Int.floor_lt]
    push_cast
    linarith
  have : k.num = ⌊I⌋ := by omega
  rw [this]

lemma sharesOverε_nonneg : 0 ≤ sharesOverε := by unfold sharesOverε; norm_num

lemma sharesOverε_le : sharesOverε ≤ sharesε := by unfold sharesOverε sharesε; norm_num

lemma sharesShortε_le : sharesShortε ≤ sharesε := by unfold sharesShortε sharesε; norm_num

lemma sharesε_nonneg : 0 ≤ sharesε := by unfold sharesε; norm_num

end XRPL.Model.SingleAssetVault
