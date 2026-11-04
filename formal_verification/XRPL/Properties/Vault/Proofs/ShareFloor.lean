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

lemma sharesOverε_nonneg : 0 ≤ sharesOverε := by unfold sharesOverε; norm_num

lemma sharesOverε_le : sharesOverε ≤ sharesε := by unfold sharesOverε sharesε; norm_num

lemma sharesShortε_le : sharesShortε ≤ sharesε := by unfold sharesShortε sharesε; norm_num

lemma sharesε_nonneg : 0 ≤ sharesε := by unfold sharesε; norm_num

/-- The ideal share amount of a nonnegative deposit is nonnegative. -/
lemma Vault.idealSharesDeposit_nonneg (v : Vault) (a : ℚ) (ha : 0 ≤ a) : 0 ≤ v.idealSharesDeposit a := by
  have h1 := v.exact.assetsAvailable_nonneg
  have h2 := v.exact.assetsDeployed_nonneg
  unfold RawVault.idealSharesDeposit RawVault.depositNav RawVault.Exact.assetsTotal
  split_ifs
  · positivity
  · exact div_nonneg (mul_nonneg (Nat.cast_nonneg _) ha) (by linarith)

/-- A successful deposit rounds the requested amount to a positive amount. -/
lemma Vault.deposit_rounded_pos (v : Vault) (amountDeposit roundedAmount : STAmount) (t : UInt32)
    (hpos : 0 < amountDeposit.toRat) (hcanon : amountDeposit.Canonical)
    (hrounded : (v.roundedDepositAmount amountDeposit).run = .ok (.ok roundedAmount))
    (r : VaultWithAmounts) (hok : (v.deposit amountDeposit false t hpos).run = .ok (.ok r)) :
    0 < roundedAmount.toRat := by
  obtain ⟨ra, -, -, hra, -, hrp, -⟩ := DepAcc.Vault.deposit_success_reduces v amountDeposit t hpos hcanon r hok
  rw [hrounded] at hra
  obtain rfl := Except.ok.inj (Except.ok.inj hra)
  exact hrp

end XRPL.Model.SingleAssetVault
