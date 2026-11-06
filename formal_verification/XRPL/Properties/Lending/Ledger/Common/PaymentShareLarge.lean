import XRPL.Properties.Lending.Ledger.Common.PaymentShareBound
import XRPL.Properties.Lending.Ledger.Common.DefaultCredit
import XRPL.Properties.Lending.Loan.Common.PaymentRoom
import XRPL.Properties.Lending.Loan.Common.ValueDecrease

/-! # A credit above `10^16` base units

An IOU credit above `10^16` base units leaves AssetsAvailable' less than `3·10^3` base units below AssetsAvailable plus
the credit, while that sum stays below `2^63` base units. -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault (Vault RawVault)

open private add_downward_ge_any Number.pow_le_of_normalized STAmount.ofNumber_frac_downward_ge
  from XRPL.Properties.Lending.Ledger.Common.AssetsTotalSteps
open private roundDown_shape pow_add_nat from XRPL.Properties.Lending.Ledger.Common.DefaultCredit
open private sub_exact from XRPL.Properties.Lending.Common.SumRounding
open private Loan.unimpairIfImpaired_balances from XRPL.Properties.Lending.Ledger.Common.AssetsTotalSteps
open private Loan.unimpairIfImpaired Loan.settlePayment from XRPL.Model.Lending.Loan.LoanPay

/-- An IOU amount above `10^16` base units leaves AssetsAvailable' less than `3·10^3` base units below AssetsAvailable
plus the amount, while that sum stays below `2^63` base units. -/
private lemma sumRoundAndSubtract_credit_large (A c : Number) (b : Int) (st : STAmount) (cr aa a' : Number)
    (hA : A.isNormalized) (hA0 : 0 ≤ A.toRat) (hAg : ∃ k : ℕ, A.toRat = k * 10 ^ b)
    (hc : c.isNormalized) (hcg : ∃ k : ℕ, c.toRat = k * 10 ^ b) (hcbig : 10 ^ 16 * 10 ^ b < c.toRat)
    (hb : -10 ≤ b ∧ b ≤ 0) (hfit : A.toRat + c.toRat < 2 ^ 63 * 10 ^ b)
    (h : sumRoundAndSubtract A c b .fractional .downward = .ok st) (hcr : st.toNumber .to_nearest = .ok cr)
    (haa : A.operator_add cr .to_nearest = .ok aa)
    (ha' : STAmount.roundToNumericType .fractional aa .to_nearest = .ok a') :
    A.toRat + c.toRat - a'.toRat < 3 * 10 ^ (b + 3) := by
  have hp : (0 : ℚ) < 10 ^ b := zpow_pos (by norm_num) _
  have hp3 : (0 : ℚ) < 10 ^ (b + 3) := zpow_pos (by norm_num) _
  have h3 : (10 : ℚ) ^ (b + 3) = 1000 * 10 ^ b := by
    rw [zpow_add₀ (by norm_num : (10 : ℚ) ≠ 0)]; norm_num; ring
  have hc0 : 0 ≤ c.toRat := by linarith
  obtain ⟨hstc, hcrx⟩ := sumRoundAndSubtract_downward_le A c b .fractional st hA hA0 hc hc0 ⟨by omega, by omega⟩ h
  obtain ⟨hcrv, hcrn⟩ := hcrx cr hcr
  unfold sumRoundAndSubtract at h
  rw [if_neg (by decide)] at h
  obtain ⟨_, -, h⟩ := bind_ok_peel _ _ _ h
  obtain ⟨E, hE, h⟩ := bind_ok_peel _ _ _ h
  obtain ⟨sum, hsum, h⟩ := bind_ok_peel _ _ _ h
  obtain ⟨sum', hsum', h⟩ := bind_ok_peel _ _ _ h
  obtain ⟨d, hd, hst⟩ := bind_ok_peel _ _ _ h
  have hErange := postSumExponent_range _ _ _ _ _ (by omega) (by omega) hE

  -- AssetsAvailable plus the amount is a `Number`, so the downward sum is exact
  obtain ⟨kA, hkA⟩ := hAg
  obtain ⟨kc, hkc⟩ := hcg
  have hK : ((kA + kc : ℕ) : ℤ) < 2 ^ 63 := by
    have : ((kA + kc : ℕ) : ℚ) * 10 ^ b < (2 ^ 63 : ℚ) * 10 ^ b := by
      push_cast; rw [add_mul, ← hkA, ← hkc]; exact hfit
    exact_mod_cast lt_of_mul_lt_mul_right this hp.le
  obtain ⟨w, hw, hwv⟩ := Number.exists_normalized_int_mul_pow ((kA + kc : ℕ) : ℤ) b ⟨by omega, hK⟩
    ⟨by unfold minExponent; omega, by unfold maxExponent; omega⟩
  have hwv' : w.toRat = A.toRat + c.toRat := by rw [hwv, hkA, hkc]; push_cast; ring
  have hsumn := Number.operator_add_isNormalized_any _ _ _ _ hA hc hsum
  obtain ⟨hsle, hs0⟩ := Number.operator_add_downward_nonneg_le A c sum hA hc hA0 hc0 hsum
  have hsumv : sum.toRat = A.toRat + c.toRat :=
    le_antisymm hsle (by rw [← hwv']; exact add_downward_ge_any A c sum w hA hc hsum hw (by linarith) hwv'.le)

  have hE3 : E ≤ b + 3 := by
    obtain ⟨sN, hsN, hsNE⟩ := postSumExponent_reduces _ _ _ _ _ hE
    have hsNv := Number.operator_add_exact_of_fits hA hc hsN ⟨w, hw, hwv'⟩
    by_contra hgt
    push Not at hgt
    have hsNn := operator_add_isNormalized_to_nearest_sz _ _ _ hA hc hsN
    obtain ⟨-, hge⟩ := numberExponent_frac_lower sN b E hsNn (by rw [hsNv]; linarith) (by omega) hsNE (by omega)
    have h1 : (10 : ℚ) ^ (b + 19) ≤ 10 ^ (E + 15) := zpow_le_zpow_right₀ (by norm_num) (by omega)
    have h2 : (10 : ℚ) ^ (b + 19) = 10 ^ 19 * 10 ^ b := by
      rw [zpow_add₀ (by norm_num : (10 : ℚ) ≠ 0)]; norm_num; ring
    rw [hsNv] at hge
    linarith
  obtain ⟨G, j, hEG, hG80, -, hj, hsum'v, hs'le, hsfl, hGj⟩ :=
    roundDown_shape sum sum' E hsumn hs0 ⟨by omega, hErange.2.2⟩ hsum'
  have hG3 : G ≤ b + 3 := by
    rcases hGj with hGE | hj15
    · omega
    · by_contra hgt
      push Not at hgt
      have h1 : (10 : ℚ) ^ (b + 4) ≤ 10 ^ G := zpow_le_zpow_right₀ (by norm_num) (by omega)
      have h2 : (10 : ℚ) ^ (b + 4) = 10 ^ 4 * 10 ^ b := by
        rw [zpow_add₀ (by norm_num : (10 : ℚ) ≠ 0)]; norm_num; ring
      have hj' : (10 : ℚ) ^ 15 ≤ j := by exact_mod_cast hj15
      have : (10 : ℚ) ^ 15 * 10 ^ G ≤ sum'.toRat := by
        rw [hsum'v]; exact mul_le_mul_of_nonneg_right hj' (zpow_pos (by norm_num) _).le
      linarith
  have hpG : (10 : ℚ) ^ G ≤ 10 ^ (b + 3) := zpow_le_zpow_right₀ (by norm_num) hG3
  have hsum'n := STAmount.roundToNumericType_isNormalized _ _ _ _ _ hsum'
  have hs'0 : 0 ≤ sum'.toRat := by rw [hsum'v]; positivity

  -- the floored sum less AssetsAvailable is a `Number`, so the downward difference is exact
  have hsplit : (10 : ℚ) ^ G = ((10 ^ (G - b).toNat : ℕ) : ℚ) * 10 ^ b := by
    rw [← pow_add_nat]; congr 1; omega
  set K : ℤ := ((j * 10 ^ (G - b).toNat : ℕ) : ℤ) - kA with hKdef
  have hKv : sum'.toRat - A.toRat = (K : ℚ) * 10 ^ b := by
    rw [hsum'v, hkA, hsplit, hKdef]; push_cast; ring
  have hKlo : -2 ^ 63 < K := by
    have : ((kA : ℤ) : ℚ) * 10 ^ b < (2 ^ 63 : ℚ) * 10 ^ b := by push_cast; rw [← hkA]; linarith
    have := lt_of_mul_lt_mul_right this hp.le
    have : (kA : ℤ) < 2 ^ 63 := by exact_mod_cast this
    rw [hKdef]; omega
  have hKhi : K < 2 ^ 63 := by
    have : (K : ℚ) * 10 ^ b < (2 ^ 63 : ℚ) * 10 ^ b := by rw [← hKv]; linarith
    exact_mod_cast lt_of_mul_lt_mul_right this hp.le
  obtain ⟨w2, hw2, hw2v⟩ := Number.exists_normalized_int_mul_pow K b ⟨hKlo, hKhi⟩
    ⟨by unfold minExponent; omega, by unfold maxExponent; omega⟩
  have hdv : d.toRat = sum'.toRat - A.toRat := sub_exact sum' A d w2 _ hsum'n hA hs'0 hA0 hd hw2 (by rw [hw2v, hKv])
  have hdn := Number.operator_sub_isNormalized_any _ _ _ _ hsum'n hA hd
  have hd15 : 1000 * 10 ^ b ≤ d.toRat := by rw [hdv]; linarith

  -- the 16-digit floor of the difference keeps it to within `10^(b+3)`
  have hdm : d.mantissa_ ≠ 0 := fun h0 => by
    rw [Number.toRat_eq_zero_of_mantissa_zero d h0] at hd15; linarith
  have hdexp : d.exponent_ ≤ b := by
    have hlow := Number.pow_le_of_normalized d hdn hdm (by linarith)
    by_contra hgt
    push Not at hgt
    have h1 : (10 : ℚ) ^ (b + 1) ≤ 10 ^ d.exponent_ := zpow_le_zpow_right₀ (by norm_num) (by omega)
    have h2 : (10 : ℚ) ^ (b + 1) = 10 * 10 ^ b := by
      rw [zpow_add₀ (by norm_num : (10 : ℚ) ≠ 0)]; norm_num; ring
    have : d.toRat < 2 ^ 63 * 10 ^ b := by rw [hdv]; linarith
    norm_num at hlow
    linarith
  set q : ℤ := ⌊d.toRat / 10 ^ (b + 3)⌋ with hq
  have hq1 : (1 : ℤ) ≤ q := by
    rw [hq]; apply Int.le_floor.mpr; push_cast; rw [le_div_iff₀ hp3]; linarith
  have hqle : (q : ℚ) * 10 ^ (b + 3) ≤ d.toRat := by
    have := Int.floor_le (d.toRat / 10 ^ (b + 3)); rw [← hq] at this
    rwa [le_div_iff₀ hp3] at this
  have hqgt : d.toRat < (q : ℚ) * 10 ^ (b + 3) + 10 ^ (b + 3) := by
    have := Int.lt_floor_add_one (d.toRat / 10 ^ (b + 3)); rw [← hq] at this
    rw [div_lt_iff₀ hp3] at this; linarith
  have hstg : (q : ℚ) * 10 ^ (b + 3) ≤ st.toRat := by
    refine STAmount.ofNumber_frac_downward_ge d st _ hdn ?_ hqle ?_ hst
    · have : (10 : ℚ) ^ (-81 : ℤ) ≤ 10 ^ (b + 3) := zpow_le_zpow_right₀ (by norm_num) (by omega)
      have hq1' : (1 : ℚ) ≤ q := by exact_mod_cast hq1
      have := mul_le_mul_of_nonneg_right hq1' hp3.le
      linarith
    · intro s hs
      left
      refine ⟨q * 10 ^ (b - d.exponent_).toNat, ?_⟩
      rw [hs, show (10 : ℚ) ^ (b + 3) = ((10 ^ (b - d.exponent_).toNat : ℕ) : ℚ) * 10 ^ (d.exponent_ + 3) by
        rw [← pow_add_nat]; congr 1; omega]
      push_cast; ring

  have hqA : ((kA : ℤ) + q * 1000 : ℤ) < 2 ^ 63 := by
    have : (((kA : ℤ) + q * 1000 : ℤ) : ℚ) * 10 ^ b < (2 ^ 63 : ℚ) * 10 ^ b := by
      push_cast; rw [add_mul, ← hkA, mul_assoc, ← h3]; rw [hdv] at hqle; linarith
    exact_mod_cast lt_of_mul_lt_mul_right this hp.le
  obtain ⟨w3, hw3, hw3v⟩ := Number.exists_normalized_int_mul_pow ((kA : ℤ) + q * 1000) b ⟨by omega, hqA⟩
    ⟨by unfold minExponent; omega, by unfold maxExponent; omega⟩
  have hw3v' : w3.toRat = A.toRat + (q : ℚ) * 10 ^ (b + 3) := by rw [hw3v, hkA, h3]; push_cast; ring
  have hR := operator_add_rounded_to_nearest A cr aa hA hcrn haa
  have haa_ge : A.toRat + (q : ℚ) * 10 ^ (b + 3) ≤ aa.toRat := by
    rw [← hw3v']; exact Number.roundsToRepresentable_ge aa _ hR w3 hw3 (by rw [hw3v', hcrv]; linarith)
  -- the 16-digit rounding of AssetsAvailable' moves it by at most half of `10^(b+3)`
  have haan := operator_add_isNormalized_to_nearest_sz _ _ _ hA hcrn haa
  have haa_le : aa.toRat ≤ w.toRat :=
    Number.roundsToRepresentable_le aa _ hR w hw (by rw [hwv', hcrv]; linarith)
  have haa_pos : 10 ^ (b + 3) ≤ aa.toRat := by
    have hq1' : (1 : ℚ) ≤ q := by exact_mod_cast hq1
    have := mul_le_mul_of_nonneg_right hq1' hp3.le
    linarith
  have haam : aa.mantissa_ ≠ 0 := fun h0 => by
    rw [Number.toRat_eq_zero_of_mantissa_zero aa h0] at haa_pos; linarith
  obtain ⟨hmlo, hmhi⟩ := haan.mantissaBounds_nat haam
  have haaexp : aa.exponent_ ≤ b := by
    have hlow := Number.pow_le_of_normalized aa haan haam (by linarith)
    by_contra hgt
    push Not at hgt
    have h1 : (10 : ℚ) ^ (b + 1) ≤ 10 ^ aa.exponent_ := zpow_le_zpow_right₀ (by norm_num) (by omega)
    have h2 : (10 : ℚ) ^ (b + 1) = 10 * 10 ^ b := by
      rw [zpow_add₀ (by norm_num : (10 : ℚ) ≠ 0)]; norm_num; ring
    norm_num at hlow
    linarith
  have haaexp' : b - 16 ≤ aa.exponent_ := by
    have hsv := Number.toRat_of_nonneg aa (Number.negative_false_of_nonneg aa haan (by linarith))
    have hm : (aa.mantissa_.toNat : ℚ) < 10 ^ (19 : ℤ) := by norm_num; exact_mod_cast hmhi
    have hpe : (0 : ℚ) < 10 ^ aa.exponent_ := zpow_pos (by norm_num) _
    have h1 : (10 : ℚ) ^ (b + 3) < 10 ^ (aa.exponent_ + 19) := by
      rw [zpow_add₀ (by norm_num : (10 : ℚ) ≠ 0) aa.exponent_]
      calc (10 : ℚ) ^ (b + 3) ≤ aa.toRat := haa_pos
        _ = aa.mantissa_.toNat * 10 ^ aa.exponent_ := hsv
        _ < 10 ^ (19 : ℤ) * 10 ^ aa.exponent_ := mul_lt_mul_of_pos_right hm hpe
        _ = 10 ^ aa.exponent_ * 10 ^ (19 : ℤ) := mul_comm _ _
    have := (zpow_lt_zpow_iff_right₀ (by norm_num : (1 : ℚ) < 10)).mp h1
    omega
  unfold STAmount.roundToNumericType at ha'
  cases hret : STAmount.ofNumber .fractional aa .to_nearest with
  | error e => rw [hret] at ha'; cases ha'
  | ok ret =>
  rw [hret] at ha'
  simp only at ha'
  have hrm := STAmount.ofNumber_iou_ne_zero_of_exponent aa _ ret haan haam (by omega) hret
  have hhalf := STAmount.ofNumber_iou_within_half_ulp .fractional aa ret rfl hmlo hmhi
    (Number.exponent_ge_min aa haan haam) (by unfold maxExponent; omega) hret hrm
  have ha'v : a'.toRat = ret.toRat :=
    STAmount.FracCanonZero.toNumber_val (STAmount.ofNumber_fractional_fczr aa _ ret hret) _ a' ha'
  have hpa : (10 : ℚ) ^ (aa.exponent_ + 3) ≤ 10 ^ (b + 3) := zpow_le_zpow_right₀ (by norm_num) (by omega)
  rw [ha'v]
  have := (abs_le.mp hhalf.1).1
  rw [hsumv] at hsfl
  linarith

end XRPL.Model.Lending
