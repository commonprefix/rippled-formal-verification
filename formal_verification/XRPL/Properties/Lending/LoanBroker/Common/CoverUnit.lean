import XRPL.Properties.Lending.LoanBroker.Common.CoverReduction
import XRPL.Properties.Protocol.STAmount.RoundToScale.Common.Grid
import XRPL.Properties.Protocol.STAmount.Common.FracCanonZero

/-! # One unit at the cover scale

The smallest amount the scale check accepts: one unit in the last place of CoverAvailable in the vault
asset, `10 ^ s.exponent` for `s` CoverAvailable converted to the asset. Taking it from CoverAvailable
is exact. The `_decrease_possible` theorems withdraw and claw back this unit. -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.Result

/-- A cover that converts to a nonzero amount of the vault asset is within half a unit of that
amount. -/
private lemma LoanBroker.cover_le_of_ofNumber (lb : LoanBroker) (s : STAmount)
    (hs : STAmount.ofNumber lb.numericType lb.coverAvailable .to_nearest = .ok s)
    (hnz : s.mValue ≠ 0) :
    s.ExactCanonical ∧ 0 < s.toRat ∧
      lb.coverAvailable.toRat ≤ s.toRat + (1 / 2 : ℚ) * (10 : ℚ) ^ s.exponent := by
  have hcn := lb.wf.coverAvailable_norm
  have hcov0 : 0 ≤ lb.coverAvailable.toRat := lb.exact.coverAvailable_nonneg
  have hc : s.ExactCanonical := STAmount.ofNumber_exactCanonical _ _ .to_nearest s hcn hcov0 hs hnz
  have hhalf := STAmount.ofNumber_to_nearest_within_half _ _ s hcn hcov0 hs hnz
  have hnn : 0 ≤ s.toRat :=
    STAmount.ofNumber_nonneg _ _ _ s hcn (Number.negative_false_of_nonneg _ hcn hcov0) hs
  have hpos : 0 < s.toRat := lt_of_le_of_ne hnn (Ne.symm (STAmount.toRat_ne_zero s hnz))
  refine ⟨hc, hpos, ?_⟩
  have := (abs_le.mp hhalf).1
  linarith

/-- A cover that converts to a nonzero amount of the vault asset is below `10^96`, like every
amount. -/
lemma LoanBroker.cover_lt_cap_of_ofNumber (lb : LoanBroker) (s : STAmount)
    (hs : STAmount.ofNumber lb.numericType lb.coverAvailable .to_nearest = .ok s)
    (hnz : s.mValue ≠ 0) : lb.toExact.coverAvailable < 10 ^ 96 := by
  obtain ⟨hc, hpos, hle⟩ := LoanBroker.cover_le_of_ofNumber lb s hs hnz
  have hp : (0 : ℚ) < (10 : ℚ) ^ s.exponent := zpow_pos (by norm_num) _
  show lb.coverAvailable.toRat < 10 ^ 96
  rcases hc with hiou | ⟨hint, hsz⟩
  · obtain ⟨_, hb⟩ := STAmount.IOUCanonical.toRat_bounds s hiou hpos
    have hexp : s.exponent = s.mOffset := rfl
    have he : (10 : ℚ) ^ (s.exponent + 16) ≤ (10 : ℚ) ^ (96 : ℤ) :=
      zpow_le_zpow_right₀ (by norm_num) (by rw [hexp]; have := hiou.exp_hi; omega)
    have h96 : (10 : ℚ) ^ (96 : ℤ) = 10 ^ 96 := by norm_num
    linarith
  · have hoff : s.exponent = 0 := hint.offset_zero
    rw [hoff, zpow_zero, mul_one] at hle
    have habs := STAmount.IntegralCanonical.abs_toRat_le_of_mValue_le s hint hsz
    have h2 : ((2 : ℚ) ^ 63 - 1) + 1 / 2 < 10 ^ 96 := by norm_num
    linarith [le_abs_self s.toRat]

/-- A cover that converts to a nonzero amount of the vault asset is below `2^63` units at the cover
scale. -/
lemma LoanBroker.cover_lt_units_of_ofNumber (lb : LoanBroker) (s : STAmount)
    (hs : STAmount.ofNumber lb.numericType lb.coverAvailable .to_nearest = .ok s)
    (hnz : s.mValue ≠ 0) : lb.toExact.coverAvailable < 2 ^ 63 * (10 : ℚ) ^ s.exponent := by
  obtain ⟨hc, hpos, hle⟩ := LoanBroker.cover_le_of_ofNumber lb s hs hnz
  have hp : (0 : ℚ) < (10 : ℚ) ^ s.exponent := zpow_pos (by norm_num) _
  show lb.coverAvailable.toRat < 2 ^ 63 * (10 : ℚ) ^ s.exponent
  rcases hc with hiou | ⟨hint, hsz⟩
  · obtain ⟨_, hb⟩ := STAmount.IOUCanonical.toRat_bounds s hiou hpos
    have h16 : (10 : ℚ) ^ (s.exponent + 16) = 10 ^ 16 * (10 : ℚ) ^ s.exponent := by
      rw [zpow_add₀ (by norm_num : (10 : ℚ) ≠ 0)]; norm_num; ring
    have h63 : (10 : ℚ) ^ 16 + 1 / 2 ≤ 2 ^ 63 := by norm_num
    nlinarith
  · have hoff : s.exponent = 0 := hint.offset_zero
    rw [hoff, zpow_zero, mul_one] at hle ⊢
    have habs := STAmount.IntegralCanonical.abs_toRat_le_of_mValue_le s hint hsz
    linarith [le_abs_self s.toRat]

/-- The exponent of CoverAvailable in the vault asset is at most `80`, the IOU maximum. -/
lemma LoanBroker.cover_exponent_le (lb : LoanBroker) (s : STAmount)
    (hs : STAmount.ofNumber lb.numericType lb.coverAvailable .to_nearest = .ok s)
    (hnz : s.mValue ≠ 0) : s.exponent ≤ 80 := by
  obtain ⟨hc, _, _⟩ := LoanBroker.cover_le_of_ofNumber lb s hs hnz
  rcases hc with hiou | ⟨hint, _⟩
  · exact hiou.exp_hi
  · show s.mOffset ≤ 80
    rw [hint.offset_zero]; norm_num

/-- One unit at the cover scale: a nonzero amount of the vault asset of value `10 ^ s.exponent` that
passes the scale check. For XRP and MPT it is one drop or unit, for an IOU the 16-digit amount
`10^15 · 10^(s.exponent - 15)`, which needs `s.exponent` at least `-81`. -/
lemma LoanBroker.coverUnit_exists (lb : LoanBroker) (s : STAmount)
    (hs : STAmount.ofNumber lb.numericType lb.coverAvailable .to_nearest = .ok s)
    (hnz : s.mValue ≠ 0) (hunit : (-81 : Int) ≤ s.exponent) :
    ∃ u : STAmount, u.ExactCanonical ∧ u.mNumericType = lb.numericType ∧ u.mValue ≠ 0 ∧
      u.toRat = (10 : ℚ) ^ s.exponent ∧
      canApplyToBrokerCover lb.numericType lb.coverAvailable u = .ok .tesSUCCESS := by
  obtain ⟨hc, _, _⟩ := LoanBroker.cover_le_of_ofNumber lb s hs hnz
  have hst : s.mNumericType = lb.numericType := STAmount.ofNumber_mNumericType _ _ _ _ hs
  have hscale : numberExponent lb.coverAvailable lb.numericType = .ok s.exponent := by
    simp [numberExponent, hs]
  have hexp : s.exponent = s.mOffset := rfl
  rcases hc with hiou | ⟨hint, _⟩
  · -- an IOU: the smallest 16-digit amount at the exponent below the cover's
    have hfr : lb.numericType = .fractional := by rw [← hst]; exact hiou.is_fractional
    have hkMin : kMinValue.toNat = 10 ^ 15 := by decide
    set u : STAmount := ⟨.fractional, kMinValue, s.exponent - 15, false⟩ with hu_def
    have huc : u.IOUCanonical :=
      ⟨rfl, by show 10 ^ 15 ≤ kMinValue.toNat; omega, by show kMinValue.toNat < 10 ^ 16; omega,
        by show (-96 : ℤ) ≤ s.exponent - 15; omega,
        by show s.exponent - 15 ≤ 80; have := hiou.exp_hi; omega⟩
    have hu0 : u.mValue ≠ 0 := by show kMinValue ≠ 0; decide
    have huv : u.toRat = (10 : ℚ) ^ s.exponent := by
      rw [STAmount.toRat_of_nonneg u rfl]
      show (kMinValue.toNat : ℚ) * 10 ^ (s.exponent - 15) = 10 ^ s.exponent
      have h15 : (10 : ℚ) ^ s.exponent = 10 ^ (s.exponent - 15) * (10 : ℚ) ^ (15 : ℤ) := by
        rw [← zpow_add₀ (by norm_num : (10 : ℚ) ≠ 0)]; congr 1; ring
      rw [hkMin, h15]; norm_num [mul_comm]
    have hround : roundToCoverScale lb.numericType lb.coverAvailable u .to_nearest = .ok u := by
      rw [roundToCoverScale_eq _ _ _ _ _ hscale]
      exact STAmount.roundToExponent_grid_self u s.exponent 1 huc rfl le_rfl
        (by rw [huv]; push_cast; ring) hunit (by rw [hexp]; exact hiou.exp_hi)
    have hsg : u.signum ≠ 0 := by
      show (if kMinValue == 0 then (0 : Int) else if false then -1 else 1) ≠ 0
      decide
    exact ⟨u, Or.inl huc, by rw [hfr], hu0, huv,
      canApplyToBrokerCover_pass _ _ _ _ (by simp [STAmount.isZero, hu0]) hround hsg⟩
  · -- XRP or MPT: one drop or unit, which the scale check never rounds
    have hint' : lb.numericType.isIntegral = true := by rw [← hst]; exact hint.is_integral
    have hoff : s.exponent = 0 := hint.offset_zero
    have hmax : 1 ≤ lb.numericType.maxValue.toNat := by
      have h1 := hint.in_range
      rw [hst] at h1
      have h2 : s.mValue.toNat ≠ 0 := fun h => hnz (by rw [← UInt64.toNat_inj, h]; rfl)
      omega
    set u : STAmount := ⟨lb.numericType, 1, 0, false⟩ with hu_def
    have huc : u.IntegralCanonical := ⟨hint', rfl, by show (1 : UInt64).toNat ≤ _; exact hmax⟩
    have hu0 : u.mValue ≠ 0 := by show (1 : UInt64) ≠ 0; decide
    have huv : u.toRat = (10 : ℚ) ^ s.exponent := by
      rw [hoff, STAmount.toRat_of_nonneg u rfl]
      show (((1 : UInt64).toNat : ℕ) : ℚ) * 10 ^ (0 : ℤ) = 10 ^ (0 : ℤ)
      simp
    have hround : roundToCoverScale lb.numericType lb.coverAvailable u .to_nearest = .ok u := by
      rw [roundToCoverScale_eq _ _ _ _ _ hscale]
      exact STAmount.roundToExponent_eq_self u _ _ (Or.inl hint')
    have hsg : u.signum ≠ 0 := by
      show (if (1 : UInt64) == 0 then (0 : Int) else if false then -1 else 1) ≠ 0
      decide
    exact ⟨u, Or.inr ⟨huc, by show (1 : UInt64).toNat ≤ 2 ^ 63 - 1; decide⟩, rfl, hu0, huv,
      canApplyToBrokerCover_pass _ _ _ _ (by simp [STAmount.isZero, hu0]) hround hsg⟩

/-- Taking one unit at the cover scale from CoverAvailable is exact: the difference is a `Number`. -/
lemma LoanBroker.coverUnit_sub_exact (lb : LoanBroker) (s : STAmount)
    (hs : STAmount.ofNumber lb.numericType lb.coverAvailable .to_nearest = .ok s)
    (hnz : s.mValue ≠ 0) (hunit : (-81 : Int) ≤ s.exponent)
    (hle : (10 : ℚ) ^ s.exponent ≤ lb.toExact.coverAvailable) :
    ∃ w : Number, w.isNormalized ∧ w.toRat = lb.toExact.coverAvailable - (10 : ℚ) ^ s.exponent :=
  Number.exists_normalized_sub_pow lb.coverAvailable s.exponent lb.wf.coverAvailable_norm
    lb.exact.coverAvailable_nonneg hle (LoanBroker.cover_lt_units_of_ofNumber lb s hs hnz)
    (by unfold minExponent; omega)
    (by have := LoanBroker.cover_exponent_le lb s hs hnz; unfold maxExponent; omega)

end XRPL.Model.Lending
