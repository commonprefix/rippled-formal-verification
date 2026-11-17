import XRPL.Properties.Protocol.STAmount.Range.Common.Checked
import XRPL.Properties.Protocol.STAmount.Common.Checked
import XRPL.Properties.Protocol.STAmount.Sub.Common.Neg
import XRPL.Properties.Protocol.Common.AmountArith

/-! # When adding XRP or MPT amounts returns a result

XRP and MPT amounts are added as int64 values. XRP has no range check after the sum. MPT fails when the sum wraps
int64, and puts `-2^63` through a conversion that drops its last digit. -/

namespace XRPL.Model.Protocol

/-- A whole number is in range in every mode exactly when its size is at most `L`. -/
lemma roundsWithinUnits_int_iff (mode : rounding_mode) (L : ℕ) (z : ℤ) :
    RoundsWithinUnits mode L 1 (z : ℚ) ↔ |z| ≤ (L : ℤ) := by
  have h := roundsWithinUnits_iff mode (decide (z < 0)) |z| L 0 1 false (abs_nonneg z) le_rfl (by norm_num)
    one_pos ⟨fun h => absurd h (by decide), fun h => absurd h (not_roundsUp_zero _ _ _)⟩
  have hz : (if decide (z < 0) = true then (-1 : ℚ) else 1) * (((|z| : ℤ) : ℚ) + 0) * 1 = (z : ℚ) := by
    by_cases hneg : z < 0
    · simp [hneg, abs_of_neg hneg]
    · simp [hneg, abs_of_nonneg (not_lt.mp hneg)]
  rw [hz] at h
  simpa using h.symm

/-- The int64 view of a canonical integral amount within int64 is its signed value. -/
lemma STAmount.signedDrops_bounds (s : STAmount) :
    -(s.mValue.toNat : ℤ) ≤ s.signedDrops ∧ s.signedDrops ≤ (s.mValue.toNat : ℤ) := by
  unfold STAmount.signedDrops
  split <;> omega

/-- An amount made from an int64 value and canonicalized is `checked` on its size and sign. -/
lemma STAmount.uncheckedFromInt64_canonicalize (nt : NumericType) (t : Int64) (mode : rounding_mode) :
    (STAmount.uncheckedFromInt64 nt t 0).canonicalize mode
      = STAmount.checked nt t.magnitude 0 (decide (t < 0)) mode := by
  unfold STAmount.uncheckedFromInt64 STAmount.checked
  by_cases ht : t < 0
  · rw [if_pos ht, decide_eq_true ht]
  · rw [if_neg ht, decide_eq_false ht]

/-- Proof of `STAmount.operator_add_ok_xrp`. -/
lemma STAmount.operator_add_ok_xrp_proof (v1 v2 : STAmount) (mode : rounding_mode)
    (h1 : v1.IntegralCanonical) (h2 : v2.IntegralCanonical)
    (ht1 : v1.mNumericType = NumericType.native) (ht2 : v2.mNumericType = NumericType.native) :
    ∃ result, STAmount.operator_add v1 v2 mode = .ok result := by
  have hcmp : STAmount.areComparable v1 v2 = true := by
    unfold STAmount.areComparable
    rw [ht1, ht2]
    rfl
  have hint : v1.integral = true := by
    unfold STAmount.integral
    rw [ht1]
    rfl
  have hv1 : v1.mValue.toNat ≤ 100000000000000000 := by
    have := h1.in_range
    rwa [ht1] at this
  have hv2 : v2.mValue.toNat ≤ 100000000000000000 := by
    have := h2.in_range
    rwa [ht2] at this
  have hb1 := STAmount.signedDrops_bounds v1
  have hb2 := STAmount.signedDrops_bounds v2
  have hmaxRep : maxRep.toNat = 9223372036854775807 := by decide
  unfold STAmount.operator_add
  rw [if_neg (by rw [hcmp]; decide)]
  by_cases hz2 : (v2.mValue == 0) = true
  · rw [if_pos hz2]
    exact ⟨_, rfl⟩
  rw [if_neg hz2]
  by_cases hz1 : (v1.mValue == 0) = true
  · -- zero plus an amount is that amount, put through `checked`
    have hnot : ¬ (v1.integral && decide (v2.mValue > maxRep)) = true := by
      rw [Bool.and_eq_true, decide_eq_true_eq, gt_iff_lt, UInt64.lt_iff_toNat_lt]
      omega
    rw [if_pos hz1, if_neg hnot, ht1, h2.offset_zero]
    refine (STAmount.checked_ok_iff_native v2.mValue 0 v2.mIsNegative mode (by omega)).mpr ?_
    rw [STAmount.roundsInRange_native_iff]
    refine roundsWithinUnits_of_abs_le mode _ 1 _ one_pos ?_
    rw [STAmount.abs_toRat]
    show (v2.mValue.toNat : ℚ) * 10 ^ (0 : ℤ) ≤ ((100000000000000000 : ℕ) : ℚ) * 1
    rw [zpow_zero]
    have : (v2.mValue.toNat : ℚ) ≤ ((100000000000000000 : ℕ) : ℚ) := by exact_mod_cast hv2
    linarith
  -- both nonzero: the int64 sum, with no range check for XRP
  rw [if_neg hz1, if_pos hint, STAmount.signedDrops_toInt64Checked v1 (by omega), ok_bind,
    STAmount.signedDrops_toInt64Checked v2 (by omega), ok_bind]
  have ha := STAmount.signedDrops_toInt64_toInt_of_lt v1 (by omega)
  have hb := STAmount.signedDrops_toInt64_toInt_of_lt v2 (by omega)
  rw [Int64.addChecked_of_bounds (by rw [ha, hb]; omega) (by rw [ha, hb]; omega), ok_bind]
  simp only []
  rw [if_pos (by rw [ht1]; rfl)]
  exact ⟨_, rfl⟩

/-- Proof of `STAmount.operator_add_ok_iff_mpt`. -/
lemma STAmount.operator_add_ok_iff_mpt_proof (v1 v2 : STAmount) (mode : rounding_mode)
    (h1 : v1.IntegralCanonical) (h2 : v2.IntegralCanonical)
    (ht1 : v1.mNumericType = NumericType.int64) (ht2 : v2.mNumericType = NumericType.int64)
    (hmin : v1.toRat + v2.toRat ≠ -9223372036854775808) :
    (∃ result, STAmount.operator_add v1 v2 mode = .ok result) ↔
      STAmount.RoundsInRange NumericType.int64 mode (v1.toRat + v2.toRat) := by
  have hcmp : STAmount.areComparable v1 v2 = true := by
    unfold STAmount.areComparable
    rw [ht1, ht2]
    rfl
  have hint : v1.integral = true := by
    unfold STAmount.integral
    rw [ht1]
    rfl
  have hv1 : v1.mValue.toNat ≤ 9223372036854775807 := by
    have := h1.in_range
    rwa [ht1] at this
  have hv2 : v2.mValue.toNat ≤ 9223372036854775807 := by
    have := h2.in_range
    rwa [ht2] at this
  have hb1 := STAmount.signedDrops_bounds v1
  have hb2 := STAmount.signedDrops_bounds v2
  have hr1 : v1.toRat = (v1.signedDrops : ℚ) := STAmount.toRat_of_offset_zero v1 h1.offset_zero
  have hr2 : v2.toRat = (v2.signedDrops : ℚ) := STAmount.toRat_of_offset_zero v2 h2.offset_zero
  have hmaxRep : maxRep.toNat = 9223372036854775807 := by decide
  have hrange_int : ∀ z : ℤ,
      STAmount.RoundsInRange NumericType.int64 mode (z : ℚ) ↔ |z| ≤ 9223372036854775807 := by
    intro z
    rw [STAmount.roundsInRange_int64_iff]
    exact roundsWithinUnits_int_iff mode _ z
  unfold STAmount.operator_add
  rw [if_neg (by rw [hcmp]; decide)]
  by_cases hz2 : (v2.mValue == 0) = true
  · -- an amount plus zero is that amount
    rw [if_pos hz2, STAmount.toRat_zero_aux v2 h2.offset_zero hz2, add_zero, hr1, hrange_int]
    exact iff_of_true ⟨_, rfl⟩ (abs_le.mpr ⟨by omega, by omega⟩)
  rw [if_neg hz2]
  by_cases hz1 : (v1.mValue == 0) = true
  · -- zero plus an amount is that amount, put through `checked`
    have hnot : ¬ (v1.integral && decide (v2.mValue > maxRep)) = true := by
      rw [Bool.and_eq_true, decide_eq_true_eq, gt_iff_lt, UInt64.lt_iff_toNat_lt]
      omega
    rw [if_pos hz1, if_neg hnot, ht1, h2.offset_zero, STAmount.toRat_zero_aux v1 h1.offset_zero hz1, zero_add,
      STAmount.checked_ok_iff_int64 v2.mValue 0 v2.mIsNegative mode hv2]
    have hval : (STAmount.unchecked NumericType.int64 v2.mValue 0 v2.mIsNegative).toRat = v2.toRat := by
      rw [STAmount.toRat_signed, STAmount.toRat_signed v2, h2.offset_zero]
      rfl
    rw [hval]
  -- both nonzero: the int64 sum, put through `checked`
  rw [if_neg hz1, if_pos hint, STAmount.signedDrops_toInt64Checked v1 (by omega), ok_bind,
    STAmount.signedDrops_toInt64Checked v2 (by omega), ok_bind]
  have ha := STAmount.signedDrops_toInt64_toInt_of_lt v1 (by omega)
  have hb := STAmount.signedDrops_toInt64_toInt_of_lt v2 (by omega)
  have hsum_q : v1.toRat + v2.toRat = ((v1.signedDrops + v2.signedDrops : ℤ) : ℚ) := by
    rw [hr1, hr2]
    push_cast
    rfl
  have hmin_int : v1.signedDrops + v2.signedDrops ≠ -9223372036854775808 := by
    intro h
    apply hmin
    rw [hsum_q, h]
    norm_num
  rw [hsum_q, hrange_int]
  by_cases hfit : -2 ^ 63 ≤ v1.signedDrops + v2.signedDrops ∧ v1.signedDrops + v2.signedDrops < 2 ^ 63
  · rw [Int64.addChecked_of_bounds (by rw [ha, hb]; exact hfit.1) (by rw [ha, hb]; exact hfit.2), ok_bind]
    simp only []
    rw [if_neg (by rw [ht1]; decide)]
    set total : Int64 := v1.signedDrops.toInt64 + v2.signedDrops.toInt64 with htotal
    have htot : total.toInt = v1.signedDrops + v2.signedDrops := by
      rw [htotal, Int64.toInt_add, ha, hb]
      exact AmountArith.toInt_bmod_self
        (by rw [show Int64.minValue.toInt = -9223372036854775808 from by decide]; omega)
        (by rw [show Int64.maxValue.toInt = 9223372036854775807 from by decide]; omega)
    rw [ht1, STAmount.uncheckedFromInt64_canonicalize, STAmount.checked_ok_iff_int64 total.magnitude 0 _ mode
      (by rw [Int64.toNat_magnitude, htot]; omega)]
    have hval : (STAmount.unchecked NumericType.int64 total.magnitude 0 (decide (total < 0))).toRat
        = ((v1.signedDrops + v2.signedDrops : ℤ) : ℚ) := by
      rw [← htot]
      exact STAmount.reconstruct_toRat _ total
    rw [hval, hrange_int]
  · -- the sum wraps int64, and is outside the MPT range
    have herr : ∃ err, v1.signedDrops.toInt64.addChecked v2.signedDrops.toInt64 = .error err := by
      cases h : v1.signedDrops.toInt64.addChecked v2.signedDrops.toInt64 with
      | error err => exact ⟨err, rfl⟩
      | ok c =>
        have := (Int64.addChecked_eq_ok.mp h).1
        rw [ha, hb] at this
        exact absurd ⟨by omega, by omega⟩ hfit
    obtain ⟨err, herr⟩ := herr
    rw [herr, err_bind]
    refine iff_of_false (by simp) ?_
    intro h
    have := abs_le.mp h
    omega

/-- Proof of `STAmount.operator_sub_ok_xrp`. -/
lemma STAmount.operator_sub_ok_xrp_proof (v1 v2 : STAmount) (mode : rounding_mode)
    (h1 : v1.IntegralCanonical) (h2 : v2.IntegralCanonical)
    (ht1 : v1.mNumericType = NumericType.native) (ht2 : v2.mNumericType = NumericType.native) :
    ∃ result, STAmount.operator_sub v1 v2 mode = .ok result :=
  STAmount.operator_add_ok_xrp_proof v1 v2.operator_neg mode h1 h2.operator_neg ht1
    (by rw [STAmount.operator_neg_mNumericType]; exact ht2)

/-- Proof of `STAmount.operator_sub_ok_iff_mpt`. -/
lemma STAmount.operator_sub_ok_iff_mpt_proof (v1 v2 : STAmount) (mode : rounding_mode)
    (h1 : v1.IntegralCanonical) (h2 : v2.IntegralCanonical)
    (ht1 : v1.mNumericType = NumericType.int64) (ht2 : v2.mNumericType = NumericType.int64)
    (hmin : v1.toRat - v2.toRat ≠ -9223372036854775808) :
    (∃ result, STAmount.operator_sub v1 v2 mode = .ok result) ↔
      STAmount.RoundsInRange NumericType.int64 mode (v1.toRat - v2.toRat) := by
  have htruth : v1.toRat + v2.operator_neg.toRat = v1.toRat - v2.toRat := by
    rw [STAmount.operator_neg_toRat]; ring
  rw [← htruth] at hmin ⊢
  exact STAmount.operator_add_ok_iff_mpt_proof v1 v2.operator_neg mode h1 h2.operator_neg ht1
    (by rw [STAmount.operator_neg_mNumericType]; exact ht2) hmin

end XRPL.Model.Protocol
