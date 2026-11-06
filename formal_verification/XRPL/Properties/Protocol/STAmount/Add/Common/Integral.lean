import Mathlib.Tactic

import XRPL.Properties.Protocol.Number.Common.Int64Lemmas
import XRPL.Properties.Protocol.Number.ToRep.ToRep
import XRPL.Properties.Protocol.STAmount.Common.DiscreteDefs
import XRPL.Model.Protocol.STAmount

/-! # Integral (XRP/MPT) addition exactness. -/

namespace XRPL.Model.Protocol

/-- For an integral (offset-0) STAmount, the exact value is just its signed drops. -/
lemma STAmount.toRat_of_offset_zero (s : STAmount) (ho : s.mOffset = 0) :
    s.toRat = (s.signedDrops : ℚ) := by
  unfold STAmount.toRat STAmount.signedDrops
  by_cases hm : s.mValue = 0
  · simp [hm]
  rw [if_neg hm, ho]
  simp only [ge_iff_le, le_refl, if_true, Int.toNat_zero, pow_zero, mul_one, Rat.mkRat_one]
  by_cases hneg : s.mIsNegative
  · rw [if_pos hneg, if_pos hneg]; push_cast; ring
  · rw [if_neg hneg, if_neg hneg]; push_cast; ring

/-- `uncheckedFromInt64 nt d 0` represents exactly `d`. `toRat` ignores the numericType, so this holds for any
`nt`. -/
lemma STAmount.uncheckedFromInt64_toRat (nt : NumericType) (d : Int64) :
    (STAmount.uncheckedFromInt64 nt d 0).toRat = (d.toInt : ℚ) := by
  have h0i : (0 : Int64).toInt = 0 := by decide
  rw [STAmount.uncheckedFromInt64]
  by_cases hd : d < 0
  · have hdneg : d.toInt < 0 := by
      have := Int64.lt_iff_toInt_lt.mp hd; rw [h0i] at this; exact this
    rw [if_pos hd, STAmount.toRat_of_offset_zero _ rfl]
    simp only [STAmount.signedDrops, STAmount.unchecked, if_true, Int64.toNat_magnitude]
    rw [Int.ofNat_natAbs_of_nonpos hdneg.le]; push_cast; ring
  · have hdpos : (0 : ℤ) ≤ d.toInt := by
      rcases lt_or_ge d.toInt 0 with h | h
      · exact absurd (Int64.lt_iff_toInt_lt.mpr (by rw [h0i]; exact h)) hd
      · exact h
    rw [if_neg hd, STAmount.toRat_of_offset_zero _ rfl]
    simp only [STAmount.signedDrops, STAmount.unchecked, reduceCtorEq, if_false, Int64.toNat_magnitude]
    rw [Int.natAbs_of_nonneg hdpos]

/-- A record with magnitude `|r|`, offset `0` and sign bit `r < 0` has the value `r`. -/
lemma STAmount.reconstruct_toRat (nt : NumericType) (r : Int64) :
    ({ mNumericType := nt, mValue := r.magnitude, mOffset := 0
     , mIsNegative := decide (r < 0) } : STAmount).toRat = (r.toInt : ℚ) := by
  have hsigned : (if decide (r < 0) then -(r.toInt.natAbs : ℤ) else (r.toInt.natAbs : ℤ))
      = r.toInt := by
    by_cases hrneg : r < 0
    · rw [if_pos (by simpa using hrneg)]
      have hri : r.toInt ≤ 0 := le_of_lt (by simpa using Int64.lt_iff_toInt_lt.mp hrneg)
      rw [Int.ofNat_natAbs_of_nonpos hri]; ring
    · rw [if_neg (by simpa using hrneg)]
      have hri : 0 ≤ r.toInt := by
        rcases lt_or_ge r.toInt 0 with h | h
        · exact absurd (Int64.lt_iff_toInt_lt.mpr (by simpa using h)) hrneg
        · exact h
      rw [Int.natAbs_of_nonneg hri]
  have hres : r.magnitude.toNat = r.toInt.natAbs := Int64.toNat_magnitude r
  rw [STAmount.toRat_of_offset_zero _ rfl]
  simp only [STAmount.signedDrops]
  rw [hres, hsigned]

/-- The `Int64` view of `signedDrops` is exact for any magnitude in `Int64` range -/
lemma STAmount.signedDrops_toInt64_toInt_of_lt (s : STAmount)
    (h_hi : s.mValue.toNat < 2 ^ 63) :
    s.signedDrops.toInt64.toInt = s.signedDrops := by
  apply Int64.toInt_ofInt_of_le
  · unfold STAmount.signedDrops; split <;> omega
  · unfold STAmount.signedDrops; split <;> omega

/-- `signedDrops` lies between `-mValue` and `mValue`. -/
lemma STAmount.signedDrops_bounds (s : STAmount) :
    -(s.mValue.toNat : ℤ) ≤ s.signedDrops ∧ s.signedDrops ≤ (s.mValue.toNat : ℤ) := by
  unfold STAmount.signedDrops; split <;> omega

/-- Value of a zero-magnitude offset-0 STAmount is `0`. -/
lemma STAmount.toRat_zero_aux (s : STAmount) (ho : s.mOffset = 0) (h : s.mValue == 0) :
    s.toRat = 0 := by
  rw [STAmount.toRat_of_offset_zero s ho]
  have : s.mValue.toNat = 0 := by rw [beq_iff_eq] at h; rw [h]; rfl
  unfold STAmount.signedDrops; rw [this]; simp

/-- The integral `canonicalize` round-trip is exact on an integral (offset-0) amount whose stored magnitude
fits `maxRep`: the value passes through `to_rep` unchanged. -/
lemma STAmount.canonicalize_integral_toRat (s result : STAmount) (mode : rounding_mode)
    (hint : s.integral = true) (hoff : s.mOffset = 0)
    (hval_le : s.mValue.toNat ≤ maxRep.toNat)
    (hok : s.canonicalize mode = .ok result) :
    result.toRat = s.toRat := by
  have hval_lt : s.mValue.toNat < 2 ^ 64 := by
    have hk : maxRep.toNat < 2 ^ 64 := by decide
    omega
  rw [STAmount.canonicalize, if_pos hint] at hok
  by_cases hz : s.mValue == 0
  · rw [if_pos (by rw [hz]; rfl)] at hok
    rw [beq_iff_eq] at hz
    rw [Except.ok.inj hok.symm, STAmount.toRat_of_offset_zero _ rfl,
        STAmount.toRat_of_offset_zero s hoff]
    simp only [STAmount.signedDrops]; rw [hz]; simp
  · have hz' : (s.mValue == 0) = false := by simpa using hz
    rw [if_neg (by rw [hz', hoff]; decide)] at hok
    -- The offset guard `mOffset > maxOffset` cannot fire: it would error, but `hok` succeeds.
    by_cases hmoff : s.mOffset > s.mNumericType.maxOffset
    · rw [if_pos hmoff] at hok; simp at hok
    rw [if_neg hmoff] at hok
    -- canonicalize rounds the SIGNED Number via IntAmount.ofNumber. At offset 0 `to_rep` is exact,
    -- so `r = signedDrops`, and the result reconstructs that value.
    simp only [hoff, IntAmount.ofNumber] at hok
    cases hr : (Number.unchecked s.mIsNegative s.mValue 0).to_rep mode with
    | error e => rw [hr] at hok; simp at hok
    | ok r =>
      rw [hr] at hok
      simp only [] at hok
      have hkey := to_rep_exact_of_exponent_zero s.mIsNegative s.mValue mode r hval_le hr
      have hr_sd : r.toInt = s.signedDrops := by
        have h1 : (r.toInt : ℚ) = (s.signedDrops : ℚ) := by
          rw [hkey]; simp only [STAmount.signedDrops]
          by_cases hn : s.mIsNegative <;> simp [hn]
        exact_mod_cast h1
      have hnatAbs : r.toInt.natAbs = s.mValue.toNat := by
        rw [hr_sd]; unfold STAmount.signedDrops; split <;> simp
      -- The range guard `v > maxValue` cannot fire either: it would error, but `hok` succeeds.
      by_cases hrng : r.magnitude > s.mNumericType.maxValue
      · rw [if_pos hrng] at hok; simp at hok
      rw [if_neg hrng] at hok
      rw [Except.ok.inj hok.symm,
          STAmount.reconstruct_toRat s.mNumericType r,
          hr_sd, ← STAmount.toRat_of_offset_zero s hoff]

/-- `uncheckedFromInt64 nt d 0` stores magnitude `|d|`. -/
lemma STAmount.uncheckedFromInt64_mValue_natAbs (nt : NumericType) (d : Int64) :
    (STAmount.uncheckedFromInt64 nt d 0).mValue.toNat = d.toInt.natAbs := by
  rw [STAmount.uncheckedFromInt64]
  split <;> exact Int64.toNat_magnitude d

/-- An integral `d` (within `maxRep` magnitude) passes through `canonicalize` unchanged, so the result
represents `d`. -/
lemma STAmount.canonicalize_uncheckedFromInt64_toRat (nt : NumericType) (d : Int64) (mode : rounding_mode)
    (result : STAmount) (hnt_int : nt.isIntegral = true)
    (hhi : d.toInt.natAbs ≤ maxRep.toNat)
    (hok : (STAmount.uncheckedFromInt64 nt d 0).canonicalize mode = .ok result) :
    result.toRat = (d.toInt : ℚ) := by
  have hs_int : (STAmount.uncheckedFromInt64 nt d 0).integral = true := by
    unfold STAmount.integral STAmount.uncheckedFromInt64; split <;> exact hnt_int
  have hs_off : (STAmount.uncheckedFromInt64 nt d 0).mOffset = 0 := by
    unfold STAmount.uncheckedFromInt64; split <;> rfl
  have hs_le : (STAmount.uncheckedFromInt64 nt d 0).mValue.toNat ≤ maxRep.toNat := by
    rw [STAmount.uncheckedFromInt64_mValue_natAbs nt d]; exact hhi
  rw [STAmount.canonicalize_integral_toRat _ result mode hs_int hs_off hs_le hok,
      STAmount.uncheckedFromInt64_toRat nt d]

/-- Unified integral (XRP/MPT) addition exactness. -/
theorem STAmount.operator_add_integral_exact (v1 v2 result : STAmount) (mode : rounding_mode)
    (hc1 : v1.IntegralCanonical) (hc2 : v2.IntegralCanonical)
    (hbound_val : v1.mNumericType.maxValue.toNat ≤ maxRep.toNat)
    (hsum : (v1.signedDrops + v2.signedDrops).natAbs < 2 ^ 63)
    (hok : STAmount.operator_add v1 v2 mode = .ok result) :
    result.toRat = v1.toRat + v2.toRat := by
  obtain ⟨hint1, ho1, hb1⟩ := hc1
  obtain ⟨hint2, ho2, hb2⟩ := hc2
  have hcmp : STAmount.areComparable v1 v2 = true := by
    rcases hb : STAmount.areComparable v1 v2 with _ | _
    · rw [STAmount.operator_add, hb] at hok; simp at hok
    · rfl
  have hnt : v1.mNumericType = v2.mNumericType := by
    unfold STAmount.areComparable at hcmp; exact beq_iff_eq.mp hcmp
  have hmaxlt : maxRep.toNat < 2 ^ 63 := by decide
  have hb1' : v1.mValue.toNat < 2 ^ 63 := lt_of_le_of_lt (le_trans hb1 hbound_val) hmaxlt
  have hb2' : v2.mValue.toNat < 2 ^ 63 := by
    have := hb2; rw [← hnt] at this; exact lt_of_le_of_lt (le_trans this hbound_val) hmaxlt
  rw [STAmount.operator_add, if_neg (by rw [hcmp]; decide)] at hok
  by_cases hzv2 : v2.mValue == 0
  · rw [if_pos hzv2] at hok
    rw [Except.ok.inj hok.symm, STAmount.toRat_zero_aux v2 ho2 hzv2]; ring
  rw [if_neg hzv2] at hok
  by_cases hzv1 : v1.mValue == 0
  · rw [if_pos hzv1] at hok
    have hunch : STAmount.unchecked v1.mNumericType v2.mValue v2.mOffset v2.mIsNegative = v2 := by
      rw [hnt]; rfl
    rw [STAmount.checked, hunch] at hok
    rw [STAmount.toRat_zero_aux v1 ho1 hzv1, zero_add]
    exact STAmount.canonicalize_integral_toRat v2 result mode hint2 ho2
      (le_trans hb2 (by rw [← hnt]; exact hbound_val)) hok
  -- both nonzero: integral main path
  rw [if_neg hzv1, if_pos (show v1.integral = true from hint1)] at hok
  have habs : |v1.signedDrops + v2.signedDrops| < 2 ^ 63 := by
    rw [Int.abs_eq_natAbs]; exact_mod_cast hsum
  obtain ⟨hlo, hhi⟩ := abs_lt.mp habs
  have hsd1 : v1.signedDrops.toInt64.toInt = v1.signedDrops :=
    STAmount.signedDrops_toInt64_toInt_of_lt v1 hb1'
  have hsd2 : v2.signedDrops.toInt64.toInt = v2.signedDrops :=
    STAmount.signedDrops_toInt64_toInt_of_lt v2 hb2'
  have hsumeq : (v1.signedDrops.toInt64 + v2.signedDrops.toInt64).toInt
      = v1.signedDrops + v2.signedDrops := by
    rw [toInt_add_of_bounds _ _ (by rw [hsd1, hsd2]; omega) (by rw [hsd1, hsd2]; omega),
      hsd1, hsd2]
  rw [Int.toInt64Checked_of_bounds (by have := STAmount.signedDrops_bounds v1; omega) (by
      have := STAmount.signedDrops_bounds v1; omega), ok_bind,
    Int.toInt64Checked_of_bounds (by have := STAmount.signedDrops_bounds v2; omega) (by
      have := STAmount.signedDrops_bounds v2; omega), ok_bind,
    Int64.addChecked_of_bounds (by rw [hsd1, hsd2]; omega) (by rw [hsd1, hsd2]; omega), ok_bind] at hok
  dsimp only at hok
  by_cases hnative : (v1.mNumericType == .native) = true
  · rw [if_pos hnative] at hok
    rw [Except.ok.inj hok.symm,
        STAmount.uncheckedFromInt64_toRat v1.mNumericType _, hsumeq,
        STAmount.toRat_of_offset_zero v1 ho1, STAmount.toRat_of_offset_zero v2 ho2]
    push_cast; ring
  · rw [if_neg hnative] at hok
    have hd_hi : (v1.signedDrops.toInt64 + v2.signedDrops.toInt64).toInt.natAbs ≤ maxRep.toNat := by
      have hmr : maxRep.toNat = 9223372036854775807 := by decide
      rw [hsumeq]; omega
    have hres := STAmount.canonicalize_uncheckedFromInt64_toRat v1.mNumericType
      (v1.signedDrops.toInt64 + v2.signedDrops.toInt64) mode result hint1 hd_hi hok
    rw [hres, hsumeq, STAmount.toRat_of_offset_zero v1 ho1, STAmount.toRat_of_offset_zero v2 ho2]
    push_cast; ring

end XRPL.Model.Protocol
