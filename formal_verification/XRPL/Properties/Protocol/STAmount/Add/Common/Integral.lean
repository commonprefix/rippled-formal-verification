import Mathlib.Tactic

import XRPL.Properties.Protocol.Number.Common.Int64Lemmas
import XRPL.Properties.Protocol.Number.ToRep.ToRep
import XRPL.Properties.Protocol.STAmount.Common.DiscreteDefs
import XRPL.Model.Protocol.STAmount

/-! # Value of integral (XRP/MPT) STAmounts and the exact integral `canonicalize` round-trip -/

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

end XRPL.Model.Protocol
