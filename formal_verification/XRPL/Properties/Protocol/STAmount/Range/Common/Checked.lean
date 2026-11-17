import XRPL.Properties.Protocol.STAmount.Common.ToRepUnchecked
import XRPL.Properties.Protocol.STAmount.Range.Common.Units
import XRPL.Properties.Protocol.STAmount.Add.Common.Integral

/-! # When `STAmount.checked` returns a result

For XRP and MPT, `checked` rounds `mantissa * 10 ^ exponent` to a whole number with `Number.to_rep` and then
compares it with the largest amount of the type. -/

namespace XRPL.Model.Protocol

/-- The value of an unchecked amount: the signed mantissa times the power of ten. -/
lemma STAmount.unchecked_toRat (nt : NumericType) (m : UInt64) (e : Int) (neg : Bool) :
    (STAmount.unchecked nt m e neg).toRat
      = (if neg = true then (-1 : ℚ) else 1) * ((m.toNat : ℚ) * 10 ^ e) := by
  rw [STAmount.toRat_signed]
  show (if neg = true then (-1 : ℚ) else 1) * (m.toNat : ℚ) * 10 ^ e = _
  ring

/-- A sign of `-1` or `1` drops out of an absolute value. -/
lemma abs_sign_mul_eq (neg : Bool) (x : ℚ) : |(if neg = true then (-1 : ℚ) else 1) * x| = |x| := by
  cases neg <;> simp

/-- `checked` on an integral type returns a result exactly when `mantissa * 10 ^ exponent` rounds into range.
The type must have `1 ≤ maxValue ≤ 2^63 - 1` and `maxValue < 10 ^ (maxOffset + 1)`, as XRP and MPT do. -/
lemma STAmount.checked_ok_iff_integral (mv : UInt64) (mo : Int) (ms msh : UInt64) (m : UInt64) (e : Int)
    (neg : Bool) (mode : rounding_mode) (hm : m.toNat ≤ 9223372036854775807)
    (hmv1 : 1 ≤ mv.toNat) (hmv : mv.toNat ≤ 9223372036854775807)
    (hmo : (mv.toNat : ℚ) + 1 ≤ (10 : ℚ) ^ (mo + 1)) :
    (∃ result, STAmount.checked (.integral mv mo ms msh) m e neg mode = .ok result) ↔
      STAmount.RoundsInRange (.integral mv mo ms msh) mode
        (STAmount.unchecked (.integral mv mo ms msh) m e neg).toRat := by
  have h63 : maxRep.toNat = 9223372036854775807 := by decide
  rw [STAmount.roundsInRange_integral_iff, STAmount.unchecked_toRat, STAmount.checked]
  dsimp only [STAmount.unchecked, STAmount.canonicalize, STAmount.integral, NumericType.isIntegral,
    NumericType.maxOffset, NumericType.maxValue, IntAmount.ofNumber]
  rw [if_pos rfl]
  have hmq : (0 : ℚ) ≤ (m.toNat : ℚ) := Nat.cast_nonneg _
  have hmvq : (1 : ℚ) ≤ (mv.toNat : ℚ) := by exact_mod_cast hmv1
  by_cases hz : m = 0
  · -- a zero mantissa gives the zero amount
    rw [if_pos (by rw [hz]; rfl)]
    refine iff_of_true ⟨_, rfl⟩ (roundsWithinUnits_of_abs_le mode _ 1 _ one_pos ?_)
    rw [hz]
    simp
  by_cases hsmall : e ≤ -20
  · -- an exponent of -20 or less gives the zero amount, and the value is below one
    rw [if_pos (by simp [hsmall])]
    refine iff_of_true ⟨_, rfl⟩ (roundsWithinUnits_of_abs_le mode _ 1 _ one_pos ?_)
    rw [abs_sign_mul_eq, abs_of_nonneg (mul_nonneg hmq (zpow_nonneg (by norm_num) _)), mul_one]
    have hpow : (10 : ℚ) ^ e ≤ (10 : ℚ) ^ (-20 : ℤ) := zpow_le_zpow_right₀ (by norm_num) hsmall
    have hpow_pos : (0 : ℚ) < (10 : ℚ) ^ e := zpow_pos (by norm_num) _
    have hm' : (m.toNat : ℚ) ≤ 9223372036854775807 := by exact_mod_cast hm
    have h20 : (10 : ℚ) ^ (-20 : ℤ) = 1 / 100000000000000000000 := by norm_num
    rw [h20] at hpow
    nlinarith
  rw [if_neg (by simp [hz, hsmall])]
  have hm1 : (1 : ℚ) ≤ (m.toNat : ℚ) := by
    have : m.toNat ≠ 0 := fun h => hz (UInt64.toNat_inj.mp (by rw [h]; rfl))
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr this
  by_cases hbig : e > mo
  · -- an exponent above `maxOffset` fails, and the value is above the largest amount
    rw [if_pos hbig]
    refine iff_of_false (by simp) (not_roundsWithinUnits_of_le_abs mode _ 1 _ one_pos ?_)
    rw [abs_sign_mul_eq, abs_of_nonneg (mul_nonneg hmq (zpow_nonneg (by norm_num) _)), mul_one]
    have hpow : (10 : ℚ) ^ (mo + 1) ≤ (10 : ℚ) ^ e := zpow_le_zpow_right₀ (by norm_num) (by omega)
    have hpow_pos : (0 : ℚ) < (10 : ℚ) ^ e := zpow_pos (by norm_num) _
    nlinarith
  rw [if_neg hbig]
  -- the mantissa and exponent are rounded to a whole number by `to_rep`
  obtain ⟨q, f, up, hq, hf0, hf1, hval, hup, hok, herr⟩ :=
    Number.to_rep_unchecked_eq neg m e mode (by rw [h63]; exact hm)
  rw [hval, ← mul_one ((if neg = true then (-1 : ℚ) else 1) * ((q : ℚ) + f)),
    ← roundsWithinUnits_iff mode neg q mv.toNat f 1 up hq hf0 hf1 one_pos hup]
  by_cases hfit : q + (if up = true then 1 else 0) ≤ (maxRep.toNat : ℤ)
  · obtain ⟨r, hr, hrv⟩ := hok hfit
    rw [hr]
    dsimp only
    have hc0 : 0 ≤ q + (if up = true then 1 else 0) := by split <;> omega
    have hmag : (r.magnitude.toNat : ℤ) = q + (if up = true then 1 else 0) := by
      rw [Int64.toNat_magnitude, hrv]
      cases neg
      · simp only [Bool.false_eq_true, if_false, one_mul]
        exact Int.natAbs_of_nonneg hc0
      · simp only [if_true, neg_one_mul, Int.natAbs_neg]
        exact Int.natAbs_of_nonneg hc0
    by_cases hrng : r.magnitude > mv
    · rw [if_pos hrng]
      have := UInt64.lt_iff_toNat_lt.mp hrng
      exact iff_of_false (by simp) (by omega)
    · rw [if_neg hrng]
      have := UInt64.le_iff_toNat_le.mp (UInt64.not_lt.mp hrng)
      exact iff_of_true ⟨_, rfl⟩ (by omega)
  · obtain ⟨err, herr'⟩ := herr (by omega)
    rw [herr']
    exact iff_of_false (by simp) (by omega)

/-- `checked` on XRP returns a result exactly when `mantissa * 10 ^ exponent` rounds into the XRP range. -/
lemma STAmount.checked_ok_iff_native (m : UInt64) (e : Int) (neg : Bool) (mode : rounding_mode)
    (hm : m.toNat ≤ 9223372036854775807) :
    (∃ result, STAmount.checked NumericType.native m e neg mode = .ok result) ↔
      STAmount.RoundsInRange NumericType.native mode (STAmount.unchecked NumericType.native m e neg).toRat :=
  STAmount.checked_ok_iff_integral 100000000000000000 17 3000000000 2095475792 m e neg mode hm (by decide)
    (by decide) (by
      show ((100000000000000000 : ℕ) : ℚ) + 1 ≤ _
      norm_num)

/-- `checked` on MPT returns a result exactly when `mantissa * 10 ^ exponent` rounds into the MPT range. -/
lemma STAmount.checked_ok_iff_int64 (m : UInt64) (e : Int) (neg : Bool) (mode : rounding_mode)
    (hm : m.toNat ≤ 9223372036854775807) :
    (∃ result, STAmount.checked NumericType.int64 m e neg mode = .ok result) ↔
      STAmount.RoundsInRange NumericType.int64 mode (STAmount.unchecked NumericType.int64 m e neg).toRat :=
  STAmount.checked_ok_iff_integral 9223372036854775807 18 3037000499 2147483648 m e neg mode hm (by decide)
    (by decide) (by
      show ((9223372036854775807 : ℕ) : ℚ) + 1 ≤ _
      norm_num)

/-- An operation that returns no result returns an error. -/
lemma exists_error_of_not_exists_ok {α : Type} {r : Except Error α} (h : ¬ ∃ a, r = .ok a) :
    ∃ err, r = .error err := by
  cases r with
  | error err => exact ⟨err, rfl⟩
  | ok a => exact absurd ⟨a, rfl⟩ h

end XRPL.Model.Protocol
