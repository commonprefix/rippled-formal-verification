import XRPL.Properties.Protocol.STAmount.Add.Common.Integral
import XRPL.Properties.Protocol.STAmount.Common.STAmountToNumber
-- Re-exported for the files that import this one (these lemmas moved to Protocol)
import XRPL.Properties.Protocol.Number.Common.NumberBridge
import XRPL.Properties.Protocol.Number.Sub.ZeroShape

/-! # Integer-valued amounts

Model-independent facts used by the exact (integral) vault theorems:

* rational bookkeeping for integer-valued `ℚ` values (`den = 1`),
* the zero-record shape chain, re-exported from `Protocol/Number/Sub/ZeroShape`,
* `STAmount` canonical-shape exactness for `toNumber` / `ofNumber .int64`. -/

namespace XRPL.Model.Protocol

/-! ## Rational bookkeeping -/

/-- An integer-valued rational is the cast of its numerator. -/
lemma rat_eq_num_cast_of_den_one (q : ℚ) (hden : q.den = 1) : ((q.num : ℤ) : ℚ) = q := by
  conv_rhs => rw [← Rat.num_div_den q]
  rw [hden, Nat.cast_one, div_one]

/-- A non-negative integer-valued rational is recovered from `q.num.toNat`. -/
lemma rat_toNat_cast_of_den_one (q : ℚ) (hden : q.den = 1) (h0 : 0 ≤ q) :
    ((q.num.toNat : ℕ) : ℚ) = q := by
  have hnum : 0 ≤ q.num := Rat.num_nonneg.mpr h0
  rw [← Int.cast_natCast, Int.toNat_of_nonneg hnum]
  exact rat_eq_num_cast_of_den_one q hden

/-- Numerator magnitude bound for a small non-negative integer-valued rational. -/
lemma rat_num_natAbs_lt_of_le (q : ℚ) (hden : q.den = 1) (h0 : 0 ≤ q)
    (hle : q ≤ 2 ^ 63 - 1) : q.num.natAbs < 2 ^ 63 := by
  have hnum0 : 0 ≤ q.num := Rat.num_nonneg.mpr h0
  have hcast := rat_eq_num_cast_of_den_one q hden
  have hle' : ((q.num : ℤ) : ℚ) ≤ ((2 ^ 63 - 1 : ℤ) : ℚ) := by
    rw [hcast]; exact le_trans hle (by norm_num)
  have hz : q.num ≤ 2 ^ 63 - 1 := by exact_mod_cast hle'
  omega

/-- An integer within distance `< 1` of an integer-valued rational equals it. -/
lemma int_cast_eq_of_abs_lt_one (a : ℤ) (q : ℚ) (hden : q.den = 1)
    (h : |(a : ℚ) - q| < 1) : (a : ℚ) = q := by
  have hcast := rat_eq_num_cast_of_den_one q hden
  rw [← hcast] at h ⊢
  have h' : |((a - q.num : ℤ) : ℚ)| < 1 := by push_cast; exact h
  have hz : (a - q.num : ℤ).natAbs < 1 := by
    have := (abs_lt.mp h')
    have h1 : ((a - q.num : ℤ) : ℚ) < 1 := this.2
    have h2 : (-1 : ℚ) < ((a - q.num : ℤ) : ℚ) := this.1
    have h1' : (a - q.num : ℤ) < 1 := by exact_mod_cast h1
    have h2' : (-1 : ℤ) < (a - q.num : ℤ) := by exact_mod_cast h2
    omega
  have : a = q.num := by omega
  rw [this]

/-- Integer-valued rationals subtract to the cast of the numerator difference. -/
lemma rat_sub_eq_num_cast (a b : ℚ) (ha : a.den = 1) (hb : b.den = 1) :
    a - b = ((a.num - b.num : ℤ) : ℚ) := by
  conv_lhs => rw [← rat_eq_num_cast_of_den_one a ha, ← rat_eq_num_cast_of_den_one b hb]
  push_cast; ring

/-- A gap between distinct integer-valued rationals is at least one. -/
lemma rat_one_le_sub_of_lt (a b : ℚ) (ha : a.den = 1) (hb : b.den = 1) (h : b < a) :
    1 ≤ a - b := by
  rw [rat_sub_eq_num_cast a b ha hb]
  have hnum : b.num < a.num := by
    have h1 : ((b.num : ℤ) : ℚ) < ((a.num : ℤ) : ℚ) := by
      rw [rat_eq_num_cast_of_den_one a ha, rat_eq_num_cast_of_den_one b hb]; exact h
    exact_mod_cast h1
  have : (1 : ℤ) ≤ a.num - b.num := by omega
  exact_mod_cast this

/-! ## STAmount canonical-shape exactness

The `ExactCanonical` shape and its `toNumber` exactness lemmas
(`toNumber_integral_small_exact`, `toNumber_exact_canonical`) live upstream in
`STAmountToNumber`; this section adds the integral-magnitude facts on top. -/

/-- On a non-negative canonical integral amount the stored magnitude is the
value. -/
lemma STAmount.IntegralCanonical.mValue_eq_toRat_of_nonneg (s : STAmount)
    (hc : s.IntegralCanonical) (hnn : 0 ≤ s.toRat) :
    ((s.mValue.toNat : ℕ) : ℚ) = s.toRat := by
  by_cases h : s.mIsNegative = true
  · have hm0 : s.mValue.toNat = 0 := by
      rw [STAmount.IntegralCanonical.toRat_eq_signedDrops s hc] at hnn
      unfold STAmount.signedDrops at hnn
      rw [if_pos h] at hnn
      have h1 : (0 : ℤ) ≤ -(s.mValue.toNat : ℤ) := by exact_mod_cast hnn
      omega
    rw [STAmount.IntegralCanonical.toRat_eq_signedDrops s hc]
    unfold STAmount.signedDrops
    rw [if_pos h, hm0]
    norm_num
  · rw [STAmount.IntegralCanonical.toRat_eq_signedDrops s hc]
    unfold STAmount.signedDrops
    rw [if_neg h]
    norm_cast

/-- **`ofNumber .int64` record shape** on a non-negative integer-valued
normalized `Number` within `Int64`: the stored record is offset-`0`,
positive-signed, `.int64`-typed, and value-exact. -/
lemma STAmount.ofNumber_int64_shape (n : Number) (mode : rounding_mode) (sta : STAmount)
    (hn : n.isNormalized) (hnn : 0 ≤ n.toRat) (hden : n.toRat.den = 1)
    (hfit : n.toRat ≤ 2 ^ 63 - 1)
    (hok : STAmount.ofNumber .int64 n mode = .ok sta) :
    sta.mNumericType = .int64 ∧ sta.mOffset = 0 ∧ sta.mIsNegative = false ∧
      ((sta.mValue.toNat : ℕ) : ℚ) = n.toRat ∧ sta.toRat = n.toRat := by
  have hnegf : n.negative_ = false := Number.negative_false_of_nonneg n hn hnn
  have hsig : decide (n.signum < 0) = false := by
    unfold Number.signum
    rw [hnegf]
    simp only [Bool.false_eq_true, if_false]
    by_cases hm : (n.mantissa_ != 0) = true
    · rw [if_pos hm]; decide
    · rw [if_neg hm]; decide
  unfold STAmount.ofNumber at hok
  rw [hsig] at hok
  simp only [Bool.false_eq_true, if_false,
    show NumericType.int64.isIntegral = true from rfl, if_true] at hok
  cases hrep : n.to_rep mode with
  | error e => rw [hrep] at hok; simp at hok
  | ok rv =>
    rw [hrep] at hok
    simp only [] at hok
    have hexact : (rv.toInt : ℚ) = n.toRat :=
      int_cast_eq_of_abs_lt_one rv.toInt n.toRat hden (to_rep_within_one n mode rv hn hrep)
    have h0 : 0 ≤ rv.toInt := by
      have : (0 : ℚ) ≤ (rv.toInt : ℚ) := by rw [hexact]; exact hnn
      exact_mod_cast this
    have hhi : rv.toInt ≤ 2 ^ 63 - 1 := by
      have : (rv.toInt : ℚ) ≤ ((2 ^ 63 - 1 : ℤ) : ℚ) := by
        rw [hexact]; exact le_trans hfit (by norm_num)
      exact_mod_cast this
    have hu64 : (rv.toUInt64.toNat : ℤ) = rv.toInt := toUInt64_toNat_of_nonneg rv h0
    unfold STAmount.checked STAmount.canonicalize at hok
    rw [if_pos (show (STAmount.unchecked .int64 rv.toUInt64 0 false).integral = true
      from rfl)] at hok
    by_cases hz : (rv.toUInt64 == 0) = true
    · rw [if_pos (show ((STAmount.unchecked .int64 rv.toUInt64 0 false).mValue == 0 ||
          decide ((STAmount.unchecked .int64 rv.toUInt64 0 false).mOffset ≤ -20)) = true
          from by rw [show (STAmount.unchecked .int64 rv.toUInt64 0 false).mValue
            = rv.toUInt64 from rfl, hz]; rfl)] at hok
      have hsta : sta = { STAmount.unchecked .int64 rv.toUInt64 0 false with
          mValue := 0, mOffset := 0, mIsNegative := false } := (Except.ok.inj hok).symm
      have hval0 : n.toRat = 0 := by
        rw [← hexact, ← hu64, show rv.toUInt64 = 0 from by exact_mod_cast beq_iff_eq.mp hz]
        rfl
      subst hsta
      refine ⟨rfl, rfl, rfl, ?_, ?_⟩
      · rw [hval0]; rfl
      · rw [hval0]
        exact STAmount.toRat_zero_aux _ rfl rfl
    · rw [if_neg (show ¬ ((STAmount.unchecked .int64 rv.toUInt64 0 false).mValue == 0 ||
          decide ((STAmount.unchecked .int64 rv.toUInt64 0 false).mOffset ≤ -20)) = true
          from by
        rw [show (STAmount.unchecked .int64 rv.toUInt64 0 false).mValue = rv.toUInt64 from rfl,
          show (STAmount.unchecked .int64 rv.toUInt64 0 false).mOffset = (0 : Int) from rfl]
        rw [Bool.or_eq_true, not_or]
        exact ⟨by simpa using hz, by decide⟩)] at hok
      rw [if_neg (show ¬ (STAmount.unchecked .int64 rv.toUInt64 0 false).mOffset >
          (STAmount.unchecked .int64 rv.toUInt64 0 false).mNumericType.maxOffset
          from by show ¬ ((0 : Int) > (18 : Int)); decide)] at hok
      simp only [IntAmount.ofNumber] at hok
      cases hr2 : (Number.unchecked (STAmount.unchecked .int64 rv.toUInt64 0 false).mIsNegative
          (STAmount.unchecked .int64 rv.toUInt64 0 false).mValue
          (STAmount.unchecked .int64 rv.toUInt64 0 false).mOffset).to_rep mode with
      | error e => rw [hr2] at hok; simp at hok
      | ok r2 =>
        rw [hr2] at hok
        simp only [] at hok
        have hmaxrep : rv.toUInt64.toNat ≤ maxRep.toNat := by
          rw [maxRep_val]; omega
        have hkey := to_rep_exact_of_exponent_zero false rv.toUInt64 mode r2 hmaxrep hr2
        rw [if_neg (by exact Bool.false_ne_true)] at hkey
        have hr2v : r2.toInt = (rv.toUInt64.toNat : ℤ) := by
          have : (r2.toInt : ℚ) = ((rv.toUInt64.toNat : ℤ) : ℚ) := by
            rw [hkey]; push_cast; ring
          exact_mod_cast this
        have hna : r2.toInt.natAbs = rv.toUInt64.toNat := by omega
        have hvNat : r2.toInt.natAbs.toUInt64.toNat = r2.toInt.natAbs := by
          have hlt : r2.toInt.natAbs < 2 ^ 64 := by
            have := UInt64.toNat_lt_size rv.toUInt64
            omega
          exact UInt64.toNat_ofNat_of_lt hlt

        rw [if_neg (show ¬ (r2.toInt.natAbs.toUInt64 >
            (STAmount.unchecked .int64 rv.toUInt64 0 false).mNumericType.maxValue)
            from by
          show ¬ ((9223372036854775807 : UInt64) < r2.toInt.natAbs.toUInt64)
          rw [UInt64.lt_iff_toNat_lt, hvNat, hna,
            show (9223372036854775807 : UInt64).toNat = 9223372036854775807 from by decide]
          omega)] at hok

        have hnegr2 : decide (r2 < 0) = false := by
          rw [decide_eq_false_iff_not]
          intro hlt
          have h1 : r2.toInt < (0 : Int64).toInt := Int64.lt_iff_toInt_lt.mp hlt
          have h2 : (0 : Int64).toInt = 0 := by decide
          rw [h2, hr2v] at h1
          omega
        have hsta : sta = { mNumericType := NumericType.int64,
                            mValue := r2.toInt.natAbs.toUInt64, mOffset := 0,
                            mIsNegative := decide (r2 < 0) } :=
          (Except.ok.inj hok).symm
        subst hsta
        refine ⟨rfl, rfl, hnegr2, ?_, ?_⟩
        · show ((r2.toInt.natAbs.toUInt64.toNat : ℕ) : ℚ) = n.toRat
          rw [hvNat, hna, ← hexact, ← hu64]
          norm_cast
        · rw [STAmount.toRat_of_offset_zero _ rfl]
          unfold STAmount.signedDrops
          rw [show ({ mNumericType := NumericType.int64,
                      mValue := r2.toInt.natAbs.toUInt64, mOffset := 0,
                      mIsNegative := decide (r2 < 0) } : STAmount).mIsNegative
            = decide (r2 < 0) from rfl, hnegr2]
          simp only [Bool.false_eq_true, if_false]
          show ((r2.toInt.natAbs.toUInt64.toNat : ℤ) : ℚ) = n.toRat
          rw [hvNat, hna, ← hexact, ← hu64]

end XRPL.Model.Protocol
