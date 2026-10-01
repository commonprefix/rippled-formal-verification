import XRPL.Model.Protocol.Rounding
import XRPL.Properties.Protocol.Number.Compare.Compare
import XRPL.Properties.Protocol.Number.Common.Constants
import XRPL.Properties.Protocol.Number.Common.ToRatLemmas
import XRPL.Properties.Protocol.Number.Common.Closest.Tightness
import XRPL.Properties.Protocol.Number.Common.Closest.GridPoint
import XRPL.Properties.Protocol.Number.Constructors.FromRepExact
import XRPL.Properties.Protocol.Number.Sub.RoundsToRepresentable
import XRPL.Properties.Protocol.Number.Sub.ZeroShape
import XRPL.Properties.Protocol.Number.Totality

/-! # Amounts held at an exponent

`Number.isAtExponent value exponent nt` says `value` is a whole number of units at `exponent`, with a unit count an
STAmount of the type can carry. This file gives its exact reading (`Number.AtExponent`) and the
consequence the lending invariants rest on: a `to_nearest` subtraction of two such amounts is total
and exact while the difference stays below `2^63` units. -/

namespace XRPL.Model.Protocol

/-- The exact reading of `Number.isAtExponent`: a whole number of units at the exponent, below the bound. -/
def Number.AtExponent (value : ℚ) (exponent : Int) (bound : ℕ) : Prop :=
  ∃ m : ℕ, m < bound ∧ value = (m : ℚ) * (10 : ℚ) ^ exponent

lemma NumericType.mantissaBound_pos (nt : NumericType) : 0 < nt.mantissaBound := by
  unfold NumericType.mantissaBound; split <;> positivity

lemma NumericType.mantissaBound_le (nt : NumericType) : nt.mantissaBound ≤ 2 ^ 63 := by
  cases nt with
  | fractional => norm_num [NumericType.mantissaBound]
  | integral mv _ _ _ =>
    show min mv.toNat maxRep.toNat + 1 ≤ 2 ^ 63
    have h : maxRep.toNat = 9223372036854775807 := by decide
    have h2 := Nat.min_le_right mv.toNat maxRep.toNat
    have h3 : (2 : ℕ) ^ 63 = 9223372036854775808 := by norm_num
    rw [h3]; omega

private lemma zero_norm : (Number.zero).isNormalized := Or.inl rfl

/-- A normalized nonnegative `Number` has a clear sign bit. -/
private lemma neg_false_of_nonneg (n : Number) (hn : n.isNormalized) (h0 : 0 ≤ n.toRat) :
    n.negative_ = false := by
  by_contra hb
  have hb' : n.negative_ = true := by simpa using hb
  have hle := Number.toRat_nonpos_of_negative n hb'
  have hm0 : n.mantissa_ = 0 := Number.toRat_eq_zero_iff.mp (le_antisymm hle h0)
  rw [Number.eq_zero_of_mantissa_zero n hn hm0] at hb'; exact absurd hb' (by decide)

/-- Every integer count below `2^63` units at a scale with exponent room is a normalized `Number`. -/
lemma Number.exists_normalized_int_mul_pow (a : ℤ) (s : Int)
    (ha : -2 ^ 63 < a ∧ a < 2 ^ 63) (hs : minExponent + 18 ≤ s ∧ s ≤ maxExponent - 1) :
    ∃ w : Number, w.isNormalized ∧ w.toRat = (a : ℚ) * (10 : ℚ) ^ s := by
  have hval : (Int64.ofInt a).toInt = a := by
    rw [Int64.toInt_ofInt]
    exact Int.bmod_eq_of_le (by simp [Int64.size]; omega) (by simp [Int64.size]; omega)
  have hne : Int64.ofInt a ≠ Int64.minValue := by
    intro h
    have h' : (Int64.ofInt a).toInt = Int64.minValue.toInt := by rw [h]
    rw [hval, show Int64.minValue.toInt = -2 ^ 63 from by decide] at h'
    omega
  obtain ⟨w, _, hw, hnorm⟩ := Number.from_rep_exact (Int64.ofInt a) s .to_nearest hne hs.1 hs.2
  exact ⟨w, hnorm, by rw [hw, hval]⟩

/-- A `to_nearest` rounding of a representable value is that value. -/
lemma Number.roundsToRepresentable_eq (d : Number) (truth : ℚ)
    (hR : d.RoundsToRepresentable truth .to_nearest) (w : Number) (hw : w.isNormalized)
    (hwt : w.toRat = truth) : d.toRat = truth := by
  by_cases h0 : truth = 0
  · subst h0
    rcases hR with ⟨n, hn, hd⟩ | ⟨n, hn, hd⟩
    · unfold Number.lower at hn; rw [if_pos rfl] at hn
      rw [hd, ← Option.some.inj hn, Number.toRat_zero]
    · unfold Number.upper at hn; rw [if_pos rfl] at hn
      rw [hd, ← Option.some.inj hn, Number.toRat_zero]
  · have hwne : w.toRat ≠ 0 := by rw [hwt]; exact h0
    rcases hR with ⟨n, hn, hd⟩ | ⟨n, hn, hd⟩
    · obtain ⟨n', hn', hval⟩ := Number.lower_value_self w hw hwne
      rw [hwt] at hn' hval
      have hnn : n = n' := Option.some.inj (hn.symm.trans hn')
      rw [hd, hnn]; exact hval.symm
    · obtain ⟨n', hn', hval⟩ := Number.upper_value_self w hw hwne
      rw [hwt] at hn' hval
      have hnn : n = n' := Option.some.inj (hn.symm.trans hn')
      rw [hd, hnn]; exact hval.symm

/-- A `to_nearest` rounding never lands above a representable value that bounds the truth. -/
lemma Number.roundsToRepresentable_le (d : Number) (truth : ℚ)
    (hR : d.RoundsToRepresentable truth .to_nearest) (w : Number) (hw : w.isNormalized)
    (hwt : truth ≤ w.toRat) : d.toRat ≤ w.toRat := by
  rcases hR with ⟨n, hn, hd⟩ | ⟨n, hn, hd⟩
  · rw [hd]; exact (Number.lower_le truth n hn).trans hwt
  · rw [hd]; exact Number.upper_tight truth n hn w hw hwt

/-- A nonzero normalized nonnegative `Number` below `10^19` units at a scale has its exponent at
most the scale: its 19-digit mantissa cannot sit any higher. -/
lemma Number.exponent_le_of_toRat_lt_of_ne (n : Number) (s : Int) (hn : n.isNormalized)
    (hneg : n.negative_ = false) (hm0 : n.mantissa_ ≠ 0)
    (hlt : n.toRat < (10 : ℚ) ^ (19 : ℕ) * (10 : ℚ) ^ s) : n.exponent_ ≤ s := by
  rcases hn with hz | ⟨hmin, _, _, _, _⟩
  · exact absurd (by rw [hz]; rfl) hm0
  · have hval := Number.toRat_of_nonneg n hneg
    have hmant : (10 : ℚ) ^ (18 : ℕ) ≤ (n.mantissa_.toNat : ℚ) := by
      have h1 : largeRange.min.toNat ≤ n.mantissa_.toNat := UInt64.le_iff_toNat_le.mp hmin
      have h2 : largeRange.min.toNat = 10 ^ 18 := largeRange_min_val
      exact_mod_cast h2 ▸ h1
    have hpos : (0 : ℚ) < (10 : ℚ) ^ n.exponent_ := zpow_pos (by norm_num) _
    have h3 : (10 : ℚ) ^ (18 : ℕ) * (10 : ℚ) ^ n.exponent_ < (10 : ℚ) ^ (19 : ℕ) * (10 : ℚ) ^ s := by
      calc (10 : ℚ) ^ (18 : ℕ) * (10 : ℚ) ^ n.exponent_
          ≤ (n.mantissa_.toNat : ℚ) * (10 : ℚ) ^ n.exponent_ := by
            exact mul_le_mul_of_nonneg_right hmant hpos.le
        _ = n.toRat := hval.symm
        _ < _ := hlt
    have h4 : (10 : ℚ) ^ n.exponent_ < (10 : ℚ) ^ (s + 1) := by
      rw [zpow_add_one₀ (by norm_num : (10 : ℚ) ≠ 0)]
      have h3' : (10 : ℚ) ^ (18 : ℕ) * (10 : ℚ) ^ n.exponent_ <
          (10 : ℚ) ^ (18 : ℕ) * ((10 : ℚ) ^ s * 10) := by
        have h19 : (10 : ℚ) ^ (19 : ℕ) * (10 : ℚ) ^ s = (10 : ℚ) ^ (18 : ℕ) * ((10 : ℚ) ^ s * 10) := by
          ring
        linarith [h3, h19]
      exact lt_of_mul_lt_mul_left h3' (by positivity)
    have := (zpow_lt_zpow_iff_right₀ (by norm_num : (1 : ℚ) < 10)).mp h4
    omega

/-- The same bound for any normalized nonnegative `Number`, given the scale is in exponent range. -/
lemma Number.exponent_le_of_toRat_lt (n : Number) (s : Int) (hn : n.isNormalized)
    (hneg : n.negative_ = false) (hs : minExponent + 18 ≤ s)
    (hlt : n.toRat < (10 : ℚ) ^ (19 : ℕ) * (10 : ℚ) ^ s) : n.exponent_ ≤ s := by
  by_cases hm0 : n.mantissa_ = 0
  · rw [Number.eq_zero_of_mantissa_zero n hn hm0]
    show (-2147483648 : Int) ≤ s
    unfold minExponent at hs; omega
  · exact Number.exponent_le_of_toRat_lt_of_ne n s hn hneg hm0 hlt

/-- `Number.isAtExponent` read exactly, for a normalized nonnegative amount. -/
theorem Number.isAtExponent_iff (value : Number) (exponent : Int) (nt : NumericType) (hn : value.isNormalized)
    (hnn : 0 ≤ value.toRat) :
    value.isAtExponent exponent nt = true ↔ Number.AtExponent value.toRat exponent nt.mantissaBound := by
  unfold Number.isAtExponent Number.AtExponent
  simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq]
  by_cases hz : value = Number.zero
  · subst hz
    simp only [true_or, true_iff]
    exact ⟨0, NumericType.mantissaBound_pos nt, by rw [Number.toRat_zero]; simp⟩
  · have hm0 : value.mantissa_ ≠ 0 := fun h => hz (Number.eq_zero_of_mantissa_zero value hn h)
    have hneg : value.negative_ = false := neg_false_of_nonneg value hn hnn
    have hval := Number.toRat_of_nonneg value hneg
    have hten : (10 : ℚ) ≠ 0 := by norm_num
    constructor
    · rintro (h | ⟨⟨hshift, hdiv⟩, hlt⟩)
      · exact absurd h hz
      · set k := (exponent - value.exponent_).toNat with hk
        have hkz : (k : Int) = exponent - value.exponent_ := by rw [hk]; exact Int.toNat_of_nonneg hshift
        refine ⟨value.mantissa_.toNat / 10 ^ k, hlt, ?_⟩
        have hdvd : 10 ^ k ∣ value.mantissa_.toNat := Nat.dvd_of_mod_eq_zero hdiv
        have hmul : (value.mantissa_.toNat / 10 ^ k) * 10 ^ k = value.mantissa_.toNat := Nat.div_mul_cancel hdvd
        rw [hval]
        have hmq : (value.mantissa_.toNat : ℚ) = ((value.mantissa_.toNat / 10 ^ k : ℕ) : ℚ) * (10 : ℚ) ^ (k : ℤ) := by
          rw [zpow_natCast]; exact_mod_cast hmul.symm
        rw [hmq, mul_assoc, ← zpow_add₀ hten, hkz]; congr 2; ring
    · rintro ⟨m, hm, hmv⟩
      right
      have hm0' : m ≠ 0 := by
        rintro rfl
        apply hz
        apply Number.eq_zero_of_mantissa_zero value hn
        apply Number.toRat_eq_zero_iff.mp
        rw [hmv]; simp
      have hbound : (m : ℚ) < (10 : ℚ) ^ (19 : ℕ) := by
        have h1 : m < 2 ^ 63 := lt_of_lt_of_le hm (NumericType.mantissaBound_le nt)
        have h2 : (m : ℚ) < (2 : ℚ) ^ 63 := by exact_mod_cast h1
        linarith [show (2 : ℚ) ^ 63 < (10 : ℚ) ^ (19 : ℕ) by norm_num]
      -- the exponent cannot exceed the exponent, or the mantissa alone would overshoot the count
      have hexp : value.exponent_ ≤ exponent :=
        Number.exponent_le_of_toRat_lt_of_ne value exponent hn hneg hm0 (by
          calc value.toRat = (m : ℚ) * (10 : ℚ) ^ exponent := hmv
            _ < (10 : ℚ) ^ (19 : ℕ) * (10 : ℚ) ^ exponent :=
              mul_lt_mul_of_pos_right hbound (zpow_pos (by norm_num) _))
      set k := (exponent - value.exponent_).toNat with hk
      have hshift : 0 ≤ exponent - value.exponent_ := by omega
      have hkz : (k : Int) = exponent - value.exponent_ := by rw [hk]; exact Int.toNat_of_nonneg hshift
      -- mantissa = m · 10^k as naturals
      have hmant_eq : value.mantissa_.toNat = m * 10 ^ k := by
        have h1 : (value.mantissa_.toNat : ℚ) * (10 : ℚ) ^ value.exponent_ = (m : ℚ) * (10 : ℚ) ^ exponent := by
          rw [← hval, hmv]
        have h2 : (10 : ℚ) ^ exponent = (10 : ℚ) ^ (k : ℤ) * (10 : ℚ) ^ value.exponent_ := by
          rw [← zpow_add₀ hten, hkz]; congr 1; ring
        rw [h2, ← mul_assoc] at h1
        have hpos : (0 : ℚ) < (10 : ℚ) ^ value.exponent_ := zpow_pos (by norm_num) _
        have h3 : (value.mantissa_.toNat : ℚ) = (m : ℚ) * (10 : ℚ) ^ (k : ℤ) :=
          mul_right_cancel₀ hpos.ne' h1
        rw [zpow_natCast] at h3
        exact_mod_cast h3
      refine ⟨⟨hshift, ?_⟩, ?_⟩
      · rw [hmant_eq]; exact Nat.mul_mod_left m (10 ^ k)
      · rw [hmant_eq, Nat.mul_div_cancel m (by positivity)]; exact hm

/-- A successful `to_nearest` subtraction of two whole-unit amounts at one scale is exact while the
difference stays below `2^63` units. -/
lemma Number.operator_sub_toRat_of_grid (x y d : Number) (a b : ℤ) (s : Int)
    (hx : x.isNormalized) (hy : y.isNormalized)
    (hxv : x.toRat = (a : ℚ) * (10 : ℚ) ^ s) (hyv : y.toRat = (b : ℚ) * (10 : ℚ) ^ s)
    (hab : -2 ^ 63 < a - b ∧ a - b < 2 ^ 63) (hs : minExponent + 18 ≤ s ∧ s ≤ maxExponent - 1)
    (hok : x.operator_sub y .to_nearest = .ok d) :
    d.toRat = ((a - b : ℤ) : ℚ) * (10 : ℚ) ^ s := by
  have hR := operator_sub_rounded_to_nearest x y d hx hy hok
  obtain ⟨w, hw, hwt⟩ := Number.exists_normalized_int_mul_pow (a - b) s hab hs
  have htruth : x.toRat - y.toRat = ((a - b : ℤ) : ℚ) * (10 : ℚ) ^ s := by
    rw [hxv, hyv]; push_cast; ring
  rw [htruth] at hR
  exact Number.roundsToRepresentable_eq d _ hR w hw hwt

/-- Subtracting two nonnegative whole-unit amounts at an STAmount scale always succeeds. -/
lemma Number.operator_sub_ok_of_grid (x y : Number) (a b : ℕ) (s : Int)
    (hx : x.isNormalized) (hy : y.isNormalized)
    (hxv : x.toRat = (a : ℚ) * (10 : ℚ) ^ s) (hyv : y.toRat = (b : ℚ) * (10 : ℚ) ^ s)
    (ha : a < 2 ^ 63) (hb : b < 2 ^ 63) (hs : cMinOffset ≤ s ∧ s ≤ cMaxOffset) :
    ∃ d, x.operator_sub y .to_nearest = .ok d := by
  have hs' : minExponent + 18 ≤ s := by have := hs.1; unfold cMinOffset at this; unfold minExponent; omega
  have hpos : (0 : ℚ) < (10 : ℚ) ^ s := zpow_pos (by norm_num) _
  have hxnn : 0 ≤ x.toRat := by rw [hxv]; positivity
  have hynn : 0 ≤ y.toRat := by rw [hyv]; positivity
  have hxneg := neg_false_of_nonneg x hx hxnn
  have hyneg := neg_false_of_nonneg y hy hynn
  have hbig : ((2 : ℚ) ^ 63) < (10 : ℚ) ^ (19 : ℕ) := by norm_num
  have hxe : x.exponent_ ≤ s := by
    apply Number.exponent_le_of_toRat_lt x s hx hxneg hs'
    rw [hxv]
    have : (a : ℚ) < (10 : ℚ) ^ (19 : ℕ) := by
      have : (a : ℚ) < (2 : ℚ) ^ 63 := by exact_mod_cast ha
      linarith
    exact mul_lt_mul_of_pos_right this hpos
  have hye : y.exponent_ ≤ s := by
    apply Number.exponent_le_of_toRat_lt y s hy hyneg hs'
    rw [hyv]
    have : (b : ℚ) < (10 : ℚ) ^ (19 : ℕ) := by
      have : (b : ℚ) < (2 : ℚ) ^ 63 := by exact_mod_cast hb
      linarith
    exact mul_lt_mul_of_pos_right this hpos
  have hsmax := hs.2
  unfold cMaxOffset at hsmax
  exact Number.operator_sub_ok_of_normalized_exp x y .to_nearest hx hy hxneg hyneg
    (by unfold maxExponent; omega) (by unfold maxExponent; omega)

end XRPL.Model.Protocol
