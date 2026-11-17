import XRPL.Properties.Protocol.STAmount.Common.OfNumberBoundary
import XRPL.Properties.Protocol.STAmount.RoundToScale.Common.Proofs
import XRPL.Properties.Protocol.STAmount.Range.Common.Units

/-! # When rounding a Number to 16 digits gives an IOU amount

`IOUAmount.ofNumber` rounds a 19-digit Number to 16 digits and fails when the exponent of the result is above
80. `IOUAmount.ofNumber_ok_iff` says it returns a result exactly when the Number rounds into the IOU range. -/

namespace XRPL.Model.Protocol

/-- Rounding a 19-digit Number to 16 digits keeps the first 16 digits `q` or adds one to them. The exponent
goes up by 3, or by 4 when `q + 1` needs 17 digits. -/
lemma normalizeToRange_16_shape (n : Number) (mode : rounding_mode)
    (h_lo : 10 ^ 18 ≤ n.mantissa_.toNat) (h_hi : n.mantissa_.toNat < 10 ^ 19)
    (he_lo : minExponent ≤ n.exponent_ + 3) (he_hi : n.exponent_ + 4 ≤ maxExponent) :
    ∃ (up : Bool) (mant : Int64) (exp : Int),
      (up = true ↔ RoundsUp mode n.negative_ ((n.mantissa_.toNat / 1000 : ℕ) : ℤ)
        (((n.mantissa_.toNat % 1000 : ℕ) : ℚ) / 1000)) ∧
      n.normalizeToRange cMinValue cMaxValue mode = .ok (mant, exp) ∧
      (exp = n.exponent_ + 3 ∨ exp = n.exponent_ + 4) ∧
      (exp = n.exponent_ + 3 ↔
        ((n.mantissa_.toNat / 1000 : ℕ) : ℤ) + (if up = true then 1 else 0) ≤ 9999999999999999) := by
  obtain ⟨g, hrep, hsbit, -, h_red⟩ :=
    doNormalize_small_facts n.negative_ n.mantissa_ n.exponent_ mode h_lo h_hi he_lo (by omega)
  have hm3 : (n.mantissa_ / 10 / 10 / 10).toNat = n.mantissa_.toNat / 1000 :=
    m_div_thousand_toNat n.mantissa_
  have hcMax : cMaxValue.toNat = 10 ^ 16 - 1 := by decide
  have hcMin : cMinValue.toNat = 10 ^ 15 := by decide
  have hround := Guard.round_bool_iff hrep mode ((n.mantissa_ / 10 / 10 / 10) % 2 == 1)
    ((n.mantissa_.toNat / 1000 : ℕ) : ℤ) (by rw [UInt64.mod_two_beq_one_iff, hm3])
  rw [hsbit] at hround
  by_cases hb : (g.round mode == 1 || (g.round mode == 0 && (n.mantissa_ / 10 / 10 / 10) % 2 == 1)) = true
  · by_cases hcusp : n.mantissa_ / 10 / 10 / 10 = cMaxValue
    · -- the 16 digits are all nines, so adding one carries into the exponent
      have hbr : (g.round mode == 1 || (g.round mode == 0 && cMaxValue % 2 == 1)) = true := by
        rw [hcusp] at hb; exact hb
      have hcusp_eq := doRoundUp_small_cusp_eq g n.negative_ (n.exponent_ + 3) mode .normalize2 hbr (by omega)
      have hcompute : n.normalizeToRange cMinValue cMaxValue mode
          = .ok (if n.negative_ then -cMinValue.toInt64 else cMinValue.toInt64, (n.exponent_ + 3) + 1) := by
        unfold Number.normalizeToRange
        rw [h_red, hcusp, hcusp_eq, if_neg (by omega)]
        ntr_tail
      have hq : n.mantissa_.toNat / 1000 = 10 ^ 16 - 1 := by rw [← hm3, hcusp, hcMax]
      refine ⟨true, _, _, ⟨fun _ => hround.mp hb, fun _ => rfl⟩, hcompute, Or.inr (by ring), ?_⟩
      rw [hq]
      constructor
      · intro h; omega
      · intro h; simp at h
    · -- one is added in place
      have hlt : (n.mantissa_ / 10 / 10 / 10).toNat < cMaxValue.toNat := by
        have hne : (n.mantissa_ / 10 / 10 / 10).toNat ≠ cMaxValue.toNat :=
          fun h => hcusp (UInt64.toNat_inj.mp h)
        rw [hcMax, hm3] at hne ⊢
        omega
      have hcompute : n.normalizeToRange cMinValue cMaxValue mode
          = .ok (if n.negative_ then -(n.mantissa_ / 10 / 10 / 10 + 1).toInt64
                 else (n.mantissa_ / 10 / 10 / 10 + 1).toInt64, n.exponent_ + 3) := by
        unfold Number.normalizeToRange
        rw [h_red, doRoundUp_small_fire g n.negative_ _ (n.exponent_ + 3) mode
          .normalize2 hb (by rw [hcMin, hm3]; omega) hlt (by omega) (by omega)]
        ntr_tail
      refine ⟨true, _, _, ⟨fun _ => hround.mp hb, fun _ => rfl⟩, hcompute, Or.inl rfl, ?_⟩
      rw [hcMax, hm3] at hlt
      simp only [if_true, true_iff]
      omega
  · -- the 16 digits are kept
    have hcompute : n.normalizeToRange cMinValue cMaxValue mode
        = .ok (if n.negative_ then -(n.mantissa_ / 10 / 10 / 10).toInt64
               else (n.mantissa_ / 10 / 10 / 10).toInt64, n.exponent_ + 3) := by
      unfold Number.normalizeToRange
      rw [h_red, doRoundUp_small_truncate g n.negative_ _ (n.exponent_ + 3) mode
        .normalize2 (by simpa using hb) (by rw [hcMin, hm3]; omega)
        (by rw [hcMax, hm3]; omega) (by omega) (by omega)]
      ntr_tail
    refine ⟨false, _, _, ⟨fun h => absurd h (by decide), fun h => absurd (hround.mpr h) hb⟩, hcompute,
      Or.inl rfl, ?_⟩
    simp only [Bool.false_eq_true, if_false, add_zero, true_iff]
    omega

/-- Once the 16-digit rounding has a result, `IOUAmount.ofNumber` only checks that the exponent is at most 80. -/
lemma IOUAmount.ofNumber_ok_iff_of_norm (n : Number) (mode : rounding_mode) (mant : Int64) (exp : Int)
    (h : n.normalizeToRange cMinValue cMaxValue mode = .ok (mant, exp)) :
    (∃ r, IOUAmount.ofNumber n mode = .ok r) ↔ exp ≤ cMaxOffset := by
  unfold IOUAmount.ofNumber IOUAmount.fromNumber
  rw [h]
  dsimp only
  by_cases hhi : exp > cMaxOffset
  · rw [if_pos hhi]
    exact iff_of_false (by simp) (by omega)
  · rw [if_neg hhi]
    refine iff_of_true ?_ (by omega)
    split <;> exact ⟨_, rfl⟩

/-- The value of a 19-digit Number as its first 16 digits plus a fraction, in units of `10 ^ (exponent + 3)`. -/
lemma Number.toRat_eq_units16 (n : Number) :
    n.toRat = (if n.negative_ = true then (-1 : ℚ) else 1) *
      (((n.mantissa_.toNat / 1000 : ℕ) : ℤ) + ((n.mantissa_.toNat % 1000 : ℕ) : ℚ) / 1000) *
        (10 : ℚ) ^ (n.exponent_ + 3) := by
  have hdm : (n.mantissa_.toNat : ℚ)
      = 1000 * ((n.mantissa_.toNat / 1000 : ℕ) : ℚ) + ((n.mantissa_.toNat % 1000 : ℕ) : ℚ) := by
    exact_mod_cast (Nat.div_add_mod n.mantissa_.toNat 1000).symm
  have hpow : (10 : ℚ) ^ (n.exponent_ + 3) = (10 : ℚ) ^ n.exponent_ * 1000 := by
    rw [zpow_add₀ (by norm_num : (10 : ℚ) ≠ 0)]
    norm_num
  rw [hpow, Int.cast_natCast]
  rcases hb : n.negative_ with _ | _
  · rw [Number.toRat_of_nonneg n hb, hdm]
    simp only [Bool.false_eq_true, if_false]
    ring
  · rw [Number.toRat_of_neg n hb, hdm]
    simp only [if_true]
    ring

/-- The size of a 19-digit Number is between `10^15` and `10^16` units of `10 ^ (exponent + 3)`. -/
lemma Number.abs_toRat_units16_bounds (n : Number) (h_lo : 10 ^ 18 ≤ n.mantissa_.toNat)
    (h_hi : n.mantissa_.toNat < 10 ^ 19) :
    (10 : ℚ) ^ 15 * (10 : ℚ) ^ (n.exponent_ + 3) ≤ |n.toRat| ∧
      |n.toRat| < (10 : ℚ) ^ 16 * (10 : ℚ) ^ (n.exponent_ + 3) := by
  have hpow : (10 : ℚ) ^ (n.exponent_ + 3) = (10 : ℚ) ^ n.exponent_ * 1000 := by
    rw [zpow_add₀ (by norm_num : (10 : ℚ) ≠ 0)]
    norm_num
  have hp : (0 : ℚ) < (10 : ℚ) ^ n.exponent_ := zpow_pos (by norm_num) _
  have h1 : (10 : ℚ) ^ 18 ≤ (n.mantissa_.toNat : ℚ) := by exact_mod_cast h_lo
  have h2 : (n.mantissa_.toNat : ℚ) < (10 : ℚ) ^ 19 := by exact_mod_cast h_hi
  rw [abs_toRat_eq n, hpow]
  constructor <;> nlinarith

/-- Rounding a normalized Number to an IOU amount returns a result exactly when the Number rounds into the IOU
range. -/
lemma IOUAmount.ofNumber_ok_iff (n : Number) (mode : rounding_mode) (hn : n.isNormalized) :
    (∃ r, IOUAmount.ofNumber n mode = .ok r) ↔ STAmount.RoundsInRange .fractional mode n.toRat := by
  rw [STAmount.roundsInRange_fractional_iff]
  have hu80 : (0 : ℚ) < (10 : ℚ) ^ (80 : ℤ) := zpow_pos (by norm_num) _
  by_cases hm0 : n.mantissa_ = 0
  · -- zero
    rw [IOUAmount.ofNumber_zero_mantissa n mode hm0, Number.toRat_eq_zero_of_mantissa_zero n hm0]
    exact iff_of_true ⟨_, rfl⟩ (roundsWithinUnits_of_abs_le mode _ _ _ hu80 (by rw [abs_zero]; positivity))
  obtain ⟨h_lo, h_hi⟩ := mantissaBounds_nat_of (hn.mantissaBounds hm0)
  have hemin : minExponent ≤ n.exponent_ := by
    rcases hn with hz | ⟨_, _, _, h, _⟩
    · exact absurd (by rw [hz]; rfl) hm0
    · exact h
  obtain ⟨habs_lo, habs_hi⟩ := Number.abs_toRat_units16_bounds n h_lo h_hi
  by_cases hbig : 80 < n.exponent_ + 3
  · -- the exponent of the result is above 80, and the value is at least `10^96`
    refine iff_of_false ?_ (not_roundsWithinUnits_of_le_abs mode _ _ _ hu80 ?_)
    · rintro ⟨r, hr⟩
      unfold IOUAmount.ofNumber IOUAmount.fromNumber at hr
      cases hnorm : n.normalizeToRange cMinValue cMaxValue mode with
      | error err => rw [hnorm] at hr; exact absurd hr (by simp)
      | ok me =>
        obtain ⟨mant, exp⟩ := me
        rw [hnorm] at hr
        dsimp only at hr
        have hexp3 := normalizeToRange_iou_exp_hi n mode mant exp h_lo h_hi hnorm
        obtain ⟨-, ⟨hexp_lo, -⟩, -⟩ :=
          normalizeToRange_iou_ok_facts n mode mant exp h_lo h_hi (by omega) hexp3 hnorm
        rw [if_pos (by unfold cMaxOffset; omega)] at hr
        exact absurd hr (by simp)
    · have hpow : (10 : ℚ) ^ (81 : ℤ) ≤ (10 : ℚ) ^ (n.exponent_ + 3) :=
        zpow_le_zpow_right₀ (by norm_num) (by omega)
      have h81 : (10 : ℚ) ^ (81 : ℤ) = 10 * (10 : ℚ) ^ (80 : ℤ) := by norm_num
      rw [h81] at hpow
      push_cast
      nlinarith
  · obtain ⟨up, mant, exp, hup, hnorm, hexp_cases, hexp_iff⟩ :=
      normalizeToRange_16_shape n mode h_lo h_hi (by omega) (by unfold maxExponent; omega)
    rw [IOUAmount.ofNumber_ok_iff_of_norm n mode mant exp hnorm]
    by_cases htop : n.exponent_ + 3 = 80
    · -- at the largest exponent the result fits exactly when the 16 digits do not carry
      have hf0 : (0 : ℚ) ≤ ((n.mantissa_.toNat % 1000 : ℕ) : ℚ) / 1000 := by positivity
      have hf1 : ((n.mantissa_.toNat % 1000 : ℕ) : ℚ) / 1000 < 1 := by
        rw [div_lt_one (by norm_num)]
        exact_mod_cast Nat.mod_lt n.mantissa_.toNat (by norm_num)
      rw [Number.toRat_eq_units16 n, htop,
        ← roundsWithinUnits_iff mode n.negative_ _ 9999999999999999 _ _ up (by positivity) hf0 hf1 hu80 hup]
      unfold cMaxOffset
      omega
    · -- below the largest exponent the result always fits
      refine iff_of_true (by unfold cMaxOffset; omega)
        (roundsWithinUnits_of_abs_le mode _ _ _ hu80 ?_)
      have hpow : (10 : ℚ) ^ (n.exponent_ + 3) ≤ (10 : ℚ) ^ (79 : ℤ) :=
        zpow_le_zpow_right₀ (by norm_num) (by omega)
      have hpos : (0 : ℚ) < (10 : ℚ) ^ (n.exponent_ + 3) := zpow_pos (by norm_num) _
      have h80 : (10 : ℚ) ^ (80 : ℤ) = 10 * (10 : ℚ) ^ (79 : ℤ) := by norm_num
      rw [h80]
      push_cast
      nlinarith

end XRPL.Model.Protocol
